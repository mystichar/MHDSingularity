import NavierStokes.MagneticPeriodicCoefficient
import Mathlib.Analysis.Calculus.DerivativeTest

/-! A scalar maximum principle on the physical periodic cover. Time
derivatives are required only in the open forward interval. The scalar
operators below differentiate slices, just as the vector PDE operators do. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Slice
open Set Filter ProblemStatement
open scoped Topology ContDiff

def time (q : SpaceTime → ℝ) (t : ℝ) (x : Space) : ℝ :=
  deriv (fun s => q (s,x)) t

def gradient (q : SpaceTime → ℝ) (t : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  fderiv ℝ (fun y => q (t,y)) x

def laplacian (q : SpaceTime → ℝ) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => gradient q t y (coordinateVector i)) x (coordinateVector i)

def operator (u : VelocityField) (eta_m : ℝ) (q : SpaceTime → ℝ)
    (t : ℝ) (x : Space) : ℝ :=
  time q t x + gradient q t x (u (t,x)) - eta_m * laplacian q t x

/-- The sign of the derivative at a maximum over past times. -/
theorem time_nonneg_at_past_max {f : ℝ → ℝ} {a t : ℝ} (hat : a < t)
    (hd : DifferentiableAt ℝ f t) (hm : ∀ s ∈ Icc a t, f s ≤ f t) :
    0 ≤ deriv f t := by
  apply ge_of_tendsto (hd.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t))
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds hat)] with s hs has
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hm s ⟨has.le,hs.le⟩)) (sub_nonpos.mpr hs.le)

/-- The elementary second derivative sign, obtained without assuming that
the derivative of a spatial supremum exists. -/
theorem second_deriv_nonpos_at_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hmin := isLocalMin_of_deriv_deriv_pos (lt_of_not_ge hn) hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm,hmin] with y hy hy'
    exact le_antisymm hy hy'
  have he' := he.deriv
  have he'' := he'.deriv_eq
  have hz : deriv (deriv f) x = 0 := by simpa using he''
  exact hn hz.le

theorem second_direction_nonpos {f : Space → ℝ} (hf : ContDiff ℝ 2 f)
    {x : Space} (hm : ∀ y, f y ≤ f x) (v : Space) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v ≤ 0 := by
  let g : ℝ → ℝ := fun s => f (x+s • v)
  have hd (s : ℝ) : HasDerivAt g (fderiv ℝ f (x+s • v) v) s := by
    convert! ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const v))) using 1; simp
  have he : deriv g = fun s => fderiv ℝ f (x+s • v) v := funext (fun s => (hd s).deriv)
  have hG : Differentiable ℝ (fun y => fderiv ℝ f y v) :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => x+s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1; simp
  have hd2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • v) v)
      (fderiv ℝ (fun y => fderiv ℝ f y v) x v) 0 := by
    convert! (hG (x+(0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hline using 1; simp
  have hm' : IsLocalMax g 0 := Eventually.of_forall (fun s => by simpa [g] using hm (x+s • v))
  have hs := second_deriv_nonpos_at_max hm' (hd 0).continuousAt
  rw [he] at hs
  rwa [hd2.deriv] at hs

theorem laplacian_nonpos_at_max {q : SpaceTime → ℝ} {t : ℝ}
    (hq : ContDiff ℝ 2 (fun y => q (t,y))) {x : Space}
    (hm : ∀ y, q (t,y) ≤ q (t,x)) : laplacian q t x ≤ 0 :=
  Finset.sum_nonpos (fun i _ => second_direction_nonpos hq hm (coordinateVector i))

/-- A strict maximum principle. A spatial cell maximizer is a global
spatial maximizer because of the actual unit-coordinate periods. -/
theorem nonpos_of_strict {q : SpaceTime → ℝ} {u : VelocityField} {a b eta_m : ℝ}
    (heta : 0 ≤ eta_m)
    (hc : ContinuousOn q (Icc a b ×ˢ univ))
    (hp : UnitSpatialPeriodsOn (Icc a b) q)
    (htd : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => q (s,x)) t)
    (hxd : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => q (t,x)))
    (hineq : ∀ t ∈ Ioo a b, ∀ x, operator u eta_m q t x < 0)
    (hi : ∀ x, q (a,x) ≤ 0) {t : ℝ} (ht : t ∈ Ico a b) (x : Space) :
    q (t,x) ≤ 0 := by
  by_contra hn
  have hpos : 0 < q (t,x) := lt_of_not_ge hn
  let cell := Icc a t ×ˢ CompactForceDecay.unitCube
  have hcell : IsCompact cell := isCompact_Icc.prod CompactForceDecay.isCompact_unitCube
  have hsub : cell ⊆ Icc a b ×ˢ (univ : Set Space) :=
    fun z hz => ⟨⟨hz.1.1,hz.1.2.trans ht.2.le⟩,mem_univ _⟩
  obtain ⟨z,hz,hm⟩ := hcell.exists_isMaxOn
    ⟨(a,CompactForceDecay.fractionalPoint x), ⟨⟨le_rfl,ht.1⟩,
      CompactForceDecay.fractionalPoint_mem_unitCube x⟩⟩ (hc.mono hsub)
  have hmax (s : ℝ) (hs : s ∈ Icc a t) (y : Space) : q (s,y) ≤ q z := by
    rw [← MagneticPeriodicCoefficient.fractional_eq
      (fun p : Unit × Space => q (s,p.2))
      (fun _ y i => hp s ⟨hs.1,hs.2.trans ht.2.le⟩ y i) () y]
    exact hm ⟨hs,CompactForceDecay.fractionalPoint_mem_unitCube y⟩
  have hzpos : 0 < q z := hpos.trans_le (hmax t ⟨ht.1,le_rfl⟩ x)
  have hza : a < z.1 := lt_of_le_of_ne hz.1.1 (by
    intro he
    have hh := hi z.2
    rw [he] at hh
    exact (not_lt_of_ge hh) hzpos)
  have hzi : z.1 ∈ Ioo a b := ⟨hza,hz.1.2.trans_lt ht.2⟩
  have hxmax : ∀ y, q (z.1,y) ≤ q z := hmax z.1 hz.1
  have hgrad : gradient q z.1 z.2 = 0 :=
    (show IsLocalMax (fun y => q (z.1,y)) z.2 from Eventually.of_forall hxmax).fderiv_eq_zero
  have htime := time_nonneg_at_past_max hza (htd z.1 hzi z.2)
    (fun s hs => hmax s ⟨hs.1,hs.2.trans hz.1.2⟩ z.2)
  have hlap := laplacian_nonpos_at_max (hxd z.1 hzi) hxmax
  have hh := hineq z.1 hzi z.2
  simp only [operator,hgrad,zero_apply] at hh
  have := mul_nonpos_of_nonneg_of_nonpos heta hlap
  change 0 ≤ time q z.1 z.2 at htime
  linarith

/-- Slice calculus for a time-dependent affine scalar transformation. -/
theorem operator_affine {q : SpaceTime → ℝ} {u : VelocityField} {eta_m t : ℝ}
    {w v : ℝ → ℝ} {w' v' : ℝ} (hw : HasDerivAt w w' t) (hv : HasDerivAt v v' t)
    (ht : DifferentiableAt ℝ (fun s => q (s,x)) t)
    (hx : ContDiff ℝ 2 (fun y => q (t,y))) :
    operator u eta_m (fun z => w z.1 * q z + v z.1) t x =
      w t * operator u eta_m q t x + w' * q (t,x) + v' := by
  have htime := ((hw.mul ht.hasDerivAt).add hv).deriv
  have hgrad (y : Space) : gradient (fun z => w z.1 * q z + v z.1) t y =
      w t • gradient q t y := by
    exact (((hx.differentiable (by norm_num) y).hasFDerivAt.const_mul (w t)).add_const (v t)).fderiv
  have hlap : laplacian (fun z => w z.1 * q z + v z.1) t x = w t * laplacian q t x := by
    unfold laplacian
    simp only [hgrad,smul_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hd := (((hx.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      (contDiff_const (c := coordinateVector i))).differentiable (by norm_num) x).hasFDerivAt.const_mul (w t)
    unfold gradient
    rw [hd.fderiv]
    rfl
  change deriv (fun s => w s * q (s,x) + v s) t = _ at htime
  unfold operator time
  dsimp only
  rw [htime,hgrad,hlap]
  simp only [smul_apply,smul_eq_mul]
  ring

/-- Weak maximum principle, including both endpoints by continuity. -/
theorem nonpos {q : SpaceTime → ℝ} {u : VelocityField} {a b eta_m : ℝ}
    (hab : a < b) (heta : 0 ≤ eta_m)
    (hc : ContinuousOn q (Icc a b ×ˢ univ))
    (hp : UnitSpatialPeriodsOn (Icc a b) q)
    (htd : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => q (s,x)) t)
    (hxd : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => q (t,x)))
    (hineq : ∀ t ∈ Ioo a b, ∀ x, operator u eta_m q t x ≤ 0)
    (hi : ∀ x, q (a,x) ≤ 0) {t : ℝ} (ht : t ∈ Icc a b) (x : Space) :
    q (t,x) ≤ 0 := by
  have hforward (s : ℝ) (hs : s ∈ Ico a b) (y : Space) : q (s,y) ≤ 0 := by
    by_contra hn
    have hqpos : 0 < q (s,y) := lt_of_not_ge hn
    let ε := q (s,y) / (2*(s-a+1))
    have hden : 0 < 2*(s-a+1) := by linarith [hs.1]
    have hε : 0 < ε := div_pos hqpos hden
    have hεeq : ε * (2*(s-a+1)) = q (s,y) := div_mul_cancel₀ _ hden.ne'
    let r : SpaceTime → ℝ := fun z => q z - ε*(z.1-a)
    have hr : r (s,y) ≤ 0 := nonpos_of_strict (q := r) (u := u) heta
      (hc.sub (continuousOn_const.mul (continuousOn_fst.sub continuousOn_const)))
      (fun t ht x i => by dsimp [r]; rw [hp t ht x i])
      (fun t ht x => (htd t ht x).sub (by fun_prop))
      (fun t ht => by
        change ContDiff ℝ 2 (fun x => q (t,x) - ε*(t-a))
        exact (hxd t ht).sub contDiff_const)
      (fun t ht x => by
        have he := operator_affine (q := q) (u := u) (eta_m := eta_m)
          (hasDerivAt_const t (1 : ℝ))
          (((hasDerivAt_id t).sub_const a).const_mul (-ε))
          (htd t ht x) (hxd t ht)
        have hr : r = (fun z => (1 : ℝ)*q z + (-ε)*(z.1-a)) := by funext z; dsimp [r]; ring
        dsimp only [id_eq] at he
        rw [hr,he]
        have := hineq t ht x
        simp only [one_mul,zero_mul,mul_one]
        linarith)
      (fun x => by simpa [r] using hi x) hs y
    dsimp [r] at hr
    nlinarith
  have hct : ContinuousOn (fun s => q (s,x)) (Icc a b) :=
    hc.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs,mem_univ _⟩)
  apply le_on_closure (s := Ico a b) (g := fun _ => (0 : ℝ))
    (fun s hs => hforward s hs x)
  · simpa [closure_Ico hab.ne] using hct
  · exact continuousOn_const
  · simpa [closure_Ico hab.ne] using ht

/-- Endpoint-compatible periodic scalar comparison. No bounds or
incompressibility assumptions on the drift are needed. -/
theorem comparison {q : SpaceTime → ℝ} {u : VelocityField} {a b eta_m c F0 : ℝ}
    (hab : a < b) (heta : 0 ≤ eta_m) (hcpos : 0 < c) (_hF : 0 ≤ F0)
    (hc : ContinuousOn q (Icc a b ×ˢ univ))
    (hp : UnitSpatialPeriodsOn (Icc a b) q)
    (htd : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => q (s,x)) t)
    (hxd : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => q (t,x)))
    (hineq : ∀ t ∈ Ioo a b, ∀ x, operator u eta_m q t x ≤ c*q (t,x)+F0)
    (hi : ∀ x, q (a,x) ≤ 0) {t : ℝ} (ht : t ∈ Icc a b) (x : Space) :
    q (t,x) ≤ F0*(Real.exp (c*(t-a))-1)/c := by
  let w : ℝ → ℝ := fun t => Real.exp (-c*(t-a))
  have hw (t : ℝ) : HasDerivAt w (-c*w t) t := by
    convert! ((((hasDerivAt_id t).sub_const a).const_mul (-c)).exp) using 1; simp [w,mul_comm]
  let r : SpaceTime → ℝ := fun z => w z.1 * q z + F0/c*(w z.1-1)
  have hr : r (t,x) ≤ 0 := nonpos (q := r) (u := u) hab heta
    (((by fun_prop : Continuous (fun z : SpaceTime => w z.1)).continuousOn.mul hc).add
      (show ContinuousOn (fun z : SpaceTime => F0/c*(w z.1-1)) _ from by dsimp [w]; fun_prop))
    (fun s hs y i => by dsimp [r]; rw [hp s hs y i])
    (fun s hs y => ((hw s).differentiableAt.mul (htd s hs y)).add
      ((((hw s).sub_const 1).const_mul (F0/c)).differentiableAt))
    (fun s hs => by
      change ContDiff ℝ 2 (fun x => w s*q (s,x) + F0/c*(w s-1))
      exact (contDiff_const.mul (hxd s hs)).add contDiff_const)
    (fun s hs y => by
      have he := operator_affine (q := q) (u := u) (eta_m := eta_m) (hw s)
        (((hw s).sub_const 1).const_mul (F0/c)) (htd s hs y) (hxd s hs)
      change operator u eta_m (fun z => w z.1*q z + F0/c*(w z.1-1)) s y ≤ 0
      rw [he]
      have hh := mul_le_mul_of_nonneg_left (hineq s hs y)
        (show 0 ≤ w s from (Real.exp_pos _).le)
      have hcancel : F0/c*(-c*w s) = -F0*w s := by field_simp
      rw [hcancel]
      nlinarith)
    (fun y => by simpa [r,w] using hi y) ht x
  have he : w t * Real.exp (c*(t-a)) = 1 := by
    dsimp [w]
    rw [← Real.exp_add]
    convert! Real.exp_zero using 2; ring
  have hh := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (c*(t-a))).le hr
  change Real.exp (c*(t-a)) * (w t*q (t,x)+F0/c*(w t-1)) ≤ 0 at hh
  have heq : Real.exp (c*(t-a)) * (w t*q (t,x)+F0/c*(w t-1)) =
      q (t,x)-F0*(Real.exp (c*(t-a))-1)/c := by
    calc
      _ = (w t*Real.exp (c*(t-a)))*q (t,x) +
        F0/c*((w t*Real.exp (c*(t-a)))-Real.exp (c*(t-a))) := by ring
      _ = _ := by rw [he]; ring
  rw [heq] at hh
  linarith

end NavierStokes.ResistiveMagnetic.Slice
