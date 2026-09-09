import NavierStokes.MagneticSimilarityGradient
import NavierStokes.MagneticCauchy

/-! Exact amplification along the distinguished natural-core trajectory, conditional
on a supplied ideal induction solution. No magnetic PDE existence or transfer to
the assembled Navier–Stokes velocity is asserted. -/

noncomputable section
namespace NavierStokes.MagneticCoreAmplification

open Set ProblemStatement NaturalAxisData NaturalCore MagneticSimilarityTrajectory
open MagneticSimilarityGradient MagneticTransport
open scoped Topology ContDiff

/-- Exact dimensionless axial exponent of the distinguished natural-core path. -/
def axialExponent {h j : ℝ} (p : SmallParameters h j) : ℝ :=
  (4 * d (distinguishedEta p) ^ 2 +
    2 * A h * D h * distinguishedEta p ^ 2) / L h (distinguishedEta p)

theorem distinguishedEta_mem {h j : ℝ} (p : SmallParameters h j) :
    distinguishedEta p ∈ Icc (-1 : ℝ) 1 := by
  have hs := distinguishedEta_sq_lt_one p
  constructor <;> nlinarith [sq_nonneg (distinguishedEta p + 1),
    sq_nonneg (distinguishedEta p - 1)]

theorem axialExponent_pos {h j : ℝ} (p : SmallParameters h j) :
    0 < axialExponent p := by
  have hd : 0 < d (distinguishedEta p) := sub_pos.mpr (distinguishedEta_sq_lt_one p)
  exact div_pos (add_pos_of_pos_of_nonneg (mul_pos (by norm_num) (sq_pos_of_pos hd))
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (A_pos p).le) (D_pos p).le)
      (sq_nonneg _))) (L_pos p (distinguishedEta_mem p))

theorem axialExponent_defect {h j : ℝ} (p : SmallParameters h j) :
    4 - axialExponent p = distinguishedEta p ^ 2 *
      (15 / 2 - 8 * h + 2 * h ^ 2 - 4 * distinguishedEta p ^ 2) /
      (1 - 2 * h * distinguishedEta p ^ 2) := by
  have hL := (L_pos p (distinguishedEta_mem p)).ne'
  apply (eq_div_iff hL).mpr
  unfold axialExponent
  rw [sub_mul, div_mul_cancel₀ _ hL]
  unfold A D d L
  ring

theorem axialExponent_defect_bounds {h j : ℝ} (p : SmallParameters h j) :
    0 < 4 - axialExponent p ∧ 4 - axialExponent p < j ^ 2 / 2 := by
  let η := distinguishedEta p
  have hr := (distinguishedEta_spec p).1
  have hηneg : η < 0 := by dsimp [η]; linarith [hr.2, p.j_pos]
  have hηpos : 0 < η ^ 2 := sq_pos_of_ne_zero (ne_of_lt hηneg)
  have hηbound : η ^ 2 < j ^ 2 / 16 := by
    have hm : 0 < (η + j / 4) * (j / 4 - η) :=
      mul_pos (by dsimp [η]; linarith [hr.1]) (by linarith [p.j_pos])
    nlinarith
  have hηone : η ^ 2 < 1 := distinguishedEta_sq_lt_one p
  have hh2 : h ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg p.h_pos.le (sub_nonneg.mpr p.h_le)]
  have hL := L_lower_bound p (distinguishedEta_mem p)
  have hLp := L_pos p (distinguishedEta_mem p)
  have hfacpos : 0 < 15 / 2 - 8 * h + 2 * h ^ 2 - 4 * η ^ 2 := by
    nlinarith [p.h_le, sq_nonneg h]
  have hfaclt : 15 / 2 - 8 * h + 2 * h ^ 2 - 4 * η ^ 2 < 8 * L h η := by
    change 499 / 500 ≤ L h η at hL
    nlinarith [p.h_pos, sq_nonneg η]
  rw [axialExponent_defect]
  change 0 < η ^ 2 * _ / L h η ∧ η ^ 2 * _ / L h η < j ^ 2 / 2
  constructor
  · exact div_pos (mul_pos hηpos hfacpos) hLp
  · apply lt_trans _ (show 8 * η ^ 2 < j ^ 2 / 2 by linarith)
    apply (div_lt_iff₀ hLp).mpr
    nlinarith [mul_lt_mul_of_pos_left hfaclt hηpos]

theorem axialExponent_bounds {h j : ℝ} (p : SmallParameters h j) :
    (7999999 / 2000000 : ℝ) < axialExponent p ∧ axialExponent p < 4 := by
  have hd := axialExponent_defect_bounds p
  have hj2 : j ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg p.j_pos.le (sub_nonneg.mpr p.j_le)]
  constructor <;> linarith [hd.1, hd.2]

/-- The root identity converts the gradient coefficient into `K/(1-t)`. -/
theorem axialStrain_eq_exponent {h j Λ t : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (p : SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr) (ht : t < 1) :
    axialStrain h (distinguishedEta p) V t = axialExponent p / (1 - t) := by
  rw [axialStrain_eq p.h_pos (by linarith [p.h_le]) hs
    (distinguishedEta_sq_lt_one p) ht]
  have hd : d (distinguishedEta p) ≠ 0 :=
    (sub_pos.mpr (distinguishedEta_sq_lt_one p)).ne'
  have hL := (L_pos p (distinguishedEta_mem p)).ne'
  have ht0 := (sub_pos.mpr ht).ne'
  have hr := (distinguishedEta_spec p).2.1
  unfold H at hr
  unfold pathQ axialCoefficientExact axialExponent
  field_simp
  have hm := congrArg (fun r : ℝ => 2 * A h * distinguishedEta p * r) hr
  nlinarith [hm]

/-- Positive power-law amplification factor on any preterminal interval. -/
def amplificationFactor (K a t : ℝ) : ℝ := ((1 - a) / (1 - t)) ^ K

theorem amplificationFactor_hasDerivAt {K a t : ℝ} (ha : a < 1) (ht : t < 1) :
    HasDerivAt (amplificationFactor K a)
      (K / (1 - t) * amplificationFactor K a t) t := by
  have ht0 := (sub_pos.mpr ht).ne'
  have hr : 0 < (1 - a) / (1 - t) := div_pos (sub_pos.mpr ha) (sub_pos.mpr ht)
  have hd := ((hasDerivAt_const t (1 - a)).div
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) ht0).rpow_const
      (p := K) (Or.inl hr.ne')
  dsimp only [Pi.div_apply, Pi.sub_apply, id_eq] at hd
  convert! hd using 1
  simp only [zero_sub, zero_mul, Real.rpow_sub_one hr.ne', amplificationFactor]
  field_simp [(sub_pos.mpr ha).ne', ht0]

theorem amplificationFactor_initial {K a : ℝ} (ha : a < 1) :
    amplificationFactor K a a = 1 := by
  simp [amplificationFactor, (sub_pos.mpr ha).ne']

theorem amplificationFactor_pos {K a t : ℝ} (ha : a < 1) (ht : t < 1) :
    0 < amplificationFactor K a t :=
  Real.rpow_pos_of_pos (div_pos (sub_pos.mpr ha) (sub_pos.mpr ht)) K

theorem amplificationFactor_gt_one {h j a t : ℝ} (p : SmallParameters h j)
    (hat : a < t) (ht : t < 1) : 1 < amplificationFactor (axialExponent p) a t := by
  apply Real.one_lt_rpow _ (axialExponent_pos p)
  apply (lt_div_iff₀ (sub_pos.mpr ht)).mpr
  linarith

/-- Minimal directional transport principle. Only the action of the velocity
Jacobian on the axial vector is specified; its other columns are unrestricted.
The field `B` and its ideal induction equation are supplied hypotheses. -/
theorem pure_axial_transport_of_directional_gradient
    {u : VelocityField} {B : MagneticField} {γ : ℝ → Space}
    {K a b Bz0 : ℝ} {x₀ : Space}
    (hγ : IsLagrangianTrajectoryOn u γ a b x₀) (hb : b < 1)
    (hind : IdealInductionOn (Ioo a b) u B)
    (hBc : ContinuousOn (fun t => B (t, γ t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t, γ t))
    (hA : ContinuousOn (fun t => spatialDerivative u t (γ t)) (Icc a b))
    (haxis : ∀ t ∈ Ioo a b, spatialDerivative u t (γ t) (coordinateVector 2) =
      (K / (1 - t)) • coordinateVector 2)
    (hseed : B (a, γ a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (t, γ t) = (Bz0 * amplificationFactor K a t) • coordinateVector 2 := by
  have ha : a < 1 := hγ.ordered.trans_lt hb
  let v : ℝ → Space := fun s => (Bz0 * amplificationFactor K a s) • coordinateVector 2
  have hv : ∀ s < 1, HasDerivAt v
      ((K / (1 - s)) • v s) s := by
    intro s hs
    convert! ((amplificationFactor_hasDerivAt ha hs).const_mul Bz0).smul_const
      (coordinateVector 2) using 1
    simp only [v, smul_smul]
    congr 1
    ring
  have hvc : ContinuousOn v (Icc a b) :=
    fun s hs => (hv s (hs.2.trans_lt hb)).continuousAt.continuousWithinAt
  have hz := linearODE_eq_zero_on_interval (fun s => B (s, γ s) - v s)
    (fun s => spatialDerivative u s (γ s)) (hBc.sub hvc) hA
    (by
      intro s hs
      have hd := (hasDerivAt_magnetic_along_trajectory hγ hind hs (hBd s hs)).sub
        (hv s (hs.2.trans hb))
      convert! hd using 1
      simp only [map_sub, v, map_smul, haxis s hs, smul_smul]
      congr 2
      ring)
    (by simp [v, hseed, amplificationFactor_initial ha]) ht
  exact sub_eq_zero.mp hz

/-- The core's axial column is independent of the transverse rotation. -/
theorem spatialDerivative_core_axial {h j Λ t : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (p : SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr) (ht : t < 1) :
    spatialDerivative (coreVelocity h f V) t (trajectory h (distinguishedEta p) t)
      (coordinateVector 2) = (axialExponent p / (1 - t)) • coordinateVector 2 := by
  rw [spatialDerivative_naturalCore_on_trajectory p.h_pos (by linarith [p.h_le]) hs
    (distinguishedEta_sq_lt_one p) ht, axialStrain_eq_exponent p hs ht]
  simp [axisOperator_apply, coordinateVector]

theorem core_gradient_continuousOn {h j Λ a b : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (p : SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr) (hb : b < 1) :
    ContinuousOn (fun t => spatialDerivative (coreVelocity h f V) t
      (trajectory h (distinguishedEta p) t)) (Icc a b) := by
  have hop : Continuous (fun v : ℝ × ℝ => axisOperator v.1 v.2) := by
    unfold axisOperator
    fun_prop
  have hq : Continuous (pathQ (distinguishedEta p)) := by unfold pathQ; fun_prop
  have hqp : ∀ t ∈ Icc a b, pathQ (distinguishedEta p) t ≠ 0 :=
    fun t ht => (pathQ_pos (distinguishedEta_sq_lt_one p) (ht.2.trans_lt hb)).ne'
  have halpha := (hq.continuousOn.inv₀ hqp).mul
    (continuousOn_const (c := axialCoefficientExact h j (distinguishedEta p)))
  have hrot := ((hq.continuousOn.rpow_const
    (p := -h) (fun t ht => Or.inl (hqp t ht))).div hq.continuousOn hqp).mul
      (continuousOn_const (c := a0 (distinguishedEta p)))
  have hc := hop.comp_continuousOn (halpha.prodMk hrot)
  apply hc.congr
  intro t ht
  exact spatialDerivative_naturalCore_on_distinguishedTrajectory p hs (ht.2.trans_lt hb)

/-- Exact pure-axial-seed amplification for a supplied ideal induction solution.
Only path continuity and interior joint differentiability of `B` are needed. -/
theorem pure_axial_seed_transport
    {h j Λ a b Bz0 : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (p : SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hab : a ≤ b) (hb : b < 1) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a b) (coreVelocity h f V) B)
    (hBc : ContinuousOn (fun t => B (t, trajectory h (distinguishedEta p) t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ B (t, trajectory h (distinguishedEta p) t))
    (hseed : B (a, trajectory h (distinguishedEta p) a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (t, trajectory h (distinguishedEta p) t) =
      (Bz0 * ((1 - a) / (1 - t)) ^ axialExponent p) • coordinateVector 2 :=
  pure_axial_transport_of_directional_gradient
    (distinguished_trajectory_isLagrangian p hs hab hb) hb hind hBc hBd
    (core_gradient_continuousOn p hs hb)
    (fun _ hs' => spatialDerivative_core_axial p hs (hs'.2.trans hb)) hseed ht

/-- The axial component obeys the same exact law for an arbitrary initial
magnetic direction. Transverse components need not vanish. -/
theorem axial_component_transport
    {h j Λ a b : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (p : SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hab : a ≤ b) (hb : b < 1) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a b) (coreVelocity h f V) B)
    (hBc : ContinuousOn (fun t => B (t, trajectory h (distinguishedEta p) t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ B (t, trajectory h (distinguishedEta p) t))
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (t, trajectory h (distinguishedEta p) t) 2 =
      B (a, trajectory h (distinguishedEta p) a) 2 *
        ((1 - a) / (1 - t)) ^ axialExponent p := by
  let γ := trajectory h (distinguishedEta p)
  let c := B (a, γ a) 2
  let g := amplificationFactor (axialExponent p) a
  let M : ℝ → Space →L[ℝ] Space := fun s =>
    (axialExponent p / (1 - s)) • ContinuousLinearMap.id ℝ Space
  have ha : a < 1 := hab.trans_lt hb
  have hgc : ContinuousOn g (Icc a b) := fun s hs' =>
    (amplificationFactor_hasDerivAt ha (hs'.2.trans_lt hb)).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Icc a b) :=
    (continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun s hs' => (sub_pos.mpr (hs'.2.trans_lt hb)).ne')).smul continuousOn_const
  have hγ := distinguished_trajectory_isLagrangian p hs hab hb
  have hproj := (AxisymmetricFields.projection 2).continuous.comp_continuousOn hBc
  have hz := linearODE_eq_zero_on_interval
    (fun s => (B (s, γ s) 2 - c * g s) • coordinateVector 2) M
    ((hproj.sub (continuousOn_const.mul hgc)).smul continuousOn_const) hMc
    (by
      intro s hs'
      have hmag := hasDerivAt_magnetic_along_trajectory hγ hind hs' (hBd s hs')
      have hp := (AxisymmetricFields.projection 2).hasFDerivAt.comp_hasDerivAt s hmag
      have hd := (hp.sub ((amplificationFactor_hasDerivAt (K := axialExponent p) ha (hs'.2.trans hb)).const_mul c)).smul_const
        (coordinateVector 2)
      rw [spatialDerivative_naturalCore_on_trajectory p.h_pos (by linarith [p.h_le]) hs
        (distinguishedEta_sq_lt_one p) (hs'.2.trans hb),
        axialStrain_eq_exponent p hs (hs'.2.trans hb)] at hd
      convert! hd using 1
      simp [M, g, axisOperator_apply, coordinateVector, γ, smul_smul]
      ring)
    (by simp [g, c, amplificationFactor_initial ha]) ht
  have hz2 := congrArg (fun x : Space => x 2) hz
  simpa [coordinateVector, sub_eq_zero, g, amplificationFactor, γ, c] using hz2

end NavierStokes.MagneticCoreAmplification
