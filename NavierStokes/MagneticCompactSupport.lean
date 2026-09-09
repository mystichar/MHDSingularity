import NavierStokes.MagneticCompactFlow
import NavierStokes.MagneticPeriodicNorms

/-! Finite constructions with the same physical initial time agree wherever
both are defined. The proof compares the actual nonlinear flows first. -/
noncomputable section
namespace NavierStokes.MagneticCompactFlow.Slab
open Set ProblemStatement
open scoped Topology
private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance

variable (S R : Slab)

theorem Phi_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.Phi t x = R.Phi t x := by
  have hSc : Continuous (fun s => S.Phi s x) := S.Phi_continuous.comp
    (continuous_id.prodMk continuous_const)
  have hRc : Continuous (fun s => R.Phi s x) := R.Phi_continuous.comp
    (continuous_id.prodMk continuous_const)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun s => S.Phi s x-R.Phi s x)
    (f' := fun s => S.velocity (s,S.Phi s x)-S.velocity (s,R.Phi s x))
    (K := (S.data.lipschitzConstant : ℝ))
    (a := S.a) (b := t) (hSc.sub hRc).continuousOn
    (fun s hs => by
      have hS : s ∈ Icc S.a S.b := ⟨hs.1, hs.2.le.trans htS.2⟩
      have hR : s ∈ Icc R.a R.b := ⟨ha ▸ hs.1, hs.2.le.trans htR.2⟩
      convert! ((S.Phi_hasDerivAt s hS x).sub
        (R.Phi_hasDerivAt s hR x)).hasDerivWithinAt using 1
      simp only [hu])
    (by rw [S.Phi_initial, ha, R.Phi_initial, sub_self])
    (fun s hs => by
      have hS : s ∈ Icc S.a S.b := ⟨hs.1, hs.2.le.trans htS.2⟩
      have hl := (S.data.lipschitz (s-S.a)).dist_le_mul (S.Phi s x) (R.Phi s x)
      simpa only [S.data_velocity s hS, dist_eq_norm] using hl)
    t ⟨htS.1,le_rfl⟩
  exact sub_eq_zero.mp hz

theorem F_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.F t x = R.F t x := by
  unfold F
  rw [show S.Phi t = R.Phi t from funext (S.Phi_overlap R hu ha t htS htR)]

theorem Y_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.Y t x = R.Y t x := by
  have he := S.Phi_overlap R hu ha t htS htR (R.Y t x)
  rw [R.Phi_Y] at he
  have hh := congrArg (S.Y t) he
  simpa only [S.Y_Phi] using hh.symm

theorem magnetic_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (W : Space → Space) (t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.magnetic W (t,x) = R.magnetic W (t,x) := by
  unfold magnetic
  rw [S.Y_overlap R hu ha t htS htR x, S.F_overlap R hu ha t htS htR]

/-- Closed support is contained in the image of the initial closed support. -/
theorem transported_support (W : Space → Space) (hW : HasCompactSupport W) (t : ℝ) :
    tsupport (fun x => S.magnetic W (t,x)) ⊆ S.Phi t '' tsupport W := by
  apply closure_minimal
  · intro x hx
    refine ⟨S.Y t x,?_,S.Phi_Y t x⟩
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [magnetic,hz])
  · exact (hW.image (S.Phi_continuous.comp (continuous_const.prodMk continuous_id))).isClosed

/-- The image of a compact slab times the seed support is a compact tube. -/
def supportTube (W : Space → Space) : Set Space :=
  Function.uncurry S.Phi '' (Icc S.a S.b ×ˢ tsupport W)

theorem supportTube_compact (W : Space → Space) (hW : HasCompactSupport W) :
    IsCompact (S.supportTube W) :=
  (isCompact_Icc.prod hW).image S.Phi_continuous

theorem magnetic_supported_tube (W : Space → Space) (hW : HasCompactSupport W)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) :
    tsupport (fun x => S.magnetic W (t,x)) ⊆ S.supportTube W := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := S.transported_support W hW t hx
  exact ⟨(t,y),⟨ht,hy⟩,rfl⟩

end NavierStokes.MagneticCompactFlow.Slab

namespace NavierStokes.MagneticCompactFlow
open Set Filter MeasureTheory ProblemStatement
open scoped Topology ENNReal

def energy (B : MagneticField) (t : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, ENNReal.ofReal (‖B (t,x)‖^2)

/-- Uniform bounds follow from one compact support and continuity on one
fixed slab. No terminal-time uniform estimate is asserted. -/
theorem compact_slab_bounds {B : MagneticField} {a b : ℝ} {K : Set Space}
    (hK : IsCompact K) (hc : ContinuousOn B (Icc a b ×ˢ univ))
    (hs : ∀ t ∈ Icc a b, ∀ x, x ∉ K → B (t,x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E : ℝ≥0∞, E < ⊤ ∧ ∀ t ∈ Icc a b,
      (∀ x, ‖B (t,x)‖ ≤ C) ∧ MagneticPeriodicNorms.supNorm B t ≤ C ∧
      energy B t ≤ E ∧ energy B t < ⊤ := by
  have hk := (isCompact_Icc (a := a) (b := b)).prod hK
  obtain ⟨C,hC,hbound⟩ := (hk.image_of_continuousOn
    (hc.mono (prod_subset_prod_right (subset_univ _)))).isBounded.exists_pos_norm_le
  have hn : ∀ t ∈ Icc a b, ∀ x, ‖B (t,x)‖ ≤ C := by
    intro t ht x
    by_cases hx : x ∈ K
    · exact hbound _ ⟨(t,x),⟨ht,hx⟩,rfl⟩
    · simp only [hs t ht x hx,norm_zero]; exact hC.le
  let E := (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (C^2) * volume K)
  have hE : E < ⊤ := ENNReal.mul_lt_top (by norm_num)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top)
  have he : ∀ t ∈ Icc a b, energy B t ≤ E := by
    intro t ht
    apply mul_le_mul_right
    calc
      _ ≤ ∫⁻ x, K.indicator (fun _ => ENNReal.ofReal (C^2)) x := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ K
        · simp only [Set.indicator_of_mem hx]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hn t ht x) 2)
        · simp [Set.indicator_of_notMem hx, hs t ht x hx]
      _ = _ := lintegral_indicator_const hK.measurableSet _
  exact ⟨C,hC.le,E,hE,fun t ht => ⟨hn t ht,
    (MagneticPeriodicNorms.supNorm_bounds hC.le (hn t ht)).2.1,he t ht,(he t ht).trans_lt hE⟩⟩

end NavierStokes.MagneticCompactFlow
