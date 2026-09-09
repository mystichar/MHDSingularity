import NavierStokes.ResistivePeriodicHeatSmoothing
import NavierStokes.ResistivePeriodicHeatC1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Euler.VolterraFixedPoint

/-! The derivative-gaining physical periodic kernel and its integrable time
budget. This module does not construct a resistive induction solution. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProblemStatement Filter intervalIntegral
open scoped Topology NNReal

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

section Codomain
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance
private local instance : NormedAddCommGroup (PeriodicC1Value V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicC1Value V) := inferInstance

theorem gainVariance_tsub (e r : ℝ≥0) (he : 0 < e) (her : e ≤ r) (f : PeriodicValue V) :
    gainVariance e he (valueSpatial (r - e) f) = gainVariance r (he.trans_le her) f := by
  apply c1Value_injective
  rw [gainVariance_value, gainVariance_value, valueSpatial_semigroup, add_tsub_cancel_of_le her]

/-- A fixed positive smoothing step plus strong continuity gives continuity
in the target C1 norm, without operator-norm continuity at zero. -/
theorem gainVariance_joint_continuous :
    Continuous (fun p : {r : ℝ≥0 // 0 < r} × PeriodicValue V => gainVariance p.1.val p.1.property p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let e : ℝ≥0 := p.1.val / 2
  have he : 0 < e := div_pos p.1.property (by norm_num)
  have hep : e < p.1.val := by exact half_lt_self p.1.property
  have hc : Continuous (fun z : {r : ℝ≥0 // 0 < r} × PeriodicValue V =>
      gainVariance e he (valueSpatial (z.1.val - e) z.2)) :=
    (gainVariance e he).continuous.comp
      (valueSpatial_joint_continuous.comp
        (((continuous_subtype_val.comp continuous_fst).sub continuous_const).prodMk continuous_snd))
  apply hc.continuousAt.congr_of_eventuallyEq
  have hlate : ∀ᶠ z : {r : ℝ≥0 // 0 < r} × PeriodicValue V in 𝓝 p, e < z.1.val :=
    ((continuous_subtype_val.comp continuous_fst).tendsto p).eventually (Ioi_mem_nhds hep)
  filter_upwards [hlate] with z hz
  exact (gainVariance_tsub e z.1.val he hz.le z.2).symm

theorem gainVariance_C1 (r : ℝ≥0) (hr : 0 < r) (f : PeriodicC1Value V) :
    gainVariance r hr (c1Value f) = spatialC1 r f := by
  apply c1Value_injective
  rw [gainVariance_value, spatialC1_value]

end Codomain

def positiveVariance (eta_m : ℝ) (heta : 0 < eta_m) (t : {t : ℝ // 0 < t}) :
    {r : ℝ≥0 // 0 < r} :=
  ⟨(2 * eta_m * t.val).toNNReal, Real.toNNReal_pos.mpr (by have ht := t.property; positivity)⟩

theorem positiveVariance_continuous (eta_m : ℝ) (heta : 0 < eta_m) :
    Continuous (positiveVariance eta_m heta) := by
  apply Continuous.subtype_mk
  fun_prop

theorem heatGain_joint_continuous (eta_m : ℝ) (heta : 0 < eta_m) :
    Continuous (fun p : {t : ℝ // 0 < t} × PeriodicField => heatGain eta_m p.1.val heta p.1.property p.2) :=
  gainVariance_joint_continuous.comp
    (((positiveVariance_continuous eta_m heta).comp continuous_fst).prodMk continuous_snd)

/-- The Volterra kernel is zero for nonpositive elapsed time. This convention
is separate from `heat eta_m 0 = id`. -/
def heatKernel (eta_m : ℝ) (heta : 0 < eta_m) (tau : ℝ) : PeriodicField →L[ℝ] PeriodicC1 :=
  if htau : 0 < tau then heatGain eta_m tau heta htau else 0

@[simp] theorem heatKernel_nonpositive (eta_m : ℝ) (heta : 0 < eta_m) {tau : ℝ} (htau : tau ≤ 0) :
    heatKernel eta_m heta tau = 0 := by simp [heatKernel, not_lt.mpr htau]

set_option maxHeartbeats 800000 in
theorem heatKernel_joint_continuous (eta_m : ℝ) (heta : 0 < eta_m) :
    ContinuousOn (fun p : ℝ × PeriodicField => heatKernel eta_m heta p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set PeriodicField)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let P := {p : ℝ × PeriodicField // p ∈ Ioi 0 ×ˢ (univ : Set PeriodicField)}
  let F : P → {t : ℝ // 0 < t} × PeriodicField := fun p => (⟨p.val.1, p.property.1⟩, p.val.2)
  have hF : Continuous F :=
    (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  have hh := (heatGain_joint_continuous eta_m heta).comp hF
  convert! hh using 1
  funext p
  change heatKernel eta_m heta p.val.1 p.val.2 = _
  have ht : 0 < p.val.1 := p.property.1
  rw [heatKernel, dite_eq_left ht]
  rfl

def kernelMajorant (eta_m tau : ℝ) : ℝ := 1 + heatConstant / Real.sqrt (eta_m * tau)

theorem kernelMajorant_nonneg (eta_m tau : ℝ) : 0 ≤ kernelMajorant eta_m tau :=
  add_nonneg zero_le_one (div_nonneg heatConstant_nonneg (Real.sqrt_nonneg _))

theorem heatKernel_bound (eta_m : ℝ) (heta : 0 < eta_m) {tau : ℝ} (htau : 0 < tau)
    (f : PeriodicField) : ‖heatKernel eta_m heta tau f‖ ≤ kernelMajorant eta_m tau * ‖f‖ := by
  rw [heatKernel, dite_eq_left htau]
  exact (heatGain eta_m tau heta htau).le_of_opNorm_le (heatGain_norm_le eta_m tau heta htau) f

theorem kernelMajorant_rpow {eta_m tau : ℝ} (heta : 0 < eta_m) (htau : 0 ≤ tau) :
    kernelMajorant eta_m tau = 1 + (heatConstant / Real.sqrt eta_m) * tau ^ (-(1 / 2 : ℝ)) := by
  rw [kernelMajorant, Real.sqrt_mul heta.le, Real.rpow_neg htau, ← Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The derivative loss is integrable at zero for every fixed positive
diffusivity. No uniformity as eta_m tends to zero is asserted. -/
theorem kernelMajorant_integrable (eta_m T : ℝ) (heta : 0 < eta_m) (hT : 0 ≤ T) :
    IntegrableOn (kernelMajorant eta_m) (Ioc 0 T) := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 T :=
    intervalIntegrable_rpow' (by norm_num)
  have hi : IntegrableOn (fun t : ℝ => 1 + (heatConstant / Real.sqrt eta_m) * t ^ (-(1 / 2 : ℝ)))
      (Ioc 0 T) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
    (intervalIntegrable_const.add (hr.const_mul _))
  apply hi.congr_fun
  · intro t ht
    exact (kernelMajorant_rpow heta ht.1.le).symm
  · exact measurableSet_Ioc

theorem kernelMajorant_integral (eta_m T : ℝ) (heta : 0 < eta_m) (hT : 0 ≤ T) :
    (∫ t in Ioc 0 T, kernelMajorant eta_m t) = T + 2 * heatConstant * Real.sqrt (T / eta_m) := by
  have he : (∫ t in Ioc 0 T, kernelMajorant eta_m t) =
      ∫ t in Ioc 0 T, 1 + (heatConstant / Real.sqrt eta_m) * t ^ (-(1 / 2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact kernelMajorant_rpow heta ht.1.le
  rw [he, ← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegrable_rpow' (by norm_num : -1 < -(1 / 2 : ℝ))).const_mul _),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div hT]
  ring

@[simp] theorem kernelMajorant_integral_zero (eta_m : ℝ) :
    (∫ t in Ioc (0 : ℝ) 0, kernelMajorant eta_m t) = 0 := by simp

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
