import NavierStokes.ResistivePeriodicHeatSemigroup
import Euler.GaussianHeatDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiating the Gaussian kernel on the physical periodic cover.
The input in `valueLine_hasDerivAt` is merely continuous. The derivative is
a limit in the periodic uniform space, not only a pointwise limit. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement Filter
open EulerGaussianCylinderHeat
open scoped BoundedContinuousFunction NNReal Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

theorem valueKernel_integrable (v : Space) (f : PeriodicValue V)
    (k : ℝ → ℝ) (hk : Integrable k) :
    Integrable (fun s : ℝ => k s • translate (s • v) f) := by
  apply (hk.norm.mul_const ‖f‖).mono'
    (hk.1.smul ((translate_continuous f).comp
      (continuous_id.smul continuous_const)).aestronglyMeasurable)
  exact Eventually.of_forall (fun s => by
    change ‖k s • translate (s • v) f‖ ≤ ‖k s‖ * ‖f‖
    rw [norm_smul, translate_norm])

theorem valueMoment_integrable (v : Space) (r : ℝ≥0) (f : PeriodicValue V) :
    Integrable (fun s : ℝ => s • translate (s • v) f) (gaussianReal 0 r) := by
  apply ((gaussianId_integrable r).norm.mul_const ‖f‖).mono'
    ((gaussianId_integrable r).1.smul ((translate_continuous f).comp
      (continuous_id.smul continuous_const)).aestronglyMeasurable)
  exact Eventually.of_forall (fun s => by
    change ‖s • translate (s • v) f‖ ≤ ‖s‖ * ‖f‖
    rw [norm_smul, translate_norm])

def valueLineDerivative (v : Space) (r : ℝ≥0) : PeriodicValue V →L[ℝ] PeriodicValue V :=
  LinearMap.mkContinuous
    { toFun := fun f => (r : ℝ)⁻¹ • ∫ s : ℝ, s • translate (s • v) f ∂gaussianReal 0 r
      map_add' := fun f g => by
        simp only [map_add, smul_add]
        rw [integral_add (valueMoment_integrable v r f) (valueMoment_integrable v r g), smul_add]
      map_smul' := fun c f => by
        simp only [map_smul, smul_comm _ c, integral_smul, RingHom.id_apply] }
    ((r : ℝ)⁻¹ * gaussianAbsMoment r) (fun f => by
      have hi := norm_integral_le_of_norm_le ((gaussianId_integrable r).norm.mul_const ‖f‖)
        (Eventually.of_forall (fun s => by
          change ‖s • translate (s • v) f‖ ≤ ‖s‖ * ‖f‖
          rw [norm_smul, translate_norm]))
      change ‖(r : ℝ)⁻¹ • ∫ s : ℝ, s • translate (s • v) f ∂gaussianReal 0 r‖ ≤ _
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr r.coe_nonneg)]
      apply (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr r.coe_nonneg)).trans
      simp only [integral_mul_const, Real.norm_eq_abs, gaussianAbsMoment]
      exact le_of_eq (mul_assoc _ _ _).symm)

theorem valueLineDerivative_norm_le (v : Space) (r : ℝ≥0) (f : PeriodicValue V) :
    ‖valueLineDerivative v r f‖ ≤ (r : ℝ)⁻¹ * gaussianAbsMoment r * ‖f‖ := by
  apply (valueLineDerivative v r).le_of_opNorm_le
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (inv_nonneg.mpr r.coe_nonneg) (gaussianAbsMoment_nonneg r)) _

theorem valueLineDerivative_sqrt_bound (v : Space) {r : ℝ≥0} (hr : 0 < r)
    (f : PeriodicValue V) :
    ‖valueLineDerivative v r f‖ ≤ gaussianAbsMoment 1 / Real.sqrt (r : ℝ) * ‖f‖ := by
  have hs : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hr)).ne'
  have he : (r : ℝ)⁻¹ * gaussianAbsMoment r = gaussianAbsMoment 1 / Real.sqrt (r : ℝ) := by
    rw [gaussianAbsMoment_scale]
    field_simp
    rw [Real.sq_sqrt r.coe_nonneg]
  rw [← he]
  exact valueLineDerivative_norm_le v r f

/-- An explicit locally uniform integrable envelope for the shifted
Gaussian derivative. Its constant may depend on the positive variance. -/
def shiftEnvelope (r : ℝ≥0) (x : ℝ) : ℝ :=
  ((Real.sqrt (2 * Real.pi * (r : ℝ)))⁻¹ / (r : ℝ) * Real.exp (1 / (2 * (r : ℝ)))) *
    ((|x| + 1) * Real.exp (-((4 * (r : ℝ))⁻¹) * x ^ 2))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
theorem shiftEnvelope_integrable {r : ℝ≥0} (hr : 0 < r) : Integrable (shiftEnvelope r) := by
  have hp : 0 < (4 * (r : ℝ))⁻¹ := by exact inv_pos.mpr (mul_pos (by norm_num) (NNReal.coe_pos.mpr hr))
  have h0 := integrable_exp_neg_mul_sq hp
  have h1 := (integrable_mul_exp_neg_mul_sq hp).norm
  have hi : Integrable (fun x : ℝ => (|x| + 1) * Real.exp (-((4 * (r : ℝ))⁻¹) * x ^ 2)) := by
    convert! h1.add h0 using 1
    ext x
    dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  exact hi.const_mul _

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
theorem shiftedGaussian_derivative_bound {r : ℝ≥0} (hr : 0 < r) (x h : ℝ) (hh : |h| ≤ 1) :
    ‖((x - h) / (r : ℝ)) * gaussianPDFReal 0 r (x - h)‖ ≤ shiftEnvelope r x := by
  have hp : 0 < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hsq : h ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg h) zero_le_one).mpr hh
  have hquad : x ^ 2 / 2 - 1 ≤ (x - h) ^ 2 := by nlinarith [sq_nonneg (x - 2 * h)]
  have hexp : -((x - h) ^ 2) / (2 * (r : ℝ)) ≤
      1 / (2 * (r : ℝ)) + -((4 * (r : ℝ))⁻¹) * x ^ 2 := by
    calc
      _ ≤ -(x ^ 2 / 2 - 1) / (2 * (r : ℝ)) :=
        div_le_div_of_nonneg_right (neg_le_neg hquad) (by positivity)
      _ = _ := by ring
  have he := Real.exp_le_exp.mpr hexp
  rw [Real.exp_add] at he
  have hx : |x - h| ≤ |x| + 1 := (abs_sub x h).trans (add_le_add_right hh _)
  have hn : 0 ≤ (Real.sqrt (2 * Real.pi * (r : ℝ)))⁻¹ := by positivity
  rw [norm_mul, Real.norm_eq_abs, abs_div, abs_of_pos hp,
    Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  simp only [gaussianPDFReal, sub_zero]
  calc
    _ ≤ ((|x| + 1) / (r : ℝ)) *
        ((Real.sqrt (2 * Real.pi * (r : ℝ)))⁻¹ *
          (Real.exp (1 / (2 * (r : ℝ))) * Real.exp (-((4 * (r : ℝ))⁻¹) * x ^ 2))) :=
      mul_le_mul (div_le_div_of_nonneg_right hx hp.le)
        (mul_le_mul_of_nonneg_left he hn) (by positivity) (by positivity)
    _ = shiftEnvelope r x := by unfold shiftEnvelope; ring

theorem valueLine_shift_kernel (v : Space) {r : ℝ≥0} (hr : r ≠ 0)
    (f : PeriodicValue V) (h : ℝ) :
    translate (h • v) (valueLine v r f) =
      ∫ x : ℝ, gaussianPDFReal 0 r (x - h) • translate (x • v) f := by
  rw [valueLine_translate]
  change (∫ s : ℝ, translate (s • v) (translate (h • v) f) ∂gaussianReal 0 r) = _
  rw [integral_gaussianReal_eq_integral_smul hr]
  have he := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => gaussianPDFReal 0 r (x - h) • translate (x • v) f) h
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by simp only [add_sub_cancel_right, translate_add, add_smul])

/-- Genuine derivative gain from C0 data: differentiation is performed on
the shifted density, with `shiftEnvelope` justifying the Bochner limit. -/
theorem valueLine_hasDerivAt (v : Space) {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) :
    HasDerivAt (fun h : ℝ => translate (h • v) (valueLine v r f))
      (valueLineDerivative v r f) 0 := by
  let F := fun h x : ℝ => gaussianPDFReal 0 r (x - h) • translate (x • v) f
  let F' := fun h x : ℝ => (((x - h) / (r : ℝ)) * gaussianPDFReal 0 r (x - h)) • translate (x • v) f
  have hpdf : Continuous (gaussianPDFReal 0 r) :=
    continuous_iff_continuousAt.mpr (fun x => (gaussianPDF_hasDerivAt r x).continuousAt)
  have hdiff (x h : ℝ) : HasDerivAt (fun s => F s x) (F' h x) h := by
    have hd := (gaussianPDF_hasDerivAt r (x - h)).comp h ((hasDerivAt_id h).const_sub x)
    change HasDerivAt (fun s => gaussianPDFReal 0 r (x - s) • translate (x • v) f)
      ((((x - h) / (r : ℝ)) * gaussianPDFReal 0 r (x - h)) • translate (x • v) f) h
    convert! hd.smul_const (translate (x • v) f) using 1
    congr 1
    ring
  have hmeas (h : ℝ) : AEStronglyMeasurable (F h) :=
    ((hpdf.comp (continuous_id.sub continuous_const)).smul
      ((translate_continuous f).comp (continuous_id.smul continuous_const))).aestronglyMeasurable
  have hint : Integrable (F 0) := by
    simpa only [F, sub_zero] using valueKernel_integrable v f _ (integrable_gaussianPDFReal 0 r)
  have hdmeas : AEStronglyMeasurable (F' 0) := by
    exact ((((continuous_id.sub continuous_const).div_const (r : ℝ)).mul
      (hpdf.comp (continuous_id.sub continuous_const))).smul
      ((translate_continuous f).comp (continuous_id.smul continuous_const))).aestronglyMeasurable
  have hb : ∀ᵐ x : ℝ, ∀ h ∈ Ioo (-1 : ℝ) 1, ‖F' h x‖ ≤ shiftEnvelope r x * ‖f‖ := by
    apply Eventually.of_forall
    intro x h hh
    change ‖(((x - h) / (r : ℝ)) * gaussianPDFReal 0 r (x - h)) • translate (x • v) f‖ ≤ _
    rw [norm_smul, translate_norm]
    exact mul_le_mul_of_nonneg_right (shiftedGaussian_derivative_bound hr x h
      (abs_le.mpr ⟨hh.1.le, hh.2.le⟩)) (norm_nonneg f)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun x => shiftEnvelope r x * ‖f‖)
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) hint hdmeas hb ((shiftEnvelope_integrable hr).mul_const ‖f‖)
    (Eventually.of_forall (fun x h _ => hdiff x h))).2
  have he : (∫ x : ℝ, F' 0 x) = valueLineDerivative v r f := by
    change (∫ x : ℝ, F' 0 x) = (r : ℝ)⁻¹ • ∫ x : ℝ, x • translate (x • v) f ∂gaussianReal 0 r
    rw [integral_gaussianReal_eq_integral_smul hr.ne', ← integral_smul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp [F']; simp only [sub_zero, smul_smul]; congr 1; ring)
  rw [he] at hd
  convert! hd using 1
  funext h
  exact valueLine_shift_kernel v hr.ne' f h

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
