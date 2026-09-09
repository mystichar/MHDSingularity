import NavierStokes.ResistivePeriodicHeatC1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Supplied classical spatial derivatives give genuine strong translation
derivatives in the physical periodic uniform norm. -/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement Filter
open scoped Topology BoundedContinuousFunction NNReal

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

def valueMap (L : V →L[ℝ] W) : PeriodicValue V →L[ℝ] PeriodicValue W :=
  ((L.compLeftContinuousBounded Space).comp (periodicValues V).toSubmodule.subtypeL).codRestrict
    (periodicValues W).toSubmodule (fun f x i => by
      change L (f.val (x + coordinateVector i)) = L (f.val x)
      rw [f.property])

@[simp] theorem valueMap_apply (L : V →L[ℝ] W) (f : PeriodicValue V) (x : Space) :
    (valueMap L f).val x = L (f.val x) := rfl

theorem valueMap_translate (L : V →L[ℝ] W) (y : Space) (f : PeriodicValue V) :
    valueMap L (translate y f) = translate y (valueMap L f) := by
  apply Subtype.ext
  ext x
  rfl

theorem valueMap_line [CompleteSpace V] [CompleteSpace W] (L : V →L[ℝ] W)
    (v : Space) (r : ℝ≥0) (f : PeriodicValue V) :
    valueMap L (valueLine v r f) = valueLine v r (valueMap L f) := by
  change valueMap L (∫ s : ℝ, translate (s • v) f ∂gaussianReal 0 r) = _
  rw [← (valueMap L).integral_comp_comm (translation_integrable v f _)]
  exact integral_congr_ae (Eventually.of_forall (fun s => valueMap_translate L (s • v) f))

theorem valueMap_spatial [CompleteSpace V] [CompleteSpace W] (L : V →L[ℝ] W)
    (r : ℝ≥0) (f : PeriodicValue V) :
    valueMap L (valueSpatial r f) = valueSpatial r (valueMap L f) := by
  simp only [valueSpatial, ContinuousLinearMap.comp_apply, valueMap_line]

theorem value_fderiv_periodic (f : PeriodicValue V) (x : Space) (i : Fin 3) :
    fderiv ℝ f.val (x + coordinateVector i) = fderiv ℝ f.val x := by
  have he : (fun y => f.val (y + coordinateVector i)) = f.val := funext (fun y => f.property y i)
  rw [← fderiv_comp_add_right (coordinateVector i), he]

/-- Every supplied classical C1 periodic field belongs to the graph. The
derivative's uniform bound is obtained from the physical compact cell. -/
def c1OfContDiff (f : PeriodicValue V) (hf : ContDiff ℝ 1 f.val) : PeriodicC1Value V :=
  ⟨(f, ⟨MagneticPeriodicCoefficient.boundedSlice
      (fun p : ℝ × Space => fderiv ℝ f.val p.2)
      ((hf.continuous_fderiv (by norm_num)).comp continuous_snd)
      (fun _ x i => value_fderiv_periodic f x i) 0,
      fun x i => value_fderiv_periodic f x i⟩),
    fun x => (hf.differentiable (by norm_num) x).hasFDerivAt⟩

@[simp] theorem c1OfContDiff_value (f : PeriodicValue V) (hf : ContDiff ℝ 1 f.val) :
    c1Value (c1OfContDiff f hf) = f := rfl

@[simp] theorem c1OfContDiff_derivative (f : PeriodicValue V) (hf : ContDiff ℝ 1 f.val) (x : Space) :
    (c1Derivative (c1OfContDiff f hf)).val x = fderiv ℝ f.val x := rfl

def directionalField (f : PeriodicC1Value V) (v : Space) : PeriodicValue V :=
  valueMap (ContinuousLinearMap.apply ℝ V v) (c1Derivative f)

@[simp] theorem directionalField_apply (f : PeriodicC1Value V) (v x : Space) :
    (directionalField f v).val x = (c1Derivative f).val x v := rfl

/-- The fundamental theorem of calculus upgrades the actual spatial C1
derivative to a derivative in the uniform function-space norm. -/
theorem c1_translation_hasDerivAt [CompleteSpace V] (f : PeriodicC1Value V) (v : Space) :
    HasDerivAt (fun s : ℝ => translate (s • v) (c1Value f)) (directionalField f v) 0 := by
  let g := directionalField f v
  have hc : Continuous (fun s : ℝ => translate (s • v) g) :=
    (translate_continuous g).comp (continuous_id.smul continuous_const)
  have he (t : ℝ) : (∫ s in (0 : ℝ)..t, translate (s • v) g) =
      translate (t • v) (c1Value f) - c1Value f := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    have hi := (valueEval x).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
    change valueEval x (∫ s in (0 : ℝ)..t, translate (s • v) g) = _
    rw [← hi]
    have hd (s : ℝ) : HasDerivAt (fun r : ℝ => (c1Value f).val (x + r • v))
        (g.val (x + s • v)) s := by
      have hcurve := ((hasDerivAt_id s).smul_const v).const_add x
      have hh := (c1_hasFDerivAt f (x + s • v)).comp_hasDerivAt s hcurve
      simpa only [one_smul] using! hh
    have hint : IntervalIntegrable (fun s : ℝ => g.val (x + s • v)) volume 0 t :=
      (g.val.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hint
    simpa only [valueEval_apply, translate_apply, zero_smul, add_zero, map_sub,
      BoundedContinuousFunction.sub_apply] using! hFTC
  have hFTC := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const (c1Value f)
  have hfun : (fun t : ℝ => (∫ s in (0 : ℝ)..t, translate (s • v) g) + c1Value f) =
      fun t : ℝ => translate (t • v) (c1Value f) := by
    funext t
    rw [he, sub_add_cancel]
  change HasDerivAt (fun t : ℝ => (∫ s in (0 : ℝ)..t, translate (s • v) g) + c1Value f)
    (translate ((0 : ℝ) • v) g) 0 at hFTC
  rw [hfun, zero_smul, translate_zero] at hFTC
  exact hFTC

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
