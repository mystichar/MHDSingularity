import NavierStokes.ResistivePeriodicHeatSemigroup
import NavierStokes.ResistivePeriodicC1

/-! Derivative commutation and strong continuity on the complete physical
C1 graph. Integration takes place in that proved complete graph. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement Filter
open scoped Topology BoundedContinuousFunction NNReal

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance
private local instance : NormedAddCommGroup (PeriodicValue (Space →L[ℝ] V)) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue (Space →L[ℝ] V)) := inferInstance
private local instance : NormedAddCommGroup (PeriodicC1Value V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicC1Value V) := inferInstance

def translateC1 (y : Space) : PeriodicC1Value V →L[ℝ] PeriodicC1Value V :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨(translate y (c1Value f), translate y (c1Derivative f)), fun x =>
        (hasFDerivAt_comp_add_right y).mpr (c1_hasFDerivAt f (x + y))⟩
      map_add' := fun f g => by apply Subtype.ext; exact Prod.ext (map_add _ _ _) (map_add _ _ _)
      map_smul' := fun c f => by apply Subtype.ext; apply Prod.ext <;> rfl }
    1 (fun f => by
      change max ‖translate y (c1Value f)‖ ‖translate y (c1Derivative f)‖ ≤ 1 * ‖f‖
      rw [translate_norm, translate_norm, one_mul]
      exact le_rfl)

@[simp] theorem translateC1_value (y : Space) (f : PeriodicC1Value V) :
    c1Value (translateC1 y f) = translate y (c1Value f) := rfl

@[simp] theorem translateC1_derivative (y : Space) (f : PeriodicC1Value V) :
    c1Derivative (translateC1 y f) = translate y (c1Derivative f) := rfl

@[simp] theorem translateC1_norm (y : Space) (f : PeriodicC1Value V) : ‖translateC1 y f‖ = ‖f‖ := by
  change max ‖translate y (c1Value f)‖ ‖translate y (c1Derivative f)‖ =
    max ‖c1Value f‖ ‖c1Derivative f‖
  rw [translate_norm, translate_norm]

theorem translateC1_continuous (f : PeriodicC1Value V) : Continuous (fun y => translateC1 y f) := by
  apply Continuous.subtype_mk
  exact (translate_continuous (c1Value f)).prodMk (translate_continuous (c1Derivative f))

theorem translateC1_integrable (v : Space) (r : ℝ≥0) (f : PeriodicC1Value V) :
    Integrable (fun s : ℝ => translateC1 (s • v) f) (gaussianReal 0 r) :=
  Integrable.of_bound ((translateC1_continuous f).comp
    (show Continuous (fun s : ℝ => s • v) by fun_prop)).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (fun s => (translateC1_norm _ f).le))

def lineC1 (v : Space) (r : ℝ≥0) : PeriodicC1Value V →L[ℝ] PeriodicC1Value V :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ s : ℝ, translateC1 (s • v) f ∂gaussianReal 0 r
      map_add' := fun f g => by
        simp only [map_add]
        exact integral_add (translateC1_integrable v r f) (translateC1_integrable v r g)
      map_smul' := fun c f => by simp only [map_smul, integral_smul, RingHom.id_apply] }
    1 (fun f => by
      have h := norm_integral_le_of_norm_le
        (integrable_const ‖f‖ : Integrable (fun _ : ℝ => ‖f‖) (gaussianReal 0 r))
        (Eventually.of_forall (fun s => (translateC1_norm (s • v) f).le))
      simpa using h)

@[simp] theorem lineC1_value (v : Space) (r : ℝ≥0) (f : PeriodicC1Value V) :
    c1Value (lineC1 v r f) = valueLine v r (c1Value f) :=
  ((c1Value (V := V)).integral_comp_comm (translateC1_integrable v r f)).symm

/-- The actual derivative commutes with the same Gaussian average, using
its derivative-valued codomain extension. No solenoidal projection occurs. -/
@[simp] theorem lineC1_derivative (v : Space) (r : ℝ≥0) (f : PeriodicC1Value V) :
    c1Derivative (lineC1 v r f) = valueLine v r (c1Derivative f) :=
  ((c1Derivative (V := V)).integral_comp_comm (translateC1_integrable v r f)).symm

def spatialC1 (r : ℝ≥0) : PeriodicC1Value V →L[ℝ] PeriodicC1Value V :=
  (lineC1 (coordinateVector 0) r).comp
    ((lineC1 (coordinateVector 1) r).comp (lineC1 (coordinateVector 2) r))

@[simp] theorem spatialC1_value (r : ℝ≥0) (f : PeriodicC1Value V) :
    c1Value (spatialC1 r f) = valueSpatial r (c1Value f) := by
  simp [spatialC1, valueSpatial]

@[simp] theorem spatialC1_derivative (r : ℝ≥0) (f : PeriodicC1Value V) :
    c1Derivative (spatialC1 r f) = valueSpatial r (c1Derivative f) := by
  simp [spatialC1, valueSpatial]

@[simp] theorem spatialC1_zero (f : PeriodicC1Value V) : spatialC1 0 f = f := by
  apply c1Value_injective
  simp

theorem spatialC1_norm_le (r : ℝ≥0) (f : PeriodicC1Value V) : ‖spatialC1 r f‖ ≤ ‖f‖ := by
  rw [c1_norm (spatialC1 r f), spatialC1_value, spatialC1_derivative, c1_norm f]
  exact max_le_max (valueSpatial_norm_le _ _) (valueSpatial_norm_le _ _)

theorem spatialC1_strong_continuous (f : PeriodicC1Value V) :
    Continuous (fun r : ℝ≥0 => spatialC1 r f) := by
  apply Continuous.subtype_mk
  have h1 : Continuous (fun r : ℝ≥0 => valueSpatial r (c1Value f)) :=
    valueSpatial_joint_continuous.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous (fun r : ℝ≥0 => valueSpatial r (c1Derivative f)) :=
    valueSpatial_joint_continuous.comp (continuous_id.prodMk continuous_const)
  convert h1.prodMk h2 using 1
  funext r
  exact Prod.ext (spatialC1_value r f) (spatialC1_derivative r f)

def heatC1 (eta_m tau : ℝ) : PeriodicC1Value V →L[ℝ] PeriodicC1Value V :=
  spatialC1 (2 * eta_m * tau).toNNReal

theorem heatC1_strong_continuous (eta_m : ℝ) (f : PeriodicC1Value V) :
    Continuous (fun tau : ℝ => heatC1 eta_m tau f) :=
  (spatialC1_strong_continuous f).comp (by fun_prop)

@[simp] theorem heatC1_zero (eta_m : ℝ) (f : PeriodicC1Value V) : heatC1 eta_m 0 f = f := by
  simp [heatC1]

theorem heatC1_value (eta_m tau : ℝ) (f : PeriodicC1) :
    c1Inclusion (heatC1 eta_m tau f) = heat eta_m tau (c1Inclusion f) := by
  change c1Value (spatialC1 _ f) = spatialOperator _ (c1Value f)
  exact (spatialC1_value _ f).trans (congrArg (fun L => L (c1Value f))
    (valueSpatial_eq_spatialOperator _))

theorem heatC1_derivative (eta_m tau : ℝ) (f : PeriodicC1Value V) :
    c1Derivative (heatC1 eta_m tau f) = valueSpatial (2 * eta_m * tau).toNNReal (c1Derivative f) :=
  spatialC1_derivative _ f

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
