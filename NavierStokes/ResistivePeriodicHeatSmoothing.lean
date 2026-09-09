import NavierStokes.ResistivePeriodicHeatKernel
import NavierStokes.ResistivePeriodicTranslationDerivative

/-! Genuine C0-to-C1 smoothing by the existing physical Gaussian operator.
Coordinate estimates are converted to the full Fréchet operator norm. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement Filter
open EulerGaussianCylinderHeat
open scoped Topology BoundedContinuousFunction NNReal

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance
private local instance : NormedAddCommGroup (PeriodicC1Value V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicC1Value V) := inferInstance

theorem valueLine_strongDerivative (v w : Space) (r : ℝ≥0) (f g : PeriodicValue V)
    (hg : HasDerivAt (fun s : ℝ => translate (s • w) f) g 0) :
    HasDerivAt (fun s : ℝ => translate (s • w) (valueLine v r f)) (valueLine v r g) 0 := by
  have h := (valueLine v r).hasFDerivAt.comp_hasDerivAt 0 hg
  have he : (fun s : ℝ => valueLine v r (translate (s • w) f)) =
      fun s : ℝ => translate (s • w) (valueLine v r f) := by
    funext s
    exact (valueLine_translate v r (s • w) f).symm
  change HasDerivAt (fun s : ℝ => valueLine v r (translate (s • w) f)) (valueLine v r g) 0 at h
  rw [he] at h
  exact h

def spatialDirections (r : ℝ≥0) : Fin 3 → PeriodicValue V →L[ℝ] PeriodicValue V :=
  ![(valueLineDerivative (coordinateVector 0) r).comp
      ((valueLine (coordinateVector 1) r).comp (valueLine (coordinateVector 2) r)),
    (valueLine (coordinateVector 0) r).comp
      ((valueLineDerivative (coordinateVector 1) r).comp (valueLine (coordinateVector 2) r)),
    (valueLine (coordinateVector 0) r).comp
      ((valueLine (coordinateVector 1) r).comp (valueLineDerivative (coordinateVector 2) r))]

theorem spatialDirections_hasDerivAt {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => translate (s • coordinateVector i) (valueSpatial r f))
      (spatialDirections r i f) 0 := by
  fin_cases i
  · exact valueLine_hasDerivAt _ hr _
  · exact valueLine_strongDerivative _ _ _ _ _ (valueLine_hasDerivAt _ hr _)
  · exact valueLine_strongDerivative _ _ _ _ _
      (valueLine_strongDerivative _ _ _ _ _ (valueLine_hasDerivAt _ hr _))

theorem spatialDirections_norm_le {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) (i : Fin 3) :
    ‖spatialDirections r i f‖ ≤ gaussianAbsMoment 1 / Real.sqrt (r : ℝ) * ‖f‖ := by
  have hc : 0 ≤ gaussianAbsMoment 1 / Real.sqrt (r : ℝ) :=
    div_nonneg (gaussianAbsMoment_nonneg 1) (Real.sqrt_nonneg _)
  fin_cases i
  · change ‖valueLineDerivative (coordinateVector 0) r
      (valueLine (coordinateVector 1) r (valueLine (coordinateVector 2) r f))‖ ≤ _
    exact (valueLineDerivative_sqrt_bound _ hr _).trans
      (mul_le_mul_of_nonneg_left ((valueLine_norm_le _ _ _).trans (valueLine_norm_le _ _ _)) hc)
  · change ‖valueLine (coordinateVector 0) r
      (valueLineDerivative (coordinateVector 1) r (valueLine (coordinateVector 2) r f))‖ ≤ _
    exact (valueLine_norm_le _ _ _).trans ((valueLineDerivative_sqrt_bound _ hr _).trans
      (mul_le_mul_of_nonneg_left (valueLine_norm_le _ _ _) hc))
  · change ‖valueLine (coordinateVector 0) r
      (valueLine (coordinateVector 1) r (valueLineDerivative (coordinateVector 2) r f))‖ ≤ _
    exact (valueLine_norm_le _ _ _).trans
      ((valueLine_norm_le _ _ _).trans (valueLineDerivative_sqrt_bound _ hr _))

def spatialGradient (r : ℝ≥0) (f : PeriodicValue V) : PeriodicValue (Space →L[ℝ] V) :=
  derivativeTranspose (coordinateGradient (fun i => spatialDirections r i f))

theorem valueSpatial_hasFDerivAt {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) (x : Space) :
    HasFDerivAt (valueSpatial r f).val ((spatialGradient r f).val x) x :=
  hasFDerivAt_of_translation _ _
    (translate_hasFDerivAt_coordinates _ _ (spatialDirections_hasDerivAt hr f)) x

theorem spatialGradient_norm_le {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) :
    ‖spatialGradient r f‖ ≤ (3 * gaussianAbsMoment 1 / Real.sqrt (r : ℝ)) * ‖f‖ := by
  apply (derivativeTranspose_norm_le _).trans
  have h := coordinateGradient_norm_le (fun i => spatialDirections r i f)
    (mul_nonneg (div_nonneg (gaussianAbsMoment_nonneg 1) (Real.sqrt_nonneg _)) (norm_nonneg f))
    (spatialDirections_norm_le hr f)
  exact h.trans_eq (by ring)

/-- This bound is on the full spatial Fréchet operator, uniformly in x. -/
theorem valueSpatial_fderiv_bound {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) (x : Space) :
    ‖fderiv ℝ (valueSpatial r f).val x‖ ≤ (3 * gaussianAbsMoment 1 / Real.sqrt (r : ℝ)) * ‖f‖ := by
  rw [(valueSpatial_hasFDerivAt hr f x).fderiv]
  exact ((spatialGradient r f).val.norm_coe_le_norm x).trans (spatialGradient_norm_le hr f)

def gainVariance (r : ℝ≥0) (hr : 0 < r) : PeriodicValue V →L[ℝ] PeriodicC1Value V :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨(valueSpatial r f, spatialGradient r f), valueSpatial_hasFDerivAt hr f⟩
      map_add' := fun f g => by
        apply Subtype.ext
        apply Prod.ext (map_add _ _ _)
        apply Subtype.ext
        ext x w
        simp [spatialGradient, coordinateGradient, map_add]
        module
      map_smul' := fun c f => by
        apply Subtype.ext
        apply Prod.ext (map_smul _ _ _)
        apply Subtype.ext
        ext x w
        simp [spatialGradient, coordinateGradient, map_smul, smul_smul, mul_comm, smul_add] }
    (1 + 3 * gaussianAbsMoment 1 / Real.sqrt (r : ℝ)) (fun f => by
      change max ‖valueSpatial r f‖ ‖spatialGradient r f‖ ≤ _
      apply max_le
      · have h := valueSpatial_norm_le r f
        have hp := mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (gaussianAbsMoment_nonneg 1))
            (Real.sqrt_nonneg (r : ℝ)))
          (norm_nonneg f)
        nlinarith
      · have h := spatialGradient_norm_le hr f
        nlinarith [norm_nonneg f])

@[simp] theorem gainVariance_value (r : ℝ≥0) (hr : 0 < r) (f : PeriodicValue V) :
    c1Value (gainVariance r hr f) = valueSpatial r f := rfl

@[simp] theorem gainVariance_derivative (r : ℝ≥0) (hr : 0 < r) (f : PeriodicValue V) :
    c1Derivative (gainVariance r hr f) = spatialGradient r f := rfl

theorem gainVariance_norm_le (r : ℝ≥0) (hr : 0 < r) :
    ‖gainVariance (V := V) r hr‖ ≤ 1 + 3 * gaussianAbsMoment 1 / Real.sqrt (r : ℝ) :=
  LinearMap.mkContinuous_norm_le _
    (add_nonneg zero_le_one (div_nonneg (mul_nonneg (by norm_num) (gaussianAbsMoment_nonneg 1))
      (Real.sqrt_nonneg _))) _

/-- A finite, nonoptimized dimensional constant independent of diffusivity,
elapsed time, and input. The factor sqrt(2) improves the actual bound; this
larger constant is convenient for the Volterra majorant. -/
def heatConstant : ℝ := 3 * gaussianAbsMoment 1

theorem heatConstant_nonneg : 0 ≤ heatConstant :=
  mul_nonneg (by norm_num) (gaussianAbsMoment_nonneg 1)

def heatGain (eta_m tau : ℝ) (heta : 0 < eta_m) (htau : 0 < tau) :
    PeriodicField →L[ℝ] PeriodicC1 :=
  gainVariance (2 * eta_m * tau).toNNReal (Real.toNNReal_pos.mpr (by positivity))

@[simp] theorem heatGain_value (eta_m tau : ℝ) (heta : 0 < eta_m) (htau : 0 < tau) (f : PeriodicField) :
    c1Inclusion (heatGain eta_m tau heta htau f) = heat eta_m tau f := by
  exact congrArg (fun L => L f) (valueSpatial_eq_spatialOperator _)

theorem heatGain_norm_le (eta_m tau : ℝ) (heta : 0 < eta_m) (htau : 0 < tau) :
    ‖heatGain eta_m tau heta htau‖ ≤ 1 + heatConstant / Real.sqrt (eta_m * tau) := by
  apply (gainVariance_norm_le _ _).trans
  rw [Real.coe_toNNReal _ (by positivity)]
  apply add_le_add_right
  exact div_le_div_of_nonneg_left heatConstant_nonneg (Real.sqrt_pos.mpr (mul_pos heta htau))
    (Real.sqrt_le_sqrt (by nlinarith [mul_pos heta htau]))

/-- The physical-time derivative estimate, in the full spatial operator
norm. The same constant works for every positive eta_m and tau. -/
theorem heat_fderiv_bound (eta_m tau : ℝ) (heta : 0 < eta_m) (htau : 0 < tau)
    (f : PeriodicField) (x : Space) :
    ‖fderiv ℝ (heat eta_m tau f).val x‖ ≤ heatConstant / Real.sqrt (eta_m * tau) * ‖f‖ := by
  rw [heat, ← valueSpatial_eq_spatialOperator]
  apply (valueSpatial_fderiv_bound (Real.toNNReal_pos.mpr (by positivity)) f x).trans
  rw [Real.coe_toNNReal _ (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  exact div_le_div_of_nonneg_left heatConstant_nonneg (Real.sqrt_pos.mpr (mul_pos heta htau))
    (Real.sqrt_le_sqrt (by nlinarith [mul_pos heta htau]))

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
