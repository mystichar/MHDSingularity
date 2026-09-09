import NavierStokes.ResistivePeriodicHeatSpace

/-! Variance and physical elapsed-time semigroup laws for the existing
three-coordinate Gaussian averages. Strong continuity is in the uniform
norm for each datum, including at zero variance; it is not operator-norm
continuity at zero. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement
open scoped BoundedContinuousFunction NNReal

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

omit [CompleteSpace V] in
theorem translation_integrable (v : Space) (f : PeriodicValue V)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun s : ℝ => translate (s • v) f) μ :=
  Integrable.of_bound ((translate_continuous f).comp
    (continuous_id.smul continuous_const)).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (fun s => (translate_norm (s • v) f).le))

/-- Codomain extension, with an equality bridge to `lineOperator` below. -/
def valueLine (v : Space) (variance : ℝ≥0) : PeriodicValue V →L[ℝ] PeriodicValue V :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ s : ℝ, translate (s • v) f ∂gaussianReal 0 variance
      map_add' := fun f g => by
        simp only [map_add]
        exact integral_add (translation_integrable v f _) (translation_integrable v g _)
      map_smul' := fun c f => by simp only [map_smul, integral_smul, RingHom.id_apply] }
    1 (fun f => by
      have h := norm_integral_le_of_norm_le
        (integrable_const ‖f‖ : Integrable (fun _ : ℝ => ‖f‖) (gaussianReal 0 variance))
        (Filter.Eventually.of_forall (fun s => (translate_norm (s • v) f).le))
      simpa using h)

theorem valueLine_eval (v : Space) (variance : ℝ≥0) (f : PeriodicValue V) (x : Space) :
    (valueLine v variance f).val x = ∫ s : ℝ, f.val (x + s • v) ∂gaussianReal 0 variance :=
  ((valueEval x).integral_comp_comm (translation_integrable v f _)).symm

/-- The codomain extension specializes to the original physical operator. -/
theorem valueLine_eq_lineOperator (v : Space) (variance : ℝ≥0) :
    valueLine (V := Space) v variance = lineOperator v variance := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact (valueLine_eval v variance f x).trans
    (lineAverage_apply f.val f.property v variance x).symm

theorem valueLine_norm_le (v : Space) (variance : ℝ≥0) (f : PeriodicValue V) :
    ‖valueLine v variance f‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le
    (integrable_const ‖f‖ : Integrable (fun _ : ℝ => ‖f‖) (gaussianReal 0 variance))
    (Filter.Eventually.of_forall (fun s => (translate_norm (s • v) f).le))
  change ‖∫ s : ℝ, translate (s • v) f ∂gaussianReal 0 variance‖ ≤ ‖f‖
  simpa using h

theorem valueLine_opNorm_le (v : Space) (variance : ℝ≥0) :
    ‖valueLine (V := V) v variance‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa only [one_mul] using valueLine_norm_le v variance f)

@[simp] theorem valueLine_zero (v : Space) (f : PeriodicValue V) : valueLine v 0 f = f := by
  change (∫ s : ℝ, translate (s • v) f ∂gaussianReal 0 0) = f
  simp

@[simp] theorem valueLine_constant (v : Space) (variance : ℝ≥0) (c : V) :
    valueLine v variance (valueConstant c) = valueConstant c := by
  apply Subtype.ext
  ext x
  rw [valueLine_eval]
  simp [valueConstant]

theorem valueLine_translate (v : Space) (variance : ℝ≥0) (y : Space) (f : PeriodicValue V) :
    translate y (valueLine v variance f) = valueLine v variance (translate y f) := by
  change translate y (∫ s : ℝ, translate (s • v) f ∂gaussianReal 0 variance) = _
  rw [← (translate y).integral_comp_comm (translation_integrable v f _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => translate_commute y (s • v) f)

theorem valueLine_semigroup (v : Space) (r s : ℝ≥0) (f : PeriodicValue V) :
    valueLine v r (valueLine v s f) = valueLine v (r + s) f := by
  have hi : Integrable (fun p : ℝ × ℝ => translate ((p.1 + p.2) • v) f)
      ((gaussianReal 0 r).prod (gaussianReal 0 s)) :=
    Integrable.of_bound ((translate_continuous f).comp
      ((continuous_fst.add continuous_snd).smul continuous_const)).aestronglyMeasurable
      ‖f‖ (Filter.Eventually.of_forall (fun p => (translate_norm _ f).le))
  have hc : gaussianReal 0 r ∗ gaussianReal 0 s = gaussianReal 0 (r + s) := by
    simpa using (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := r) (v₂ := s))
  calc
    _ = ∫ x : ℝ, ∫ y : ℝ, translate ((x + y) • v) f
        ∂gaussianReal 0 s ∂gaussianReal 0 r := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [valueLine_translate]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only
        rw [translate_add, add_smul, add_comm (y • v)])
    _ = ∫ p : ℝ × ℝ, translate ((p.1 + p.2) • v) f
        ∂(gaussianReal 0 r).prod (gaussianReal 0 s) := (integral_prod _ hi).symm
    _ = ∫ x : ℝ, translate (x • v) f ∂(gaussianReal 0 r ∗ gaussianReal 0 s) := by
      rw [Measure.conv]
      exact (integral_map_of_stronglyMeasurable
        (show Measurable (fun p : ℝ × ℝ => p.1 + p.2) by fun_prop)
        (show StronglyMeasurable (fun x : ℝ => translate (x • v) f) from
          ((translate_continuous f).comp
            (continuous_id.smul continuous_const)).stronglyMeasurable)).symm
    _ = _ := by rw [hc]; rfl

theorem valueLine_commute (v w : Space) (r s : ℝ≥0) (f : PeriodicValue V) :
    valueLine v r (valueLine w s f) = valueLine w s (valueLine v r f) := by
  change valueLine v r (∫ x : ℝ, translate (x • w) f ∂gaussianReal 0 s) = _
  rw [← (valueLine v r).integral_comp_comm (translation_integrable w f _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (valueLine_translate v r (x • w) f).symm)

omit [CompleteSpace V] in
theorem valueLine_standard (v : Space) (variance : ℝ≥0) (f : PeriodicValue V) :
    valueLine v variance f =
      ∫ s : ℝ, translate ((Real.sqrt (variance : ℝ) * s) • v) f ∂gaussianReal 0 1 := by
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt (variance : ℝ))
  have he : Measure.map (fun s => Real.sqrt (variance : ℝ) * s) (gaussianReal 0 1) =
      gaussianReal 0 variance := by
    convert hmap using 2
    · simp
    · ext
      simp [Real.sq_sqrt variance.coe_nonneg]
  change (∫ s : ℝ, translate (s • v) f ∂gaussianReal 0 variance) = _
  rw [← he]
  exact integral_map_of_stronglyMeasurable (by fun_prop)
    (show StronglyMeasurable (fun s : ℝ => translate (s • v) f) from
      ((translate_continuous f).comp (continuous_id.smul continuous_const)).stronglyMeasurable)

theorem valueLine_continuous (v : Space) (f : PeriodicValue V) :
    Continuous (fun variance : ℝ≥0 => valueLine v variance f) := by
  simp_rw [valueLine_standard]
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro r
    exact ((translate_continuous f).comp
      ((continuous_const.mul continuous_id).smul continuous_const)).aestronglyMeasurable
  · intro r
    exact Filter.Eventually.of_forall (fun s => (translate_norm _ f).le)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun s => (translate_continuous f).comp
      (((Real.continuous_sqrt.comp continuous_subtype_val).mul_const s).smul continuous_const))

theorem valueLine_joint_continuous (v : Space) :
    Continuous (fun p : ℝ≥0 × PeriodicValue V => valueLine v p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro r
    exact (valueLine v r).lipschitzWith_of_opNorm_le (valueLine_opNorm_le v r)
  · exact valueLine_continuous v

def valueSpatial (variance : ℝ≥0) : PeriodicValue V →L[ℝ] PeriodicValue V :=
  (valueLine (coordinateVector 0) variance).comp
    ((valueLine (coordinateVector 1) variance).comp (valueLine (coordinateVector 2) variance))

theorem valueSpatial_eq_spatialOperator (variance : ℝ≥0) :
    valueSpatial (V := Space) variance = spatialOperator variance := by
  simp only [valueSpatial, spatialOperator, valueLine_eq_lineOperator]
  rfl

@[simp] theorem valueSpatial_zero (f : PeriodicValue V) : valueSpatial 0 f = f := by
  simp [valueSpatial]

@[simp] theorem valueSpatial_constant (variance : ℝ≥0) (c : V) :
    valueSpatial variance (valueConstant c) = valueConstant c := by
  simp [valueSpatial]

theorem valueSpatial_norm_le (variance : ℝ≥0) (f : PeriodicValue V) :
    ‖valueSpatial variance f‖ ≤ ‖f‖ :=
  (valueLine_norm_le _ _ _).trans ((valueLine_norm_le _ _ _).trans (valueLine_norm_le _ _ _))

theorem valueSpatial_semigroup (r s : ℝ≥0) (f : PeriodicValue V) :
    valueSpatial r (valueSpatial s f) = valueSpatial (r + s) f := by
  simp only [valueSpatial, ContinuousLinearMap.comp_apply]
  rw [valueLine_commute (coordinateVector 2) (coordinateVector 0) r s,
    valueLine_commute (coordinateVector 1) (coordinateVector 0) r s,
    valueLine_semigroup]
  rw [valueLine_commute (coordinateVector 2) (coordinateVector 1) r s,
    valueLine_semigroup, valueLine_semigroup]

theorem valueSpatial_joint_continuous :
    Continuous (fun p : ℝ≥0 × PeriodicValue V => valueSpatial p.1 p.2) := by
  exact (valueLine_joint_continuous (coordinateVector 0)).comp (continuous_fst.prodMk
    ((valueLine_joint_continuous (coordinateVector 1)).comp (continuous_fst.prodMk
      (valueLine_joint_continuous (coordinateVector 2)))))

/-- The requested variance law for the original operator, including zero. -/
theorem spatialOperator_semigroup (r s : ℝ≥0) :
    spatialOperator (r + s) = (spatialOperator r).comp (spatialOperator s) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [← valueSpatial_eq_spatialOperator, ← valueSpatial_eq_spatialOperator,
    ← valueSpatial_eq_spatialOperator]
  change valueSpatial (r + s) f = valueSpatial r (valueSpatial s f)
  exact (valueSpatial_semigroup r s f).symm

@[simp] theorem spatialOperator_zero : spatialOperator 0 = ContinuousLinearMap.id ℝ PeriodicField := by
  apply ContinuousLinearMap.ext
  intro f
  rw [← valueSpatial_eq_spatialOperator]
  exact valueSpatial_zero f

theorem spatialOperator_strong_continuous (f : PeriodicField) :
    Continuous (fun r : ℝ≥0 => spatialOperator r f) := by
  simp_rw [← valueSpatial_eq_spatialOperator]
  exact valueSpatial_joint_continuous.comp (continuous_id.prodMk continuous_const)

/-- Elapsed physical time. Semigroup statements below require nonnegative
diffusivity and elapsed times; clamping does not extend them to negative times. -/
def heat (eta_m tau : ℝ) : PeriodicField →L[ℝ] PeriodicField :=
  spatialOperator (2 * eta_m * tau).toNNReal

@[simp] theorem heat_zero (eta_m : ℝ) : heat eta_m 0 = ContinuousLinearMap.id ℝ PeriodicField := by
  simp [heat]

theorem heat_semigroup {eta_m r s : ℝ} (heta : 0 ≤ eta_m) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    heat eta_m (r + s) = (heat eta_m r).comp (heat eta_m s) := by
  have he : (2 * eta_m * (r + s)).toNNReal =
      (2 * eta_m * r).toNNReal + (2 * eta_m * s).toNNReal := by
    rw [mul_add, Real.toNNReal_add (by positivity) (by positivity)]
  rw [heat, he, spatialOperator_semigroup]
  rfl

theorem heat_norm_le (eta_m tau : ℝ) : ‖heat eta_m tau‖ ≤ 1 := spatialOperator_norm_le _

theorem heat_apply_norm_le (eta_m tau : ℝ) (f : PeriodicField) : ‖heat eta_m tau f‖ ≤ ‖f‖ :=
  average_norm_le _ f

@[simp] theorem heat_constant (eta_m tau : ℝ) (c : Space) :
    heat eta_m tau (constantField c) = constantField c := average_constant _ c

theorem heat_strong_continuous (eta_m : ℝ) (f : PeriodicField) :
    Continuous (fun tau : ℝ => heat eta_m tau f) :=
  (spatialOperator_strong_continuous f).comp (by fun_prop)

theorem heat_joint_continuous (eta_m : ℝ) :
    Continuous (fun p : ℝ × PeriodicField => heat eta_m p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro tau
    exact (heat eta_m tau).lipschitzWith_of_opNorm_le (heat_norm_le eta_m tau)
  · exact heat_strong_continuous eta_m

/-- Equality with the earlier absolute-time averaging convention. -/
theorem heat_eq_physicalAverage (eta_m a t : ℝ) (f : PeriodicField) :
    (heat eta_m (t - a) f).val = physicalAverage eta_m a t f.val f.property := rfl

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
