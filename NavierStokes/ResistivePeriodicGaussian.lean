import NavierStokes.MagneticPeriodicCoefficient
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! Gaussian averaging on actual three-dimensional periodic bounded
continuous fields. Constants are retained. This constructs the averaging
operators; smoothing and generator estimates are separate obligations. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement
open scoped BoundedContinuousFunction NNReal

abbrev Field := Space →ᵇ Space
private local instance : NormedAddCommGroup Field := inferInstance
private local instance : NormedSpace ℝ Field := inferInstance
private local instance : CompleteSpace Field := inferInstance

def orbit (f : Field) (hf : ∀ x i, f (x+coordinateVector i) = f x) (v : Space) (s : ℝ) : Field :=
  MagneticPeriodicCoefficient.boundedSlice (fun z : ℝ × Space => f (z.2+z.1 • v))
    (f.continuous.comp (continuous_snd.add (continuous_fst.smul continuous_const)))
    (fun s x i => by simpa only [add_right_comm] using hf (x+s • v) i) s

@[simp] theorem orbit_apply (f : Field) (hf) (v : Space) (s : ℝ) (x : Space) :
    orbit f hf v s x = f (x+s • v) := rfl

theorem orbit_continuous (f : Field) (hf) (v : Space) : Continuous (orbit f hf v) := by
  unfold orbit
  exact MagneticPeriodicCoefficient.boundedSlice_continuous _ _ _

theorem orbit_norm_le (f : Field) (hf) (v : Space) (s : ℝ) : ‖orbit f hf v s‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact f.norm_coe_le_norm _

theorem orbit_integrable (f : Field) (hf) (v : Space) (variance : ℝ≥0) :
    Integrable (orbit f hf v) (gaussianReal 0 variance) :=
  Integrable.of_bound (orbit_continuous f hf v).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (orbit_norm_le f hf v))

def lineAverage (f : Field) (hf : ∀ x i, f (x+coordinateVector i) = f x)
    (v : Space) (variance : ℝ≥0) : Field :=
  ∫ s, orbit f hf v s ∂gaussianReal 0 variance

theorem lineAverage_apply (f : Field) (hf) (v : Space) (variance : ℝ≥0) (x : Space) :
    lineAverage f hf v variance x = ∫ s, f (x+s • v) ∂gaussianReal 0 variance :=
  ((BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm (orbit_integrable f hf v variance)).symm

theorem lineAverage_norm_le (f : Field) (hf) (v : Space) (variance : ℝ≥0) :
    ‖lineAverage f hf v variance‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le
    (integrable_const ‖f‖ : Integrable (fun _ : ℝ => ‖f‖) (gaussianReal 0 variance))
    (Filter.Eventually.of_forall (orbit_norm_le f hf v))
  simpa [lineAverage] using h

theorem lineAverage_periodic (f : Field) (hf) (v : Space) (variance : ℝ≥0) (x : Space) (i : Fin 3) :
    lineAverage f hf v variance (x+coordinateVector i) = lineAverage f hf v variance x := by
  simp only [lineAverage_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by simpa only [add_right_comm] using hf (x+s • v) i)

@[simp] theorem lineAverage_zero (f : Field) (hf) (v : Space) : lineAverage f hf v 0 = f := by
  apply BoundedContinuousFunction.ext
  intro x
  rw [lineAverage_apply]
  simp

@[simp] theorem lineAverage_const (c : Space) (v : Space) (variance : ℝ≥0) :
    lineAverage (BoundedContinuousFunction.const Space c) (by intro x i; simp) v variance =
      BoundedContinuousFunction.const Space c := by
  apply BoundedContinuousFunction.ext
  intro x
  rw [lineAverage_apply]
  simp

/-- A product of exactly the three physical coordinate averages. -/
def spatialAverage (f : Field) (hf : ∀ x i, f (x+coordinateVector i) = f x)
    (variance : ℝ≥0) : Field :=
  let f2 := lineAverage f hf (coordinateVector 2) variance
  let h2 := lineAverage_periodic f hf (coordinateVector 2) variance
  let f1 := lineAverage f2 h2 (coordinateVector 1) variance
  let h1 := lineAverage_periodic f2 h2 (coordinateVector 1) variance
  lineAverage f1 h1 (coordinateVector 0) variance

theorem spatialAverage_norm_le (f : Field) (hf) (variance : ℝ≥0) :
    ‖spatialAverage f hf variance‖ ≤ ‖f‖ :=
  (lineAverage_norm_le _ _ _ _).trans ((lineAverage_norm_le _ _ _ _).trans (lineAverage_norm_le _ _ _ _))

theorem spatialAverage_periodic (f : Field) (hf) (variance : ℝ≥0) (x : Space) (i : Fin 3) :
    spatialAverage f hf variance (x+coordinateVector i) = spatialAverage f hf variance x :=
  lineAverage_periodic _ _ _ _ x i

@[simp] theorem spatialAverage_zero (f : Field) (hf) : spatialAverage f hf 0 = f := by
  simp [spatialAverage]

@[simp] theorem spatialAverage_const (c : Space) (variance : ℝ≥0) :
    spatialAverage (BoundedContinuousFunction.const Space c) (by intro x i; simp) variance =
      BoundedContinuousFunction.const Space c := by
  simp [spatialAverage]

/-- Physical elapsed time to variance, with the necessary factor two.
The generator identity for spatialAverage is not yet proved. -/
def physicalAverage (eta_m a t : ℝ) (f : Field) (hf : ∀ x i, f (x+coordinateVector i) = f x) : Field :=
  spatialAverage f hf (2*eta_m*(t-a)).toNNReal

theorem physical_variance {eta_m a t : ℝ} (heta : 0 ≤ eta_m) (ht : a ≤ t) :
    ((2*eta_m*(t-a)).toNNReal : ℝ) = 2*eta_m*(t-a) :=
  Real.coe_toNNReal _ (by positivity)

@[simp] theorem physicalAverage_initial (eta_m a : ℝ) (f : Field) (hf) :
    physicalAverage eta_m a a f hf = f := by simp [physicalAverage]

@[simp] theorem physicalAverage_axial_seed (eta_m a t Bz0 : ℝ) :
    physicalAverage eta_m a t (BoundedContinuousFunction.const Space (Bz0 • coordinateVector 2))
      (by intro x i; simp) = BoundedContinuousFunction.const Space (Bz0 • coordinateVector 2) := by
  simp [physicalAverage]
/-- The physical periodic Banach space is a closed subspace of bounded
continuous functions on the three-dimensional cover, with the uniform norm.
There is no whole-cover L2 or zero-mean condition. -/
def periodicFields : ClosedSubmodule ℝ Field where
  carrier := {f | ∀ x i, f (x+coordinateVector i) = f x}
  zero_mem' := by
    change ∀ x i, (0 : Field) (x+coordinateVector i) = (0 : Field) x
    intro x i
    rfl
  add_mem' := by
    intro f g hf hg x i
    change f (x+coordinateVector i)+g (x+coordinateVector i) = f x+g x
    rw [hf,hg]
  smul_mem' := by
    intro c f hf x i
    change c • f (x+coordinateVector i) = c • f x
    rw [hf]
  isClosed' := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun i => isClosed_eq
      (BoundedContinuousFunction.evalCLM ℝ (x+coordinateVector i)).continuous
      (BoundedContinuousFunction.evalCLM ℝ x).continuous))

abbrev PeriodicField := periodicFields.toSubmodule

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance

instance periodicFieldCompleteSpace : CompleteSpace PeriodicField := periodicFields.isClosed'.isComplete.completeSpace_coe

/-- Every constant vector, including the fixed nonzero axial seed, belongs. -/
def constantField (c : Space) : PeriodicField :=
  ⟨BoundedContinuousFunction.const Space c,by intro x i; simp⟩

def average (variance : ℝ≥0) (f : PeriodicField) : PeriodicField :=
  ⟨spatialAverage f.val f.property variance,spatialAverage_periodic f.val f.property variance⟩

theorem average_norm_le (variance : ℝ≥0) (f : PeriodicField) : ‖average variance f‖ ≤ ‖f‖ :=
  spatialAverage_norm_le f.val f.property variance

@[simp] theorem average_constant (variance : ℝ≥0) (c : Space) :
    average variance (constantField c) = constantField c := by
  apply Subtype.ext
  exact spatialAverage_const c variance

/-- Standard-Gaussian representation, suitable for dominated convergence. -/
theorem lineAverage_standard (f : Field) (hf) (v : Space) (variance : ℝ≥0) :
    lineAverage f hf v variance = ∫ s, orbit f hf v (Real.sqrt (variance:ℝ)*s) ∂gaussianReal 0 1 := by
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := (1:ℝ≥0)) (Real.sqrt (variance:ℝ))
  have he : Measure.map (fun s => Real.sqrt (variance:ℝ)*s) (gaussianReal 0 1) = gaussianReal 0 variance := by
    convert hmap using 2
    · simp
    · ext
      simp [Real.sq_sqrt variance.coe_nonneg]
  rw [lineAverage,← he,integral_map_of_stronglyMeasurable (by fun_prop) (orbit_continuous f hf v).stronglyMeasurable]

theorem lineAverage_continuous (f : Field) (hf) (v : Space) :
    Continuous (fun variance : ℝ≥0 => lineAverage f hf v variance) := by
  simp_rw [lineAverage_standard]
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro variance
    exact ((orbit_continuous f hf v).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro variance
    exact Filter.Eventually.of_forall (fun s => orbit_norm_le f hf v _)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun s => (orbit_continuous f hf v).comp
      ((Real.continuous_sqrt.comp continuous_subtype_val).mul_const s))
theorem lineAverage_add (f g : Field) (hf) (hg)
    (hfg : ∀ x i, (f+g) (x+coordinateVector i) = (f+g) x) (v : Space) (variance : ℝ≥0) :
    lineAverage (f+g) hfg v variance = lineAverage f hf v variance+lineAverage g hg v variance := by
  have he : orbit (f+g) hfg v = fun s => orbit f hf v s+orbit g hg v s := by
    funext s
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  unfold lineAverage
  rw [he,integral_add (orbit_integrable f hf v variance) (orbit_integrable g hg v variance)]

theorem lineAverage_smul (c : ℝ) (f : Field) (hf)
    (hcf : ∀ x i, (c • f) (x+coordinateVector i) = (c • f) x) (v : Space) (variance : ℝ≥0) :
    lineAverage (c • f) hcf v variance = c • lineAverage f hf v variance := by
  have he : orbit (c • f) hcf v = fun s => c • orbit f hf v s := by
    funext s
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  unfold lineAverage
  rw [he,integral_smul]

def lineOperator (v : Space) (variance : ℝ≥0) : PeriodicField →L[ℝ] PeriodicField :=
  LinearMap.mkContinuous
    { toFun := fun f : PeriodicField => ⟨lineAverage f.val f.property v variance,lineAverage_periodic f.val f.property v variance⟩
      map_add' := fun (f g : PeriodicField) => Subtype.ext (lineAverage_add f.val g.val f.property g.property _ v variance)
      map_smul' := fun (c : ℝ) (f : PeriodicField) => Subtype.ext (lineAverage_smul c f.val f.property _ v variance) }
    1 (fun f : PeriodicField => by
      change ‖lineAverage f.val f.property v variance‖ ≤ 1*‖f.val‖
      simpa only [one_mul] using lineAverage_norm_le f.val f.property v variance)

/-- A constructed bounded linear operator on the physical periodic Banach
space. Identification of its generator and derivative gain is still needed. -/
def spatialOperator (variance : ℝ≥0) : PeriodicField →L[ℝ] PeriodicField :=
  (lineOperator (coordinateVector 0) variance).comp
    ((lineOperator (coordinateVector 1) variance).comp (lineOperator (coordinateVector 2) variance))

@[simp] theorem spatialOperator_apply (variance : ℝ≥0) (f : PeriodicField) :
    spatialOperator variance f = average variance f := rfl

theorem spatialOperator_norm_le (variance : ℝ≥0) : ‖spatialOperator variance‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    rw [one_mul,spatialOperator_apply]
    exact average_norm_le variance f)
end NavierStokes.ResistiveMagnetic.PeriodicGaussian
