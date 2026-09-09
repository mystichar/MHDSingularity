import NavierStokes.ResistivePeriodicTranslationRegularity
import NavierStokes.ResistiveMildParameter

/-! Exact spatial translation covariance of the existing physical mild
equation and smooth translation of its prescribed coefficients. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicTranslation
open Set Filter MeasureTheory ProblemStatement PeriodicGaussian PeriodicSource PeriodicMild
open scoped Topology ContDiff BoundedContinuousFunction NNReal

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup DerivativeField := inferInstance
private local instance : NormedSpace ℝ DerivativeField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

private local instance {K : Type} [TopologicalSpace K] [CompactSpace K] :
    NormedAddCommGroup (ValuePath K Space) := inferInstance
private local instance {K : Type} [TopologicalSpace K] [CompactSpace K] :
    NormedSpace ℝ (ValuePath K Space) := inferInstance
private local instance {K : Type} [TopologicalSpace K] [CompactSpace K] :
    NormedAddCommGroup (ValuePath K (Space →L[ℝ] Space)) := inferInstance
private local instance {K : Type} [TopologicalSpace K] [CompactSpace K] :
    NormedSpace ℝ (ValuePath K (Space →L[ℝ] Space)) := inferInstance
private local instance {K : Type} [TopologicalSpace K] [CompactSpace K] :
    NormedAddCommGroup C(K,PeriodicC1 →L[ℝ] PeriodicField) := inferInstance
private local instance {K : Type} [TopologicalSpace K] [CompactSpace K] :
    NormedSpace ℝ C(K,PeriodicC1 →L[ℝ] PeriodicField) := inferInstance
private local instance {T : ℝ} : NormedAddCommGroup (Path T) := inferInstance
private local instance {T : ℝ} : NormedSpace ℝ (Path T) := inferInstance

private local instance : NormedAddCommGroup (PeriodicC1 →L[ℝ] PeriodicField) := inferInstance
private local instance : NormedSpace ℝ (PeriodicC1 →L[ℝ] PeriodicField) := inferInstance

def sourceValueLinear : PeriodicField →L[ℝ] PeriodicC1 →L[ℝ] PeriodicField :=
  -(((ContinuousLinearMap.compL ℝ PeriodicC1 DerivativeField PeriodicField).flip c1Derivative).comp pairing.flip)

def sourceDerivativeLinear : DerivativeField →L[ℝ] PeriodicC1 →L[ℝ] PeriodicField :=
  ((ContinuousLinearMap.compL ℝ PeriodicC1 PeriodicField PeriodicField).flip c1Value).comp pairing

def sourcePaths {K : Type} [TopologicalSpace K] [CompactSpace K]
    (U : ValuePath K Space) (G : ValuePath K (Space →L[ℝ] Space)) : C(K,PeriodicC1 →L[ℝ] PeriodicField) :=
  sourceValueLinear.compLeftContinuous ℝ K U + sourceDerivativeLinear.compLeftContinuous ℝ K G

@[simp] theorem sourcePaths_apply {K : Type} [TopologicalSpace K] [CompactSpace K]
    (U : ValuePath K Space) (G : ValuePath K (Space →L[ℝ] Space)) (t : K) (B : PeriodicC1) :
    sourcePaths U G t B = sourceOperator (U t) (G t) B := rfl

def shiftedSource {K : Type} [TopologicalSpace K] [CompactSpace K]
    (U : ValuePath K Space) (G : ValuePath K (Space →L[ℝ] Space)) (y : Space) :
    C(K,PeriodicC1 →L[ℝ] PeriodicField) := sourcePaths (translatePath y U) (translatePath y G)

theorem shiftedSource_contDiff {K : Type} [TopologicalSpace K] [CompactSpace K]
    (A : SmoothTimeField K Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x) :
    ContDiff ℝ ∞ (shiftedSource (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) := by
  exact ((sourceValueLinear.compLeftContinuous ℝ K).contDiff.comp (translatePath_contDiff A hp)).add
    ((sourceDerivativeLinear.compLeftContinuous ℝ K).contDiff.comp
      (translatePath_contDiff A.derivative (derivative_periodic A hp)))

theorem source_translate (u : PeriodicField) (G : DerivativeField) (B : PeriodicC1) (y : Space) :
    PeriodicGaussian.translate y (sourceOperator u G B) =
      sourceOperator (PeriodicGaussian.translate y u) (PeriodicGaussian.translate y G) (translateC1 y B) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem valueSpatial_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (r : ℝ≥0) (y : Space) (f : PeriodicValue V) :
    PeriodicGaussian.translate y (valueSpatial r f) = valueSpatial r (PeriodicGaussian.translate y f) := by
  simp only [valueSpatial, ContinuousLinearMap.comp_apply, valueLine_translate]

theorem heat_translate (eta_m r : ℝ) (y : Space) (f : PeriodicField) :
    PeriodicGaussian.translate y (heat eta_m r f) = heat eta_m r (PeriodicGaussian.translate y f) := by
  rw [heat,← valueSpatial_eq_spatialOperator]
  exact valueSpatial_translate _ y f

theorem heatC1_translate (eta_m r : ℝ) (y : Space) (B : PeriodicC1) :
    translateC1 y (heatC1 eta_m r B) = heatC1 eta_m r (translateC1 y B) := by
  apply c1Value_injective
  change c1Inclusion (translateC1 y (heatC1 eta_m r B)) = c1Inclusion (heatC1 eta_m r (translateC1 y B))
  rw [heatC1_value]
  change PeriodicGaussian.translate y (c1Inclusion (heatC1 eta_m r B)) = _
  rw [heatC1_value,heat_translate]
  rfl

theorem heatKernel_translate (eta_m : ℝ) (heta : 0 < eta_m) (r : ℝ) (y : Space) (f : PeriodicField) :
    translateC1 y (heatKernel eta_m heta r f) = heatKernel eta_m heta r (PeriodicGaussian.translate y f) := by
  by_cases hr : 0 < r
  · apply c1Value_injective
    change PeriodicGaussian.translate y (c1Inclusion (heatKernel eta_m heta r f)) =
      c1Inclusion (heatKernel eta_m heta r (PeriodicGaussian.translate y f))
    have h1 := heatKernel_value eta_m heta hr f
    have h2 := heatKernel_value eta_m heta hr (PeriodicGaussian.translate y f)
    exact (congrArg (PeriodicGaussian.translate y) h1).trans ((heat_translate eta_m r y f).trans h2.symm)
  · rw [heatKernel_nonpositive eta_m heta (not_lt.mp hr)]
    change translateC1 y 0 = 0
    exact map_zero _

def translateC1Path {T : ℝ} (y : Space) : Path T →L[ℝ] Path T :=
  (translateC1 y).compLeftContinuous ℝ (Icc (0 : ℝ) T)

set_option maxHeartbeats 2400000 in
theorem mild_translate {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    (U : ValuePath (Icc (0 : ℝ) T) Space) (G : ValuePath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    {B_a : PeriodicC1} {z : Path T} (hz : Mild T hT eta_m heta (sourcePaths U G) B_a z) (y : Space) :
    Mild T hT eta_m heta (shiftedSource U G y) (translateC1 y B_a) (translateC1Path y z) := by
  intro t
  have he := congrArg (translateC1 y) (mild_equation hz t)
  rw [map_add,heatC1_translate,
    ← (translateC1 y).intervalIntegral_comp_comm (mild_integrable T hT eta_m heta (sourcePaths U G) z t)] at he
  refine he.trans ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  let s := projIcc 0 T hT (t.val-r)
  exact (heatKernel_translate eta_m heta r y (sourceOperator (U s) (G s) (z s))).trans
    (congrArg (heatKernel eta_m heta r) (source_translate (U s) (G s) (z s) y))

theorem translateC1_constant (y : Space) (c : Space) : translateC1 y (c1Constant c) = c1Constant c := by
  apply c1Value_injective
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  rfl

end NavierStokes.ResistiveMagnetic.PeriodicTranslation
