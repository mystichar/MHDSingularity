import NavierStokes.ResistivePeriodicTranslatedMild
import Euler.SmoothPathTimeJets
import NavierStokes.ResistivePeriodicPathJets

/-! Spatial regularity of the SAME mild path from a constant seed. Smooth
translation of the prescribed coefficients and the linear residual inverse
give smooth label-to-path dependence. This does not assert parabolic
smoothing for an arbitrary C1 initial datum. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicTranslation
open Set Filter MeasureTheory ProblemStatement PeriodicGaussian PeriodicSource PeriodicMild
open WeightedVolterra EulerVolterraConvolution
open scoped Topology ContDiff BoundedContinuousFunction

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

private local instance {T : ℝ} : NormedAddCommGroup (Path T) := inferInstance
private local instance {T : ℝ} : NormedSpace ℝ (Path T) := inferInstance
private local instance {T : ℝ} : NormedAddCommGroup C(Icc (0 : ℝ) T, Space) := inferInstance
private local instance {T : ℝ} : NormedSpace ℝ C(Icc (0 : ℝ) T, Space) := inferInstance

def weightCLM (T lambda : ℝ) : Path T →L[ℝ] Path T :=
  EulerContinuousTimeIntegral.multiplier
    ⟨fun t : Icc (0 : ℝ) T => Real.exp (lambda*t.val) • ContinuousLinearMap.id ℝ PeriodicC1,
      (show Continuous (fun t : Icc (0 : ℝ) T => Real.exp (lambda*t.val)) by fun_prop).smul continuous_const⟩

@[simp] theorem weightCLM_apply (T lambda : ℝ) (z : Path T) :
    weightCLM T lambda z = weightPath lambda z := rfl

theorem shiftedSource_zero {K : Type} [TopologicalSpace K] [CompactSpace K]
    (U : ValuePath K Space) (G : ValuePath K (Space →L[ℝ] Space)) :
    shiftedSource U G 0 = sourcePaths U G := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousLinearMap.ext
  intro B
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  change -(c1Derivative B).val x ((U t).val (x+0)) + (G t).val (x+0) ((c1Value B).val x) = _
  simp only [add_zero]
  rfl

theorem translateC1Path_add {T : ℝ} (y w : Space) (z : Path T) :
    translateC1Path y (translateC1Path w z) = translateC1Path (y+w) z := by
  apply ContinuousMap.ext
  intro t
  apply c1Value_injective
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  change (c1Value (z t)).val ((x+y)+w) = (c1Value (z t)).val (x+(y+w))
  rw [add_assoc]

theorem constant_seed_translation_contDiffAt_zero
    (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (c : Space) (z : Path T)
    (hz : Mild T hT eta_m heta
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) (c1Constant c) z) :
    ContDiffAt ℝ ∞ (fun y => translateC1Path y z) 0 := by
  let U := periodicPath A hp
  let G := periodicPath A.derivative (derivative_periodic A hp)
  let S := sourcePaths U G
  let n : ℝ := contractionWeight T hT eta_m heta S
  let Kw := weightedKernel (heatKernel eta_m heta) n
  let kw := weightedMajorant (kernelMajorant eta_m) n
  let fw := weightPath (-n) (freePath T eta_m (c1Constant c))
  let Z := fun y => weightPath (-n) (translateC1Path y z)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hKw := weightedKernel_continuous (heatKernel eta_m heta) (heatKernel_joint_continuous eta_m heta) n
  have hkw := weightedMajorant_integrable (kernelMajorant eta_m)
    (kernelMajorant_integrable eta_m T heta hT) hn
  have hk0 : ∀ r ∈ Ioc 0 T, 0 ≤ kw r := fun r _ =>
    weightedMajorant_nonneg _ _ _ (kernelMajorant_nonneg eta_m r)
  have hb : ∀ r ∈ Ioc 0 T, ∀ f : PeriodicField, ‖Kw r f‖ ≤ kw r * ‖f‖ :=
    fun r hr => weightedKernel_bound _ _ _ _ (fun f => heatKernel_bound eta_m heta hr.1 f)
  have hZ (y : Space) : LinearMild.IsMild T hT Kw (shiftedSource U G y) fw (Z y) := by
    have hh := mild_translate U G hz y
    rw [translateC1_constant] at hh
    exact LinearMild.weight T hT hh n
  have hsmall : kernelMass T kw * ‖shiftedSource U G 0‖ < 1 := by
    rw [shiftedSource_zero]
    exact (contractionWeight_small T hT eta_m heta S).trans_lt (by norm_num)
  have hreg := LinearMild.mild_family_contDiffAt T hT Kw kw hKw hkw hk0 hb
    (shiftedSource U G) (fun _ => fw) Z (shiftedSource_contDiff A hp) contDiff_const hZ 0 hsmall
  have hc := (weightCLM T n).contDiff.contDiffAt.comp 0 hreg
  simpa only [Function.comp_def,weightCLM_apply,Z,weightPath_cancel] using! hc

set_option maxHeartbeats 2400000 in
theorem constant_seed_translation_contDiff
    (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (c : Space) (z : Path T)
    (hz : Mild T hT eta_m heta
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) (c1Constant c) z) :
    ContDiff ℝ ∞ (fun y => translateC1Path y z) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have h0 := constant_seed_translation_contDiffAt_zero T hT eta_m heta A hp c z hz
  have hsub : ContDiffAt ℝ ∞ (fun w => translateC1Path w z) (y-y) := by simpa using h0
  have hc := ((translateC1Path y).contDiff.contDiffAt.comp (y-y) hsub).comp (f := fun w : Space => w-y) y
    (contDiffAt_id.sub contDiffAt_const)
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with w
  change translateC1Path w z = translateC1Path y (translateC1Path (w-y) z)
  rw [translateC1Path_add,show y+(w-y) = w by abel]

def fieldPath {T : ℝ} (z : Path T) (x : Space) : C(Icc (0 : ℝ) T,Space) :=
  ((valueEval x).comp c1Inclusion).compLeftContinuous ℝ (Icc (0 : ℝ) T) z

theorem fieldPath_contDiff {T : ℝ} (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) : ContDiff ℝ ∞ (fieldPath z) := by
  let E := ((valueEval (0 : Space)).comp c1Inclusion).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have hc := E.contDiff.comp hz
  have he : (fun y => E (translateC1Path y z)) = fieldPath z := by
    funext y
    apply ContinuousMap.ext
    intro t
    change (c1Value (z t)).val (0+y) = (c1Value (z t)).val y
    rw [zero_add]
  exact he ▸ hc

theorem slice_smooth {T : ℝ} (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (c1Value (z t)).val := by
  let E : C(Icc (0 : ℝ) T,Space) →L[ℝ] Space := ContinuousMap.evalCLM ℝ t
  exact E.contDiff.comp (fieldPath_contDiff z hz)

def magneticValues {T : ℝ} (z : Path T) : ValuePath (Icc (0 : ℝ) T) Space :=
  c1Inclusion.compLeftContinuous ℝ (Icc (0 : ℝ) T) z

theorem magneticValues_translation_contDiff {T : ℝ} (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) :
    ContDiff ℝ ∞ (fun y => translatePath y (magneticValues z)) := by
  have h := (c1Inclusion.compLeftContinuous ℝ (Icc (0 : ℝ) T)).contDiff.comp hz
  exact h

/-- This is continuity of actual spatial jets in time and space, derived
from differentiability into the full uniform time-path space. -/
theorem spatial_jet_continuous {T : ℝ} (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) (n : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × Space =>
      iteratedFDeriv ℝ n (c1Value (z p.1)).val p.2) := by
  have h := (EulerSmoothPathTimeJets.jetFamily_contDiff T (fieldPath z)
    (fieldPath_contDiff z hz) n).continuous
  have hc := continuous_eval.comp ((h.comp continuous_snd).prodMk continuous_fst)
  simpa only [Function.comp_def, EulerSmoothPathTimeJets.jetFamily_apply T (fieldPath z)
    (fieldPath_contDiff z hz) n] using! hc

theorem magnetic_laplacianPath_eq {T : ℝ} (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) (t : Icc (0 : ℝ) T) :
    laplacianPath (magneticValues z) t = laplacianField (c1Inclusion (z t))
      ((slice_smooth z hz t).of_le (by simp)) :=
  laplacianPath_eq _ (magneticValues_translation_contDiff z hz) t

set_option maxHeartbeats 2400000 in
theorem physical_laplacian_continuous {T : ℝ} (a : ℝ) (hT : 0 ≤ T) (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) :
    Continuous (fun p : SpaceTime => spatialLaplacian (physicalField a T hT z) p.1 p.2) := by
  let L := laplacianPath (magneticValues z)
  have he (p : SpaceTime) : spatialLaplacian (physicalField a T hT z) p.1 p.2 =
      (L (projIcc 0 T hT (p.1-a))).val p.2 := by
    have h := congrArg (fun f : PeriodicField => f.val p.2)
      (magnetic_laplacianPath_eq z hz (projIcc 0 T hT (p.1-a)))
    exact (h.trans (laplacianField_eq_spatialLaplacian _ _ p.1 p.2)).symm
  simp_rw [he]
  exact continuous_eval.comp
    (((continuous_subtype_val.comp L.continuous).comp
      (continuous_projIcc.comp (continuous_fst.sub continuous_const))).prodMk continuous_snd)

open MagneticPeriodicMain (budget threshold geometry Selected)

theorem actual_constant_translation_contDiff (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space) :
    ContDiff ℝ ∞ (fun y => translateC1Path y (actualPath scales hsel a b hab hb eta_m heta (c1Constant c))) := by
  let A := MagneticPeriodicCoefficient.actualOnSlab budget threshold geometry scales hsel a b hb
  have hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x :=
    fun t x i => MagneticPeriodicCoefficient.actual_periodic budget threshold geometry scales
      (a+t) (by have ht := t.property.2; change a+t.val < 1; linarith) x i
  apply constant_seed_translation_contDiff (b-a) (sub_nonneg.mpr hab.le) eta_m heta A hp c
  exact actual_mild scales hsel a b hab hb eta_m heta (c1Constant c)

theorem actual_constant_spatial_smooth (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => physicalField a (b-a) (sub_nonneg.mpr hab.le)
      (actualPath scales hsel a b hab hb eta_m heta (c1Constant c)) (t,x)) :=
  slice_smooth _ (actual_constant_translation_contDiff scales hsel a b hab hb eta_m heta c)
    (projIcc 0 (b-a) (sub_nonneg.mpr hab.le) (t-a))

theorem actual_constant_laplacian_continuous (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space) :
    Continuous (fun p : SpaceTime => spatialLaplacian
      (physicalField a (b-a) (sub_nonneg.mpr hab.le)
        (actualPath scales hsel a b hab hb eta_m heta (c1Constant c))) p.1 p.2) :=
  physical_laplacian_continuous a _ _
    (actual_constant_translation_contDiff scales hsel a b hab hb eta_m heta c)

end NavierStokes.ResistiveMagnetic.PeriodicTranslation
