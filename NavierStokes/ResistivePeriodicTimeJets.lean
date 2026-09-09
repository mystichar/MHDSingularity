import NavierStokes.ResistivePeriodicClassical

/-! Mixed derivatives are obtained from the proved time equation in
continuous path spaces. No joint C-infinity hypothesis is imposed. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace NavierStokes.ResistiveMagnetic.PeriodicTranslation
open Set Filter ProblemStatement PeriodicGaussian PeriodicSource PeriodicMild
open EulerVolterraConvolution EulerSmoothPathTimeJets
open scoped Topology ContDiff BoundedContinuousFunction
private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance
private local instance {T : ℝ} : NormedAddCommGroup (Path T) := inferInstance
private local instance {T : ℝ} : NormedSpace ℝ (Path T) := inferInstance
private local instance {T : ℝ} : NormedAddCommGroup (ValuePath (Icc (0 : ℝ) T) Space) := inferInstance
private local instance {T : ℝ} : NormedSpace ℝ (ValuePath (Icc (0 : ℝ) T) Space) := inferInstance

theorem source_translation_contDiff {T : ℝ}
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (z : Path T) (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) :
    ContDiff ℝ ∞ (fun y => translatePath y (valueSource
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) z)) := by
  let U := periodicPath A hp
  let G := periodicPath A.derivative (derivative_periodic A hp)
  have hc := EulerContinuousPathCalculus.contDiff_apply (shiftedSource U G)
    (fun y => translateC1Path y z) (shiftedSource_contDiff A hp) hz
  have he : (fun y => EulerContinuousTimeIntegral.multiplier (shiftedSource U G y) (translateC1Path y z)) =
      fun y => translatePath y (valueSource (sourcePaths U G) z) := by
    funext y
    apply ContinuousMap.ext
    intro t
    exact (source_translate (U t) (G t) (z t) y).symm
  exact he ▸ hc

def pointPath {T : ℝ} (f : ValuePath (Icc (0 : ℝ) T) Space) (x : Space) : C(Icc (0 : ℝ) T,Space) :=
  (valueEval x).compLeftContinuous ℝ (Icc (0 : ℝ) T) f

theorem pointPath_contDiff {T : ℝ} (f : ValuePath (Icc (0 : ℝ) T) Space)
    (hf : ContDiff ℝ ∞ (fun y => translatePath y f)) : ContDiff ℝ ∞ (pointPath f) := by
  let E : ValuePath (Icc (0 : ℝ) T) Space →L[ℝ] C(Icc (0 : ℝ) T,Space) :=
    (valueEval (0 : Space)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have hc := E.contDiff.comp hf
  have he : (fun y => E (translatePath y f)) = pointPath f := by
    funext y
    apply ContinuousMap.ext
    intro t
    change (f t).val (0+y) = (f t).val y
    rw [zero_add]
  exact he ▸ hc

def rhsPath {T : ℝ} (eta_m : ℝ) (S : Coefficient T) (z : Path T) : C(Icc (0 : ℝ) T,PeriodicField) :=
  eta_m • laplacianEvolution z + valueSource S z

theorem rhs_translation_contDiff {T : ℝ} (eta_m : ℝ)
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (z : Path T) (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) :
    ContDiff ℝ ∞ (fun y => translatePath y (rhsPath eta_m
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) z)) := by
  simp only [rhsPath,laplacianEvolution]
  exact ((laplacianPath_contDiff _ (magneticValues_translation_contDiff z hz)).const_smul eta_m).add
    (source_translation_contDiff A hp z hz)

/-- Actual spatial jets satisfy the differentiated time equation within
the forward slab, including its initial endpoint. -/
theorem mild_spatial_jet_time_derivative {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (c : Space) (z : Path T)
    (hz : Mild T hT eta_m heta
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) (c1Constant c) z)
    (n : ℕ) (x : Space) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (jetFamily T (fieldPath z) n x))
      (jetFamily T (pointPath (rhsPath eta_m
        (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) z)) n x t)
      (Icc (0 : ℝ) T) t := by
  have hs := constant_seed_translation_contDiff T hT eta_m heta A hp c z hz
  apply jetFamily_hasDerivWithinAt T hT (fieldPath z) _
    (fieldPath_contDiff z hs) (pointPath_contDiff _ (rhs_translation_contDiff eta_m A hp z hs))
  intro y s
  have hd := mild_hasDerivWithinAt_of_laplacianPath hz
    (fun s => (slice_smooth z hs s).of_le (by simp))
    (laplacianPath (magneticValues z)) (magnetic_laplacianPath_eq z hs) s
  exact (valueEval y).hasFDerivAt.comp_hasDerivWithinAt (s : ℝ) hd

end NavierStokes.ResistiveMagnetic.PeriodicTranslation
