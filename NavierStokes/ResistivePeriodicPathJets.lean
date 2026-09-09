import NavierStokes.ResistivePeriodicTranslationRegularity
import NavierStokes.ResistivePeriodicHeatEquation

/-! Actual spatial derivatives as continuous uniform-space paths. The
smooth translation hypothesis is in the full time-path norm; separate
spatial smoothness is not used as a substitute for this hypothesis. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicTranslation
open Set Filter ProblemStatement PeriodicGaussian
open scoped Topology ContDiff BoundedContinuousFunction

variable {K V : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance
private local instance : NormedAddCommGroup (ValuePath K V) := inferInstance
private local instance : NormedSpace ℝ (ValuePath K V) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] ValuePath K V) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] ValuePath K V) := inferInstance

def pathEval (t : K) (x : Space) : ValuePath K V →L[ℝ] V :=
  (valueEval x).comp (ContinuousMap.evalCLM ℝ t)

omit [CompactSpace K] in
@[simp] theorem pathEval_apply (t : K) (x : Space) (f : ValuePath K V) :
    pathEval t x f = (f t).val x := rfl

omit [CompactSpace K] in
theorem translatePath_add (f : ValuePath K V) (y w : Space) :
    translatePath y (translatePath w f) = translatePath (y+w) f := by
  apply ContinuousMap.ext
  intro t
  exact PeriodicGaussian.translate_add y w (f t)

def direction (f : ValuePath K V) (v : Space) : ValuePath K V :=
  fderiv ℝ (fun y => translatePath y f) 0 v

theorem direction_apply (f : ValuePath K V)
    (hf : ContDiff ℝ ∞ (fun y => translatePath y f)) (v : Space) (t : K) (x : Space) :
    (direction f v t).val x = fderiv ℝ (f t).val x v := by
  have h := ((pathEval (V := V) t x).hasFDerivAt.comp 0
    ((hf.differentiable (by simp)) 0).hasFDerivAt).fderiv
  have he : (fun y => pathEval t x (translatePath y f)) = fun y => (f t).val (x+y) := rfl
  change fderiv ℝ ((pathEval t x) ∘ (fun y => translatePath y f)) 0 = _ at h
  rw [show ((pathEval t x) ∘ (fun y => translatePath y f)) =
    (fun y => (f t).val (x+y)) from he, fderiv_comp_add_left, add_zero] at h
  exact (congrArg (fun L => L v) h).symm

theorem translate_direction (f : ValuePath K V)
    (hf : ContDiff ℝ ∞ (fun y => translatePath y f)) (v y : Space) :
    translatePath y (direction f v) = fderiv ℝ (fun w => translatePath w f) y v := by
  have h := ((translatePath (K := K) (V := V) y).hasFDerivAt.comp 0
    ((hf.differentiable (by simp)) 0).hasFDerivAt).fderiv
  have he : ((translatePath y) ∘ (fun w => translatePath w f)) =
      fun w => translatePath (y+w) f := funext (fun w => translatePath_add f y w)
  rw [he, fderiv_comp_add_left (f := fun w : Space => translatePath w f) y, add_zero] at h
  exact (congrArg (fun L => L v) h).symm

theorem direction_contDiff (f : ValuePath K V)
    (hf : ContDiff ℝ ∞ (fun y => translatePath y f)) (v : Space) :
    ContDiff ℝ ∞ (fun y => translatePath y (direction f v)) := by
  simp_rw [translate_direction f hf v]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem value_slice_smooth (f : ValuePath K V)
    (hf : ContDiff ℝ ∞ (fun y => translatePath y f)) (t : K) :
    ContDiff ℝ ∞ (f t).val := by
  have h := (pathEval (V := V) t 0).contDiff.comp hf
  simpa only [Function.comp_def, pathEval_apply, translatePath_apply, PeriodicGaussian.translate_apply, zero_add] using! h

def laplacianPath (f : ValuePath K V) : ValuePath K V :=
  direction (direction f (coordinateVector 0)) (coordinateVector 0) +
  direction (direction f (coordinateVector 1)) (coordinateVector 1) +
  direction (direction f (coordinateVector 2)) (coordinateVector 2)

theorem laplacianPath_contDiff (f : ValuePath K V)
    (hf : ContDiff ℝ ∞ (fun y => translatePath y f)) :
    ContDiff ℝ ∞ (fun y => translatePath y (laplacianPath f)) := by
  simp only [laplacianPath, map_add]
  exact ((direction_contDiff _ (direction_contDiff f hf _) _).add
    (direction_contDiff _ (direction_contDiff f hf _) _)).add
    (direction_contDiff _ (direction_contDiff f hf _) _)

theorem laplacianPath_eq [CompleteSpace V] (f : ValuePath K V)
    (hf : ContDiff ℝ ∞ (fun y => translatePath y f)) (t : K) :
    laplacianPath f t = laplacianField (f t) ((value_slice_smooth f hf t).of_le (by simp)) := by
  have hd (v : Space) : (direction f v t).val = fun x => fderiv ℝ (f t).val x v :=
    funext (direction_apply f hf v t)
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  simp only [laplacianPath, ContinuousMap.add_apply, Submodule.coe_add,
    BoundedContinuousFunction.add_apply, direction_apply _ (direction_contDiff f hf _) _ t x,
    hd, laplacianField, secondField_apply]

end NavierStokes.ResistiveMagnetic.PeriodicTranslation
