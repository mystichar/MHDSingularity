import NavierStokes.ResistivePeriodicMildActual
import Euler.SmoothCoefficientPath

/-! Spatial translations of the actual periodic coefficient paths are
smooth in the uniform path norm. This is coefficient regularity, not a
parabolic smoothing assertion about a C1 magnetic solution. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicTranslation
open Set Filter ProblemStatement PeriodicGaussian
open scoped Topology ContDiff BoundedContinuousFunction

variable {K V : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

abbrev ValuePath (K V : Type) [TopologicalSpace K] [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  C(K, PeriodicValue V)

private local instance : NormedAddCommGroup (ValuePath K V) := inferInstance
private local instance : NormedSpace ℝ (ValuePath K V) := inferInstance
private local instance : NormedAddCommGroup (ValuePath K (Space →L[ℝ] V)) := inferInstance
private local instance : NormedSpace ℝ (ValuePath K (Space →L[ℝ] V)) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] ValuePath K V) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] ValuePath K V) := inferInstance

def forgetPath : ValuePath K V →L[ℝ] C(K, Space →ᵇ V) :=
  (periodicValues V).toSubmodule.subtypeL.compLeftContinuous ℝ K

theorem forgetPath_norm (f : ValuePath K V) : ‖forgetPath f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro t
    exact f.norm_coe_le_norm t
  · apply (ContinuousMap.norm_le _ (norm_nonneg (forgetPath f))).mpr
    intro t
    exact (forgetPath f).norm_coe_le_norm t

theorem hasFDerivAt_of_norm_preserving_comp
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (hL : ∀ v, ‖L v‖ = ‖v‖) {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt (fun y => L (f y)) (L.comp f') x) : HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_tendsto] at h ⊢
  simpa only [ContinuousLinearMap.comp_apply, ← map_sub, hL] using h

def translatePath (y : Space) : ValuePath K V →L[ℝ] ValuePath K V :=
  (PeriodicGaussian.translate y).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem translatePath_apply (y : Space) (f : ValuePath K V) (t : K) (x : Space) :
    (translatePath y f t).val x = (f t).val (x+y) := rfl

def directionPath (D : ValuePath K (Space →L[ℝ] V)) (v : Space) : ValuePath K V :=
  (valueMap (ContinuousLinearMap.apply ℝ V v)).compLeftContinuous ℝ K D

theorem directionPath_norm_le (D : ValuePath K (Space →L[ℝ] V)) (v : Space) :
    ‖directionPath D v‖ ≤ ‖D‖ * ‖v‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg v))).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg D) (norm_nonneg v))).mpr
  intro x
  exact ((D t).val x).le_of_opNorm_le
    (((D t).val.norm_coe_le_norm x).trans (D.norm_coe_le_norm t)) v

def directionMap (D : ValuePath K (Space →L[ℝ] V)) : Space →L[ℝ] ValuePath K V :=
  LinearMap.mkContinuous
    { toFun := directionPath D
      map_add' := fun v w => by
        apply ContinuousMap.ext; intro t; apply Subtype.ext; apply BoundedContinuousFunction.ext; intro x
        exact map_add ((D t).val x) v w
      map_smul' := fun c v => by
        apply ContinuousMap.ext; intro t; apply Subtype.ext; apply BoundedContinuousFunction.ext; intro x
        exact map_smul ((D t).val x) c v }
    ‖D‖ (directionPath_norm_le D)

def directionBundling : ValuePath K (Space →L[ℝ] V) →L[ℝ] Space →L[ℝ] ValuePath K V :=
  LinearMap.mkContinuous
    { toFun := fun D : ValuePath K (Space →L[ℝ] V) => directionMap D
      map_add' := fun D E => by
        apply ContinuousLinearMap.ext; intro v; apply ContinuousMap.ext; intro t
        apply Subtype.ext; apply BoundedContinuousFunction.ext; intro x; rfl
      map_smul' := fun c D => by
        apply ContinuousLinearMap.ext; intro v; apply ContinuousMap.ext; intro t
        apply Subtype.ext; apply BoundedContinuousFunction.ext; intro x; rfl }
    1 (fun D => by
      rw [one_mul]
      exact (directionMap D).opNorm_le_bound (norm_nonneg D) (directionPath_norm_le D))

def periodicPath (A : SmoothTimeField K Space V)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x) : ValuePath K V :=
  ⟨fun t => ⟨A.field t,hp t⟩, Continuous.subtype_mk A.field.continuous _⟩

theorem derivative_periodic (A : SmoothTimeField K Space V)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x) :
    ∀ t x i, A.derivative.field t (x+coordinateVector i) = A.derivative.field t x := by
  intro t x i
  change A.derivativeField t (x+coordinateVector i) = A.derivativeField t x
  rw [A.derivativeField_eq,A.derivativeField_eq]
  exact value_fderiv_periodic (periodicPath A hp t) x i

theorem translatePath_hasFDerivAt (A : SmoothTimeField K Space V)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x) (y : Space) :
    HasFDerivAt (fun w => translatePath w (periodicPath A hp))
      (directionMap (translatePath y (periodicPath A.derivative (derivative_periodic A hp)))) y := by
  apply hasFDerivAt_of_norm_preserving_comp (forgetPath (K := K) (V := V)) forgetPath_norm
  let A' : EulerMeanCoefficients.SmoothCoefficientPath K V := ⟨A.field,A.smooth,A.jet,A.jet_eq⟩
  convert! A'.translation_hasFDerivAt y using 1

private theorem translatePath_contDiff_nat (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (A : SmoothTimeField K Space V)
      (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x),
      ContDiff ℝ n (fun y => translatePath y (periodicPath A hp)) := by
  induction n with
  | zero =>
    intro V _ _ A hp
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun y => (translatePath_hasFDerivAt A hp y).continuousAt))
  | succ n ih =>
    intro V _ _ A hp
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
    refine ⟨fun y => (translatePath_hasFDerivAt A hp y).differentiableAt, by simp, ?_⟩
    have he : fderiv ℝ (fun y => translatePath y (periodicPath A hp)) =
        fun y => directionBundling (translatePath y (periodicPath A.derivative (derivative_periodic A hp))) :=
      funext (fun y => (translatePath_hasFDerivAt A hp y).fderiv)
    rw [he]
    exact (directionBundling (K := K) (V := V)).contDiff.comp
      (ih _ A.derivative (derivative_periodic A hp))

theorem translatePath_contDiff (A : SmoothTimeField K Space V)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x) :
    ContDiff ℝ ∞ (fun y => translatePath y (periodicPath A hp)) :=
  contDiff_infty.mpr (fun n => translatePath_contDiff_nat n V A hp)

end NavierStokes.ResistiveMagnetic.PeriodicTranslation
