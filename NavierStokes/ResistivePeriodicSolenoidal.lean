import NavierStokes.ResistivePeriodicTimeJets
import NavierStokes.ResistiveSpatialDivergence
import NavierStokes.ResistivePeriodicClassicalGlue

/-! Forward divergence preservation for the constructed constant-seed
field, using the actual mixed-jet time equation and scalar maximum principle. -/
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


def traceOne : (Space [×1]→L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    ((ContinuousLinearMap.id ℝ (Space [×1]→L[ℝ] Space)).flipMultilinear (fun _ => coordinateVector i))

theorem traceOne_apply (L : Space [×1]→L[ℝ] Space) :
    traceOne L = ∑ i : Fin 3, (L (fun _ => coordinateVector i)) i := rfl

theorem traceOne_jet {T : ℝ} (f : Space → C(Icc (0 : ℝ) T,Space))
    (hf : ContDiff ℝ ∞ f) (x : Space) (t : Icc (0 : ℝ) T) :
    traceOne (jetFamily T f 1 x t) =
      ∑ i : Fin 3, (fderiv ℝ (fun y => f y t) x (coordinateVector i)) i := by
  rw [jetFamily_apply T f hf,traceOne_apply]
  simp only [iteratedFDeriv_one_apply]

def delta {T : ℝ} (hT : 0 ≤ T) (z : Path T) (p : SpaceTime) : ℝ :=
  spatialDivergence (physicalField 0 T hT z) p.1 p.2

theorem delta_continuous {T : ℝ} (hT : 0 ≤ T) (z : Path T) : Continuous (delta hT z) := by
  unfold delta spatialDivergence
  apply continuous_finsetSum
  intro i _
  exact (EuclideanSpace.proj i).continuous.comp
    ((physicalField_derivative_continuous 0 T hT z).clm_apply continuous_const)

theorem delta_periodic {T : ℝ} (hT : 0 ≤ T) (z : Path T) : UnitSpatialPeriodsOn univ (delta hT z) := by
  intro t _ x i
  unfold delta spatialDivergence
  simp only [physicalField_spatialDerivative]
  rw [(c1Derivative (z (projIcc 0 T hT (t-0)))).property x i]

theorem delta_spatial_smooth {T : ℝ} (hT : 0 ≤ T) (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => delta hT z (t,x)) := by
  unfold delta spatialDivergence spatialDerivative
  apply ContDiff.sum
  intro i _
  have hs := slice_smooth z hz (projIcc 0 T hT (t-0))
  exact (EuclideanSpace.proj i).contDiff.comp
    ((hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem delta_eq_jet {T : ℝ} (hT : 0 ≤ T) (z : Path T)
    (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z)) (t : ℝ) (x : Space) :
    delta hT z (t,x) = traceOne (extendPath T hT (jetFamily T (fieldPath z) 1 x) t) := by
  rw [extendPath,traceOne_jet _ (fieldPath_contDiff z hz)]
  simp only [delta,spatialDivergence,spatialDerivative,physicalField,sub_zero]
  rfl

theorem delta_hasDerivAt {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (c : Space) (z : Path T)
    (hz : Mild T hT eta_m heta
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) (c1Constant c) z)
    (t : Icc (0 : ℝ) T) (ht : t.val ∈ Ioo 0 T) (x : Space) :
    HasDerivAt (fun s => delta hT z (s,x))
      (spatialDivergence (fun p : SpaceTime =>
        (rhsPath eta_m (sourcePaths (periodicPath A hp)
          (periodicPath A.derivative (derivative_periodic A hp))) z t).val p.2) 0 x) t.val := by
  have hs := constant_seed_translation_contDiff T hT eta_m heta A hp c z hz
  have hd := (mild_spatial_jet_time_derivative A hp c z hz 1 x t).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  have hc := traceOne.hasFDerivAt.comp_hasDerivAt t.val hd
  rw [traceOne_jet _ (pointPath_contDiff _ (rhs_translation_contDiff eta_m A hp z hs))] at hc
  have he : (fun s => delta hT z (s,x)) =
      fun s => traceOne (extendPath T hT (jetFamily T (fieldPath z) 1 x) s) :=
    funext (fun s => delta_eq_jet hT z hs s x)
  rw [he]
  exact hc

theorem rhs_spatial_equation {T : ℝ} (eta_m : ℝ)
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (z : Path T) (hz : ContDiff ℝ ∞ (fun y => translateC1Path y z))
    (t : Icc (0 : ℝ) T) (x : Space) :
    (rhsPath eta_m (sourcePaths (periodicPath A hp)
      (periodicPath A.derivative (derivative_periodic A hp))) z t).val x +
        fderiv ℝ (c1Value (z t)).val x (A.field t x) =
      fderiv ℝ (A.field t) x ((c1Value (z t)).val x) +
        eta_m • spatialLaplacian (fun p : SpaceTime => (c1Value (z t)).val p.2) 0 x := by
  have hl := congrArg (fun f : PeriodicField => f.val x) (magnetic_laplacianPath_eq z hz t)
  have he := hl.trans (laplacianField_eq_spatialLaplacian _ _ 0 x)
  change eta_m • (laplacianEvolution z t).val x +
    (-(c1Derivative (z t)).val x (A.field t x) + A.derivative.field t x ((c1Value (z t)).val x)) + _ = _
  change (laplacianEvolution z t).val x =
    spatialLaplacian (fun p : SpaceTime => (c1Value (z t)).val p.2) 0 x at he
  rw [he,c1_fderiv]
  change _ + (-_ + A.derivativeField t x _) + _ = _
  rw [A.derivativeField_eq]
  abel

theorem delta_operator_zero {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (hdiv : ∀ t x, spatialDivergence (fun p : SpaceTime => A.field t p.2) 0 x = 0)
    (c : Space) (z : Path T)
    (hz : Mild T hT eta_m heta
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) (c1Constant c) z)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    Slice.operator (fun p => A.field (projIcc 0 T hT p.1) p.2) eta_m (delta hT z) t x = 0 := by
  let tt : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
  have hs := constant_seed_translation_contDiff T hT eta_m heta A hp c z hz
  let Q := rhsPath eta_m (sourcePaths (periodicPath A hp)
    (periodicPath A.derivative (derivative_periodic A hp))) z
  have hQ := value_slice_smooth Q (rhs_translation_contDiff eta_m A hp z hs) tt
  have hd := (delta_hasDerivAt A hp c z hz tt ht x).deriv
  have h := spatial_divergence_rhs (A.field tt) (c1Value (z tt)).val (Q tt).val
    (A.smooth tt) (slice_smooth z hs tt) hQ eta_m (rhs_spatial_equation eta_m A hp z hs tt) (hdiv tt) x
  have he : (fun y => delta hT z (t,y)) =
      fun y => spatialDivergence (fun p : SpaceTime => (c1Value (z tt)).val p.2) 0 y := by
    simp only [delta,spatialDivergence,spatialDerivative,physicalField,sub_zero,
      projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩]
    rfl
  unfold Slice.operator Slice.time Slice.laplacian Slice.gradient
  dsimp only
  rw [hd,projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩,he]
  exact sub_eq_zero.mpr h

end NavierStokes.ResistiveMagnetic.PeriodicTranslation
