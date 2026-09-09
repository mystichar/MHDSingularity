import NavierStokes.ResistivePeriodicSmoothSeed
import NavierStokes.ResistiveMildToPDE

/-! Classical regularity of the same constructed mild field for a constant
seed. No new solution is selected. Time differentiation is asserted only
on the forward slab interior; spatial jets are continuous through both
endpoints. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace NavierStokes.ResistiveMagnetic.PeriodicMild
open Set Filter MeasureTheory ProblemStatement PeriodicGaussian PeriodicSource PeriodicTranslation
open EulerVolterraConvolution
open scoped Topology ContDiff BoundedContinuousFunction
private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

/-- The actual Laplacian path in the original physical uniform space. -/
def laplacianEvolution {T : ℝ} (z : Path T) : C(Icc (0 : ℝ) T,PeriodicField) :=
  laplacianPath (magneticValues z)

theorem smooth_mild_hasDerivAt {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z)
    (hs : ContDiff ℝ ∞ (fun y => translateC1Path y z))
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (valueEvolution hT z)
      (eta_m • extendPath T hT (laplacianEvolution z) t +
        extendPath T hT (valueSource S z) t) t :=
  mild_hasDerivAt_of_laplacianPath hz (fun t => (slice_smooth z hs t).of_le (by simp))
    (laplacianEvolution z) (magnetic_laplacianPath_eq z hs) ht

theorem smooth_mild_physical_hasDerivAt {a T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z)
    (hs : ContDiff ℝ ∞ (fun y => translateC1Path y z))
    {t : ℝ} (ht : t ∈ Ioo a (a+T)) (x : Space) :
    HasDerivAt (fun s => physicalField a T hT z (s,x))
      (eta_m • spatialLaplacian (physicalField a T hT z) t x +
        (extendPath T hT (valueSource S z) (t-a)).val x) t := by
  have hta : t-a ∈ Ioo 0 T := ⟨sub_pos.mpr ht.1,by linarith [ht.2]⟩
  have hd := smooth_mild_hasDerivAt hz hs hta
  have hp := (valueEval x).hasFDerivAt.comp_hasDerivAt (t-a) hd
  have hc := hp.scomp t ((hasDerivAt_id t).sub_const a)
  simp only [one_smul] at hc
  have he : (extendPath T hT (laplacianEvolution z) (t-a)).val x =
      spatialLaplacian (physicalField a T hT z) t x := by
    change (laplacianEvolution z (projIcc 0 T hT (t-a))).val x = _
    have h := congrArg (fun f : PeriodicField => f.val x)
      (magnetic_laplacianPath_eq z hs (projIcc 0 T hT (t-a)))
    exact h.trans (laplacianField_eq_spatialLaplacian _ _ t x)
  change HasDerivAt (fun s => physicalField a T hT z (s,x))
    (eta_m • (extendPath T hT (laplacianEvolution z) (t-a)).val x +
      (extendPath T hT (valueSource S z) (t-a)).val x) t at hc
  rwa [he] at hc

open MagneticPeriodicMain (budget threshold geometry Selected)

theorem actual_constant_time_differentiable (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space)
    (t : ℝ) (ht : t ∈ Ioo a b) (x : Space) :
    DifferentiableAt ℝ (fun s => physicalField a (b-a) (sub_nonneg.mpr hab.le)
      (actualPath scales hsel a b hab hb eta_m heta (c1Constant c)) (s,x)) t := by
  apply (smooth_mild_physical_hasDerivAt
    (actual_mild scales hsel a b hab hb eta_m heta (c1Constant c))
    (actual_constant_translation_contDiff scales hsel a b hab hb eta_m heta c)
    (show t ∈ Ioo a (a+(b-a)) by simpa only [add_sub_cancel] using ht) x).differentiableAt

/-- The actual stretching-form resistive PDE, with the prescribed
physical viscosity-one velocity and separate positive diffusivity. -/
theorem actual_constant_induction (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space) :
    ResistiveInductionOn eta_m (Ioo a b)
      (MagneticAxisTransfer.actualPeriodicVelocity budget threshold geometry scales)
      (physicalField a (b-a) (sub_nonneg.mpr hab.le)
        (actualPath scales hsel a b hab hb eta_m heta (c1Constant c))) := by
  intro t ht x
  let hT := sub_nonneg.mpr hab.le
  let z := actualPath scales hsel a b hab hb eta_m heta (c1Constant c)
  let B := physicalField a (b-a) hT z
  let S := actualSourcePath scales hsel a b hb
  let tt : Icc (0 : ℝ) (b-a) := ⟨t-a,by linarith [ht.1],by linarith [ht.2]⟩
  have hd := smooth_mild_physical_hasDerivAt
    (actual_mild scales hsel a b hab hb eta_m heta (c1Constant c))
    (actual_constant_translation_contDiff scales hsel a b hab hb eta_m heta c)
    (show t ∈ Ioo a (a+(b-a)) by simpa only [add_sub_cancel] using ht) x
  have he : (extendPath (b-a) hT (valueSource S z) (t-a)).val x =
      Comparison.source (MagneticAxisTransfer.actualPeriodicVelocity budget threshold geometry scales) B t x := by
    change (S (projIcc 0 (b-a) hT (t-a)) (z (projIcc 0 (b-a) hT (t-a)))).val x = _
    rw [projIcc_of_mem hT tt.property]
    have hh := actualSourcePath_eq_field_source scales hsel a b hab hb z tt x
    simpa only [tt,S,B,hT,add_sub_cancel] using! hh
  change temporalDerivative B t x + _ = _
  rw [show temporalDerivative B t x = eta_m • spatialLaplacian B t x +
    (extendPath (b-a) hT (valueSource S z) (t-a)).val x from hd.deriv, he]
  unfold Comparison.source
  abel

end NavierStokes.ResistiveMagnetic.PeriodicMild
