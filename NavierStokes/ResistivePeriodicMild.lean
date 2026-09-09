import NavierStokes.ResistiveLinearMild

/-! Actual periodic C1-valued mild paths for the physical heat kernel and
a continuous bounded-linear coefficient path. No classical induction
regularity is inferred from the Duhamel integral at its singular endpoint. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicMild
open Set MeasureTheory ProblemStatement PeriodicGaussian WeightedVolterra EulerVolterraConvolution
open scoped Topology

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

abbrev Path (T : ℝ) := C(Icc (0 : ℝ) T, PeriodicC1)
abbrev Coefficient (T : ℝ) := C(Icc (0 : ℝ) T, PeriodicC1 →L[ℝ] PeriodicField)

def freePath (T eta_m : ℝ) (B_a : PeriodicC1) : Path T :=
  ⟨fun t => heatC1 eta_m t.val B_a,
    (heatC1_strong_continuous eta_m B_a).comp continuous_subtype_val⟩

@[simp] theorem freePath_apply (T eta_m : ℝ) (B_a : PeriodicC1) (t : Icc (0 : ℝ) T) :
    freePath T eta_m B_a t = heatC1 eta_m t.val B_a := rfl

theorem freePath_norm_le (T eta_m : ℝ) (B_a : PeriodicC1) : ‖freePath T eta_m B_a‖ ≤ ‖B_a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg B_a)).mpr
  intro t
  exact spatialC1_norm_le _ B_a

def Mild (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) (B_a : PeriodicC1) (z : Path T) : Prop :=
  LinearMild.IsMild T hT (heatKernel eta_m heta) S (freePath T eta_m B_a) z

theorem mild_equation {T : ℝ} {hT : 0 ≤ T} {eta_m : ℝ} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z) (t : Icc (0 : ℝ) T) :
    z t = heatC1 eta_m t.val B_a + ∫ r in (0 : ℝ)..t.val,
      heatKernel eta_m heta r
        (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r)))) := hz t

theorem mild_integrable (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) (z : Path T) (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun r : ℝ => heatKernel eta_m heta r
      (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r))))) volume 0 t.val :=
  LinearMild.duhamel_integrable T hT (heatKernel eta_m heta) (kernelMajorant eta_m)
    (heatKernel_joint_continuous eta_m heta) (kernelMajorant_integrable eta_m T heta hT)
    (fun r _ => kernelMajorant_nonneg eta_m r)
    (fun _ hr y => heatKernel_bound eta_m heta hr.1 y) S z t

theorem mild_initial {T : ℝ} {hT : 0 ≤ T} {eta_m : ℝ} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z) : z ⟨0,le_rfl,hT⟩ = B_a := by
  simpa only [freePath_apply, heatC1_zero] using LinearMild.initial T hT hz

/-- This integer is chosen from T, eta_m and the actual coefficient norm;
the initial magnetic datum is not an argument. -/
def contractionWeight (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) : ℕ :=
  Classical.choose (exists_weight (kernelMajorant eta_m)
    (kernelMajorant_integrable eta_m T heta hT) ‖S‖)

theorem contractionWeight_small (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) :
    kernelMass T (weightedMajorant (kernelMajorant eta_m) (contractionWeight T hT eta_m heta S)) *
      ‖S‖ ≤ (1 / 2 : ℝ) :=
  Classical.choose_spec (exists_weight (kernelMajorant eta_m)
    (kernelMajorant_integrable eta_m T heta hT) ‖S‖)

theorem exists_mild (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) (B_a : PeriodicC1) :
    ∃ z : Path T, Mild T hT eta_m heta S B_a z ∧
      ‖z‖ ≤ 2 * Real.exp ((contractionWeight T hT eta_m heta S : ℝ)*T) * ‖B_a‖ ∧
      ∀ w, Mild T hT eta_m heta S B_a w → w = z := by
  obtain ⟨z,hz,hn,hu⟩ := LinearMild.exists_unique_of_weight T hT
    (heatKernel eta_m heta) (kernelMajorant eta_m)
    (heatKernel_joint_continuous eta_m heta) (kernelMajorant_integrable eta_m T heta hT)
    (fun r _ => kernelMajorant_nonneg eta_m r)
    (fun _ hr y => heatKernel_bound eta_m heta hr.1 y) S ‖S‖ (norm_nonneg S) S.norm_coe_le_norm
    (contractionWeight T hT eta_m heta S) (Nat.cast_nonneg _)
    (contractionWeight_small T hT eta_m heta S) (freePath T eta_m B_a)
  exact ⟨z,hz,hn.trans (mul_le_mul_of_nonneg_left (freePath_norm_le T eta_m B_a) (by positivity)),hu⟩

/-- A chosen actual fixed-point path, obtained from the proved existence
theorem. Its uniqueness below removes dependence on the choice. -/
def solution (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) (B_a : PeriodicC1) : Path T :=
  Classical.choose (exists_mild T hT eta_m heta S B_a)

theorem solution_mild (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) (B_a : PeriodicC1) :
    Mild T hT eta_m heta S B_a (solution T hT eta_m heta S B_a) :=
  (Classical.choose_spec (exists_mild T hT eta_m heta S B_a)).1

theorem solution_bound (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) (B_a : PeriodicC1) :
    ‖solution T hT eta_m heta S B_a‖ ≤
      2 * Real.exp ((contractionWeight T hT eta_m heta S : ℝ)*T) * ‖B_a‖ :=
  (Classical.choose_spec (exists_mild T hT eta_m heta S B_a)).2.1

theorem mild_unique {T : ℝ} {hT : 0 ≤ T} {eta_m : ℝ} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z w : Path T}
    (hz : Mild T hT eta_m heta S B_a z) (hw : Mild T hT eta_m heta S B_a w) : z = w :=
  LinearMild.unique T hT (heatKernel eta_m heta) (kernelMajorant eta_m)
    (heatKernel_joint_continuous eta_m heta) (kernelMajorant_integrable eta_m T heta hT)
    (fun r _ => kernelMajorant_nonneg eta_m r)
    (fun _ hr y => heatKernel_bound eta_m heta hr.1 y) S (freePath T eta_m B_a) z w hz hw

/-- Explicit independence of the auxiliary weight, in the entire mild
class. Both weighted equations recover the same unweighted equation. -/
theorem recovered_unique {T : ℝ} {hT : 0 ≤ T} {eta_m : ℝ} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {Z W : Path T} (lambda mu : ℝ)
    (hZ : LinearMild.IsMild T hT (weightedKernel (heatKernel eta_m heta) lambda) S
      (weightPath (-lambda) (freePath T eta_m B_a)) Z)
    (hW : LinearMild.IsMild T hT (weightedKernel (heatKernel eta_m heta) mu) S
      (weightPath (-mu) (freePath T eta_m B_a)) W) :
    weightPath lambda Z = weightPath mu W :=
  mild_unique (LinearMild.unweight T hT lambda hZ) (LinearMild.unweight T hT mu hW)

theorem solution_initial (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) (B_a : PeriodicC1) :
    solution T hT eta_m heta S B_a ⟨0,le_rfl,hT⟩ = B_a :=
  mild_initial (solution_mild T hT eta_m heta S B_a)

@[simp] theorem solution_zero (T : ℝ) (hT : 0 ≤ T) (eta_m : ℝ) (heta : 0 < eta_m)
    (S : Coefficient T) : solution T hT eta_m heta S 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero, mul_zero] using solution_bound T hT eta_m heta S 0

theorem freePath_restrict {T T' : ℝ} (h : T' ≤ T) (eta_m : ℝ) (B_a : PeriodicC1) :
    LinearMild.restrictPath h (freePath T eta_m B_a) = freePath T' eta_m B_a := by
  apply ContinuousMap.ext
  intro t
  rfl

theorem mild_restrict {T T' : ℝ} {hT : 0 ≤ T} (hT' : 0 ≤ T') (h : T' ≤ T)
    {eta_m : ℝ} {heta : 0 < eta_m} {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z) :
    Mild T' hT' eta_m heta (LinearMild.restrictPath h S) B_a (LinearMild.restrictPath h z) := by
  have hh := LinearMild.restrict T hT (heatKernel eta_m heta) hT' h hz
  rw [freePath_restrict] at hh
  exact hh

/-- Different slab weights yield the same recovered path on the overlap. -/
theorem solution_restrict {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (h : T' ≤ T)
    (eta_m : ℝ) (heta : 0 < eta_m) (S : Coefficient T) (B_a : PeriodicC1) :
    LinearMild.restrictPath h (solution T hT eta_m heta S B_a) =
      solution T' hT' eta_m heta (LinearMild.restrictPath h S) B_a :=
  mild_unique (mild_restrict hT' h (solution_mild T hT eta_m heta S B_a))
    (solution_mild T' hT' eta_m heta (LinearMild.restrictPath h S) B_a)

end NavierStokes.ResistiveMagnetic.PeriodicMild
