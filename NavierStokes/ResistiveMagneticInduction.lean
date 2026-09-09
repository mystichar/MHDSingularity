import NavierStokes.MagneticAssembledAmplification
import NavierStokes.PeriodicUniqueness

/-! Paper II: passive resistive induction. The diffusivity `eta_m` is
independent of the similarity coordinate eta. Existence is not part of this
interface. Solenoidality is a separate conclusion to be propagated. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set ProblemStatement MagneticTransport
open scoped Topology ContDiff

/-- Constant magnetic diffusivity, in the project's physical derivative conventions. -/
def ResistiveInductionOn (eta_m : ℝ) (times : Set ℝ)
    (u : VelocityField) (B : MagneticField) : Prop :=
  ∀ t ∈ times, ∀ x,
    temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x

@[simp] theorem resistive_zero_iff (times : Set ℝ) (u : VelocityField) (B : MagneticField) :
    ResistiveInductionOn 0 times u B ↔ IdealInductionOn times u B := by
  simp [ResistiveInductionOn, IdealInductionOn]

/-- The material derivative includes the actual Laplacian; the ideal
trajectory law alone cannot determine a resistive solution. -/
theorem material_derivative {eta_m t : ℝ} {times : Set ℝ}
    {u : VelocityField} {B : MagneticField} {gamma : ℝ → Space}
    (hB : DifferentiableAt ℝ B (t,gamma t))
    (hg : HasDerivAt gamma (u (t,gamma t)) t)
    (hind : ResistiveInductionOn eta_m times u B) (ht : t ∈ times) :
    HasDerivAt (fun s => B (s,gamma s))
      (spatialDerivative u t (gamma t) (B (t,gamma t)) + eta_m • spatialLaplacian B t (gamma t)) t := by
  have hd := hB.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hg)
  simpa only [Function.comp_def, id_eq, joint_fderiv_material hB, hind t ht (gamma t)] using hd
end NavierStokes.ResistiveMagnetic
