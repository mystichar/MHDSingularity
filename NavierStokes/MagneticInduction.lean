import NavierStokes.ProblemStatement

/-! Generic ideal magnetic induction on the existing physical spacetime.
Regularity and solenoidality are explicit hypotheses, independent of any
Navier--Stokes candidate construction. -/

noncomputable section

namespace NavierStokes.ProblemStatement

/-- Magnetic fields use precisely the existing velocity-field representation. -/
abbrev MagneticField := VelocityField

end NavierStokes.ProblemStatement

namespace NavierStokes.MagneticTransport

open Set ProblemStatement

/-- Spatial incompressibility on the specified times. -/
def DivergenceFreeOn (times : Set ℝ) (B : MagneticField) : Prop :=
  ∀ t ∈ times, ∀ x, spatialDivergence B t x = 0

/-- The ideal induction equation in incompressible stretching form.
The two divergence constraints are recorded separately by
`IncompressibleInductionOn`. -/
def IdealInductionOn (times : Set ℝ) (u : VelocityField) (B : MagneticField) : Prop :=
  ∀ t ∈ times, ∀ x,
    temporalDerivative B t x + spatialDerivative B t x (u (t, x)) =
      spatialDerivative u t x (B (t, x))

/-- An incompressible velocity and magnetic field satisfying ideal induction. -/
structure IncompressibleInductionOn (times : Set ℝ)
    (u : VelocityField) (B : MagneticField) : Prop where
  velocity_divergence_free : DivergenceFreeOn times u
  magnetic_divergence_free : DivergenceFreeOn times B
  induction : IdealInductionOn times u B

end NavierStokes.MagneticTransport
