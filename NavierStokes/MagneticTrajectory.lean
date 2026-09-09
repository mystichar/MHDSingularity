import NavierStokes.MagneticInduction
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Particle trajectories use endpoint continuity and ordinary derivatives only
at interior times. No extension beyond the closed time interval is constrained. -/

noncomputable section

namespace NavierStokes.MagneticTransport

open Set ProblemStatement

/-- A particle starting at `x₀` at time `a` on a finite closed interval. -/
structure IsLagrangianTrajectoryOn (u : VelocityField) (γ : ℝ → Space)
    (a b : ℝ) (x₀ : Space) : Prop where
  ordered : a ≤ b
  initial : γ a = x₀
  continuous : ContinuousOn γ (Icc a b)
  hasDerivAt : ∀ t ∈ Ioo a b, HasDerivAt γ (u (t, γ t)) t

/-- Split the joint derivative into its time and space directions. -/
theorem joint_fderiv_material {B : MagneticField} {t : ℝ} {x : Space}
    (hB : DifferentiableAt ℝ B (t, x)) (v : Space) :
    fderiv ℝ B (t, x) (1, v) =
      temporalDerivative B t x + spatialDerivative B t x v := by
  have htime : HasFDerivAt (fun s : ℝ => (s, x))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const x t)
  have hspace : HasFDerivAt (fun y : Space => (t, y))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have ht := hB.hasFDerivAt.comp t htime
  have hx := hB.hasFDerivAt.comp x hspace
  have hsplit : ((1 : ℝ), v) = (1, (0 : Space)) + (0, v) := by simp
  rw [hsplit, map_add]
  change _ = fderiv ℝ (B ∘ (fun s : ℝ => (s, x))) t 1 +
    fderiv ℝ (B ∘ (fun y : Space => (t, y))) x v
  rw [ht.fderiv, hx.fderiv]
  rfl

/-- Ideal induction becomes the magnetic stretching ODE along a particle.
Only joint differentiability of `B` at the point in question is needed. -/
theorem hasDerivAt_magnetic_along_trajectory
    {u : VelocityField} {B : MagneticField} {γ : ℝ → Space}
    {a b : ℝ} {x₀ : Space}
    (hγ : IsLagrangianTrajectoryOn u γ a b x₀)
    (hind : IdealInductionOn (Ioo a b) u B)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (hB : DifferentiableAt ℝ B (t, γ t)) :
    HasDerivAt (fun s => B (s, γ s))
      (spatialDerivative u t (γ t) (B (t, γ t))) t := by
  have h := hB.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hγ.hasDerivAt t ht))
  simpa only [Function.comp_def, id_eq, joint_fderiv_material hB,
    hind t ht (γ t)] using h

end NavierStokes.MagneticTransport
