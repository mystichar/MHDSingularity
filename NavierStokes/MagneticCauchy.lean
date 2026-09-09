import NavierStokes.MagneticTrajectory
import NavierStokes.TangentODE
import Euler.VorticityTransport
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Deformation and magnetic Cauchy transport along a supplied trajectory.
The deformation solves a linear operator ODE; no spatial flow derivative is assumed. -/

noncomputable section

namespace NavierStokes.MagneticTransport

open Set ProblemStatement
open scoped ContDiff

/-- Relative smoothness on a closed slab supplies the interior magnetic ODE. -/
theorem hasDerivAt_magnetic_along_trajectory_of_smooth
    {u : VelocityField} {B : MagneticField} {γ : ℝ → Space}
    {a b : ℝ} {x₀ : Space}
    (hγ : IsLagrangianTrajectoryOn u γ a b x₀)
    (hind : IdealInductionOn (Ioo a b) u B)
    (hB : ContDiffOn ℝ ∞ B (Icc a b ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => B (s, γ s))
      (spatialDerivative u t (γ t) (B (t, γ t))) t := by
  apply hasDerivAt_magnetic_along_trajectory hγ hind ht
  exact (hB.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    Filter.univ_mem)).differentiableAt (by simp)

/-- The ordinary derivative version of the magnetic chain rule. -/
theorem deriv_magnetic_along_trajectory
    {u : VelocityField} {B : MagneticField} {γ : ℝ → Space}
    {a b : ℝ} {x₀ : Space}
    (hγ : IsLagrangianTrajectoryOn u γ a b x₀)
    (hind : IdealInductionOn (Ioo a b) u B)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (hB : DifferentiableAt ℝ B (t, γ t)) :
    deriv (fun s => B (s, γ s)) t =
      spatialDerivative u t (γ t) (B (t, γ t)) :=
  (hasDerivAt_magnetic_along_trajectory hγ hind ht hB).deriv

/-- The deformation operator starts at the identity and satisfies the
variational ODE on interior times, with continuity through the endpoints. -/
structure IsDeformationAlong (u : VelocityField) (γ : ℝ → Space)
    (a b : ℝ) (F : ℝ → Space →L[ℝ] Space) : Prop where
  ordered : a ≤ b
  initial : F a = ContinuousLinearMap.id ℝ Space
  continuous : ContinuousOn F (Icc a b)
  hasDerivAt : ∀ t ∈ Ioo a b,
    HasDerivAt F ((spatialDerivative u t (γ t)).comp (F t)) t

/-- A continuous velocity gradient along the compact trajectory suffices to
construct the deformation. No global spatial bound is required. -/
theorem exists_deformation_along_trajectory
    {u : VelocityField} {γ : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn (fun t => spatialDerivative u t (γ t)) (Icc a b)) :
    ∃ F, IsDeformationAlong u γ a b F := by
  let A : ℝ → (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space) :=
    fun t => ContinuousLinearMap.compL ℝ Space Space Space (spatialDerivative u t (γ t))
  have hAc : ContinuousOn A (Icc a b) :=
    (ContinuousLinearMap.compL ℝ Space Space Space).continuous.comp_continuousOn hA
  obtain ⟨F, hinit, hd⟩ := TangentODE.exists_linear_solution hab A (fun _ => 0)
    hAc continuousOn_const (ContinuousLinearMap.id ℝ Space)
  refine ⟨F, hab, hinit, ?_, ?_⟩
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    simpa [A] using hd t (Ioo_subset_Icc_self ht)

/-- The existing zero-solution uniqueness theorem translated to `[a,b]`.
Only endpoint continuity and interior derivatives are used. -/
theorem linearODE_eq_zero_on_interval
    (w : ℝ → Space) (A : ℝ → Space →L[ℝ] Space) {a b : ℝ}
    (hw : ContinuousOn w (Icc a b)) (hA : ContinuousOn A (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt w (A t (w t)) t)
    (hzero : w a = 0) {t : ℝ} (ht : t ∈ Icc a b) : w t = 0 := by
  have hshift : MapsTo (fun r : ℝ => a + r) (Icc 0 (b - a)) (Icc a b) := by
    intro r hr
    constructor <;> dsimp <;> linarith [hr.1, hr.2]
  have hz := Euler.ComparatorBridge.linearODE_eq_zero
    (fun r => w (a + r)) (fun r => A (a + r)) (b - a)
    (hw.comp (continuous_const.add continuous_id).continuousOn hshift)
    (hA.comp (continuous_const.add continuous_id).continuousOn hshift)
    (by
      intro r hr
      have hmem : a + r ∈ Ioo a b := by
        constructor <;> linarith [hr.1, hr.2]
      have hshiftderiv : HasDerivAt (fun s : ℝ => a + s) 1 r := by
        convert! (hasDerivAt_const r a).add (hasDerivAt_id r) using 1
        simp
      convert! (hd (a + r) hmem).scomp r hshiftderiv using 1
      simp)
    (by simpa using hzero) (t - a)
    (by constructor <;> linarith [ht.1, ht.2])
  simpa using hz

/-- The deformation satisfying the initial-value problem is unique on its interval. -/
theorem deformation_along_trajectory_unique
    {u : VelocityField} {γ : ℝ → Space} {a b : ℝ}
    {F G : ℝ → Space →L[ℝ] Space}
    (hA : ContinuousOn (fun t => spatialDerivative u t (γ t)) (Icc a b))
    (hF : IsDeformationAlong u γ a b F) (hG : IsDeformationAlong u γ a b G) :
    EqOn F G (Icc a b) := by
  intro t ht
  apply ContinuousLinearMap.ext
  intro v
  have hz := linearODE_eq_zero_on_interval (fun s => F s v - G s v)
    (fun s => spatialDerivative u s (γ s))
    ((hF.continuous.clm_apply continuousOn_const).sub
      (hG.continuous.clm_apply continuousOn_const)) hA
    (by
      intro s hs
      have hd := ((hF.hasDerivAt s hs).clm_apply (hasDerivAt_const s v)).sub
        ((hG.hasDerivAt s hs).clm_apply (hasDerivAt_const s v))
      convert! hd using 1
      simp [ContinuousLinearMap.comp_apply])
    (by simp [hF.initial, hG.initial]) ht
  exact sub_eq_zero.mp hz

/-- Cauchy transport along one trajectory. The magnetic field needs only
continuity along the closed path and joint differentiability at interior path
points; the velocity gradient needs only continuity along the closed path. -/
theorem magnetic_cauchy_along_trajectory
    {u : VelocityField} {B : MagneticField} {γ : ℝ → Space}
    {a b : ℝ} {x₀ : Space} {F : ℝ → Space →L[ℝ] Space}
    (hγ : IsLagrangianTrajectoryOn u γ a b x₀)
    (hind : IdealInductionOn (Ioo a b) u B)
    (hBc : ContinuousOn (fun t => B (t, γ t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t, γ t))
    (hA : ContinuousOn (fun t => spatialDerivative u t (γ t)) (Icc a b))
    (hF : IsDeformationAlong u γ a b F)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (t, γ t) = F t (B (a, x₀)) := by
  have hz := linearODE_eq_zero_on_interval
    (fun s => B (s, γ s) - F s (B (a, x₀)))
    (fun s => spatialDerivative u s (γ s))
    (hBc.sub (hF.continuous.clm_apply continuousOn_const)) hA
    (by
      intro s hs
      have hd := (hasDerivAt_magnetic_along_trajectory hγ hind hs (hBd s hs)).sub
        ((hF.hasDerivAt s hs).clm_apply (hasDerivAt_const s (B (a, x₀))))
      convert! hd using 1
      simp [ContinuousLinearMap.comp_apply])
    (by simp [hγ.initial, hF.initial]) ht
  exact sub_eq_zero.mp hz

end NavierStokes.MagneticTransport
