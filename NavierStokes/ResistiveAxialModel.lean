import NavierStokes.ResistiveSimilarityScaling

/-! An exact trajectory reduction with an explicit magnetic-curvature
closure. This closure is not a theorem about the assembled velocity or an
arbitrary seed. No advection is discarded: it is removed by the trajectory. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set ProblemStatement MagneticTransport
open scoped ContDiff Topology

theorem pure_axial_of_curvature_closure {eta_m a b Bz0 : ℝ}
    {u : VelocityField} {B : MagneticField} {gamma : ℝ → Space} {x0 : Space}
    {alpha mu beta : ℝ → ℝ}
    (hg : IsLagrangianTrajectoryOn u gamma a b x0)
    (hind : ResistiveInductionOn eta_m (Ioo a b) u B)
    (hBc : ContinuousOn (fun t => B (t,gamma t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t,gamma t))
    (hA : ContinuousOn (fun t => spatialDerivative u t (gamma t)) (Icc a b))
    (hmu : ContinuousOn mu (Icc a b))
    (haxis : ∀ t ∈ Ioo a b, spatialDerivative u t (gamma t) (coordinateVector 2) =
      alpha t • coordinateVector 2)
    (hcurvature : ∀ t ∈ Ioo a b, spatialLaplacian B t (gamma t) = -mu t • B (t,gamma t))
    (hbc : ContinuousOn beta (Icc a b))
    (hbd : ∀ t ∈ Ioo a b, HasDerivAt beta ((alpha t-eta_m*mu t)*beta t) t)
    (hba : beta a = Bz0) (hseed : B (a,gamma a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Icc a b) : B (t,gamma t) = beta t • coordinateVector 2 := by
  let A : ℝ → Space →L[ℝ] Space := fun s => spatialDerivative u s (gamma s) -
    (eta_m*mu s) • ContinuousLinearMap.id ℝ Space
  have hAc : ContinuousOn A (Icc a b) := hA.sub
    ((continuousOn_const.mul hmu).smul continuousOn_const)
  have hz := linearODE_eq_zero_on_interval
    (fun s => B (s,gamma s)-beta s • coordinateVector 2) A
    (hBc.sub (hbc.smul continuousOn_const)) hAc
    (by
      intro s hs
      have hd := (material_derivative (hBd s hs) (hg.hasDerivAt s hs) hind hs).sub
        ((hbd s hs).smul_const (coordinateVector 2))
      rw [hcurvature s hs] at hd
      convert! hd using 1
      simp only [A,sub_apply,map_sub,map_smul,
        smul_apply,ContinuousLinearMap.id_apply,haxis s hs,
        smul_sub,smul_smul]
      module)
    (by rw [hseed,hba,sub_self]) ht
  exact sub_eq_zero.mp hz
end NavierStokes.ResistiveMagnetic
