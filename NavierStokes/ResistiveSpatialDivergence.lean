import NavierStokes.ResistiveSquaredNormSlices

/-! Divergence of the spatial right-hand side. Time differentiation is
deliberately separate, so this calculation requires no joint spacetime
C-infinity regularity of an evolving magnetic field. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Calculus
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem divergence_rhs {e : Fin 3 → E} {U B Q : Fin 3 → E → ℝ}
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hQ : ∀ i, ContDiff ℝ ∞ (Q i)) (eta_m : ℝ)
    (heq : ∀ y i, Q i y + Adv e U (B i) y = Adv e B (U i) y + eta_m*Lap e (B i) y)
    (hdiv : ∀ y, Div e U y = 0) (x : E) :
    Div e Q x + Adv e U (Div e B) x = eta_m * Lap e (Div e B) x := by
  have hi (i : Fin 3) : P (e i) (Q i) x + P (e i) (Adv e U (B i)) x =
      P (e i) (Adv e B (U i)) x + eta_m*P (e i) (Lap e (B i)) x := by
    have hh := congrArg (fun f : E → ℝ => P (e i) f x) (funext (fun y => heq y i))
    rw [P_add isOpen_univ (hQ i).contDiffOn (Adv_smooth isOpen_univ
        (fun j => (hU j).contDiffOn) (fun j => (hB j).contDiffOn) i) (mem_univ x),
      P_add isOpen_univ (Adv_smooth isOpen_univ (fun j => (hB j).contDiffOn)
        (fun j => (hU j).contDiffOn) i)
        (contDiffOn_const.mul (Lap_smooth isOpen_univ (fun j => (hB j).contDiffOn) i)) (mem_univ x),
      P_const_mul isOpen_univ (Lap_smooth isOpen_univ (fun j => (hB j).contDiffOn) i) (mem_univ x)] at hh
    exact hh
  have hh := congrArg (fun f : Fin 3 → ℝ => ∑ i, f i) (funext hi)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  change Div e Q x + Div e (fun i => Adv e U (B i)) x =
    Div e (fun i => Adv e B (U i)) x + eta_m*Div e (fun i => Lap e (B i)) x at hh
  rw [Div_Adv isOpen_univ (fun i => (hU i).contDiffOn) (fun i => (hB i).contDiffOn) (mem_univ x),
    Div_Adv isOpen_univ (fun i => (hB i).contDiffOn) (fun i => (hU i).contDiffOn) (mem_univ x),
    Div_Lap isOpen_univ (fun i => (hB i).contDiffOn) (mem_univ x), cross_contraction] at hh
  have hz : Adv e B (Div e U) x = 0 := by
    rw [funext hdiv]
    simp [Adv,P]
  rw [hz] at hh
  linarith

end NavierStokes.ResistiveMagnetic.Calculus

namespace NavierStokes.ResistiveMagnetic
open Set ProblemStatement Calculus
open scoped ContDiff

theorem spatial_divergence_rhs (u b q : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hb : ContDiff ℝ ∞ b) (hq : ContDiff ℝ ∞ q) (eta_m : ℝ)
    (heq : ∀ x, q x + fderiv ℝ b x (u x) = fderiv ℝ u x (b x) +
      eta_m • spatialLaplacian (fun p : SpaceTime => b p.2) 0 x)
    (hdiv : ∀ x, spatialDivergence (fun p : SpaceTime => u p.2) 0 x = 0) (x : Space) :
    spatialDivergence (fun p : SpaceTime => q p.2) 0 x +
      Slice.gradient (fun p : SpaceTime => spatialDivergence (fun z : SpaceTime => b z.2) 0 p.2) 0 x (u x) =
      eta_m * Slice.laplacian (fun p : SpaceTime => spatialDivergence (fun z : SpaceTime => b z.2) 0 p.2) 0 x := by
  let U : VelocityField := fun p => u p.2
  let B : MagneticField := fun p => b p.2
  let Q : MagneticField := fun p => q p.2
  have hU : ContDiff ℝ ∞ U := hu.comp contDiff_snd
  have hB : ContDiff ℝ ∞ B := hb.comp contDiff_snd
  have hQ : ContDiff ℝ ∞ Q := hq.comp contDiff_snd
  have hc := Calculus.divergence_rhs
    (fun i => contDiffOn_univ.mp (component_smooth hU.contDiffOn i))
    (fun i => contDiffOn_univ.mp (component_smooth hB.contDiffOn i))
    (fun i => contDiffOn_univ.mp (component_smooth hQ.contDiffOn i)) eta_m
    (e := spaceDirection) (U := component U) (B := component B) (Q := component Q)
    (fun p i => by
      change (Q p) i + (∑ j, (U p) j * P (spaceDirection j) (component B i) p) =
        (∑ j, (B p) j * P (spaceDirection j) (component U i) p) + eta_m*Lap spaceDirection (component B i) p
      rw [component_advection isOpen_univ hB.contDiffOn (mem_univ p),
        component_advection isOpen_univ hU.contDiffOn (mem_univ p),
        component_laplacian isOpen_univ hB.contDiffOn (mem_univ p)]
      exact congrArg (fun v : Space => v i) (heq p.2))
    (fun p => (divergenceScalar_eq isOpen_univ hU.contDiffOn (mem_univ p)).trans (hdiv p.2)) (0,x)
  let δ := divergenceScalar B
  have hδ : ContDiff ℝ ∞ δ := contDiffOn_univ.mp
    (Div_smooth isOpen_univ (fun i => component_smooth hB.contDiffOn i))
  have hδeq : δ = fun p : SpaceTime => spatialDivergence (fun z : SpaceTime => b z.2) 0 p.2 := by
    funext p
    exact divergenceScalar_eq isOpen_univ hB.contDiffOn (mem_univ p)
  have hAdv : Adv spaceDirection (component U) δ (0,x) = Slice.gradient δ 0 x (u x) := by
    unfold Adv
    simp_rw [show ∀ i, P (spaceDirection i) δ (0,x) = Slice.gradient δ 0 x (coordinateVector i) from
      fun i => Slice.scalarPartial_eq (hδ.differentiable (by simp) _) i]
    conv_rhs => rw [← PeriodicUniqueness.sum_coordinates (u x), map_sum]
    simp only [map_smul,smul_eq_mul]
    rfl
  change divergenceScalar Q (0,x) + Adv spaceDirection (component U) δ (0,x) = eta_m*scalarLaplacian δ (0,x) at hc
  rw [divergenceScalar_eq isOpen_univ hQ.contDiffOn (mem_univ (0,x)), hAdv,
    Slice.scalarLaplacian_eq (fun _ => hδ.differentiable (by simp) _)
      (fun i => ((P_smooth isOpen_univ hδ.contDiffOn (spaceDirection i)).contDiffAt (by simp)).differentiableAt (by simp)),
    hδeq] at hc
  exact hc

end NavierStokes.ResistiveMagnetic
