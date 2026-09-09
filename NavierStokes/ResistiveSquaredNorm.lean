import NavierStokes.ResistiveIdealComparison

/-! Squared-norm calculus for the vector comparison equation. All
second derivatives are computed; the norm itself is never differentiated. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Comparison
open Set Filter ProblemStatement Calculus
open scoped ContDiff InnerProductSpace Topology

variable {O : Set SpaceTime} (hO : IsOpen O) {W : MagneticField}
    (hW : ContDiffOn ℝ ∞ W O) {z : SpaceTime} (hz : z ∈ O)

include hO hW hz in
theorem norm_sq_directional (v : SpaceTime) :
    P v (fun z => ‖W z‖^2) z = 2*⟪W z,fderiv ℝ W z v⟫_ℝ := by
  have hd := ((hW.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.norm_sq
  rw [P,hd.fderiv]
  simp

include hO hW hz in
theorem norm_sq_second_directional (v : SpaceTime) :
    P v (P v (fun z => ‖W z‖^2)) z = 2*‖fderiv ℝ W z v‖^2 +
      2*⟪W z,fderiv ℝ (fun y => fderiv ℝ W y v) z v⟫_ℝ := by
  let G := fun y => fderiv ℝ W y v
  have hG : ContDiffOn ℝ ∞ G O := (hW.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have he : P v (fun z => ‖W z‖^2) =ᶠ[𝓝 z] (fun y => 2*⟪W y,G y⟫_ℝ) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact norm_sq_directional hO hW hy v
  have hd := (((hW.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.inner ℝ
    ((hG.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt).const_mul 2
  change fderiv ℝ (P v (fun y => ‖W y‖^2)) z v = _
  rw [he.fderiv_eq,hd.fderiv]
  simp [G,fderivInnerCLM_apply,mul_add,add_comm]

include hO hW hz in
theorem norm_sq_time : scalarTime (fun z => ‖W z‖^2) z =
    2*⟪W z,temporalDerivative W z.1 z.2⟫_ℝ := by
  rw [scalarTime,norm_sq_directional hO hW hz]
  congr 2
  ext i
  exact (P_component hO hW hz _ i).symm.trans (component_time hO hW hz i)

include hO hW hz in
theorem norm_sq_advection (u : Space) :
    Adv spaceDirection (fun i _ => u i) (fun z => ‖W z‖^2) z =
      2*⟪W z,spatialDerivative W z.1 z.2 u⟫_ℝ := by
  have he : ∀ i, fderiv ℝ W z (spaceDirection i) = spatialDerivative W z.1 z.2 (coordinateVector i) := by
    intro j
    ext i
    exact (P_component hO hW hz _ i).symm.trans (component_space hO hW hz i j)
  simp only [Adv,norm_sq_directional hO hW hz,he]
  conv_rhs => rw [← PeriodicUniqueness.sum_coordinates u,map_sum,inner_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul,inner_smul_right]
  ring

include hO hW hz in
theorem norm_sq_laplacian : scalarLaplacian (fun z => ‖W z‖^2) z =
    2*(∑ i : Fin 3, ‖spatialDerivative W z.1 z.2 (coordinateVector i)‖^2) +
      2*⟪W z,spatialLaplacian W z.1 z.2⟫_ℝ := by
  have he : ∀ j, fderiv ℝ W z (spaceDirection j) = spatialDerivative W z.1 z.2 (coordinateVector j) := by
    intro j
    ext i
    exact (P_component hO hW hz _ i).symm.trans (component_space hO hW hz i j)
  have hsum : (∑ j, fderiv ℝ (fun y => fderiv ℝ W y (spaceDirection j)) z (spaceDirection j)) =
      spatialLaplacian W z.1 z.2 := by
    ext i
    change (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ W y (spaceDirection j)) z (spaceDirection j)) = _
    rw [map_sum,← component_laplacian hO hW hz i]
    apply Finset.sum_congr rfl
    intro j _
    let G := fun y => fderiv ℝ W y (spaceDirection j)
    have hG : ContDiffOn ℝ ∞ G O := (hW.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    have hp : P (spaceDirection j) (component W i) =ᶠ[𝓝 z] component G i := by
      filter_upwards [hO.mem_nhds hz] with y hy
      exact P_component hO hW hy _ i
    change _ = fderiv ℝ (P (spaceDirection j) (component W i)) z (spaceDirection j)
    rw [hp.fderiv_eq]
    exact (P_component hO hG hz _ i).symm
  simp only [scalarLaplacian,Lap,norm_sq_second_directional hO hW hz,
    Finset.sum_add_distrib,← Finset.mul_sum,he,← inner_sum,hsum]

/-- Exact vector squared-norm identity with a supplied forcing f. -/
theorem squared_equation {O : Set SpaceTime} (hO : IsOpen O) {W u : VelocityField}
    (hW : ContDiffOn ℝ ∞ W O) {z : SpaceTime} (hz : z ∈ O) {eta_m : ℝ} {f : Space}
    (heq : temporalDerivative W z.1 z.2 + spatialDerivative W z.1 z.2 (u z) =
      spatialDerivative u z.1 z.2 (W z) + eta_m • spatialLaplacian W z.1 z.2 + eta_m • f) :
    scalarTime (fun z => ‖W z‖^2) z +
      Adv spaceDirection (fun i _ => (u z) i) (fun z => ‖W z‖^2) z -
      eta_m*scalarLaplacian (fun z => ‖W z‖^2) z =
      2*⟪W z,spatialDerivative u z.1 z.2 (W z)⟫_ℝ -
      2*eta_m*(∑ i : Fin 3, ‖spatialDerivative W z.1 z.2 (coordinateVector i)‖^2) +
      2*eta_m*⟪W z,f⟫_ℝ := by
  rw [norm_sq_time hO hW hz,norm_sq_advection hO hW hz,norm_sq_laplacian hO hW hz,
    ← mul_add,← inner_add_right,heq]
  simp only [inner_add_right,inner_smul_right]
  ring
/-- The scalar differential inequality, before applying a parabolic
comparison principle. Its constants are the actual displayed input bounds. -/
theorem squared_inequality {O : Set SpaceTime} (hO : IsOpen O) {W u : VelocityField}
    (hW : ContDiffOn ℝ ∞ W O) {z : SpaceTime} (hz : z ∈ O) {eta_m L D : ℝ} {f : Space}
    (heta : 0 ≤ eta_m) (hL : ‖spatialDerivative u z.1 z.2‖ ≤ L) (hD : ‖f‖ ≤ D)
    (heq : temporalDerivative W z.1 z.2 + spatialDerivative W z.1 z.2 (u z) =
      spatialDerivative u z.1 z.2 (W z) + eta_m • spatialLaplacian W z.1 z.2 + eta_m • f) :
    scalarTime (fun z => ‖W z‖^2) z +
      Adv spaceDirection (fun i _ => (u z) i) (fun z => ‖W z‖^2) z -
      eta_m*scalarLaplacian (fun z => ‖W z‖^2) z ≤
      (2*L+1)*‖W z‖^2+eta_m^2*D^2 := by
  rw [squared_equation hO hW hz heq]
  exact squared_residual_bound heta hL hD (Finset.sum_nonneg (fun i _ => sq_nonneg _))
/-- The comparison inequality derived from the actual two PDE hypotheses,
with their common prescribed velocity and the ideal Laplacian bound. -/
theorem ideal_resistive_squared_inequality {J : Set ℝ} (hJ : IsOpen J)
    {u B I : VelocityField} (hB : ContDiffOn ℝ ∞ B (J ×ˢ univ))
    (hI : ContDiffOn ℝ ∞ I (J ×ˢ univ)) {eta_m L D t : ℝ}
    (heta : 0 ≤ eta_m) (hres : ResistiveInductionOn eta_m J u B)
    (hideal : MagneticTransport.IdealInductionOn J u I) (ht : t ∈ J) (x : Space)
    (hL : ‖spatialDerivative u t x‖ ≤ L) (hD : ‖spatialLaplacian I t x‖ ≤ D) :
    scalarTime (fun z => ‖(B-I) z‖^2) (t,x) +
      Adv spaceDirection (fun i _ => (u (t,x)) i) (fun z => ‖(B-I) z‖^2) (t,x) -
      eta_m*scalarLaplacian (fun z => ‖(B-I) z‖^2) (t,x) ≤
      (2*L+1)*‖(B-I) (t,x)‖^2+eta_m^2*D^2 := by
  have hz : (t,x) ∈ J ×ˢ univ := ⟨ht,mem_univ x⟩
  have hBt : DifferentiableAt ℝ (fun s => B (s,x)) t :=
    ((hB.contDiffAt ((hJ.prod isOpen_univ).mem_nhds hz)).differentiableAt (by simp)).comp t
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hIt : DifferentiableAt ℝ (fun s => I (s,x)) t :=
    ((hI.contDiffAt ((hJ.prod isOpen_univ).mem_nhds hz)).differentiableAt (by simp)).comp t
      (differentiableAt_id.prodMk (differentiableAt_const x))
  exact squared_inequality (hJ.prod isOpen_univ) (hB.sub hI) hz heta hL hD
    (difference_equation (SpatialCurl.contDiff_spatialSlice hB ht)
      (SpatialCurl.contDiff_spatialSlice hI ht) hBt hIt (hres t ht x) (hideal t ht x))
end NavierStokes.ResistiveMagnetic.Comparison
