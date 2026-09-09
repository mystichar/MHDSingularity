import NavierStokes.ResistiveMagneticDivergence
import NavierStokes.ResistiveMagneticEnergy

/-! Periodic divergence is propagated by a scalar advection-diffusion
energy argument, not imposed as a perpetual magnetic hypothesis. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set Filter ProblemStatement PeriodicIntegration PeriodicUniqueness Calculus
open scoped Topology ContDiff InnerProductSpace

theorem passive_energy_balance {eta_m t : ℝ} {u W : VelocityField}
    (hu : ContDiff ℝ ∞ (fun x => u (t,x))) (hW : ContDiff ℝ ∞ (fun x => W (t,x)))
    (hpu : UnitPeriods (fun x => u (t,x))) (hpW : UnitPeriods (fun x => W (t,x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ x, temporalDerivative W t x + spatialDerivative W t x (u (t,x)) =
      eta_m • spatialLaplacian W t x) :
    cubeIntegral (fun x => ⟪W (t,x),temporalDerivative W t x⟫_ℝ) =
      -eta_m*dissipation W t := by
  have hL := (hW.inner ℝ (spatialLaplacian_contDiff hW)).continuous
  have hT := (hW.inner ℝ ((hW.fderiv_right (by simp)).clm_apply hu)).continuous
  have he : ∀ x, ⟪W (t,x),temporalDerivative W t x⟫_ℝ =
      eta_m*⟪W (t,x),spatialLaplacian W t x⟫_ℝ -
      ⟪W (t,x),spatialDerivative W t x (u (t,x))⟫_ℝ := by
    intro x
    rw [eq_sub_of_add_eq (heq x)]
    simp [inner_sub_right,inner_smul_right]
  simp_rw [he]
  dsimp only [spatialDerivative]
  rw [cubeIntegral_sub (continuous_const.fun_mul hL) hT,cubeIntegral_const_mul,
    cubeIntegral_laplacian_energy hW hpW,cubeIntegral_transport_energy_zero hW hu hpW hpu hdiv]
  simp [dissipation]

/-- Zero-data uniqueness for periodic vector advection-diffusion, with
nonnegative diffusivity, including eta_m=0. -/
theorem periodic_passive_zero {eta_m a b : ℝ} {u W : VelocityField}
    (heta : 0 ≤ eta_m) (hab : a ≤ b)
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hW : ContDiffOn ℝ ∞ W (slab a b))
    (hpu : UnitSpatialPeriodsOn (Icc a b) u) (hpW : UnitSpatialPeriodsOn (Icc a b) W)
    (hdiv : ∀ t ∈ Ioo a b, ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ t ∈ Ioo a b, ∀ x, temporalDerivative W t x + spatialDerivative W t x (u (t,x)) =
      eta_m • spatialLaplacian W t x)
    (hinit : ∀ x, W (a,x) = 0) : ∀ t ∈ Icc a b, ∀ x, W (t,x) = 0 := by
  have hz := gronwall_zero (E := energy W 0) (E' := fun t => -2*eta_m*dissipation W t)
    (K := 0) hab (energy_continuousOn hW contDiffOn_const)
    (energy_initial_zero hinit) (fun t _ => energy_nonneg W 0 t)
    (fun t ht => by
      have hd := energy_hasDerivAt (u := W) (v := 0) hW contDiffOn_const ht
      have he := passive_energy_balance (spatial_smooth hu (Ioo_subset_Icc_self ht))
        (spatial_smooth hW (Ioo_subset_Icc_self ht)) (hpu t (Ioo_subset_Icc_self ht))
        (hpW t (Ioo_subset_Icc_self ht)) (hdiv t ht) (heq t ht)
      simp only [energyRate,sub_zero,cubeIntegral_const_mul] at hd
      rw [he] at hd
      convert! hd using 1; ring)
    (fun t _ => by
      have hd := dissipation_nonneg W t
      simp only [zero_mul]
      nlinarith)
  intro t ht x
  exact eq_of_energy_zero (spatial_smooth hW ht).continuous continuous_const
    (hpW t ht) (fun _ _ => rfl) (hz t ht) x

def scalarLift (f : SpaceTime → ℝ) : VelocityField := fun z => f z • coordinateVector 2

theorem scalarLift_passive {I : Set ℝ} (hI : IsOpen I) {eta_m : ℝ}
    {u : VelocityField} {f : SpaceTime → ℝ} (hf : ContDiffOn ℝ ∞ f (I ×ˢ univ))
    (heq : ∀ t ∈ I, ∀ x, scalarTime f (t,x) + Adv spaceDirection (component u) f (t,x) =
      eta_m*scalarLaplacian f (t,x)) :
    ∀ t ∈ I, ∀ x, temporalDerivative (scalarLift f) t x +
      spatialDerivative (scalarLift f) t x (u (t,x)) = eta_m • spatialLaplacian (scalarLift f) t x := by
  have hW : ContDiffOn ℝ ∞ (scalarLift f) (I ×ˢ univ) := hf.smul contDiffOn_const
  intro t ht x
  ext i
  change (temporalDerivative (scalarLift f) t x) i +
    (spatialDerivative (scalarLift f) t x (u (t,x))) i = eta_m*(spatialLaplacian (scalarLift f) t x) i
  rw [← component_time (z := (t,x)) (hI.prod isOpen_univ) hW ⟨ht,mem_univ x⟩,
    ← component_advection (z := (t,x)) (hI.prod isOpen_univ) hW ⟨ht,mem_univ x⟩,
    ← component_laplacian (z := (t,x)) (hI.prod isOpen_univ) hW ⟨ht,mem_univ x⟩]
  have hi : component (scalarLift f) i = fun z => f z * (coordinateVector 2) i := by
    funext z
    simp [component,scalarLift]
  rw [hi]
  fin_cases i
  · dsimp [P,Lap]
    simp [coordinateVector]
    right
    apply Finset.sum_eq_zero
    intro j _
    have hz : P (spaceDirection j) (fun _ : SpaceTime => (0:ℝ)) = fun _ => 0 := by
      funext w
      simp [P]
    rw [hz]
    simp
  · dsimp [P,Lap]
    simp [coordinateVector]
    right
    apply Finset.sum_eq_zero
    intro j _
    have hz : P (spaceDirection j) (fun _ : SpaceTime => (0:ℝ)) = fun _ => 0 := by
      funext w
      simp [P]
    rw [hz]
    simp
  · simpa [coordinateVector,scalarTime,scalarLaplacian,Adv,component] using heq t ht x

/-- Classical periodic divergence preservation on any finite slab inside
an open smoothness domain. Only the initial magnetic divergence is assumed. -/
theorem periodic_divergence_preserved {I : Set ℝ} (hI : IsOpen I)
    {eta_m a b : ℝ} (heta : 0 ≤ eta_m) (hab : a ≤ b) (hsub : Icc a b ⊆ I)
    {u : VelocityField} {B : MagneticField}
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hpu : UnitSpatialPeriodsOn I u) (hpB : UnitSpatialPeriodsOn I B)
    (hdiv : ∀ t ∈ I, ∀ x, spatialDivergence u t x = 0)
    (hind : ResistiveInductionOn eta_m (Ioo a b) u B)
    (hinit : ∀ x, spatialDivergence B a x = 0) :
    ∀ t ∈ Icc a b, ∀ x, spatialDivergence B t x = 0 := by
  let f := divergenceScalar B
  have hf : ContDiffOn ℝ ∞ f (I ×ˢ univ) := Div_smooth (hI.prod isOpen_univ) (fun i => component_smooth hB i)
  have hp : UnitSpatialPeriodsOn I (scalarLift f) := by
    intro t ht x j
    unfold scalarLift
    congr 1
    change divergenceScalar B (t,x+coordinateVector j) = divergenceScalar B (t,x)
    rw [divergenceScalar_eq (hI.prod isOpen_univ) hB ⟨ht,mem_univ _⟩,
      divergenceScalar_eq (hI.prod isOpen_univ) hB ⟨ht,mem_univ _⟩]
    unfold spatialDivergence
    simp_rw [ResidualRegularity.spatialDerivative_periods hpB t ht x j]
  have hsmall : Ioo a b ⊆ I := Ioo_subset_Icc_self.trans hsub
  have heq := scalarLift_passive isOpen_Ioo (hf.mono (prod_subset_prod_left hsmall))
    (fun t ht x => divergence_transport isOpen_Ioo
      (hu.mono (prod_subset_prod_left hsmall)) (hB.mono (prod_subset_prod_left hsmall))
      hind (fun s hs => hdiv s (hsmall hs)) ht x)
  have hz := periodic_passive_zero heta hab (hu.mono (prod_subset_prod_left hsub))
    ((hf.smul contDiffOn_const).mono (prod_subset_prod_left hsub))
    (fun t ht => hpu t (hsub ht)) (fun t ht => hp t (hsub ht))
    (fun t ht => hdiv t (hsub (Ioo_subset_Icc_self ht)))
    (fun t ht => heq t ht)
    (fun x => by
      dsimp [scalarLift,f]
      rw [divergenceScalar_eq (hI.prod isOpen_univ) hB ⟨hsub ⟨le_rfl,hab⟩,mem_univ x⟩,hinit x,zero_smul])
  intro t ht x
  have hh := congrArg (fun v : Space => v 2) (hz t ht x)
  simp [coordinateVector] at hh
  exact (divergenceScalar_eq (hI.prod isOpen_univ) hB ⟨hsub ht,mem_univ x⟩).symm.trans hh
end NavierStokes.ResistiveMagnetic
