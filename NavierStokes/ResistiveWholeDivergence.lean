import NavierStokes.ResistiveMagneticL2Energy
import NavierStokes.ResistiveDivergencePreservation

/-! Whole-space divergence preservation in an explicit smooth-L2 energy
class. No compact support of the magnetic field or its divergence is assumed. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set MeasureTheory ProblemStatement PeriodicIntegration PeriodicUniqueness
open EulerLpTranslation EulerOrdinarySobolev
open scoped ContDiff InnerProductSpace

theorem whole_passive_balance_l2 {eta_m t : ℝ} {u W : VelocityField}
    (A : SmoothL2Field Space) (hA : (fun x => W (t,x)) = A.field)
    (hu : ContDiff ℝ ∞ (fun x => u (t,x))) (hcu : HasCompactSupport (fun x => u (t,x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ x, temporalDerivative W t x + spatialDerivative W t x (u (t,x)) =
      eta_m • spatialLaplacian W t x) :
    (∫ x, ⟪W (t,x),temporalDerivative W t x⟫_ℝ) =
      -eta_m*NavierStokesR3.CompactEnergy.dissipation W t := by
  have hW : ContDiff ℝ ∞ (fun x => W (t,x)) := by rw [hA]; exact A.smooth
  have hT : Integrable (fun x => ⟪W (t,x),spatialDerivative W t x (u (t,x))⟫_ℝ) := by
    apply (hW.inner ℝ ((hW.fderiv_right (by simp)).clm_apply hu)).continuous.integrable_of_hasCompactSupport
    apply hcu.mono'
    intro x hx
    by_contra hn
    exact hx (by dsimp only; rw [image_eq_zero_of_notMem_tsupport hn]; simp)
  have hAp : ∀ x, W (t,x) = A.field x := fun x => congrFun hA x
  have hL : Integrable (fun x => ⟪W (t,x),spatialLaplacian W t x⟫_ℝ) := by
    simpa only [spatialLaplacian,spatialDerivative,hA,hAp] using l2_laplacian_integrable A
  have hLap : (∫ x, ⟪W (t,x),spatialLaplacian W t x⟫_ℝ) =
      -NavierStokesR3.CompactEnergy.dissipation W t := by
    simpa only [spatialLaplacian,spatialDerivative,NavierStokesR3.CompactEnergy.dissipation,spatialPartial,hA,hAp]
      using l2_laplacian_energy A
  have htrans : (∫ x, ⟪W (t,x),spatialDerivative W t x (u (t,x))⟫_ℝ) = 0 :=
    NavierStokesR3.CompactEnergy.integral_transport_energy_zero hW hu hcu hdiv
  have he : ∀ x, ⟪W (t,x),temporalDerivative W t x⟫_ℝ =
      eta_m*⟪W (t,x),spatialLaplacian W t x⟫_ℝ - ⟪W (t,x),spatialDerivative W t x (u (t,x))⟫_ℝ := by
    intro x
    rw [eq_sub_of_add_eq (heq x)]
    simp [inner_sub_right,inner_smul_right]
  simp_rw [he]
  rw [integral_sub (hL.const_mul eta_m) hT,integral_const_mul,hLap,htrans]
  ring

/-- Zero-data uniqueness; the L2 curve assumptions justify differentiating
its norm, and the smooth spatial jets justify integration by parts. -/
theorem whole_passive_zero_l2 {eta_m a b : ℝ} {u W : VelocityField}
    (heta : 0 ≤ eta_m) (hab : a ≤ b)
    (A C : ℝ → SmoothL2Field Space)
    (hA : ∀ t ∈ Icc a b, (fun x => W (t,x)) = (A t).field)
    (hC : ∀ t ∈ Ioo a b, (C t).field = fun x => temporalDerivative W t x)
    (hc : ContinuousOn (fun t => (A t).toLp) (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt (fun s => (A s).toLp) (C t).toLp t)
    (hu : ∀ t ∈ Ioo a b, ContDiff ℝ ∞ (fun x => u (t,x)))
    (hcu : ∀ t ∈ Ioo a b, HasCompactSupport (fun x => u (t,x)))
    (hdiv : ∀ t ∈ Ioo a b, ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ t ∈ Ioo a b, ∀ x, temporalDerivative W t x + spatialDerivative W t x (u (t,x)) =
      eta_m • spatialLaplacian W t x)
    (hinit : ∀ x, W (a,x) = 0) : ∀ t ∈ Icc a b, ∀ x, W (t,x) = 0 := by
  have hzero : (A a).toLp = 0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [← real_inner_self_eq_norm_sq,field_inner,← hA a ⟨le_rfl,hab⟩]
    simp only [hinit,inner_zero_left,integral_zero]
  have hz := gronwall_zero (E := fun t => ‖(A t).toLp‖^2)
    (E' := fun t => -2*eta_m*NavierStokesR3.CompactEnergy.dissipation W t)
    (K := 0) hab (hc.norm.pow 2) (by rw [hzero]; simp)
    (fun t _ => sq_nonneg _) (fun t ht => by
      have hder := (hd t ht).norm_sq
      have he := whole_passive_balance_l2 (A t) (hA t (Ioo_subset_Icc_self ht))
        (hu t ht) (hcu t ht) (hdiv t ht) (heq t ht)
      rw [field_inner,← hA t (Ioo_subset_Icc_self ht),hC t ht,he] at hder
      convert! hder using 1; ring)
    (fun t _ => by
      have hnonneg := NavierStokesR3.CompactEnergy.dissipation_nonneg W t
      simp only [zero_mul]
      nlinarith)
  intro t ht x
  have hn : (A t).toLp = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (hz t ht))
  exact (congrFun (hA t ht) x).trans (congrFun (field_zero_of_toLp_zero (A t) hn) x)

/-- Whole-space propagation of magnetic solenoidality. In addition to the
classical PDE, the lifted divergence must lie in the displayed L2 evolution
class. These are integrability/time regularity premises, not div B = 0. -/
theorem whole_divergence_preserved_l2 {I : Set ℝ} (hI : IsOpen I)
    {eta_m a b : ℝ} (heta : 0 ≤ eta_m) (hab : a ≤ b) (hsub : Icc a b ⊆ I)
    {u : VelocityField} {B : MagneticField}
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hcu : ∀ t ∈ Ioo a b, HasCompactSupport (fun x => u (t,x)))
    (hdiv : ∀ t ∈ I, ∀ x, spatialDivergence u t x = 0)
    (hind : ResistiveInductionOn eta_m (Ioo a b) u B)
    (A C : ℝ → SmoothL2Field Space)
    (hA : ∀ t ∈ Icc a b, (fun x => scalarLift (divergenceScalar B) (t,x)) = (A t).field)
    (hC : ∀ t ∈ Ioo a b, (C t).field = fun x => temporalDerivative (scalarLift (divergenceScalar B)) t x)
    (hc : ContinuousOn (fun t => (A t).toLp) (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt (fun s => (A s).toLp) (C t).toLp t)
    (hinit : ∀ x, spatialDivergence B a x = 0) :
    ∀ t ∈ Icc a b, ∀ x, spatialDivergence B t x = 0 := by
  have hf : ContDiffOn ℝ ∞ (divergenceScalar B) (I ×ˢ univ) := Calculus.Div_smooth (hI.prod isOpen_univ) (fun i => component_smooth hB i)
  have hsmall : Ioo a b ⊆ I := Ioo_subset_Icc_self.trans hsub
  have heq := scalarLift_passive isOpen_Ioo (hf.mono (prod_subset_prod_left hsmall))
    (fun t ht x => divergence_transport isOpen_Ioo
      (hu.mono (prod_subset_prod_left hsmall)) (hB.mono (prod_subset_prod_left hsmall))
      hind (fun s hs => hdiv s (hsmall hs)) ht x)
  have hz := whole_passive_zero_l2 heta hab A C hA hC hc hd
    (fun t ht => spatial_smooth (hu.mono (prod_subset_prod_left hsub)) (Ioo_subset_Icc_self ht))
    hcu (fun t ht => hdiv t (hsmall ht)) heq
    (fun x => by
      unfold scalarLift
      rw [divergenceScalar_eq (hI.prod isOpen_univ) hB ⟨hsub ⟨le_rfl,hab⟩,mem_univ x⟩,hinit x,zero_smul])
  intro t ht x
  have hh := congrArg (fun v : Space => v 2) (hz t ht x)
  simp [scalarLift,coordinateVector] at hh
  exact (divergenceScalar_eq (hI.prod isOpen_univ) hB ⟨hsub ht,mem_univ x⟩).symm.trans hh
end NavierStokes.ResistiveMagnetic
