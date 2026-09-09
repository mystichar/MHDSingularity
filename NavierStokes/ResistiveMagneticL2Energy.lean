import NavierStokes.ResistiveMagneticEnergy
import Euler.OrdinaryL2Integration

/-! Whole-space diffusion integration by parts without compact magnetic
support. The existing smooth-L2 jet class discharges all three required
pairings. This is compatible with diffusive tails, but its existence for
the assembled resistive PDE remains an analytic construction obligation. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open MeasureTheory ProblemStatement PeriodicIntegration PeriodicUniqueness
open EulerLpTranslation EulerOrdinarySobolev
open scoped ContDiff InnerProductSpace

theorem l2_laplacian_integrable (A : SmoothL2Field Space) :
    Integrable (fun x => ⟪A.field x,spatialLaplacian (fun z => A.field z.2) 0 x⟫_ℝ) := by
  simp only [spatialLaplacian,inner_sum]
  apply integrable_finsetSum
  intro i _
  exact field_inner_integrable A ((A.directionalField (coordinateVector i)).directionalField (coordinateVector i))

theorem l2_laplacian_energy (A : SmoothL2Field Space) :
    (∫ x, ⟪A.field x,spatialLaplacian (fun z => A.field z.2) 0 x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, ‖fderiv ℝ A.field x (coordinateVector i)‖^2) := by
  simp only [spatialLaplacian,inner_sum]
  have hi : ∀ i : Fin 3, Integrable (fun x => ⟪A.field x,
      fderiv ℝ (fun y => spatialDerivative (fun z => A.field z.2) 0 y (coordinateVector i)) x (coordinateVector i)⟫_ℝ) :=
    fun i => field_inner_integrable A ((A.directionalField (coordinateVector i)).directionalField (coordinateVector i))
  rw [integral_finsetSum _ (fun i _ => hi i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := field_directional_ibp A (A.directionalField (coordinateVector i)) (coordinateVector i)
  change (∫ x, ⟪fderiv ℝ A.field x (coordinateVector i),fderiv ℝ A.field x (coordinateVector i)⟫_ℝ) =
    -(∫ x, ⟪A.field x,fderiv ℝ (fun y => fderiv ℝ A.field y (coordinateVector i)) x (coordinateVector i)⟫_ℝ) at hi
  simp only [real_inner_self_eq_norm_sq] at hi
  dsimp only [spatialDerivative]
  linarith

/-- The magnetic field need not have compact support. Smooth L2 spatial
jets supply diffusion IBP, and compact u supplies integrability of transport
and stretching. Both actual compact velocities and diffusive magnetic tails
fit these distinct spatial hypotheses. -/
theorem whole_energy_balance_l2 {eta_m t : ℝ} {u : VelocityField} {B : MagneticField}
    (A : SmoothL2Field Space) (hA : (fun x => B (t,x)) = A.field)
    (hu : ContDiff ℝ ∞ (fun x => u (t,x))) (hcu : HasCompactSupport (fun x => u (t,x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ x, temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x) :
    (∫ x, ⟪B (t,x),temporalDerivative B t x⟫_ℝ) =
      (∫ x, ⟪B (t,x),spatialDerivative u t x (B (t,x))⟫_ℝ) - wholeOhmicDissipation eta_m B t := by
  have hB : ContDiff ℝ ∞ (fun x => B (t,x)) := by rw [hA]; exact A.smooth
  have hS : Integrable (fun x => ⟪B (t,x),spatialDerivative u t x (B (t,x))⟫_ℝ) := by
    apply (hB.inner ℝ ((hu.fderiv_right (by simp)).clm_apply hB)).continuous.integrable_of_hasCompactSupport
    apply (hcu.fderiv ℝ).mono'
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    exact hx (by change ⟪B (t,x),fderiv ℝ (fun x => u (t,x)) x (B (t,x))⟫_ℝ = 0; rw [hz]; simp)
  have hT : Integrable (fun x => ⟪B (t,x),spatialDerivative B t x (u (t,x))⟫_ℝ) := by
    apply (hB.inner ℝ ((hB.fderiv_right (by simp)).clm_apply hu)).continuous.integrable_of_hasCompactSupport
    apply hcu.mono'
    intro x hx
    by_contra hn
    exact hx (by dsimp only; rw [image_eq_zero_of_notMem_tsupport hn]; simp)
  have hAp : ∀ x, B (t,x) = A.field x := fun x => congrFun hA x
  have htrans : (∫ x, ⟪B (t,x),spatialDerivative B t x (u (t,x))⟫_ℝ) = 0 :=
    NavierStokesR3.CompactEnergy.integral_transport_energy_zero hB hu hcu hdiv
  have hL : Integrable (fun x => ⟪B (t,x),spatialLaplacian B t x⟫_ℝ) := by
    simpa only [spatialLaplacian,spatialDerivative,hA,hAp] using l2_laplacian_integrable A
  have hLap : (∫ x, ⟪B (t,x),spatialLaplacian B t x⟫_ℝ) =
      -NavierStokesR3.CompactEnergy.dissipation B t := by
    simpa only [spatialLaplacian,spatialDerivative,NavierStokesR3.CompactEnergy.dissipation,spatialPartial,hA,hAp]
      using l2_laplacian_energy A
  have he : ∀ x, ⟪B (t,x),temporalDerivative B t x⟫_ℝ =
      ⟪B (t,x),spatialDerivative u t x (B (t,x))⟫_ℝ +
      eta_m*⟪B (t,x),spatialLaplacian B t x⟫_ℝ - ⟪B (t,x),spatialDerivative B t x (u (t,x))⟫_ℝ := by
    intro x
    rw [eq_sub_of_add_eq (heq x)]
    simp [inner_sub_right,inner_add_right,inner_smul_right]
  simp_rw [he]
  have hSL : Integrable (fun x => ⟪B (t,x),spatialDerivative u t x (B (t,x))⟫_ℝ +
      eta_m*⟪B (t,x),spatialLaplacian B t x⟫_ℝ) := hS.add (hL.const_mul eta_m)
  rw [integral_sub hSL hT,integral_add hS (hL.const_mul eta_m),integral_const_mul,hLap,
    htrans]
  simp only [wholeOhmicDissipation,sub_zero,mul_neg]
  ring
/-- Whole-space classical energy identity with diffusive tails: spatial
smooth-L2 jets and differentiability of the actual magnetic curve in L2
replace compact magnetic support and justify time differentiation. -/
theorem whole_energy_hasDerivAt_l2 {eta_m t : ℝ} {u : VelocityField} {B : MagneticField}
    (A : ℝ → SmoothL2Field Space) (C : SmoothL2Field Space)
    (hA : ∀ s, (fun x => B (s,x)) = (A s).field)
    (hC : C.field = fun x => temporalDerivative B t x)
    (hd : HasDerivAt (fun s => (A s).toLp) C.toLp t)
    (hu : ContDiff ℝ ∞ (fun x => u (t,x))) (hcu : HasCompactSupport (fun x => u (t,x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ x, temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x) :
    HasDerivAt (wholeEnergy B)
      ((∫ x, ⟪B (t,x),spatialDerivative u t x (B (t,x))⟫_ℝ) - wholeOhmicDissipation eta_m B t) t := by
  have hE : wholeEnergy B = fun s => (1/2:ℝ)*‖(A s).toLp‖^2 := by
    funext s
    unfold wholeEnergy NavierStokesR3.CompactEnergy.l2Sq
    rw [← real_inner_self_eq_norm_sq,field_inner]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by rw [← hA s]; simp))
  rw [hE]
  have ht := hd.norm_sq.const_mul (1/2:ℝ)
  have hwork := whole_energy_balance_l2 (A t) (hA t) hu hcu hdiv heq
  convert! ht using 1
  rw [field_inner,← hA t,hC]
  rw [← hwork]
  ring
end NavierStokes.ResistiveMagnetic
