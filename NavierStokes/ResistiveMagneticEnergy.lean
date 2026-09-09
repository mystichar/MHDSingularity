import NavierStokes.ResistiveMagneticInduction
import NavierStokes.R3.CompactEnergy

/-! Magnetic energy is normalized by one half. Periodic boundary terms are
proved to vanish. No resistive magnetic solution is constructed here. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set MeasureTheory ProblemStatement PeriodicIntegration PeriodicUniqueness
open scoped ContDiff InnerProductSpace Topology

def periodicEnergy (B : MagneticField) (t : ℝ) : ℝ :=
  (1/2:ℝ) * cubeIntegral (fun x => ‖B (t,x)‖^2)

def ohmicDissipation (eta_m : ℝ) (B : MagneticField) (t : ℝ) : ℝ :=
  eta_m * PeriodicUniqueness.dissipation B t

theorem ohmicDissipation_nonneg {eta_m : ℝ} (heta : 0 ≤ eta_m) (B : MagneticField) (t : ℝ) :
    0 ≤ ohmicDissipation eta_m B t := mul_nonneg heta (dissipation_nonneg B t)

/-- The transport integral vanishes using only div u=0, not div B=0. -/
theorem periodic_energy_balance {eta_m t : ℝ} {u : VelocityField} {B : MagneticField}
    (hu : ContDiff ℝ ∞ (fun x => u (t,x))) (hB : ContDiff ℝ ∞ (fun x => B (t,x)))
    (hpu : UnitPeriods (fun x => u (t,x))) (hpB : UnitPeriods (fun x => B (t,x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ x, temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x) :
    cubeIntegral (fun x => ⟪B (t,x), temporalDerivative B t x⟫_ℝ) =
      cubeIntegral (fun x => ⟪B (t,x), spatialDerivative u t x (B (t,x))⟫_ℝ) -
        ohmicDissipation eta_m B t := by
  have hL := (hB.inner ℝ (spatialLaplacian_contDiff hB)).continuous
  have hS := (hB.inner ℝ ((hu.fderiv_right (by simp)).clm_apply hB)).continuous
  have hT := (hB.inner ℝ ((hB.fderiv_right (by simp)).clm_apply hu)).continuous
  have he : ∀ x, ⟪B (t,x), temporalDerivative B t x⟫_ℝ =
      ⟪B (t,x), spatialDerivative u t x (B (t,x))⟫_ℝ +
      eta_m * ⟪B (t,x), spatialLaplacian B t x⟫_ℝ -
      ⟪B (t,x), spatialDerivative B t x (u (t,x))⟫_ℝ := by
    intro x
    rw [eq_sub_of_add_eq (heq x)]
    simp [inner_sub_right, inner_add_right, inner_smul_right]
  simp_rw [he]
  dsimp only [spatialDerivative]
  rw [cubeIntegral_sub (hS.fun_add (continuous_const.fun_mul hL)) hT,
    cubeIntegral_add hS (continuous_const.fun_mul hL), cubeIntegral_const_mul,
    cubeIntegral_laplacian_energy hB hpB,
    cubeIntegral_transport_energy_zero hB hu hpB hpu hdiv]
  simp [ohmicDissipation, dissipation, sub_eq_add_neg]

theorem periodic_energy_hasDerivAt {eta_m a b t : ℝ} {u : VelocityField} {B : MagneticField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hB : ContDiffOn ℝ ∞ B (slab a b))
    (hpu : UnitSpatialPeriodsOn (Icc a b) u) (hpB : UnitSpatialPeriodsOn (Icc a b) B)
    (hdiv : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence u s x = 0)
    (hind : ResistiveInductionOn eta_m (Ioo a b) u B) (ht : t ∈ Ioo a b) :
    HasDerivAt (periodicEnergy B)
      (cubeIntegral (fun x => ⟪B (t,x), spatialDerivative u t x (B (t,x))⟫_ℝ) -
        ohmicDissipation eta_m B t) t := by
  have hd := (energy_hasDerivAt (u := B) (v := 0) hB contDiffOn_const ht).const_mul (1/2:ℝ)
  have hb := periodic_energy_balance (spatial_smooth hu (Ioo_subset_Icc_self ht))
    (spatial_smooth hB (Ioo_subset_Icc_self ht)) (hpu t (Ioo_subset_Icc_self ht))
    (hpB t (Ioo_subset_Icc_self ht)) (hdiv t ht) (hind t ht)
  simp only [energy, energyRate, sub_zero, cubeIntegral_const_mul] at hd
  convert! hd using 1
  rw [← hb]
  ring
/-- Whole-space normalization agrees with one half of the existing L2 square. -/
def wholeEnergy (B : MagneticField) (t : ℝ) : ℝ :=
  (1/2:ℝ) * NavierStokesR3.CompactEnergy.l2Sq B t

def wholeOhmicDissipation (eta_m : ℝ) (B : MagneticField) (t : ℝ) : ℝ :=
  eta_m * NavierStokesR3.CompactEnergy.dissipation B t

/-- A sufficient whole-space class: smooth, compactly supported B at this
time. Compactness discharges every spatial integrability/IBP premise.
No claim is made that positive diffusion preserves this support class. -/
theorem whole_energy_balance {eta_m t : ℝ} {u : VelocityField} {B : MagneticField}
    (hu : ContDiff ℝ ∞ (fun x => u (t,x))) (hB : ContDiff ℝ ∞ (fun x => B (t,x)))
    (hcB : HasCompactSupport (fun x => B (t,x)))
    (hcu : HasCompactSupport (fun x => u (t,x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (heq : ∀ x, temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x) :
    (∫ x, ⟪B (t,x), temporalDerivative B t x⟫_ℝ) =
      (∫ x, ⟪B (t,x), spatialDerivative u t x (B (t,x))⟫_ℝ) -
        wholeOhmicDissipation eta_m B t := by
  have hL := NavierStokesR3.CompactEnergy.integrable_inner_left hB.continuous
    (spatialLaplacian_contDiff hB).continuous hcB
  have hS := NavierStokesR3.CompactEnergy.integrable_inner_left hB.continuous
    ((hu.fderiv_right (by simp)).clm_apply hB).continuous hcB
  have hT := NavierStokesR3.CompactEnergy.integrable_inner_left hB.continuous
    ((hB.fderiv_right (by simp)).clm_apply hu).continuous hcB
  have he : ∀ x, ⟪B (t,x), temporalDerivative B t x⟫_ℝ =
      ⟪B (t,x), spatialDerivative u t x (B (t,x))⟫_ℝ +
      eta_m * ⟪B (t,x), spatialLaplacian B t x⟫_ℝ -
      ⟪B (t,x), spatialDerivative B t x (u (t,x))⟫_ℝ := by
    intro x
    rw [eq_sub_of_add_eq (heq x)]
    simp [inner_sub_right, inner_add_right, inner_smul_right]
  simp_rw [he]
  dsimp only [spatialDerivative]
  have hSL : Integrable (fun x => ⟪B (t,x), fderiv ℝ (fun y => u (t,y)) x (B (t,x))⟫_ℝ +
      eta_m * ⟪B (t,x), spatialLaplacian B t x⟫_ℝ) := hS.add (hL.const_mul eta_m)
  have hadd := integral_add hS (hL.const_mul eta_m)
  rw [integral_sub hSL hT, hadd, integral_const_mul,
    NavierStokesR3.CompactEnergy.integral_laplacian_energy hB hcB,
    NavierStokesR3.CompactEnergy.integral_transport_energy_zero hB hu hcu hdiv]
  simp [wholeOhmicDissipation, NavierStokesR3.CompactEnergy.dissipation, sub_eq_add_neg]

theorem whole_energy_hasDerivAt {eta_m a b t : ℝ} {u : VelocityField} {B : MagneticField}
    {S : Set Space} (hS : IsCompact S)
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hB : ContDiffOn ℝ ∞ B (slab a b))
    (hsupp : ∀ s ∈ Icc a b, tsupport (fun x => B (s,x)) ⊆ S)
    (hcu : ∀ s ∈ Icc a b, HasCompactSupport (fun x => u (s,x)))
    (hdiv : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence u s x = 0)
    (hind : ResistiveInductionOn eta_m (Ioo a b) u B) (ht : t ∈ Ioo a b) :
    HasDerivAt (wholeEnergy B)
      ((∫ x, ⟪B (t,x), spatialDerivative u t x (B (t,x))⟫_ℝ) -
        wholeOhmicDissipation eta_m B t) t := by
  have hd := (NavierStokesR3.CompactEnergy.energy_hasDerivAt hS hB hsupp ht).const_mul (1/2:ℝ)
  have hb := whole_energy_balance (spatial_smooth hu (Ioo_subset_Icc_self ht))
    (spatial_smooth hB (Ioo_subset_Icc_self ht))
    (hS.of_isClosed_subset (isClosed_tsupport _) (hsupp t (Ioo_subset_Icc_self ht)))
    (hcu t (Ioo_subset_Icc_self ht)) (hdiv t ht) (hind t ht)
  simp only [NavierStokesR3.CompactEnergy.energyRate, integral_const_mul] at hd
  convert! hd using 1
  rw [← hb]
  ring
/-- Time-integrated periodic Ohmic loss. Physical time and the same
unit-cell normalization are used. -/
def accumulatedOhmicDissipation (eta_m : ℝ) (B : MagneticField) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ohmicDissipation eta_m B t

theorem accumulatedOhmicDissipation_nonneg {eta_m a b : ℝ}
    (heta : 0 ≤ eta_m) (hab : a ≤ b) (B : MagneticField) :
    0 ≤ accumulatedOhmicDissipation eta_m B a b :=
  intervalIntegral.integral_nonneg hab (fun t _ => ohmicDissipation_nonneg heta B t)

theorem wholeOhmicDissipation_nonneg {eta_m : ℝ} (heta : 0 ≤ eta_m) (B : MagneticField) (t : ℝ) :
    0 ≤ wholeOhmicDissipation eta_m B t :=
  mul_nonneg heta (NavierStokesR3.CompactEnergy.dissipation_nonneg B t)
end NavierStokes.ResistiveMagnetic
