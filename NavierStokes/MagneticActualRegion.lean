import NavierStokes.MagneticMaterialRegion
import NavierStokes.MagneticEnergyCriterion

/-! Quantitative material neighborhoods for the existing actual compact
solution. The derivative bound is constructed, not assumed. -/
noncomputable section
namespace NavierStokes.MagneticCompactMain
open Set Filter Metric MeasureTheory ProblemStatement MagneticTransport
open MagneticAxisTransfer MagneticAssembledAmplification
open MagneticPeriodicMain (budget threshold geometry Selected naturalSolution gamma exponent)
open MagneticAmplificationRegion MagneticEnergyLowerBounds
open scoped Topology ContDiff ENNReal

variable (scales : ℕ → ℕ) (hsel : Selected scales) (forcing : VelocityField)
  (hNS : R3CompactCandidate.Properties (velocity scales) (pressure scales) forcing)
  (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
  (ha : lateStart budget threshold geometry scales hsel naturalSolution < a)

include ha

/-- Exact amplification at the distinguished label of the constructed flow. -/
theorem constructed_label_amplification (Bz0 t : ℝ) (ht : t ∈ Ico a 1) :
    let D := actualData scales hsel forcing hNS a ha0 ha1
    let W := MagneticCompactSeed.seed (gamma a) Bz0
    D.Phi t (gamma a) = gamma t ∧
    ‖D.Q W t (gamma a)‖ = |Bz0| * ((1-a)/(1-t)) ^ exponent := by
  let D := actualData scales hsel forcing hNS a ha0 ha1
  let W := MagneticCompactSeed.seed (gamma a) Bz0
  have hW : ContDiff ℝ ∞ W := MagneticCompactSeed.seed_smooth _ _
  have hg := (lateStart_spec budget threshold geometry scales hsel naturalSolution).2.2
  have hgc : ContinuousOn gamma (Ico a 1) := hg.path_continuous.mono
    (fun _ ht => ⟨ha.trans_le ht.1,ht.2⟩)
  have hp : D.Phi t (gamma a) = gamma t := D.Phi_eq_trajectory gamma hgc
    (fun s hs => hg.trajectory_derivative s ⟨ha.trans_le hs.1,hs.2⟩) t ht
  refine ⟨hp,?_⟩
  rw [← D.magnetic_Phi_Q W t ht, hp]
  have hBc : ContinuousOn (fun t => D.magnetic W (t,gamma t)) (Ico a 1) :=
    (D.magnetic_continuousOn W hW.continuous).comp
      (continuousOn_id.prodMk hgc) (fun _ ht => ⟨ht,mem_univ _⟩)
  have hseed : D.magnetic W (a,gamma a) = Bz0 • coordinateVector 2 :=
    (D.magnetic_initial W _).trans (MagneticCompactSeed.seed_at_center _ _)
  rw [hg.pure_axial_transport_preterminal ha (D.magnetic_induction W hW) hBc
    (fun s hs => (D.magnetic_contDiffAt W hW s hs _).differentiableAt one_ne_zero) hseed ht]
  simp only [norm_smul, coordinateVector, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, abs_mul]
  rw [abs_of_pos (Real.rpow_pos_of_pos (div_pos (sub_pos.mpr ha1) (sub_pos.mpr ht.2)) exponent)]

/-- Positive-volume high-field regions and an energy lower bound for the
same single preterminal solution, with a finite, locally uniformly bounded H. -/
theorem constructed_quantitative_region (Bz0 : ℝ) (hz : Bz0 ≠ 0)
    {r0 : ℝ} (hr : 0 < r0) (t : ℝ) (ht : t ∈ Ico a 1) :
    let D := actualData scales hsel forcing hNS a ha0 ha1
    let W := MagneticCompactSeed.seed (gamma a) Bz0
    let M := |Bz0| * ((1-a)/(1-t)) ^ exponent
    let H := D.derivativeBound W (gamma a) r0 t
    let r := radius r0 M H
    0 ≤ H ∧ 0 < r ∧ r ≤ r0/2 ∧ H*r ≤ M/2 ∧
    IsOpen (D.region t (gamma a) r) ∧
    volume (D.region t (gamma a) r) = ENNReal.ofReal (c3*r^3) ∧
    0 < volume (D.region t (gamma a) r) ∧
    (∀ x ∈ D.region t (gamma a) r, M/2 ≤ ‖D.magnetic W (t,x)‖) ∧
    ENNReal.ofReal ((c3/8)*M^2*r^3) ≤ MagneticCompactFlow.energy (D.magnetic W) t := by
  let D := actualData scales hsel forcing hNS a ha0 ha1
  let W := MagneticCompactSeed.seed (gamma a) Bz0
  have hW : ContDiff ℝ ∞ W := MagneticCompactSeed.seed_smooth _ _
  have hM : 0 < |Bz0| * ((1-a)/(1-t)) ^ exponent :=
    mul_pos (abs_pos.mpr hz) (Real.rpow_pos_of_pos (div_pos (sub_pos.mpr ha1) (sub_pos.mpr ht.2)) _)
  have hH := D.derivativeBound_spec W hW (gamma a) hr.le ht
  have hrb := radius_bounds hr hM hH.1
  have hh := D.quantitative_region W hW t ht (gamma a) hr hM hH.1
    (constructed_label_amplification scales hsel forcing hNS a ha0 ha1 ha Bz0 t ht).2 hH.2
  refine ⟨hH.1,hrb.1,hrb.2.1,hrb.2.2,hh.1,hh.2.1,?_,hh.2.2⟩
  rw [hh.2.1]
  exact ENNReal.ofReal_pos.mpr (mul_pos c3_pos (pow_pos hrb.1 3))
/-- The actual field's eventual lower bound, conditional only on the
additional power estimate for its constructed derivative supremum. -/
theorem constructed_eventual_energy_lower (Bz0 : ℝ) (hz : Bz0 ≠ 0)
    {r0 C p : ℝ} (hr : 0 < r0) (hC : 0 < C)
    (hbound : ∀ᶠ t in 𝓝[<] (1:ℝ),
      (actualData scales hsel forcing hNS a ha0 ha1).derivativeBound
        (MagneticCompactSeed.seed (gamma a) Bz0) (gamma a) r0 t ≤ C*(1-t)^(-p)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in 𝓝[<] (1:ℝ),
      ENNReal.ofReal (c*(1-t)^(-2*exponent+3*max (p-exponent) 0)) ≤
      MagneticCompactFlow.energy ((actualData scales hsel forcing hNS a ha0 ha1).magnetic
        (MagneticCompactSeed.seed (gamma a) Bz0)) t := by
  let D := actualData scales hsel forcing hNS a ha0 ha1
  let W := MagneticCompactSeed.seed (gamma a) Bz0
  let m := |Bz0| * (1-a)^exponent
  have hm : 0 < m := mul_pos (abs_pos.mpr hz) (Real.rpow_pos_of_pos (sub_pos.mpr ha1) _)
  refine eventual_power_lower _ (D.derivativeBound W (gamma a) r0) hr hm hC ?_ hbound ?_
  · filter_upwards [Ioo_mem_nhdsLT ha1] with t ht
    exact (D.derivativeBound_spec W (MagneticCompactSeed.seed_smooth _ _) (gamma a) hr.le ⟨ht.1.le,ht.2⟩).1
  · filter_upwards [Ioo_mem_nhdsLT ha1] with t ht
    have he := (constructed_quantitative_region scales hsel forcing hNS a ha0 ha1 ha Bz0 hz hr t
      ⟨ht.1.le,ht.2⟩).2.2.2.2.2.2.2.2
    have hM : |Bz0| * ((1-a)/(1-t))^exponent = m*(1-t)^(-exponent) := by
      rw [Real.div_rpow (sub_pos.mpr ha1).le (sub_pos.mpr ht.2).le, Real.rpow_neg (sub_pos.mpr ht.2).le]
      dsimp [m]
      ring
    rw [hM] at he
    exact he

/-- Only the late power bound on the actual derivative supremum remains
conditional. The magnetic field and all finite-time bounds are constructed. -/
theorem constructed_conditional_energy_divergence (Bz0 : ℝ) (hz : Bz0 ≠ 0)
    {r0 C p : ℝ} (hr : 0 < r0) (hC : 0 < C) (hp : 0 ≤ p)
    (hcrit : p < 5*exponent/3)
    (hbound : ∀ᶠ t in 𝓝[<] (1:ℝ),
      (actualData scales hsel forcing hNS a ha0 ha1).derivativeBound
        (MagneticCompactSeed.seed (gamma a) Bz0) (gamma a) r0 t ≤ C*(1-t)^(-p)) :
    Tendsto (MagneticCompactFlow.energy
      ((actualData scales hsel forcing hNS a ha0 ha1).magnetic
        (MagneticCompactSeed.seed (gamma a) Bz0))) (𝓝[<] (1:ℝ)) (𝓝 ⊤) := by
  let D := actualData scales hsel forcing hNS a ha0 ha1
  let W := MagneticCompactSeed.seed (gamma a) Bz0
  let m := |Bz0| *(1-a)^exponent
  have hm : 0 < m := mul_pos (abs_pos.mpr hz) (Real.rpow_pos_of_pos (sub_pos.mpr ha1) _)
  refine conditional_energy_divergence _ (D.derivativeBound W (gamma a) r0) hr hm hC
    (MagneticCoreAmplification.axialExponent_pos _) hp hcrit ?_ hbound ?_
  · filter_upwards [Ioo_mem_nhdsLT ha1] with t ht
    exact (D.derivativeBound_spec W (MagneticCompactSeed.seed_smooth _ _) (gamma a) hr.le ⟨ht.1.le,ht.2⟩).1
  · filter_upwards [Ioo_mem_nhdsLT ha1] with t ht
    have hh := constructed_quantitative_region scales hsel forcing hNS a ha0 ha1 ha Bz0 hz hr t ⟨ht.1.le,ht.2⟩
    have he := hh.2.2.2.2.2.2.2.2
    have hM : |Bz0| *((1-a)/(1-t))^exponent = m*(1-t)^(-exponent) := by
      rw [Real.div_rpow (sub_pos.mpr ha1).le (sub_pos.mpr ht.2).le, Real.rpow_neg (sub_pos.mpr ht.2).le]
      dsimp [m]
      ring
    rw [hM] at he
    exact he
end NavierStokes.MagneticCompactMain
