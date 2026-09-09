import NavierStokes.MagneticActualRegion

/-! Amplitude scaling uses one prescribed velocity and one initial time. -/
noncomputable section
namespace NavierStokes.MagneticCompactSeed
open ProblemStatement
open scoped ContDiff

theorem potential_homogeneous (center : Space) (c z : ℝ) :
    potential center (c*z) = fun x => c • potential center z x := by
  funext x
  simp only [potential, linearPotential, smul_apply, smul_smul]
  congr 1
  ring

theorem seed_homogeneous (center : Space) (c z : ℝ) :
    seed center (c*z) = fun x => c • seed center z x := by
  funext x
  unfold seed SpatialCurl.curl
  rw [potential_homogeneous]
  have hd : HasFDerivAt (fun y => c • potential center z y) (c • fderiv ℝ (potential center z) x) x :=
    ((potential_smooth center z).differentiable (by simp) x).hasFDerivAt.const_smul c
  rw [hd.fderiv]
  exact SpatialCurl.curlLinear.map_smul c _
end NavierStokes.MagneticCompactSeed

namespace NavierStokes.MagneticCompactSolution.Data
open Set Filter Metric MeasureTheory ProblemStatement
open scoped Topology ContDiff ENNReal
variable (D : Data)

theorem magnetic_smul (W : Space → Space) (c : ℝ) (z : SpaceTime) :
    D.magnetic (fun x => c • W x) z = c • D.magnetic W z := by
  unfold magnetic
  split_ifs <;> simp [MagneticCompactFlow.Slab.magnetic, map_smul]

theorem energy_smul (B : MagneticField) (c t : ℝ) :
    MagneticCompactFlow.energy (fun z => c • B z) t =
      ENNReal.ofReal (c^2) * MagneticCompactFlow.energy B t := by
  unfold MagneticCompactFlow.energy
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ENNReal.ofReal_mul (sq_nonneg c)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  ring

theorem initial_energy_scaling (center : Space) (c : ℝ) :
    MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed center c)) D.a =
      ENNReal.ofReal (c^2) *
        MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed center 1)) D.a := by
  have hs := MagneticCompactSeed.seed_homogeneous center c 1
  rw [mul_one] at hs
  rw [hs]
  have he : D.magnetic (fun x => c • MagneticCompactSeed.seed center 1 x) =
      fun z => c • D.magnetic (MagneticCompactSeed.seed center 1) z :=
    funext (D.magnetic_smul _ c)
  rw [he]
  exact energy_smul _ c D.a
theorem initial_unit_energy_pos (center : Space) :
    0 < MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed center 1)) D.a := by
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (MagneticCompactSeed.seed_local_constant center 1)
  have hb : ∀ x ∈ ball center r,
      (1:ℝ)/2 ≤ ‖D.magnetic (MagneticCompactSeed.seed center 1) (D.a,x)‖ := by
    intro x hx
    rw [D.magnetic_initial, hball hx]
    norm_num [coordinateVector, PiLp.norm_single]
  have he := MagneticEnergyLowerBounds.energy_of_region _ D.a 1 (by norm_num)
    (ball center r) isOpen_ball.measurableSet hb
  have hv : 0 < volume (ball center r) := by
    rw [MagneticEnergyLowerBounds.ball_volume center hr.le]
    exact ENNReal.ofReal_pos.mpr (mul_pos MagneticEnergyLowerBounds.c3_pos (pow_pos hr 3))
  exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 1^2/8)).ne' hv.ne').trans_le he

/-- Arbitrarily small positive initial total energy, at fixed velocity and a. -/
theorem small_initial_energy (center : Space) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, 0 < c ∧
      0 < MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed center c)) D.a ∧
      MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed center c)) D.a < ENNReal.ofReal epsilon := by
  let E := MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed center 1)) D.a
  obtain ⟨C,hC,J,hJ,hbound⟩ := D.slab_bounds (MagneticCompactSeed.seed center 1)
    (MagneticCompactSeed.seed_smooth center 1).continuous (MagneticCompactSeed.seed_compact center 1)
    D.a ⟨le_rfl,D.ha⟩
  have hE : E < ⊤ := (hbound D.a ⟨le_rfl,le_rfl⟩).2.2.2
  have hc : Continuous (fun c : ℝ => ENNReal.ofReal (c^2)*E) :=
    (ENNReal.continuous_mul_const hE.ne).comp (ENNReal.continuous_ofReal.comp (continuous_id.pow 2))
  have hev : ∀ᶠ c : ℝ in 𝓝[>] 0, ENNReal.ofReal (c^2)*E < ENNReal.ofReal epsilon :=
    nhdsWithin_le_nhds (hc.continuousAt.eventually
      (Iio_mem_nhds (by simpa using ENNReal.ofReal_pos.mpr hepsilon)))
  obtain ⟨c,hcE,hcp⟩ := (hev.and (self_mem_nhdsWithin (a := (0:ℝ)) (s := Ioi 0))).exists
  refine ⟨c,hcp,?_,?_⟩
  · rw [D.initial_energy_scaling]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hcp)).ne' (D.initial_unit_energy_pos center).ne'
  · rw [D.initial_energy_scaling]
    exact hcE
end NavierStokes.MagneticCompactSolution.Data

namespace NavierStokes.MagneticCompactMain
open Set Filter ProblemStatement MagneticTransport
open MagneticAxisTransfer MagneticAssembledAmplification
open MagneticPeriodicMain (budget threshold geometry Selected naturalSolution gamma exponent)
open scoped Topology ContDiff ENNReal
variable (scales : ℕ → ℕ) (hsel : Selected scales) (forcing : VelocityField)
  (hNS : R3CompactCandidate.Properties (velocity scales) (pressure scales) forcing)
  (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
  (ha : lateStart budget threshold geometry scales hsel naturalSolution < a)
include ha

theorem constructed_sup_divergence (c : ℝ) (hc : c ≠ 0) :
    let D := actualData scales hsel forcing hNS a ha0 ha1
    Tendsto (MagneticPeriodicNorms.supNorm (D.magnetic (MagneticCompactSeed.seed (gamma a) c)))
      (𝓝[<] 1) atTop := by
  let D := actualData scales hsel forcing hNS a ha0 ha1
  let W := MagneticCompactSeed.seed (gamma a) c
  have hW : ContDiff ℝ ∞ W := MagneticCompactSeed.seed_smooth _ _
  have hg := (lateStart_spec budget threshold geometry scales hsel naturalSolution).2.2
  have hgc : ContinuousOn gamma (Ico a 1) := hg.path_continuous.mono
    (fun _ ht => ⟨ha.trans_le ht.1,ht.2⟩)
  have hBc : ContinuousOn (fun t => D.magnetic W (t,gamma t)) (Ico a 1) :=
    (D.magnetic_continuousOn W hW.continuous).comp
      (continuousOn_id.prodMk hgc) (fun _ ht => ⟨ht,mem_univ _⟩)
  have hseed : D.magnetic W (a,gamma a) = c • coordinateVector 2 :=
    (D.magnetic_initial W _).trans (MagneticCompactSeed.seed_at_center _ _)
  have hdiv := compact_magnetic_norm_tendsto_atTop budget threshold geometry scales hsel naturalSolution
    ha ha1 hc (D.magnetic_induction W hW) hBc
    (fun s hs => (D.magnetic_contDiffAt W hW s hs _).differentiableAt one_ne_zero) hseed
  apply tendsto_atTop_mono' _ _ hdiv
  filter_upwards [Ioo_mem_nhdsLT ha1] with t ht
  obtain ⟨C,hC,E,hE,hbound⟩ := D.slab_bounds W hW.continuous (MagneticCompactSeed.seed_compact _ _) t ⟨ht.1.le,ht.2⟩
  exact (MagneticPeriodicNorms.supNorm_bounds hC (hbound t ⟨ht.1.le,le_rfl⟩).1).2.2 (gamma t)

/-- The prescribed compact NS velocity and reference time are fixed before
choosing the small seed amplitude. -/
theorem small_initial_energy_sup_divergence {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let D := actualData scales hsel forcing hNS a ha0 ha1
    ∃ c : ℝ, 0 < c ∧
      0 < MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed (gamma a) c)) a ∧
      MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed (gamma a) c)) a < ENNReal.ofReal epsilon ∧
      Tendsto (MagneticPeriodicNorms.supNorm (D.magnetic (MagneticCompactSeed.seed (gamma a) c)))
        (𝓝[<] 1) atTop := by
  let D := actualData scales hsel forcing hNS a ha0 ha1
  obtain ⟨c,hc,hpos,hsmall⟩ := D.small_initial_energy (gamma a) hepsilon
  exact ⟨c,hc,hpos,hsmall,constructed_sup_divergence scales hsel forcing hNS a ha0 ha1 ha c hc.ne'⟩
omit ha in
/-- Closed choice of the existing NS data, before the energy tolerance or
seed amplitude is chosen. -/
theorem small_initial_energy_main :
    ∃ scales : ℕ → ℕ, ∃ hsel : Selected scales,
    ∃ forcing : VelocityField, ∃ a : ℝ, ∃ ha0 : 0 < a, ∃ ha1 : a < 1,
    ∃ hNS : R3CompactCandidate.Properties (velocity scales) (pressure scales) forcing,
      ContDiff ℝ ∞ forcing ∧ ∀ epsilon : ℝ, 0 < epsilon →
      let D := actualData scales hsel forcing hNS a ha0.le ha1
      ∃ c : ℝ, 0 < c ∧
        0 < MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed (gamma a) c)) a ∧
        MagneticCompactFlow.energy (D.magnetic (MagneticCompactSeed.seed (gamma a) c)) a < ENNReal.ofReal epsilon ∧
        Tendsto (MagneticPeriodicNorms.supNorm (D.magnetic (MagneticCompactSeed.seed (gamma a) c)))
          (𝓝[<] 1) atTop := by
  obtain ⟨scales,hsel,ea,eb,ep,forcing,hns,hforce,hrest⟩ := ActualCandidateAssembly.selected_witness
  have hNS : R3CompactCandidate.Properties (velocity scales) (pressure scales)
      (R3CompactCandidate.compactForce forcing) := R3CompactCandidate.of_localized_fields hns
  have hF : ContDiff ℝ ∞ (R3CompactCandidate.compactForce forcing) :=
    (R3CompactCandidate.outerCutoff_smooth.comp contDiff_snd).smul hforce
  let T := lateStart budget threshold geometry scales hsel naturalSolution
  have hT : T < 1 := (lateStart_spec budget threshold geometry scales hsel naturalSolution).1
  let a := (max T 0+1)/2
  have hm : max T 0 < 1 := max_lt hT (by norm_num)
  have ha0 : 0 < a := by dsimp [a]; linarith [le_max_right T 0]
  have ha1 : a < 1 := by dsimp [a]; linarith
  have haT : T < a := by dsimp [a]; linarith [le_max_left T 0]
  exact ⟨scales,hsel,R3CompactCandidate.compactForce forcing,a,ha0,ha1,hNS,hF,
    fun epsilon hepsilon => small_initial_energy_sup_divergence scales hsel _ hNS a ha0.le ha1 haT hepsilon⟩
end NavierStokes.MagneticCompactMain
