import NavierStokes.MagneticCompactSeed
import NavierStokes.MagneticCompactSolution

/-! Closed whole-space passive-induction theorem for the existing actual
compact NS velocity. Neither the velocity nor its localization is changed. -/
noncomputable section
namespace NavierStokes.MagneticCompactMain
open Set Filter ProblemStatement MagneticTransport MagneticCompactSolution
open MagneticAxisTransfer MagneticAssembledAmplification MagneticCoreAmplification
open CorrectionInitialization.ActualPrimary
open MagneticPeriodicMain (budget threshold geometry Selected naturalSolution gamma exponent)
open scoped Topology ContDiff ENNReal

abbrev velocity (scales : ℕ → ℕ) := actualCompactVelocity budget threshold geometry scales

def pressure (scales : ℕ → ℕ) : PressureField :=
  R3CompactCandidate.pressure (SolenoidalDiagonal.potentialSum (fun j => (scales j : ℝ))
    (PhysicalWaveSum.physicalQ h) (ActualCandidateAssembly.pressureStages budget threshold geometry))

theorem velocity_supported (scales : ℕ → ℕ) (t : ℝ) :
    tsupport (fun x => velocity scales (t,x)) ⊆ SpatialLocalization.supportCylinder := by
  apply closure_minimal _ SpatialLocalization.isClosed_supportCylinder
  intro x hx
  by_contra hn
  exact hx (R3CompactCandidate.velocity_supported _ _ t x hn)

/-- The actual compact velocity's coefficient data are supplied by its
existing support and selected-schedule smoothness, with no new cutoff. -/
def actualData (scales : ℕ → ℕ) (hsel : Selected scales)
    (forcing : VelocityField) (hNS : R3CompactCandidate.Properties (velocity scales) (pressure scales) forcing)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) : Data where
  velocity := velocity scales
  a := a
  ha := ha1
  smooth := (assembled_velocities_smooth budget threshold geometry scales hsel).2
  supportSet := SpatialLocalization.supportCylinder
  support_compact := SpatialLocalization.isCompact_supportCylinder
  supported := fun t _ => velocity_supported scales t
  divergence := fun t ht x => hNS.divergence_free t ⟨ha0.trans ht.1,ht.2⟩ x

structure MagneticConclusions (u : VelocityField) (a Bz0 : ℝ) (B : MagneticField) : Prop where
  initial : ∀ x, B (a,x) = MagneticCompactSeed.seed (gamma a) Bz0 x
  initial_local : (fun x => B (a,x)) =ᶠ[𝓝 (gamma a)] (fun _ => Bz0 • coordinateVector 2)
  continuous : ContinuousOn B (Ico a 1 ×ˢ univ)
  regular : ∀ t ∈ Ioo a 1, ∀ x, ContDiffAt ℝ 1 B (t,x)
  spatial_smooth : ∀ t ∈ Ico a 1, ContDiff ℝ ∞ (fun x => B (t,x))
  induction : IdealInductionOn (Ioo a 1) u B
  divergence : ∀ t ∈ Ico a 1, ∀ x, spatialDivergence B t x = 0
  support : ∀ b ∈ Ico a 1, ∃ K : Set Space, IsCompact K ∧
    ∀ t ∈ Icc a b, tsupport (fun x => B (t,x)) ⊆ K
  slab_bounds : ∀ b ∈ Ico a 1, ∃ C : ℝ, 0 ≤ C ∧ ∃ E : ℝ≥0∞, E < ⊤ ∧ ∀ t ∈ Icc a b,
    (∀ x, ‖B (t,x)‖ ≤ C) ∧ MagneticPeriodicNorms.supNorm B t ≤ C ∧
      MagneticCompactFlow.energy B t ≤ E ∧ MagneticCompactFlow.energy B t < ⊤
  amplification : ∀ t ∈ Ico a 1,
    B (t,gamma t) = (Bz0 * ((1-a)/(1-t)) ^ exponent) • coordinateVector 2
  path_divergence : Bz0 ≠ 0 → Tendsto (fun t => ‖B (t,gamma t)‖) (𝓝[<] 1) atTop
  sup_divergence : Bz0 ≠ 0 → Tendsto (MagneticPeriodicNorms.supNorm B) (𝓝[<] 1) atTop

theorem constructed_conclusions (scales : ℕ → ℕ) (hsel : Selected scales)
    (forcing : VelocityField) (hNS : R3CompactCandidate.Properties (velocity scales) (pressure scales) forcing)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (ha : lateStart budget threshold geometry scales hsel naturalSolution < a) (Bz0 : ℝ) :
    ∃ B, MagneticConclusions (velocity scales) a Bz0 B := by
  let D := actualData scales hsel forcing hNS a ha0 ha1
  let W := MagneticCompactSeed.seed (gamma a) Bz0
  have hW : ContDiff ℝ ∞ W := MagneticCompactSeed.seed_smooth _ _
  have hsupp : HasCompactSupport W := MagneticCompactSeed.seed_compact _ _
  have hdivW : ∀ x, ∑ i : Fin 3, (fderiv ℝ W x (coordinateVector i)) i = 0 :=
    MagneticCompactSeed.seed_divergence _ _
  let B := D.magnetic W
  have hc := D.magnetic_continuousOn W hW.continuous
  have hind := D.magnetic_induction W hW
  have hreg := D.magnetic_contDiffAt W hW
  have hinit : ∀ x, B (a,x) = W x := D.magnetic_initial W
  have hseed : B (a,gamma a) = Bz0 • coordinateVector 2 :=
    (hinit _).trans (MagneticCompactSeed.seed_at_center _ _)
  have hg := (lateStart_spec budget threshold geometry scales hsel naturalSolution).2.2
  have hgc : ContinuousOn gamma (Ico a 1) := hg.path_continuous.mono
    (fun _ ht => ⟨ha.trans_le ht.1,ht.2⟩)
  have hBc : ContinuousOn (fun t => B (t,gamma t)) (Ico a 1) :=
    hc.comp (continuousOn_id.prodMk hgc) (fun _ ht => ⟨ht,mem_univ _⟩)
  have hBd : ∀ t ∈ Ioo a 1, DifferentiableAt ℝ B (t,gamma t) :=
    fun t ht => (hreg t ht _).differentiableAt one_ne_zero
  have hdiv : Bz0 ≠ 0 → Tendsto (fun t => ‖B (t,gamma t)‖) (𝓝[<] 1) atTop :=
    fun hz => compact_magnetic_norm_tendsto_atTop budget threshold geometry scales hsel naturalSolution
      ha ha1 hz hind hBc hBd hseed
  refine ⟨B,hinit,?_,hc,hreg,D.magnetic_spatial_smooth W hW,hind,
    D.magnetic_divergence_free W hW hdivW,D.uniform_support W hsupp,
    D.slab_bounds W hW.continuous hsupp,?_,hdiv,?_⟩
  · have he : (fun x => B (a,x)) =ᶠ[𝓝 (gamma a)] W := Eventually.of_forall hinit
    exact he.trans (MagneticCompactSeed.seed_local_constant _ _)
  · intro t ht
    exact hg.pure_axial_transport_preterminal ha hind hBc hBd hseed ht
  · intro hz
    apply tendsto_atTop_mono' _ _ (hdiv hz)
    filter_upwards [Ioo_mem_nhdsLT ha1] with t ht
    obtain ⟨C,hC,E,hE,hbound⟩ := D.slab_bounds W hW.continuous hsupp t ⟨ht.1.le,ht.2⟩
    exact (MagneticPeriodicNorms.supNorm_bounds hC (hbound t ⟨ht.1.le,le_rfl⟩).1).2.2 (gamma t)

/-- Closed whole-space theorem: same actual NS velocity, pressure and force,
with one transported compact seed for every amplitude. No magnetic feedback. -/
theorem whole_space_main : ∃ scales : ℕ → ℕ, Selected scales ∧
    ∃ forcing : VelocityField, ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      R3CompactCandidate.Properties (velocity scales) (pressure scales) forcing ∧
      ContDiff ℝ ∞ forcing ∧
      ∀ Bz0 : ℝ, ∃ B : MagneticField, MagneticConclusions (velocity scales) a Bz0 B := by
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
    constructed_conclusions scales hsel _ hNS a ha0.le ha1 haT⟩
end NavierStokes.MagneticCompactMain
