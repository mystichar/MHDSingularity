import NavierStokes.MagneticPeriodicNorms

/-! A closed periodic passive-induction main theorem for the same actual
forced viscosity-one Navier–Stokes candidate. -/
noncomputable section
namespace NavierStokes.MagneticPeriodicMain
open Set Filter ProblemStatement MagneticTransport MagneticPeriodicSolution
open MagneticAxisTransfer MagneticAssembledAmplification MagneticCoreAmplification MagneticSimilarityTrajectory
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff ENNReal

abbrev budget := ActualCandidateConstruction.selectedBudget
abbrev threshold := ActualCandidateConstruction.selectedThreshold
abbrev geometry := ActualCandidateConstruction.selectedThreshold_geometry

/-- The natural solution ALREADY selected in the actual nominal profile.
Its h, j, pressure datum, scale, and normalization are those of ActualPrimary. -/
abbrev naturalSolution := nominal.axis.natural.profile.family.natural

abbrev velocity (scales : ℕ → ℕ) := actualPeriodicVelocity budget threshold geometry scales

def pressure (scales : ℕ → ℕ) : PressureField :=
  TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure
    (SolenoidalDiagonal.potentialSum (fun j => (scales j : ℝ)) (PhysicalWaveSum.physicalQ h)
      (ActualCandidateAssembly.pressureStages budget threshold geometry)))

abbrev Selected (scales : ℕ → ℕ) := MixedCandidateWitness.SelectedSchedule h
  (ActualCandidateConstruction.qbig budget threshold)
  (ActualCandidateAssembly.potentialStages budget threshold geometry)
  (ActualCandidateAssembly.directStages budget threshold geometry)
  (ActualCandidateAssembly.pressureStages budget threshold geometry) scales

abbrev gamma := trajectory h (distinguishedEta nominal.axis.small)
abbrev exponent := axialExponent nominal.axis.small

/-- All magnetic conclusions concern one field and one prescribed velocity.
Only separate spatial smoothness, not joint C-infinity, is asserted. -/
structure MagneticConclusions (u : VelocityField) (a Bz0 : ℝ) (B : MagneticField) : Prop where
  classical : ClassicalSolution u B a 1 Bz0
  spatial_smooth : ∀ t ∈ Ico a 1, ContDiff ℝ ∞ (fun x => B (t,x))
  amplification : ∀ t ∈ Ico a 1,
    B (t,gamma t) = (Bz0 * ((1-a)/(1-t)) ^ exponent) • coordinateVector 2
  path_divergence : Bz0 ≠ 0 → Tendsto (fun t => ‖B (t,gamma t)‖) (𝓝[<] 1) atTop
  sup_divergence : Bz0 ≠ 0 → Tendsto (MagneticPeriodicNorms.supNorm B) (𝓝[<] 1) atTop
  slab_bounds : ∀ b ∈ Ico a 1, ∃ C : ℝ, 0 ≤ C ∧ ∃ E : ℝ≥0∞, E < ⊤ ∧
    ∀ t ∈ Icc a b, MagneticPeriodicNorms.supNorm B t ≤ C ∧
      MagneticPeriodicNorms.cellEnergy B t ≤ E ∧ MagneticPeriodicNorms.cellEnergy B t < ⊤

theorem constructed_conclusions (scales : ℕ → ℕ) (hsel : Selected scales) (a : ℝ)
    (ha : lateStart budget threshold geometry scales hsel naturalSolution < a)
    (ha1 : a < 1) (Bz0 : ℝ) :
    ∃ B, MagneticConclusions (velocity scales) a Bz0 B := by
  let D := actualData budget threshold geometry scales hsel a ha1
  let B := D.magnetic Bz0
  have hc : ClassicalSolution (velocity scales) B a 1 Bz0 := D.classicalSolution Bz0
  have hg := (lateStart_spec budget threshold geometry scales hsel naturalSolution).2.1
  have hgc : ContinuousOn gamma (Ico a 1) := hg.path_continuous.mono
    (fun _ ht => ⟨ha.trans_le ht.1,ht.2⟩)
  have hBc : ContinuousOn (fun t => B (t,gamma t)) (Ico a 1) :=
    hc.continuous.comp (continuousOn_id.prodMk hgc) (fun _ ht => ⟨ht,mem_univ _⟩)
  have hBd : ∀ t ∈ Ioo a 1, DifferentiableAt ℝ B (t,gamma t) :=
    fun t ht => (hc.regular t ht _).differentiableAt one_ne_zero
  have hdiv : Bz0 ≠ 0 → Tendsto (fun t => ‖B (t,gamma t)‖) (𝓝[<] 1) atTop :=
    fun hz => periodic_magnetic_norm_tendsto_atTop budget threshold geometry scales hsel naturalSolution
      ha ha1 hz hc.induction hBc hBd (hc.initial _)
  refine ⟨B,hc,D.magnetic_spatial_smooth Bz0,?_,hdiv,?_,?_⟩
  · intro t ht
    exact hg.pure_axial_transport_preterminal ha hc.induction hBc hBd (hc.initial _) ht
  · intro hz
    exact MagneticPeriodicNorms.supNorm_tendsto hc.continuous hc.periodic ha1 (hdiv hz)
  · intro b hb
    have hsub : Icc a b ⊆ Ico a 1 := fun _ ht => ⟨ht.1,ht.2.trans_lt hb.2⟩
    exact MagneticPeriodicNorms.slab_norm_energy_bound
      (hc.continuous.mono (prod_subset_prod_left hsub)) (fun t ht => hc.periodic t (hsub ht))

/-- Closed main theorem: the upstream schedule and natural profile are
instantiated, and NS and induction use the SAME actual periodic velocity.
The velocity and late start are chosen before the magnetic seed. -/
theorem periodic_main : ∃ scales : ℕ → ℕ, Selected scales ∧
    ∃ forcing : VelocityField, ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      CandidateProperties (velocity scales) (pressure scales) forcing ∧
      ContDiff ℝ ∞ forcing ∧
      CandidateConsequences.Consequences (velocity scales) (pressure scales) forcing ∧
      ∀ Bz0 : ℝ, ∃ B : MagneticField, MagneticConclusions (velocity scales) a Bz0 B := by
  obtain ⟨scales,hsel,ea,eb,ep,forcing,hns,hforce,hcons,hrest⟩ := ActualCandidateAssembly.selected_witness
  let T := lateStart budget threshold geometry scales hsel naturalSolution
  have hT : T < 1 := (lateStart_spec budget threshold geometry scales hsel naturalSolution).1
  let a := (max T 0 + 1) / 2
  have hm : max T 0 < 1 := max_lt hT (by norm_num)
  have ha0 : 0 < a := by dsimp [a]; linarith [le_max_right T 0]
  have ha1 : a < 1 := by dsimp [a]; linarith
  have haT : T < a := by dsimp [a]; linarith [le_max_left T 0]
  exact ⟨scales,hsel,forcing,a,ha0,ha1,hns,hforce,hcons,
    constructed_conclusions scales hsel a haT ha1⟩

/-- Arbitrarily small nonzero constant axial seeds for one prescribed NS
velocity and one reference time. There is no Lorentz backreaction. -/
theorem arbitrarily_small_seed : ∃ scales : ℕ → ℕ, ∃ forcing : VelocityField, ∃ a : ℝ,
    0 < a ∧ a < 1 ∧ CandidateProperties (velocity scales) (pressure scales) forcing ∧
    ∀ ε : ℝ, 0 < ε → ∃ Bz0 : ℝ, 0 < Bz0 ∧ Bz0 < ε ∧
      ∃ B : MagneticField, MagneticConclusions (velocity scales) a Bz0 B ∧
        Tendsto (MagneticPeriodicNorms.supNorm B) (𝓝[<] 1) atTop := by
  obtain ⟨scales,_,forcing,a,ha0,ha1,hns,_,_,hB⟩ := periodic_main
  refine ⟨scales,forcing,a,ha0,ha1,hns,?_⟩
  intro ε hε
  obtain ⟨B,hB⟩ := hB (ε/2)
  exact ⟨ε/2,half_pos hε,half_lt_self hε,B,hB,hB.sup_divergence (ne_of_gt (half_pos hε))⟩
end NavierStokes.MagneticPeriodicMain
