import NavierStokes.ResistivePeriodicClassicalResult
import NavierStokes.ResistiveActualClassicalComparison
import NavierStokes.ResistiveFiniteGain

/-! Finite gains for the one constructed positive-diffusivity family.
This is a fixed-slab vanishing-diffusivity consequence, not a terminal
claim for any one positive diffusivity. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
open Set Filter ProblemStatement MagneticPeriodicMain MagneticPeriodicSolution
open MagneticAxisTransfer MagneticAssembledAmplification MagneticCoreAmplification
open scoped Topology ContDiff

/-- The actual ideal witness used by actual_family_comparison has Paper I's
exact path norm. No representation is assumed for an existential witness. -/
theorem actual_ideal_path_norm (scales : ℕ → ℕ) (hsel : Selected scales)
    (a Bz0 : ℝ) (ha : a < 1)
    (hlate : lateStart budget threshold geometry scales hsel naturalSolution < a)
    (t : ℝ) (ht : t ∈ Ico a 1) :
    ‖(actualData budget threshold geometry scales hsel a ha).magnetic Bz0 (t,gamma t)‖ =
      |Bz0| * ((1-a)/(1-t)) ^ exponent := by
  let D := actualData budget threshold geometry scales hsel a ha
  have hc := D.classicalSolution Bz0
  have hg := (lateStart_spec budget threshold geometry scales hsel naturalSolution).2.1
  have hgc : ContinuousOn gamma (Ico a 1) := hg.path_continuous.mono
    (fun _ hs => ⟨hlate.trans_le hs.1,hs.2⟩)
  have hBc : ContinuousOn (fun s => D.magnetic Bz0 (s,gamma s)) (Ico a 1) :=
    hc.continuous.comp (continuousOn_id.prodMk hgc) (fun _ hs => ⟨hs,mem_univ _⟩)
  have hBd : ∀ s ∈ Ioo a 1, DifferentiableAt ℝ (D.magnetic Bz0) (s,gamma s) :=
    fun s hs => (hc.regular s hs _).differentiableAt one_ne_zero
  have he := hg.pure_axial_transport_preterminal hlate hc.induction hBc hBd (hc.initial _) ht
  change ‖D.magnetic Bz0 (t,gamma t)‖ = _
  rw [he]
  simp only [norm_smul,coordinateVector,PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs,abs_mul]
  rw [abs_of_pos (Real.rpow_pos_of_pos (div_pos (sub_pos.mpr ha) (sub_pos.mpr ht.2)) exponent)]

/-- The velocity, reference time, seed, and entire diffusivity family are
fixed before the gain target. No axial invariance of the resistive field
is used. The threshold is the existing comparison-based sufficient one. -/
theorem actual_family_finite_gain (scales : ℕ → ℕ) (hsel : Selected scales)
    (a Bz0 : ℝ) (ha : a < 1) (hB : Bz0 ≠ 0)
    (hlate : lateStart budget threshold geometry scales hsel naturalSolution < a) :
    ∀ G > 1, ∃ t ∈ Ioo a 1, ∃ eta_G > 0, ∀ eta_m ∈ Ioo 0 eta_G,
      G*|Bz0| ≤ ‖family scales hsel a ha (Bz0 • coordinateVector 2) eta_m (t,gamma t)‖ := by
  apply Comparison.family_finite_gain ha
    (axialExponent_pos CorrectionInitialization.ActualPrimary.nominal.axis.small) hB
    ((actualData budget threshold geometry scales hsel a ha).magnetic Bz0)
  · exact actual_ideal_path_norm scales hsel a Bz0 ha hlate
  · intro b hb
    exact actual_family_comparison scales hsel a Bz0 ha hb.1 hb.2

/-- Closed passive resistive theorem with a fixed unit axial seed. All
upstream NS witnesses are instantiated from the compatible selected
construction. Each positive diffusivity has one preterminal field. -/
theorem periodic_classical_finite_gain : ∃ scales : ℕ → ℕ, Selected scales ∧
    ∃ forcing : VelocityField, ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      CandidateProperties (velocity scales) (pressure scales) forcing ∧
      ContDiff ℝ ∞ forcing ∧
      CandidateConsequences.Consequences (velocity scales) (pressure scales) forcing ∧
      ∃ family : ℝ → MagneticField,
        (∀ eta_m > 0, ClassicalOn eta_m (velocity scales) (family eta_m) a 1 (coordinateVector 2) ∧
          (∀ t ∈ Ico a 1, ContDiff ℝ ∞ (fun x => family eta_m (t,x))) ∧
          (∀ t ∈ Ico a 1, ∀ x, spatialDivergence (family eta_m) t x = 0)) ∧
        (∀ G > 1, ∃ t ∈ Ioo a 1, ∃ eta_G > 0, ∀ eta_m ∈ Ioo 0 eta_G,
          G ≤ ‖family eta_m (t,gamma t)‖) := by
  obtain ⟨scales,hsel,ea,eb,ep,forcing,hns,hforce,hcons,hrest⟩ := ActualCandidateAssembly.selected_witness
  let T := lateStart budget threshold geometry scales hsel naturalSolution
  have hT : T < 1 := (lateStart_spec budget threshold geometry scales hsel naturalSolution).1
  let a := (max T 0 + 1)/2
  have hm : max T 0 < 1 := max_lt hT (by norm_num)
  have ha0 : 0 < a := by dsimp [a]; linarith [le_max_right T 0]
  have ha1 : a < 1 := by dsimp [a]; linarith
  have haT : T < a := by dsimp [a]; linarith [le_max_left T 0]
  refine ⟨scales,hsel,forcing,a,ha0,ha1,hns,hforce,hcons,
    family scales hsel a ha1 (coordinateVector 2),?_,?_⟩
  · intro eta_m heta
    refine ⟨family_classical scales hsel a ha1 _ eta_m heta,?_,
      family_divergence_free scales hsel a ha1 _ eta_m heta⟩
    rw [family_positive scales hsel a ha1 _ heta]
    exact field_constant_spatial_smooth scales hsel a ha1 eta_m heta _
  · simpa only [one_smul,abs_one,mul_one] using
      actual_family_finite_gain scales hsel a 1 ha1 one_ne_zero haT

end NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
