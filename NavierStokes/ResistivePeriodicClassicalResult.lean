import NavierStokes.ResistivePeriodicDivergence

/-! Exported classical predicates for the actual constant-seed family.
All fields below are conclusions proved for the existing mild paths. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
open Set ProblemStatement PeriodicGaussian PeriodicMild PeriodicTranslation
open MagneticPeriodicMain (budget threshold geometry Selected velocity)
open scoped ContDiff

/-- A forward classical solution: continuity includes the initial time;
time derivatives and the PDE are required only on the open interval. -/
structure ClassicalOn (eta_m : ℝ) (u : VelocityField) (B : MagneticField)
    (a b : ℝ) (c : Space) : Prop where
  continuous : ContinuousOn B (Ico a b ×ˢ univ)
  periodic : UnitSpatialPeriodsOn (Ico a b) B
  time_differentiable : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t
  spatial_C2 : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => B (t,x))
  induction : ResistiveInductionOn eta_m (Ioo a b) u B
  initial : ∀ x, B (a,x) = c

/-- Every positive diffusivity has one actual classical field on [a,1).
The seed may be any constant vector. -/
theorem family_classical (scales : ℕ → ℕ) (hsel : Selected scales)
    (a : ℝ) (ha : a < 1) (c : Space) (eta_m : ℝ) (heta : 0 < eta_m) :
    ClassicalOn eta_m (velocity scales) (family scales hsel a ha c eta_m) a 1 c := by
  rw [family_positive scales hsel a ha c heta]
  exact ⟨field_continuousOn scales hsel a ha eta_m heta _,
    field_periodic scales hsel a ha eta_m heta _,
    field_constant_time_differentiable scales hsel a ha eta_m heta c,
    fun t ht => (field_constant_spatial_smooth scales hsel a ha eta_m heta c t
      ⟨ht.1.le,ht.2⟩).of_le (by simp),
    field_constant_induction scales hsel a ha eta_m heta c,
    field_initial scales hsel a ha eta_m heta _⟩

/-- Closed-slab classical regularity and initial data of the same actualPath.
Divergence freedom is proved, rather than a construction hypothesis. -/
theorem actual_constant_classical (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space) :
    let B := slabField scales hsel a eta_m heta (c1Constant c) b hab hb
    ContinuousOn B (Icc a b ×ˢ univ) ∧ UnitSpatialPeriodsOn (Icc a b) B ∧
      (∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t) ∧
      (∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => B (t,x))) ∧
      ResistiveInductionOn eta_m (Ioo a b) (velocity scales) B ∧
      (∀ x, B (a,x) = c) ∧ (∀ t ∈ Icc a b, ∀ x, spatialDivergence B t x = 0) := by
  exact ⟨(physicalField_continuous _ _ _ _).continuousOn,
    physicalField_periodic _ _ _ _ _,
    actual_constant_time_differentiable scales hsel a b hab hb eta_m heta c,
    fun t _ => actual_constant_spatial_smooth scales hsel a b hab hb eta_m heta c t,
    actual_constant_induction scales hsel a b hab hb eta_m heta c,
    physicalField_initial (actual_mild scales hsel a b hab hb eta_m heta (c1Constant c)),
    actual_constant_divergence_free scales hsel a b hab hb eta_m heta c⟩

/-- All spatial jets are jointly continuous through both physical slab
endpoints. This is separate from any assertion of joint spacetime C-infinity. -/
theorem actual_constant_spatial_jet_continuous (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space) (n : ℕ) :
    Continuous (fun p : SpaceTime => iteratedFDeriv ℝ n
      (fun x => slabField scales hsel a eta_m heta (c1Constant c) b hab hb (p.1,x)) p.2) := by
  have hc := spatial_jet_continuous _
    (actual_constant_translation_contDiff scales hsel a b hab hb eta_m heta c) n
  have hp : Continuous (fun p : SpaceTime => projIcc 0 (b-a) (sub_nonneg.mpr hab.le) (p.1-a)) :=
    continuous_projIcc.comp (continuous_fst.sub continuous_const)
  exact hc.comp (hp.prodMk continuous_snd)

end NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
