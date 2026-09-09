import NavierStokes.ResistiveIdealJetBounds
import NavierStokes.ResistivePeriodicComparison

/-! Comparison with the actual constructed periodic ideal witness and the
same prescribed viscosity-one NS velocity. Only the resistive field is
supplied. The comparison constants are chosen before that field and its
magnetic diffusivity. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Comparison
open Set ProblemStatement MagneticPeriodicMain MagneticPeriodicSolution
open scoped ContDiff

/-- Instantiated fixed-slab comparison. Both coefficient bounds have been
proved for the actual fields, through both slab endpoints. -/
theorem actual_ideal_resistive (scales : ℕ → ℕ) (hsel : Selected scales)
    (a Bz0 : ℝ) (ha : a < 1) {b : ℝ} (hab : a < b) (hb : b < 1) :
    let I := (actualData budget threshold geometry scales hsel a ha).magnetic Bz0
    ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧
      (∀ t ∈ Icc a b, ∀ x, ‖spatialDerivative (velocity scales) t x‖ ≤ L) ∧
      (∀ t ∈ Icc a b, ∀ x, ‖spatialLaplacian I t x‖ ≤ D) ∧
      ∀ eta_m : ℝ, 0 ≤ eta_m → ∀ B : MagneticField,
        ContinuousOn B (Icc a b ×ˢ univ) → UnitSpatialPeriodsOn (Icc a b) B →
        (∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t) →
        (∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => B (t,x))) →
        ResistiveInductionOn eta_m (Ioo a b) (velocity scales) B →
        (∀ x, B (a,x) = Bz0 • coordinateVector 2) →
        ∀ t ∈ Icc a b, ∀ x, ‖B (t,x)-I (t,x)‖ ≤ eta_m * constant L D a b := by
  let W := actualData budget threshold geometry scales hsel a ha
  change ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧ _
  obtain ⟨U,L,hU,hL,hu⟩ := actual_velocity_bounds scales hsel (a := a) hb
  obtain ⟨D,hD,hΔ⟩ := W.magnetic_laplacian_bound Bz0 hb
  refine ⟨L,D,hL,hD,(fun t ht x => (hu t ht x).2),hΔ,?_⟩
  intro eta_m heta B hBc hBp hBt hBx hres hi
  have hsub : Icc a b ⊆ Ico a 1 := fun t ht => ⟨ht.1,ht.2.trans_lt hb⟩
  have hsub' : Ioo a b ⊆ Ioo a 1 := fun t ht => ⟨ht.1,ht.2.trans hb⟩
  exact ideal_resistive hab heta hL hD hBc
    ((W.magnetic_continuousOn Bz0).mono (prod_subset_prod_left hsub)) hBp
    (fun t ht => W.magnetic_periodic Bz0 t (hsub ht)) hBt
    (fun t ht x => by
      have hd : DifferentiableAt ℝ (W.magnetic Bz0) (t,x) :=
        (W.magnetic_contDiffAt Bz0 t (hsub' ht) x).differentiableAt one_ne_zero
      have hp : DifferentiableAt ℝ (fun s : ℝ => (s,x)) t :=
        differentiableAt_id.prodMk (differentiableAt_const x)
      exact hd.comp t hp) hBx
    (fun t ht => (W.magnetic_spatial_smooth Bz0 t (hsub ⟨ht.1.le,ht.2.le⟩)).of_le (by norm_num))
    (fun t ht x => (hu t ⟨ht.1.le,ht.2.le⟩ x).2)
    (fun t ht => hΔ t ⟨ht.1.le,ht.2.le⟩) hres
    (fun t ht => W.magnetic_induction Bz0 t (hsub' ht))
    (fun x => (hi x).trans (W.magnetic_initial Bz0 x).symm)

/-- The same assertion with a single nonnegative constant chosen before
diffusivity and the supplied solution. No resistive existence is asserted. -/
theorem actual_comparison_constant (scales : ℕ → ℕ) (hsel : Selected scales)
    (a Bz0 : ℝ) (ha : a < 1) {b : ℝ} (hab : a < b) (hb : b < 1) :
    let I := (actualData budget threshold geometry scales hsel a ha).magnetic Bz0
    ∃ C : ℝ, 0 ≤ C ∧ ∀ eta_m : ℝ, 0 ≤ eta_m → ∀ B : MagneticField,
      ContinuousOn B (Icc a b ×ˢ univ) → UnitSpatialPeriodsOn (Icc a b) B →
      (∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t) →
      (∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => B (t,x))) →
      ResistiveInductionOn eta_m (Ioo a b) (velocity scales) B →
      (∀ x, B (a,x) = Bz0 • coordinateVector 2) →
      ∀ t ∈ Icc a b, ∀ x, ‖B (t,x)-I (t,x)‖ ≤ eta_m * C := by
  obtain ⟨L,D,_,hD,_,_,h⟩ := actual_ideal_resistive scales hsel a Bz0 ha hab hb
  exact ⟨constant L D a b,constant_nonneg hD,h⟩

/-- Uniqueness with the velocity-gradient bound discharged for the same
actual selected velocity; the common initial field may be arbitrary. -/
theorem actual_resistive_unique (scales : ℕ → ℕ) (hsel : Selected scales)
    {a b eta_m : ℝ} {B I : MagneticField} (hab : a < b) (hb : b < 1) (heta : 0 ≤ eta_m)
    (hBc : ContinuousOn B (Icc a b ×ˢ univ)) (hIc : ContinuousOn I (Icc a b ×ˢ univ))
    (hBp : UnitSpatialPeriodsOn (Icc a b) B) (hIp : UnitSpatialPeriodsOn (Icc a b) I)
    (hBt : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t)
    (hIt : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => I (s,x)) t)
    (hBx : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => B (t,x)))
    (hIx : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => I (t,x)))
    (hB : ResistiveInductionOn eta_m (Ioo a b) (velocity scales) B)
    (hI : ResistiveInductionOn eta_m (Ioo a b) (velocity scales) I)
    (hi : ∀ x, B (a,x) = I (a,x)) :
    ∀ t ∈ Icc a b, ∀ x, B (t,x) = I (t,x) := by
  obtain ⟨U,L,_,hL,hu⟩ := actual_velocity_bounds scales hsel (a := a) hb
  exact resistive_unique hab heta hL hBc hIc hBp hIp hBt hIt hBx hIx
    (fun t ht x => (hu t ⟨ht.1.le,ht.2.le⟩ x).2) hB hI hi

/-- Closed NS/ideal data, with a universally quantified supplied resistive
solution. The schedule, physical clock and fluid viscosity are unchanged;
this is a comparison package, not a parabolic existence theorem. -/
theorem periodic_comparison_main : ∃ scales : ℕ → ℕ, ∃ hsel : Selected scales,
    ∃ forcing : VelocityField, ∃ a : ℝ, ∃ ha : a < 1,
      0 < a ∧ CandidateProperties (velocity scales) (pressure scales) forcing ∧
      ContDiff ℝ ∞ forcing ∧ CandidateConsequences.Consequences (velocity scales) (pressure scales) forcing ∧
      ∀ Bz0 : ℝ,
        let I := (actualData budget threshold geometry scales hsel a ha).magnetic Bz0
        ClassicalSolution (velocity scales) I a 1 Bz0 ∧
        (∀ t ∈ Ico a 1, ContDiff ℝ ∞ (fun x => I (t,x))) ∧
        ∀ b : ℝ, a < b → b < 1 →
          ContinuousOn (fun z => spatialLaplacian I z.1 z.2) (Icc a b ×ˢ univ) ∧
          ∃ C : ℝ, 0 ≤ C ∧ ∀ eta_m : ℝ, 0 ≤ eta_m → ∀ B : MagneticField,
            ContinuousOn B (Icc a b ×ˢ univ) → UnitSpatialPeriodsOn (Icc a b) B →
            (∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t) →
            (∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => B (t,x))) →
            ResistiveInductionOn eta_m (Ioo a b) (velocity scales) B →
            (∀ x, B (a,x) = Bz0 • coordinateVector 2) →
            ∀ t ∈ Icc a b, ∀ x, ‖B (t,x)-I (t,x)‖ ≤ eta_m * C := by
  obtain ⟨scales,hsel,forcing,a,ha0,ha1,hns,hforce,hcons,_⟩ := MagneticPeriodicMain.periodic_main
  refine ⟨scales,hsel,forcing,a,ha1,ha0,hns,hforce,hcons,?_⟩
  intro Bz0
  let W := actualData budget threshold geometry scales hsel a ha1
  exact ⟨W.classicalSolution Bz0,W.magnetic_spatial_smooth Bz0,
    fun b hab hb => ⟨W.magnetic_laplacian_continuousOn Bz0 hb,
      actual_comparison_constant scales hsel a Bz0 ha1 hab hb⟩⟩

end NavierStokes.ResistiveMagnetic.Comparison
