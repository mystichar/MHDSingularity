import NavierStokes.ResistivePeriodicClassicalGlue
import NavierStokes.ResistiveActualComparison

/-! Actual comparison for one fixed family of constructed constant-seed
fields. The comparison constant is independent of magnetic diffusivity.
No terminal estimate at a fixed positive diffusivity is asserted. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
open Set ProblemStatement PeriodicGaussian MagneticPeriodicMain
open MagneticPeriodicSolution
open scoped ContDiff

theorem actual_family_comparison (scales : ℕ → ℕ) (hsel : Selected scales)
    (a Bz0 : ℝ) (ha : a < 1) {b : ℝ} (hab : a < b) (hb : b < 1) :
    let I := (actualData budget threshold geometry scales hsel a ha).magnetic Bz0
    ∃ C : ℝ, 0 ≤ C ∧ ∀ eta_m : ℝ, 0 < eta_m →
      ∀ t ∈ Icc a b, ∀ x,
        ‖family scales hsel a ha (Bz0 • coordinateVector 2) eta_m (t,x) - I (t,x)‖ ≤ eta_m * C := by
  obtain ⟨C,hC,h⟩ := Comparison.actual_comparison_constant scales hsel a Bz0 ha hab hb
  refine ⟨C,hC,?_⟩
  intro eta_m heta
  rw [family_positive scales hsel a ha _ heta]
  have hsub : Icc a b ⊆ Ico a 1 := fun t ht => ⟨ht.1,ht.2.trans_lt hb⟩
  have hsub' : Ioo a b ⊆ Ioo a 1 := fun t ht => ⟨ht.1,ht.2.trans hb⟩
  apply h eta_m heta.le
  · exact (field_continuousOn scales hsel a ha eta_m heta _).mono (prod_subset_prod_left hsub)
  · exact fun t ht => field_periodic scales hsel a ha eta_m heta _ t (hsub ht)
  · exact fun t ht x => field_constant_time_differentiable scales hsel a ha eta_m heta _ t (hsub' ht) x
  · exact fun t ht => (field_constant_spatial_smooth scales hsel a ha eta_m heta _ t
      (hsub ⟨ht.1.le,ht.2.le⟩)).of_le (by simp)
  · exact fun t ht => field_constant_induction scales hsel a ha eta_m heta _ t (hsub' ht)
  · exact field_initial scales hsel a ha eta_m heta _

end NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
