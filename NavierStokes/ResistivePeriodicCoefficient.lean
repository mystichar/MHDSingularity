import NavierStokes.ResistiveIdealComparison
import NavierStokes.MagneticPeriodicMain

/-! Actual velocity coefficient bounds on fixed physical-time slabs. No
bound in this file depends on magnetic diffusivity. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Comparison
open Set ProblemStatement MagneticAxisTransfer
open MagneticPeriodicMain (budget threshold geometry Selected)
open scoped ContDiff

/-- Actual selected periodic velocity, with its existing physical clock.
The constants may depend on a,b and the schedule, but contain no eta_m. -/
theorem actual_velocity_bounds (scales : ℕ → ℕ) (hsel : Selected scales)
    {a b : ℝ} (hb : b < 1) :
    ∃ U L : ℝ, 0 ≤ U ∧ 0 ≤ L ∧ ∀ t ∈ Icc a b, ∀ x,
      ‖actualPeriodicVelocity budget threshold geometry scales (t,x)‖ ≤ U ∧
      ‖spatialDerivative (actualPeriodicVelocity budget threshold geometry scales) t x‖ ≤ L := by
  let A := MagneticPeriodicCoefficient.actualOnSlab budget threshold geometry scales hsel a b hb
  refine ⟨‖A.field‖,‖A.derivative.field‖,norm_nonneg _,norm_nonneg _,?_⟩
  intro t ht x
  let s : Icc (0:ℝ) (b-a) := ⟨t-a,sub_nonneg.mpr ht.1,sub_le_sub_right ht.2 a⟩
  have he : (A.field s : Space → Space) = fun y => actualPeriodicVelocity budget threshold geometry scales (t,y) := by
    funext y
    change actualPeriodicVelocity budget threshold geometry scales (a+(t-a),y) = _
    rw [add_sub_cancel]
  constructor
  · rw [← congrFun he x]
    exact ((A.field s).norm_coe_le_norm x).trans (A.field.norm_coe_le_norm s)
  · change ‖fderiv ℝ (fun y => actualPeriodicVelocity budget threshold geometry scales (t,y)) x‖ ≤ _
    rw [← he,← A.derivativeField_eq]
    exact ((A.derivative.field s).norm_coe_le_norm x).trans (A.derivative.field.norm_coe_le_norm s)

/-- A pointwise C1-to-C0 source difference estimate. Completion of a
periodic Ck scale and heat derivative gain are not supplied by this lemma. -/
theorem source_difference_bound {u B I : VelocityField} {t : ℝ} {x : Space} {U L delta : ℝ}
    (hB : ContDiff ℝ ∞ (fun x => B (t,x))) (hI : ContDiff ℝ ∞ (fun x => I (t,x)))
    (hU : ‖u (t,x)‖ ≤ U) (hL : ‖spatialDerivative u t x‖ ≤ L)
    (hfield : ‖(B-I) (t,x)‖ ≤ delta) (hjet : ‖spatialDerivative (B-I) t x‖ ≤ delta) :
    ‖source u B t x-source u I t x‖ ≤ (U+L)*delta := by
  have hd : 0 ≤ delta := (norm_nonneg _).trans hfield
  rw [← source_sub hB hI]
  calc
    _ ≤ ‖spatialDerivative (B-I) t x‖*‖u (t,x)‖ +
        ‖spatialDerivative u t x‖*‖(B-I) (t,x)‖ := source_norm_le _ _ _ _
    _ ≤ delta*U+L*delta := add_le_add
      (mul_le_mul hjet hU (norm_nonneg _) hd)
      (mul_le_mul hL hfield (norm_nonneg _) ((norm_nonneg _).trans hL))
    _ = _ := by ring

/-- Local smoothness of the actual unprojected source. -/
theorem source_smooth {J : Set ℝ} (hJ : IsOpen J) {u B : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (J ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z => source u B z.1 z.2) (J ×ˢ univ) :=
  ((ResidualRegularity.contDiffOn_spatialDerivative (hJ.prod isOpen_univ) hB).clm_apply hu).neg.add
    ((ResidualRegularity.contDiffOn_spatialDerivative (hJ.prod isOpen_univ) hu).clm_apply hB)

/-- Compact-cell bound for the magnetic Laplacian with precisely the
needed time/space continuity premise. Separate slice smoothness is not used
to infer this premise. -/
theorem laplacian_bound_of_joint_continuity {B : MagneticField} {a b : ℝ}
    (hc : ContinuousOn (fun z => spatialLaplacian B z.1 z.2) (Icc a b ×ˢ univ))
    (hp : ∀ t ∈ Icc a b, ∀ x i, spatialLaplacian B t (x+coordinateVector i) = spatialLaplacian B t x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc a b, ∀ x, ‖spatialLaplacian B t x‖ ≤ D :=
  MagneticPeriodicNorms.slab_bound (B := fun z => spatialLaplacian B z.1 z.2) (a := a) (b := b) hc hp
end NavierStokes.ResistiveMagnetic.Comparison
