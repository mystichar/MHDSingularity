import NavierStokes.ResistiveMagneticRegions
import NavierStokes.ResistiveDivergencePreservation
import NavierStokes.MagneticPeriodicMain
import NavierStokes.MagneticCompactMain
import NavierStokes.ResistiveMagneticL2Energy

/-! The same actual selected-schedule velocities and physical clock as
Paper I. The resistive PDE solution and its magnetic curvature are not
supplied by the velocity construction. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set Filter ProblemStatement MagneticAxisTransfer MagneticAssembledAmplification
open MagneticPeriodicMain (budget threshold geometry Selected naturalSolution gamma exponent)
open scoped ContDiff Topology

/-- Both assembled candidates retain K/(1-t) axial stretching. The Laplacian
is an additional independent term even at an instant with a pure axial field. -/
theorem actual_axial_material_derivative (scales : ℕ → ℕ) (hsel : Selected scales)
    (u : VelocityField)
    (hu : u = actualPeriodicVelocity budget threshold geometry scales ∨
      u = actualCompactVelocity budget threshold geometry scales)
    (eta_m : ℝ) (B : MagneticField) {t b : ℝ}
    (ht : t ∈ Ioo (lateStart budget threshold geometry scales hsel naturalSolution) 1)
    (hB : DifferentiableAt ℝ B (t,gamma t))
    (hind : ResistiveInductionOn eta_m
      (Ioo (lateStart budget threshold geometry scales hsel naturalSolution) 1) u B)
    (haxial : B (t,gamma t) = b • coordinateVector 2) :
    HasDerivAt (fun s => B (s,gamma s))
      ((exponent/(1-t)*b) • coordinateVector 2 + eta_m • spatialLaplacian B t (gamma t)) t := by
  have hf : LateAxialFlow u gamma exponent (lateStart budget threshold geometry scales hsel naturalSolution) := by
    rcases hu with rfl | rfl
    · exact (lateStart_spec budget threshold geometry scales hsel naturalSolution).2.1
    · exact (lateStart_spec budget threshold geometry scales hsel naturalSolution).2.2
  have hd := material_derivative hB (hf.trajectory_derivative t ht) hind ht
  rw [haxial,map_smul,hf.axial_column t ht,smul_smul] at hd
  simpa only [mul_comm] using hd

/-- q is the existing pathQ. No viscosity/time conversion is hidden in the
comparison of stretching and diffusion in the distinguished region. -/
theorem stretching_pathQ {eta t K : ℝ} (heta : eta^2 < 1) :
    K/(1-t) = K/(NaturalAxisData.d eta * MagneticSimilarityTrajectory.pathQ eta t) := by
  have hd : NaturalAxisData.d eta ≠ 0 := by
    unfold NaturalAxisData.d
    linarith
  rw [MagneticSimilarityTrajectory.pathQ,mul_div_cancel₀ _ hd]

/-- Energy balance for the actual periodic velocity and a supplied resistive
solution. No magnetic solution is supplied by the ideal construction. -/
theorem actual_periodic_energy (scales : ℕ → ℕ) (hsel : Selected scales)
    {eta_m a b t : ℝ} {B : MagneticField}
    (hB : ContDiffOn ℝ ∞ B (PeriodicUniqueness.slab a b))
    (hpB : UnitSpatialPeriodsOn (Icc a b) B) (hb : b < 1)
    (hind : ResistiveInductionOn eta_m (Ioo a b)
      (actualPeriodicVelocity budget threshold geometry scales) B)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (periodicEnergy B)
      (PeriodicIntegration.cubeIntegral (fun x => inner ℝ (B (t,x))
        (spatialDerivative (actualPeriodicVelocity budget threshold geometry scales) t x (B (t,x)))) -
        ohmicDissipation eta_m B t) t := by
  have hu := (assembled_velocities_smooth budget threshold geometry scales hsel).1
  apply periodic_energy_hasDerivAt
    (hu.mono (fun z hz => ⟨hz.1.2.trans_lt hb,hz.2⟩)) hB _ hpB
      (fun s hs x => MagneticPeriodicCoefficient.actual_divergence budget threshold geometry scales hsel s (hs.2.trans hb) x) hind ht
  intro s hs x i
  exact MagneticPeriodicCoefficient.actual_periodic budget threshold geometry scales s (hs.2.trans_lt hb) x i
/-- Instantiation for the actual assembled periodic velocity. Only B's
regularity, periodicity, induction equation, and initial solenoidality are
supplied; all velocity smoothness/periodicity/divergence premises are proved. -/
theorem actual_periodic_divergence_preserved (scales : ℕ → ℕ) (hsel : Selected scales)
    {eta_m a b : ℝ} {B : MagneticField} (heta : 0 ≤ eta_m) (hab : a ≤ b) (hb : b < 1)
    (hB : ContDiffOn ℝ ∞ B (Iio (1:ℝ) ×ˢ univ))
    (hpB : UnitSpatialPeriodsOn (Iio (1:ℝ)) B)
    (hind : ResistiveInductionOn eta_m (Ioo a b)
      (actualPeriodicVelocity budget threshold geometry scales) B)
    (hinit : ∀ x, spatialDivergence B a x = 0) :
    ∀ t ∈ Icc a b, ∀ x, spatialDivergence B t x = 0 :=
  periodic_divergence_preserved isOpen_Iio heta hab (fun _ ht => ht.2.trans_lt hb)
    (assembled_velocities_smooth budget threshold geometry scales hsel).1 hB
    (MagneticPeriodicCoefficient.actual_periodic budget threshold geometry scales) hpB
    (MagneticPeriodicCoefficient.actual_divergence budget threshold geometry scales hsel) hind hinit
/-- Whole-space energy for the same actual compact NS velocity. All velocity
support and smoothness requirements are discharged; hNS is tied to its exact
pressure and forcing, as in the existing compact main theorem. -/
theorem actual_compact_energy_l2 (scales : ℕ → ℕ) (hsel : Selected scales)
    (forcing : VelocityField)
    (hNS : R3CompactCandidate.Properties (MagneticCompactMain.velocity scales)
      (MagneticCompactMain.pressure scales) forcing)
    {eta_m t : ℝ} {B : MagneticField} (ht : t ∈ Ico (0:ℝ) 1)
    (A : ℝ → EulerLpTranslation.SmoothL2Field Space) (C : EulerLpTranslation.SmoothL2Field Space)
    (hA : ∀ s, (fun x => B (s,x)) = (A s).field)
    (hC : C.field = fun x => temporalDerivative B t x)
    (hd : HasDerivAt (fun s => (A s).toLp) C.toLp t)
    (hind : ResistiveInductionOn eta_m (Ico (0:ℝ) 1) (MagneticCompactMain.velocity scales) B) :
    HasDerivAt (wholeEnergy B)
      ((∫ x, inner ℝ (B (t,x)) (spatialDerivative (MagneticCompactMain.velocity scales) t x (B (t,x)))) -
        wholeOhmicDissipation eta_m B t) t := by
  have hu := (assembled_velocities_smooth budget threshold geometry scales hsel).2
  have hs : ContDiff ℝ ∞ (fun x => MagneticCompactMain.velocity scales (t,x)) :=
    hu.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht.2,mem_univ x⟩)
  exact whole_energy_hasDerivAt_l2 A C hA hC hd hs
    (SpatialLocalization.isCompact_supportCylinder.of_isClosed_subset (isClosed_tsupport _)
      (MagneticCompactMain.velocity_supported scales t))
    (hNS.divergence_free t ht) (hind t ht)
end NavierStokes.ResistiveMagnetic
