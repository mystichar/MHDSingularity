import NavierStokes.ResistivePeriodicMild
import NavierStokes.ResistivePeriodicSource

/-! Finite-slab mild induction for Paper I's same selected periodic velocity.
The exported field is jointly continuous and spatially C1. Time derivatives,
the classical induction PDE, divergence preservation, and gluing are not
asserted here. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicMild
open Set MeasureTheory ProblemStatement PeriodicGaussian PeriodicSource
open MagneticPeriodicMain (budget threshold geometry Selected)
open MagneticAxisTransfer
open scoped Topology BoundedContinuousFunction

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

/-- Clamping is only a continuous extension outside the finite slab. The
physical-time mild equation is exported at a+tau for tau in [0,T]. -/
def physicalField (a T : ℝ) (hT : 0 ≤ T) (z : Path T) : MagneticField :=
  fun p => (c1Value (z (projIcc 0 T hT (p.1-a)))).val p.2

theorem physicalField_continuous (a T : ℝ) (hT : 0 ≤ T) (z : Path T) :
    Continuous (physicalField a T hT z) := by
  have hp : Continuous (fun p : SpaceTime => projIcc 0 T hT (p.1-a)) :=
    continuous_projIcc.comp (continuous_fst.sub continuous_const)
  have hv : Continuous (fun p : SpaceTime => (c1Value (z (projIcc 0 T hT (p.1-a)))).val) :=
    continuous_subtype_val.comp (c1Value.continuous.comp (z.continuous.comp hp))
  have he : Continuous (fun p : (Space →ᵇ Space) × Space => p.1 p.2) := continuous_eval
  exact he.comp (hv.prodMk continuous_snd)

theorem physicalField_periodic (a T : ℝ) (hT : 0 ≤ T) (z : Path T) (J : Set ℝ) :
    UnitSpatialPeriodsOn J (physicalField a T hT z) :=
  fun t _ x i => (c1Value (z (projIcc 0 T hT (t-a)))).property x i

theorem physicalField_spatialC1 (a T : ℝ) (hT : 0 ≤ T) (z : Path T) (t : ℝ) :
    ContDiff ℝ 1 (fun x => physicalField a T hT z (t,x)) :=
  c1_contDiff (z (projIcc 0 T hT (t-a)))

theorem physicalField_spatialDerivative (a T : ℝ) (hT : 0 ≤ T) (z : Path T) (t : ℝ) (x : Space) :
    spatialDerivative (physicalField a T hT z) t x =
      (c1Derivative (z (projIcc 0 T hT (t-a)))).val x :=
  c1_fderiv (z (projIcc 0 T hT (t-a))) x

theorem physicalField_derivative_continuous (a T : ℝ) (hT : 0 ≤ T) (z : Path T) :
    Continuous (fun p : SpaceTime => spatialDerivative (physicalField a T hT z) p.1 p.2) := by
  simp_rw [physicalField_spatialDerivative]
  have hp : Continuous (fun p : SpaceTime => projIcc 0 T hT (p.1-a)) :=
    continuous_projIcc.comp (continuous_fst.sub continuous_const)
  have hv : Continuous (fun p : SpaceTime => (c1Derivative (z (projIcc 0 T hT (p.1-a)))).val) :=
    continuous_subtype_val.comp (c1Derivative.continuous.comp (z.continuous.comp hp))
  have he : Continuous (fun p : (Space →ᵇ (Space →L[ℝ] Space)) × Space => p.1 p.2) := continuous_eval
  exact he.comp (hv.prodMk continuous_snd)

theorem physicalField_at_elapsed (a T : ℝ) (hT : 0 ≤ T) (z : Path T)
    (t : Icc (0 : ℝ) T) (x : Space) :
    physicalField a T hT z (a+t,x) = (c1Value (z t)).val x := by
  change (c1Value (z (projIcc 0 T hT (a+t.val-a)))).val x = _
  rw [add_sub_cancel_left, projIcc_val]

theorem physicalField_initial {a T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z) (x : Space) :
    physicalField a T hT z (a,x) = (c1Value B_a).val x := by
  change (c1Value (z (projIcc 0 T hT (a-a)))).val x = _
  rw [sub_self, projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩), mild_initial hz]

theorem heatKernel_value (eta_m : ℝ) (heta : 0 < eta_m) {r : ℝ} (hr : 0 < r) (g : PeriodicField) :
    c1Inclusion (heatKernel eta_m heta r g) = heat eta_m r g := by
  rw [heatKernel, dite_eq_left hr]
  exact heatGain_value eta_m r heta hr g

/-- The physical-time field equation uses the original heat operator.
Forgetting heatKernel agrees with it at positive integration times; the
different convention at r=0 does not change the Bochner integral. -/
theorem physicalField_mild_equation {a T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z) (t : Icc (0 : ℝ) T) (x : Space) :
    physicalField a T hT z (a+t,x) = (heat eta_m t.val (c1Inclusion B_a)).val x +
      ∫ r in (0 : ℝ)..t.val, (heat eta_m r
        (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r))))).val x := by
  let E : PeriodicC1 →L[ℝ] Space := (valueEval x).comp c1Inclusion
  have he := congrArg E (mild_equation hz t)
  rw [map_add, ← E.intervalIntegral_comp_comm (mild_integrable T hT eta_m heta S z t)] at he
  rw [physicalField_at_elapsed]
  change (c1Value (z t)).val x = (heat eta_m t.val (c1Inclusion B_a)).val x + _
  have hfree : E (heatC1 eta_m t.val B_a) = (heat eta_m t.val (c1Inclusion B_a)).val x := by
    change (c1Inclusion (heatC1 eta_m t.val B_a)).val x = _
    rw [heatC1_value]
  have hint : (∫ r in (0 : ℝ)..t.val, E (heatKernel eta_m heta r
      (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r)))))) =
      ∫ r in (0 : ℝ)..t.val, (heat eta_m r
        (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r))))).val x := by
    rw [intervalIntegral.integral_of_le t.property.1, intervalIntegral.integral_of_le t.property.1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    change (c1Inclusion (heatKernel eta_m heta r _)).val x = _
    exact congrArg (fun g : PeriodicField => g.val x) (heatKernel_value eta_m heta hr.1 _)
  exact he.trans (congrArg₂ (fun v w : Space => v+w) hfree hint)

theorem source_eq_of_slice_eq (u : VelocityField) (B C : MagneticField) (t : ℝ)
    (h : (fun x => B (t,x)) = (fun x => C (t,x))) (x : Space) :
    Comparison.source u B t x = Comparison.source u C t x := by
  unfold Comparison.source spatialDerivative
  rw [h, congrFun h x]

theorem physicalField_source (u : VelocityField) (a T : ℝ) (hT : 0 ≤ T) (z : Path T)
    (t : Icc (0 : ℝ) T) (x : Space) :
    Comparison.source u (fun p : SpaceTime => (c1Value (z t)).val p.2) (a+t) x =
      Comparison.source u (physicalField a T hT z) (a+t) x :=
  source_eq_of_slice_eq u _ _ _
    (funext (fun y => (physicalField_at_elapsed a T hT z t y).symm)) x

/-- The prescribed velocity, clock, and selected schedule are exactly the
ones used by Paper I. No coefficient or flow wrapper is assumed. -/
def actualPath (scales : ℕ → ℕ) (hsel : Selected scales) (a b : ℝ) (hab : a < b) (hb : b < 1)
    (eta_m : ℝ) (heta : 0 < eta_m) (B_a : PeriodicC1) : Path (b-a) :=
  solution (b-a) (sub_nonneg.mpr hab.le) eta_m heta (actualSourcePath scales hsel a b hb) B_a

theorem actual_mild (scales : ℕ → ℕ) (hsel : Selected scales) (a b : ℝ) (hab : a < b) (hb : b < 1)
    (eta_m : ℝ) (heta : 0 < eta_m) (B_a : PeriodicC1) :
    Mild (b-a) (sub_nonneg.mpr hab.le) eta_m heta (actualSourcePath scales hsel a b hb) B_a
      (actualPath scales hsel a b hab hb eta_m heta B_a) :=
  solution_mild _ _ _ _ _ _

theorem actual_bound (scales : ℕ → ℕ) (hsel : Selected scales) (a b : ℝ) (hab : a < b) (hb : b < 1)
    (eta_m : ℝ) (heta : 0 < eta_m) (B_a : PeriodicC1) :
    ‖actualPath scales hsel a b hab hb eta_m heta B_a‖ ≤
      2 * Real.exp ((contractionWeight (b-a) (sub_nonneg.mpr hab.le) eta_m heta
        (actualSourcePath scales hsel a b hb) : ℝ)*(b-a)) * ‖B_a‖ :=
  solution_bound _ _ _ _ _ _

/-- Identification of the actual source with the evolving physical field,
using only the C1 path derivative. This closes the source interpretation
inside the actual mild equation. -/
theorem actualSourcePath_eq_field_source (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (z : Path (b-a)) (t : Icc (0 : ℝ) (b-a)) (x : Space) :
    (actualSourcePath scales hsel a b hb t (z t)).val x =
      Comparison.source (actualPeriodicVelocity budget threshold geometry scales)
        (physicalField a (b-a) (sub_nonneg.mpr hab.le) z) (a+t) x :=
  (actualSourcePath_eq_source scales hsel a b hb t (z t) x).trans
    (physicalField_source _ a (b-a) (sub_nonneg.mpr hab.le) z t x)

/-- The constructed path gives the original physical Gaussian mild equation.
The preceding source identity identifies its integrand with -DB[u]+Du[B]
at physical time a+tau-r throughout the integration interval. -/
theorem actual_physical_mild_equation (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m)
    (B_a : PeriodicC1) (t : Icc (0 : ℝ) (b-a)) (x : Space) :
    let z := actualPath scales hsel a b hab hb eta_m heta B_a
    let hT := sub_nonneg.mpr hab.le
    physicalField a (b-a) hT z (a+t,x) = (heat eta_m t.val (c1Inclusion B_a)).val x +
      ∫ r in (0 : ℝ)..t.val, (heat eta_m r
        (actualSourcePath scales hsel a b hb (projIcc 0 (b-a) hT (t.val-r))
          (z (projIcc 0 (b-a) hT (t.val-r))))).val x :=
  physicalField_mild_equation (actual_mild scales hsel a b hab hb eta_m heta B_a) t x

/-- Every fixed a<b<1 and eta_m>0 admits one actual continuous C1-valued
mild path, unique among all such paths with the same initial datum. -/
theorem actual_exists_mild (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (B_a : PeriodicC1) :
    ∃ z : Path (b-a),
      Mild (b-a) (sub_nonneg.mpr hab.le) eta_m heta (actualSourcePath scales hsel a b hb) B_a z ∧
      Continuous (physicalField a (b-a) (sub_nonneg.mpr hab.le) z) ∧
      UnitSpatialPeriodsOn (Icc a b) (physicalField a (b-a) (sub_nonneg.mpr hab.le) z) ∧
      (∀ t, ContDiff ℝ 1 (fun x => physicalField a (b-a) (sub_nonneg.mpr hab.le) z (t,x))) ∧
      (∀ x, physicalField a (b-a) (sub_nonneg.mpr hab.le) z (a,x) = (c1Value B_a).val x) ∧
      ∀ w, Mild (b-a) (sub_nonneg.mpr hab.le) eta_m heta (actualSourcePath scales hsel a b hb) B_a w → w = z := by
  let z := actualPath scales hsel a b hab hb eta_m heta B_a
  have hz := actual_mild scales hsel a b hab hb eta_m heta B_a
  exact ⟨z,hz,physicalField_continuous _ _ _ _,physicalField_periodic _ _ _ _ _,
    physicalField_spatialC1 _ _ _ _,physicalField_initial hz,fun _ hw => mild_unique hw hz⟩

theorem actual_axial_exists (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (Bz0 : ℝ) :
    ∃ z : Path (b-a),
      Mild (b-a) (sub_nonneg.mpr hab.le) eta_m heta (actualSourcePath scales hsel a b hb)
        (c1Constant (Bz0 • coordinateVector 2)) z ∧
      (∀ x, physicalField a (b-a) (sub_nonneg.mpr hab.le) z (a,x) = Bz0 • coordinateVector 2) ∧
      ∀ w, Mild (b-a) (sub_nonneg.mpr hab.le) eta_m heta (actualSourcePath scales hsel a b hb)
        (c1Constant (Bz0 • coordinateVector 2)) w → w = z := by
  obtain ⟨z,hz,_,_,_,hi,hu⟩ := actual_exists_mild scales hsel a b hab hb eta_m heta
    (c1Constant (Bz0 • coordinateVector 2))
  exact ⟨z,hz,hi,hu⟩

theorem actualSourcePath_restrict (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b c : ℝ) (hb : b < 1) (hc : c < 1) (hcb : c ≤ b) :
    LinearMild.restrictPath (sub_le_sub_right hcb a) (actualSourcePath scales hsel a b hb) =
      actualSourcePath scales hsel a c hc := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousLinearMap.ext
  intro B
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  simp only [LinearMild.restrictPath_apply, actualSourcePath_eq_source]

/-- Compatibility for different finite slabs uses mild uniqueness, so
their construction weights need not coincide. -/
theorem actual_restrict (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b c : ℝ) (hab : a < b) (hac : a < c) (hb : b < 1) (hc : c < 1) (hcb : c ≤ b)
    (eta_m : ℝ) (heta : 0 < eta_m) (B_a : PeriodicC1) :
    LinearMild.restrictPath (sub_le_sub_right hcb a) (actualPath scales hsel a b hab hb eta_m heta B_a) =
      actualPath scales hsel a c hac hc eta_m heta B_a := by
  have hh := solution_restrict (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hac.le)
    (sub_le_sub_right hcb a) eta_m heta (actualSourcePath scales hsel a b hb) B_a
  rw [actualSourcePath_restrict scales hsel a b c hb hc hcb] at hh
  exact hh

theorem actual_overlap (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b c : ℝ) (hab : a < b) (hac : a < c) (hb : b < 1) (hc : c < 1)
    (eta_m : ℝ) (heta : 0 < eta_m) (B_a : PeriodicC1)
    (tau : ℝ) (htau : 0 ≤ tau) (htb : tau ≤ b-a) (htc : tau ≤ c-a) :
    actualPath scales hsel a b hab hb eta_m heta B_a ⟨tau,htau,htb⟩ =
      actualPath scales hsel a c hac hc eta_m heta B_a ⟨tau,htau,htc⟩ := by
  rcases le_total b c with hbc | hcb
  · have he := congrArg (fun z : Path (b-a) => z ⟨tau,htau,htb⟩)
      (actual_restrict scales hsel a c b hac hab hc hb hbc eta_m heta B_a)
    simpa only [LinearMild.restrictPath_apply] using he.symm
  · have he := congrArg (fun z : Path (c-a) => z ⟨tau,htau,htc⟩)
      (actual_restrict scales hsel a b c hab hac hb hc hcb eta_m heta B_a)
    simpa only [LinearMild.restrictPath_apply] using he

end NavierStokes.ResistiveMagnetic.PeriodicMild
