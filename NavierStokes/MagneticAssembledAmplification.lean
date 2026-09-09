import NavierStokes.MagneticAxisTransfer

/-! Conditional pure-axial ideal induction for the actual periodic and compact
viscosity-one candidates. The magnetic field is supplied, never constructed.
Only the axial Jacobian column is used; no arbitrary-seed conclusion is transferred. -/

noncomputable section
namespace NavierStokes.MagneticAssembledAmplification

open Set Filter ProblemStatement MagneticTransport MagneticCoreAmplification
open MagneticSimilarityTrajectory MagneticAxisTransfer
open scoped Topology ContDiff

/-- A scalar solution lifts to the magnetic solution along a trajectory whenever
its axial line is invariant under the velocity Jacobian. -/
theorem pure_axial_transport_of_scalar_solution
    {u : VelocityField} {B : MagneticField} {γ : ℝ → Space}
    {α β : ℝ → ℝ} {a b Bz0 : ℝ} {x₀ : Space}
    (hγ : IsLagrangianTrajectoryOn u γ a b x₀)
    (hind : IdealInductionOn (Ioo a b) u B)
    (hBc : ContinuousOn (fun t => B (t, γ t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t, γ t))
    (hA : ContinuousOn (fun t => spatialDerivative u t (γ t)) (Icc a b))
    (haxis : ∀ t ∈ Ioo a b, spatialDerivative u t (γ t) (coordinateVector 2) =
      α t • coordinateVector 2)
    (hβc : ContinuousOn β (Icc a b))
    (hβd : ∀ t ∈ Ioo a b, HasDerivAt β (α t * β t) t)
    (hβa : β a = Bz0) (hseed : B (a, γ a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Icc a b) : B (t, γ t) = β t • coordinateVector 2 := by
  have hz := linearODE_eq_zero_on_interval
    (fun s => B (s, γ s) - β s • coordinateVector 2)
    (fun s => spatialDerivative u s (γ s))
    (hBc.sub (hβc.smul continuousOn_const)) hA
    (by
      intro s hs
      have hd := (hasDerivAt_magnetic_along_trajectory hγ hind hs (hBd s hs)).sub
        ((hβd s hs).smul_const (coordinateVector 2))
      convert! hd using 1
      simp only [map_sub, map_smul, haxis s hs, smul_smul]
      rw [mul_comm])
    (by rw [hseed, hβa, sub_self]) ht
  exact sub_eq_zero.mp hz

/-- A pure axial magnetic seed stays axial and satisfies the scalar ODE.
Continuity of the full path Jacobian supplies the scalar ODE existence; no
continuity of an independently extended endpoint coefficient is assumed. -/
theorem pure_axial_follows_scalar_ode
    {u : VelocityField} {B : MagneticField} {γ : ℝ → Space}
    {α : ℝ → ℝ} {a b Bz0 : ℝ} {x₀ : Space}
    (hγ : IsLagrangianTrajectoryOn u γ a b x₀)
    (hind : IdealInductionOn (Ioo a b) u B)
    (hBc : ContinuousOn (fun t => B (t, γ t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t, γ t))
    (hA : ContinuousOn (fun t => spatialDerivative u t (γ t)) (Icc a b))
    (haxis : ∀ t ∈ Ioo a b, spatialDerivative u t (γ t) (coordinateVector 2) =
      α t • coordinateVector 2)
    (hseed : B (a, γ a) = Bz0 • coordinateVector 2) :
    ∃ β : ℝ → ℝ, β a = Bz0 ∧ ContinuousOn β (Icc a b) ∧
      (∀ t ∈ Ioo a b, HasDerivAt β (α t * β t) t) ∧
      ∀ t ∈ Icc a b, B (t, γ t) = β t • coordinateVector 2 := by
  let c : ℝ → ℝ := fun t => (spatialDerivative u t (γ t) (coordinateVector 2)) 2
  have hc : ContinuousOn c (Icc a b) :=
    (AxisymmetricFields.projection 2).continuous.comp_continuousOn
      (hA.clm_apply continuousOn_const)
  obtain ⟨β, hβa, hβd⟩ := TangentODE.exists_linear_solution hγ.ordered
    (fun t => c t • ContinuousLinearMap.id ℝ ℝ) (fun _ => 0)
    (hc.smul continuousOn_const) continuousOn_const Bz0
  have hβc : ContinuousOn β (Icc a b) :=
    fun t ht => (hβd t ht).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Ioo a b, HasDerivAt β (α t * β t) t := by
    intro t ht
    have he : c t = α t := by
      dsimp [c]
      rw [haxis t ht]
      simp [coordinateVector]
    simpa only [smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, add_zero, he] using hβd t (Ioo_subset_Icc_self ht)
  exact ⟨β, hβa, hβc, hd, fun _ ht =>
    pure_axial_transport_of_scalar_solution hγ hind hBc hBd hA haxis hβc hd hβa hseed ht⟩

/-- The late-time kinematic data needed by conditional axial induction.
This packages proved velocity facts, not an existence assumption for `B`. -/
structure LateAxialFlow (u : VelocityField) (γ : ℝ → Space) (K T : ℝ) : Prop where
  path_continuous : ContinuousOn γ (Ioo T 1)
  gradient_continuous : ContinuousOn (fun t => spatialDerivative u t (γ t)) (Ioo T 1)
  trajectory_derivative : ∀ t ∈ Ioo T 1, HasDerivAt γ (u (t, γ t)) t
  axial_column : ∀ t ∈ Ioo T 1,
    spatialDerivative u t (γ t) (coordinateVector 2) = (K / (1 - t)) • coordinateVector 2

namespace LateAxialFlow
variable {u : VelocityField} {γ : ℝ → Space} {K T : ℝ}

theorem pure_axial_transport (hf : LateAxialFlow u γ K T)
    {a b Bz0 : ℝ} (ha : T < a) (hab : a ≤ b) (hb : b < 1) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a b) u B)
    (hBc : ContinuousOn (fun t => B (t, γ t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t, γ t))
    (hseed : B (a, γ a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (t, γ t) = (Bz0 * ((1 - a) / (1 - t)) ^ K) • coordinateVector 2 := by
  have hsub : Icc a b ⊆ Ioo T 1 := fun _ hs => ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hγ : IsLagrangianTrajectoryOn u γ a b (γ a) :=
    ⟨hab, rfl, hf.path_continuous.mono hsub,
      fun _ hs => hf.trajectory_derivative _ (hsub (Ioo_subset_Icc_self hs))⟩
  exact pure_axial_transport_of_directional_gradient hγ hb hind hBc hBd
    (hf.gradient_continuous.mono hsub)
    (fun _ hs => hf.axial_column _ (hsub (Ioo_subset_Icc_self hs))) hseed ht

/-- One fixed induction field on `[a,1)` has the same power law on every
finite restriction. The field is quantified before the evaluation time. -/
theorem pure_axial_transport_preterminal (hf : LateAxialFlow u γ K T)
    {a Bz0 : ℝ} (ha : T < a) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a 1) u B)
    (hBc : ContinuousOn (fun t => B (t, γ t)) (Ico a 1))
    (hBd : ∀ t ∈ Ioo a 1, DifferentiableAt ℝ B (t, γ t))
    (hseed : B (a, γ a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Ico a 1) :
    B (t, γ t) = (Bz0 * ((1 - a) / (1 - t)) ^ K) • coordinateVector 2 := by
  apply hf.pure_axial_transport ha ht.1 ht.2
    (fun s hs => hind s ⟨hs.1, hs.2.trans ht.2⟩)
    (hBc.mono (fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩))
    (fun s hs => hBd s ⟨hs.1, hs.2.trans ht.2⟩) hseed
  exact ⟨ht.1, le_rfl⟩

/-- Conditional divergence for ONE supplied induction solution on the whole
preterminal interval and a nonzero axial seed. This is a pathwise norm limit. -/
theorem magnetic_norm_tendsto_atTop (hf : LateAxialFlow u γ K T) (hK : 0 < K)
    {a Bz0 : ℝ} (ha : T < a) (ha1 : a < 1) (hseed0 : Bz0 ≠ 0) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a 1) u B)
    (hBc : ContinuousOn (fun t => B (t, γ t)) (Ico a 1))
    (hBd : ∀ t ∈ Ioo a 1, DifferentiableAt ℝ B (t, γ t))
    (hseed : B (a, γ a) = Bz0 • coordinateVector 2) :
    Tendsto (fun t => ‖B (t, γ t)‖) (𝓝[<] 1) atTop := by
  have hc : 0 < |Bz0| * (1 - a) ^ K :=
    mul_pos (abs_pos.mpr hseed0) (Real.rpow_pos_of_pos (sub_pos.mpr ha1) K)
  have hl := (BlowupImplication.negative_power_tendsto_atTop hK
    (BlowupImplication.remaining_time_tendsto 1)).atTop_mul_pos hc tendsto_const_nhds
  apply hl.congr'
  have haev : ∀ᶠ t : ℝ in 𝓝[<] 1, a < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds ha1)
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1), haev] with t ht hat
  rw [hf.pure_axial_transport_preterminal ha hind hBc hBd hseed ⟨hat.le, ht⟩]
  simp only [norm_smul, coordinateVector, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, abs_mul]
  rw [abs_of_pos (Real.rpow_pos_of_pos (div_pos (sub_pos.mpr ha1) (sub_pos.mpr ht)) K),
    Real.div_rpow (sub_pos.mpr ha1).le (sub_pos.mpr ht).le,
    Real.rpow_neg (sub_pos.mpr ht).le]
  ring

end LateAxialFlow
/-- Smoothness on an open slab implies continuity of the actual spatial
Jacobian along every continuous path in that slab. -/
theorem gradient_continuousOn_along_path {u : VelocityField} {γ : ℝ → Space} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hγ : ContinuousOn γ S) (hS : ∀ t ∈ S, t < 1) :
    ContinuousOn (fun t => spatialDerivative u t (γ t)) S :=
  (ResidualRegularity.contDiffOn_spatialDerivative (isOpen_Iio.prod isOpen_univ) hu).continuousOn.comp
    (continuousOn_id.prodMk hγ) (fun t ht => ⟨hS t ht, Set.mem_univ _⟩)

section Actual
open CorrectionInitialization.ActualPrimary

variable (budget N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (scales : ℕ → ℕ)
    (hsel : MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig budget N0)
      (ActualCandidateAssembly.potentialStages budget N0 hN)
      (ActualCandidateAssembly.directStages budget N0 hN)
      (ActualCandidateAssembly.pressureStages budget N0 hN) scales)

local notation "γ₀" => trajectory h (distinguishedEta nominal.axis.small)
local notation "K₀" => axialExponent nominal.axis.small
local notation "uP" => actualPeriodicVelocity budget N0 hN scales
local notation "uC" => actualCompactVelocity budget N0 hN scales

include hsel

/-- The selected schedule itself supplies preterminal smoothness. -/
theorem assembled_velocities_smooth :
    ContDiffOn ℝ ∞ uP (Iio (1 : ℝ) ×ˢ (univ : Set Space)) ∧
    ContDiffOn ℝ ∞ uC (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := by
  have hsum := hsel.2.2.2.2.2.2.1
  have hp : ContDiffOn ℝ ∞ (actualPotentialSum budget N0 hN scales)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := hsum.potential.mono (fun _ hw => hw.1)
  have hc : ContDiffOn ℝ ∞ (actualDirectSum budget N0 hN scales)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := hsum.direct.mono (fun _ hw => hw.1)
  constructor
  · exact (SmoothCutoffs.timeSwitch_contDiff.comp contDiff_fst).contDiffOn.smul
      (MixedPeriodicAssembly.periodicVelocity_smoothOn hp hc)
  · have hcut : ContDiffOn ℝ ∞ (fun z : SpaceTime => SpatialLocalization.spatialCutoff z.2)
        (Iio (1 : ℝ) ×ˢ (univ : Set Space)) :=
      (SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn
    exact (SmoothCutoffs.timeSwitch_contDiff.comp contDiff_fst).contDiffOn.smul
      ((SpatialCurl.contDiffOn_spatialCurl (hcut.smul hp) (by simp)).add (hcut.smul hc))

variable {Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : NaturalProfile.IsNaturalSolution h nominal.axis.j Λ P0 a0 f U V Pr)

include hs

/-- A common late interval for the two exact viscosity-one candidates, with
all velocity continuity hypotheses discharged by their construction. -/
theorem exists_late_axial_flows : ∃ T < (1 : ℝ),
    LateAxialFlow uP γ₀ K₀ T ∧ LateAxialFlow uC γ₀ K₀ T := by
  obtain ⟨T, hT, htransfer⟩ := selected_schedule_minimal_transfer_late_interval
    budget N0 hN scales hsel hs
  have hpath : ContinuousOn γ₀ (Ioo T 1) := fun t ht =>
    ((htransfer t ht _ (by simp)).1 : HasDerivAt γ₀ (uP (t, γ₀ t)) t).continuousAt.continuousWithinAt
  have hu := assembled_velocities_smooth budget N0 hN scales hsel
  refine ⟨T, hT, ⟨hpath, gradient_continuousOn_along_path hu.1 hpath (fun _ ht => ht.2),
    ?_, ?_⟩, ⟨hpath, gradient_continuousOn_along_path hu.2 hpath (fun _ ht => ht.2), ?_, ?_⟩⟩
  · exact fun t ht => (htransfer t ht _ (by simp)).1
  · exact fun t ht => (htransfer t ht _ (by simp)).2
  · exact fun t ht => (htransfer t ht _ (by simp)).1
  · exact fun t ht => (htransfer t ht _ (by simp)).2

/-- A single threshold chosen from the proved common late interval. This is
not a new activation or a time rescaling. -/
def lateStart : ℝ := Classical.choose (exists_late_axial_flows budget N0 hN scales hsel hs)

theorem lateStart_spec : lateStart budget N0 hN scales hsel hs < 1 ∧
    LateAxialFlow uP γ₀ K₀ (lateStart budget N0 hN scales hsel hs) ∧
    LateAxialFlow uC γ₀ K₀ (lateStart budget N0 hN scales hsel hs) :=
  Classical.choose_spec (exists_late_axial_flows budget N0 hN scales hsel hs)

local notation "T₀" => lateStart budget N0 hN scales hsel hs

/-- Conditional amplification for the exact assembled PERIODIC velocity.
The induction equation is for `uP`, not for the natural core. -/
theorem periodic_pure_axial_transport
    {a b Bz0 : ℝ} (ha : T₀ < a) (hab : a ≤ b) (hb : b < 1) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a b) uP B)
    (hBc : ContinuousOn (fun t => B (t, γ₀ t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t, γ₀ t))
    (hseed : B (a, γ₀ a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (t, γ₀ t) = (Bz0 * ((1 - a) / (1 - t)) ^ K₀) • coordinateVector 2 :=
  (lateStart_spec budget N0 hN scales hsel hs).2.1.pure_axial_transport
    ha hab hb hind hBc hBd hseed ht

/-- Conditional amplification for the exact assembled compact WHOLE-SPACE
velocity. Its physical clock is the same viscosity-one clock as the periodic field. -/
theorem compact_pure_axial_transport
    {a b Bz0 : ℝ} (ha : T₀ < a) (hab : a ≤ b) (hb : b < 1) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a b) uC B)
    (hBc : ContinuousOn (fun t => B (t, γ₀ t)) (Icc a b))
    (hBd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ B (t, γ₀ t))
    (hseed : B (a, γ₀ a) = Bz0 • coordinateVector 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (t, γ₀ t) = (Bz0 * ((1 - a) / (1 - t)) ^ K₀) • coordinateVector 2 :=
  (lateStart_spec budget N0 hN scales hsel hs).2.2.pure_axial_transport
    ha hab hb hind hBc hBd hseed ht

/-- Norm divergence for one fixed periodic-velocity induction solution on
`[a,1)`, with a nonzero axial seed. Periodicity of `B` is not needed for this
pathwise inference, and magnetic PDE existence is not asserted. -/
theorem periodic_magnetic_norm_tendsto_atTop
    {a Bz0 : ℝ} (ha : T₀ < a) (ha1 : a < 1) (hseed0 : Bz0 ≠ 0) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a 1) uP B)
    (hBc : ContinuousOn (fun t => B (t, γ₀ t)) (Ico a 1))
    (hBd : ∀ t ∈ Ioo a 1, DifferentiableAt ℝ B (t, γ₀ t))
    (hseed : B (a, γ₀ a) = Bz0 • coordinateVector 2) :
    Tendsto (fun t => ‖B (t, γ₀ t)‖) (𝓝[<] 1) atTop :=
  (lateStart_spec budget N0 hN scales hsel hs).2.1.magnetic_norm_tendsto_atTop
    (axialExponent_pos nominal.axis.small) ha ha1 hseed0 hind hBc hBd hseed

/-- The same one-solution norm-divergence conclusion for the compact
whole-space velocity; no magnetic energy or volume conclusion is inferred. -/
theorem compact_magnetic_norm_tendsto_atTop
    {a Bz0 : ℝ} (ha : T₀ < a) (ha1 : a < 1) (hseed0 : Bz0 ≠ 0) {B : MagneticField}
    (hind : IdealInductionOn (Ioo a 1) uC B)
    (hBc : ContinuousOn (fun t => B (t, γ₀ t)) (Ico a 1))
    (hBd : ∀ t ∈ Ioo a 1, DifferentiableAt ℝ B (t, γ₀ t))
    (hseed : B (a, γ₀ a) = Bz0 • coordinateVector 2) :
    Tendsto (fun t => ‖B (t, γ₀ t)‖) (𝓝[<] 1) atTop :=
  (lateStart_spec budget N0 hN scales hsel hs).2.2.magnetic_norm_tendsto_atTop
    (axialExponent_pos nominal.axis.small) ha ha1 hseed0 hind hBc hBd hseed

end Actual
end NavierStokes.MagneticAssembledAmplification
