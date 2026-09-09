import NavierStokes.MagneticCoreAmplification
import NavierStokes.ActualCandidateAssembly
import NavierStokes.R3ActualCandidate

/-! Minimal axial transfer audit. Axial-line identities determine the axial
Jacobian column; no equality of transverse derivatives or swirl is asserted. -/

noncomputable section
namespace NavierStokes.MagneticAxisTransfer

open Set Filter ProblemStatement AxisymmetricFields NaturalCore
open MagneticSimilarityTrajectory MagneticCoreAmplification
open scoped Topology ContDiff

/-- A zero spacetime germ kills both the value and the axial directional
Jacobian, independently of the size of coefficients away from the path. -/
theorem zero_germ_value_and_axial_derivative {u : VelocityField} {w : SpaceTime}
    (hu : u =ᶠ[𝓝 w] fun _ => 0) :
    u w = 0 ∧ spatialDerivative u w.1 w.2 (coordinateVector 2) = 0 := by
  refine ⟨hu.self_of_nhds, ?_⟩
  unfold spatialDerivative
  rw [ResidualRegularity.space_fderiv_congr hu]
  simp

/-- Differentiable fields agreeing on an axial-line germ have the same axial
Jacobian column. Agreement at just one point would not suffice. -/
theorem axial_derivative_of_line_germ {u v : VelocityField} {t z : ℝ}
    (hu : DifferentiableAt ℝ (fun x => u (t, x)) (z • coordinateVector 2))
    (hv : DifferentiableAt ℝ (fun x => v (t, x)) (z • coordinateVector 2))
    (he : (fun r => u (t, r • coordinateVector 2)) =ᶠ[𝓝 z]
      (fun r => v (t, r • coordinateVector 2))) :
    spatialDerivative u t (z • coordinateVector 2) (coordinateVector 2) =
      spatialDerivative v t (z • coordinateVector 2) (coordinateVector 2) := by
  have hd := (hasDerivAt_id z).smul_const (coordinateVector 2)
  have hdu := hu.hasFDerivAt.comp_hasDerivAt z hd
  have hdv := hv.hasFDerivAt.comp_hasDerivAt z hd
  simpa only [spatialDerivative, one_smul] using (he.hasDerivAt_iff.mp hdu).unique hdv

theorem core_axis_profile_mem {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (Λ : ℝ) {t : ℝ} (ht : t < 1) (z : ℝ) : (t, (0, z)) ∈ profileDomain h Λ := by
  refine ⟨ht, ?_⟩
  have he := SimilarityCoordinates.coordinateEta_abs_lt_one (a := 2 * h)
    (by linarith) (by linarith) (p := (1 - t, z)) (sub_pos.mpr ht)
  have he' : -1 < physicalEta h (t, (0, z)) ∧ physicalEta h (t, (0, z)) < 1 :=
    abs_lt.mp he
  simp only [similarityPoint, zero_div]
  norm_num [NaturalProfile.domain, NaturalProfile.rescalePoint,
    AxisEvaluation.strip, NaturalAxisCoefficients.window]
  constructor <;> linarith [he'.1, he'.2]

theorem core_axis {h j Λ t : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (p : NaturalAxisData.SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr) (ht : t < 1) (z : ℝ) :
    coreVelocity h f V (t, z • coordinateVector 2) =
      (physicalQ h (t, (0, z)) ^ (-NaturalAxisData.A h) *
        NaturalAxisData.U j (physicalEta h (t, (0, z)))) • coordinateVector 2 := by
  have hh1 : h < 1 / 2 := by linarith [p.h_le]
  have hp := core_axis_profile_mem p.h_pos hh1 Λ ht z
  have hH := (meridionalPotential_contDiffAt p.h_pos hh1 hs.average_smooth hp).differentiableAt (by simp)
  have hK := (swirlPotential_contDiffAt p.h_pos hh1 hs.f_smooth hp).differentiableAt (by simp)
  have he : profilePoint t (z • coordinateVector 2) = (t, (0, z)) := by
    simp [profilePoint, radialEnergy, coordinateVector]
  change velocity _ _ _ = _
  rw [velocity_on_axis _ _ _ _ (by rw [he]; exact hH) (by rw [he]; exact hK)
    (by simp [coordinateVector]) (by simp [coordinateVector])]
  have hz : (z • coordinateVector 2 : Space) 2 = z := by simp [coordinateVector]
  rw [hz, MagneticSimilarityGradient.meridionalPotential_axis p.h_pos hh1 hs ht]

section SlowBase
variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The full Borel sum has exactly the natural axial-line velocity. Positive
axial coefficients vanish on the entire axis, including their cutoff products. -/
theorem slowBase_axis (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) (z : ℝ) :
    FinalSlowBase.velocity H v upper B (t, z • coordinateVector 2) =
      (physicalQ F.data.h (t, (0, z)) ^ (-NaturalAxisData.A F.data.h) *
        NaturalAxisData.U W.axis.j (physicalEta F.data.h (t, (0, z)))) • coordinateVector 2 := by
  let η := physicalEta F.data.h (t, (0, z))
  have he := SimilarityCoordinates.coordinateEta_abs_lt_one (a := 2 * F.data.h)
    (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (p := (1 - t, z)) (sub_pos.mpr ht)
  have heta : |η| ≤ 1 := le_of_lt he
  have heta' : η ∈ Icc (-1 : ℝ) 1 := abs_le.mp heta
  have ha := FinalSlowBase.scales_strictMono H v upper B
  have hd := FinalSlowBase.coefficients_smooth H v
  have hH := (SlowBorelBase.physicalProfile_smoothAt ha F.data.h_pos F.data.h_lt_half
    (SlowBorelBase.bundleComponent_smooth hd W.axis.normalization 0)
    (-CoordinateAlgebra.A F.data.h) (show (t, (0, z)).1 < 1 from ht)).differentiableAt (by simp)
  have hK := (SlowBorelBase.physicalProfile_smoothAt ha F.data.h_pos F.data.h_lt_half
    (SlowBorelBase.bundleComponent_smooth hd W.axis.normalization 1)
    (1 / 2 - CoordinateAlgebra.A F.data.h) (show (t, (0, z)).1 < 1 from ht)).differentiableAt (by simp)
  have hp : profilePoint t (z • coordinateVector 2) = (t, (0, z)) := by
    simp [profilePoint, radialEnergy, coordinateVector]
  change velocity _ _ _ = _
  rw [velocity_on_axis _ _ _ _ (by rw [hp]; exact hH)
    (by rw [hp]; exact hK) (by simp [coordinateVector]) (by simp [coordinateVector])]
  have hz : (z • coordinateVector 2 : Space) 2 = z := by simp [coordinateVector]
  rw [hz]
  change (SlowBorelBase.physicalProfile _ _ _ _ (t, (0, z))) • _ = _
  unfold SlowBorelBase.physicalProfile
  have hc : SlowBorelBase.physicalChart F.data.h (t, (0, z)) =
      (physicalQ F.data.h (t, (0, z)), (0, η)) := by
    change (physicalQ F.data.h (t, (0, z)),
      (0 / physicalQ F.data.h (t, (0, z)), η)) = _
    rw [zero_div]
  rw [hc, BaseResidual.slowSum_eq_leading_of_positive_zero]
  · change (_ * ProfileHistories.average (FinalSlowBase.coefficients H v |>.axial 0) (0, η)) • _ = _
    rw [ProfileHistories.average_at_axis]
    rw [show (FinalSlowBase.coefficients H v).axial 0 (0, η) = 4 * η + W.axis.j from
      EntranceAlignedBase.modulated_leading_axis H v heta']
    rfl
  · intro n hn
    change ProfileHistories.average ((FinalSlowBase.coefficients H v).axial n) (0, η) = 0
    rw [ProfileHistories.average_at_axis]
    exact (EntranceAlignedBase.modulated_positive_axis H v hn heta).2.1

/-- Exact line equality, without any assumption on higher swirl coefficients. -/
theorem slowBase_axis_eq_core (upper : ℝ) (B : ℕ)
    {Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : NaturalProfile.IsNaturalSolution F.data.h W.axis.j Λ P0 a0 f U V Pr)
    {t : ℝ} (ht : t < 1) (z : ℝ) :
    FinalSlowBase.velocity H v upper B (t, z • coordinateVector 2) =
      coreVelocity F.data.h f V (t, z • coordinateVector 2) := by
  rw [slowBase_axis H v upper B ht z, core_axis W.axis.small hs ht z]

/-- Only the axial column transfers from the core through axial-line equality. -/
theorem slowBase_axial_derivative (upper : ℝ) (B : ℕ)
    {Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : NaturalProfile.IsNaturalSolution F.data.h W.axis.j Λ P0 a0 f U V Pr)
    {t : ℝ} (ht : t < 1) :
    spatialDerivative (FinalSlowBase.velocity H v upper B) t
      (trajectory F.data.h (distinguishedEta W.axis.small) t) (coordinateVector 2) =
      (axialExponent W.axis.small / (1 - t)) • coordinateVector 2 := by
  rw [← spatialDerivative_core_axial W.axis.small hs ht]
  apply axial_derivative_of_line_germ
  · have hc := (FinalSlowBase.velocity_smooth H v upper B).contDiffAt
      (x := (t, trajectory F.data.h (distinguishedEta W.axis.small) t))
      (prod_mem_nhds (Iio_mem_nhds ht) Filter.univ_mem)
    exact (hc.differentiableAt (by simp)).comp _
      (by fun_prop)
  · have hx := trajectory_mem_core F.data.h_pos F.data.h_lt_half
      (distinguishedEta_sq_lt_one W.axis.small) ht Λ
    have hc := (coreVelocity_contDiffOn F.data.h_pos F.data.h_lt_half
      hs.f_smooth hs.average_smooth).contDiffAt
        ((coreDomain_isOpen F.data.h_pos F.data.h_lt_half Λ).mem_nhds hx)
    exact (hc.differentiableAt (by simp)).comp _
      (by fun_prop)
  · exact Filter.Eventually.of_forall (slowBase_axis_eq_core H v upper B hs ht)

/-- A slow-base germ supplies exactly the two conditions needed by pure axial
transport. This does not assert full gradient agreement with the natural core. -/
theorem minimal_transfer_of_slowBase_germ (upper : ℝ) (B : ℕ)
    {Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : NaturalProfile.IsNaturalSolution F.data.h W.axis.j Λ P0 a0 f U V Pr)
    {u : VelocityField} {t : ℝ} (ht : t < 1)
    (hg : u =ᶠ[𝓝 (t, trajectory F.data.h (distinguishedEta W.axis.small) t)]
      FinalSlowBase.velocity H v upper B) :
    HasDerivAt (trajectory F.data.h (distinguishedEta W.axis.small))
      (u (t, trajectory F.data.h (distinguishedEta W.axis.small) t)) t ∧
    spatialDerivative u t (trajectory F.data.h (distinguishedEta W.axis.small) t)
      (coordinateVector 2) = (axialExponent W.axis.small / (1 - t)) • coordinateVector 2 := by
  constructor
  · have he : FinalSlowBase.velocity H v upper B
        (t, trajectory F.data.h (distinguishedEta W.axis.small) t) =
        coreVelocity F.data.h f V (t, trajectory F.data.h (distinguishedEta W.axis.small) t) :=
      slowBase_axis_eq_core H v upper B hs ht (pathZ F.data.h (distinguishedEta W.axis.small) t)
    rw [hg.self_of_nhds, he]
    exact trajectory_hasDerivAt F.data.h_pos F.data.h_lt_half hs
      (distinguishedEta_sq_lt_one W.axis.small) (distinguishedEta_spec W.axis.small).2.1 ht
  · unfold spatialDerivative
    rw [ResidualRegularity.space_fderiv_congr hg]
    exact slowBase_axial_derivative H v upper B hs ht

end SlowBase
/-- The distinguished path eventually lies inside every required plateau.
The finite schedule value `n` is fixed before taking this late-time limit. -/
theorem path_eventually_in_plateaus {h j : ℝ} (p : NaturalAxisData.SmallParameters h j)
    {qbig : ℝ} (hqbig : 0 < qbig) (n : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[<] 1, t < 1 ∧ pathQ (distinguishedEta p) t < qbig ∧
      |n * pathQ (distinguishedEta p) t| < 1 / 2 ∧ 3 / 4 < t ∧
      trajectory h (distinguishedEta p) t ∈ SpatialLocalization.plateau := by
  have hqc : ContinuousAt (pathQ (distinguishedEta p)) 1 := by unfold pathQ; fun_prop
  have hq : Tendsto (pathQ (distinguishedEta p)) (𝓝[<] 1) (𝓝 0) := by
    simpa [pathQ] using hqc.tendsto.mono_left nhdsWithin_le_nhds
  have hgc : ContinuousAt (trajectory h (distinguishedEta p)) 1 :=
    ((hqc.rpow_const (p := NaturalAxisData.D h) (Or.inr (NaturalAxisData.D_pos p).le)).mul
      continuousAt_const).smul continuousAt_const
  have hg : Tendsto (trajectory h (distinguishedEta p)) (𝓝[<] 1) (𝓝 0) := by
    simpa [trajectory, pathZ, pathQ, Real.zero_rpow (NaturalAxisData.D_pos p).ne'] using
      hgc.tendsto.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun t => |n * pathQ (distinguishedEta p) t|) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hq).abs
  have hl : ∀ᶠ t : ℝ in 𝓝[<] 1, 3 / 4 < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (show (3 / 4 : ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1),
    hq.eventually (Iio_mem_nhds hqbig),
    hn.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)), hl,
    hg.eventually (SpatialLocalization.isOpen_plateau.mem_nhds SpatialLocalization.zero_mem_plateau)]
    with t ht hqt hnt hlt hgt
  exact ⟨ht, hqt, hnt, hlt, hgt⟩

section Actual
open CorrectionInitialization.ActualPrimary

/-- Actual potential sum for an explicit common schedule. -/
def actualPotentialSum (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.potentialStages B N0 hN)

def actualDirectSum (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.directStages B N0 hN)

/-- The periodic velocity appearing in `ActualCandidateAssembly.Witness`. -/
def actualPeriodicVelocity (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (a : ℕ → ℕ) : VelocityField :=
  TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity
    (actualPotentialSum B N0 hN a) (actualDirectSum B N0 hN a))

/-- The whole-space velocity obtained from the same selected sums. -/
def actualCompactVelocity (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (a : ℕ → ℕ) : VelocityField :=
  R3CompactCandidate.velocity (actualPotentialSum B N0 hN a) (actualDirectSum B N0 hN a)

/-- All actual potential and direct corrections have zero germs in the axis
region on the zeroth-cutoff plateau. The retained germ is the slow base. -/
theorem actual_raw_eq_slowBase_germ (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (a : ℕ → ℕ)
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    {w : SpaceTime} (hw : w ∈ MixedAxisPreservation.localDomain h
      (ActualCandidateConstruction.qbig B N0))
    (haxis : PhysicalGraphBounds.radialProjection w = 0)
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h w| < 1 / 2) :
    MixedPeriodicAssembly.velocity (actualPotentialSum B N0 hN a) (actualDirectSum B N0 hN a)
      =ᶠ[𝓝 w] FinalSlowBase.velocity certificate modulation upper B := by
  have hp := GermCandidateAssembly.potentialSum_eq_base_germ ha
    (base := TailGaugePotential.finalPotential certificate modulation upper B)
    (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos outgoing.data.h_lt_half hw.1).continuousAt
    (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
    (ActualCandidateAssembly.initialPotential_axisZeroOn B N0 w hw haxis)
    (fun j => ActualCandidateAssembly.positivePotential_axisZeroOn B N0 hN j w hw haxis) hsmall
  have hc := SolenoidalDiagonal.spatialCurl_eventuallyEq hp
  have hd := MixedAxisPreservation.directDiagonal_zero_germ
    (LocalAngularDiagonal.angularSupport (ActualCandidateAssembly.directData B N0 hN))
    outgoing.data.h_pos outgoing.data.h_lt_half ha
    (MixedAxisPreservation.localDomain_open outgoing.data.h_pos outgoing.data.h_lt_half _)
    hw hw.1 haxis
  have ht : ∀ᶠ y : SpaceTime in 𝓝 w, y.1 < 1 :=
    continuousAt_fst (Iio_mem_nhds hw.1)
  filter_upwards [hc, hd, ht] with y hy hdy hty
  change SpatialCurl.spatialCurl _ y + _ = _
  rw [show actualDirectSum B N0 hN a y = 0 from hdy, add_zero]
  exact hy.trans (TailGaugePotential.finalPotential_sameCurl certificate modulation upper B hty)

theorem actual_periodic_eq_slowBase_germ (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (a : ℕ → ℕ)
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    {w : SpaceTime} (hw : w ∈ MixedAxisPreservation.localDomain h
      (ActualCandidateConstruction.qbig B N0))
    (haxis : PhysicalGraphBounds.radialProjection w = 0)
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h w| < 1 / 2)
    (ht : 3 / 4 < w.1) (hx : w.2 ∈ SpatialLocalization.plateau) :
    actualPeriodicVelocity B N0 hN a =ᶠ[𝓝 w]
      FinalSlowBase.velocity certificate modulation upper B :=
  (TimeLocalization.activatedVelocity_eventuallyEq_late _ ht w.2).trans
    ((MixedPeriodicAssembly.periodicVelocity_eventuallyEq _ _ hx).trans
      (actual_raw_eq_slowBase_germ B N0 hN a ha hw haxis hsmall))

theorem actual_compact_eq_slowBase_germ (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (a : ℕ → ℕ)
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    {w : SpaceTime} (hw : w ∈ MixedAxisPreservation.localDomain h
      (ActualCandidateConstruction.qbig B N0))
    (haxis : PhysicalGraphBounds.radialProjection w = 0)
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h w| < 1 / 2)
    (ht : 3 / 4 < w.1) (hx : w.2 ∈ SpatialLocalization.plateau) :
    actualCompactVelocity B N0 hN a =ᶠ[𝓝 w]
      FinalSlowBase.velocity certificate modulation upper B :=
  (TimeLocalization.activatedVelocity_eventuallyEq_late _ ht w.2).trans
    ((MixedPeriodicAssembly.cutVelocity_eventuallyEq _ _ hx).trans
      (actual_raw_eq_slowBase_germ B N0 hN a ha hw haxis hsmall))

/-- Both actual final velocities satisfy the minimal axial transfer conditions
sufficiently late. The schedule need only tend to infinity, as every selected
schedule does. Natural-core data must use the actual parameters `h,j`. -/
theorem actual_minimal_transfer_eventually (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (a : ℕ → ℕ)
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    {Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : NaturalProfile.IsNaturalSolution h nominal.axis.j Λ P0 a0 f U V Pr) :
    ∀ᶠ t : ℝ in 𝓝[<] 1, ∀ u ∈ ({actualPeriodicVelocity B N0 hN a,
      actualCompactVelocity B N0 hN a} : Set VelocityField),
      HasDerivAt (trajectory h (distinguishedEta nominal.axis.small))
        (u (t, trajectory h (distinguishedEta nominal.axis.small) t)) t ∧
      spatialDerivative u t (trajectory h (distinguishedEta nominal.axis.small) t)
        (coordinateVector 2) = (axialExponent nominal.axis.small / (1 - t)) • coordinateVector 2 := by
  filter_upwards [path_eventually_in_plateaus nominal.axis.small
    (ActualCandidateConstruction.qbig_pos B N0) (a 0 : ℝ)] with t ht
  have hq : PhysicalWaveSum.physicalQ h
      (t, trajectory h (distinguishedEta nominal.axis.small) t) =
      pathQ (distinguishedEta nominal.axis.small) t := by
    change physicalQ h (t, (0, (trajectory h (distinguishedEta nominal.axis.small) t) 2)) = _
    have hz : (trajectory h (distinguishedEta nominal.axis.small) t) 2 =
        pathZ h (distinguishedEta nominal.axis.small) t := by simp [trajectory, coordinateVector]
    rw [hz]
    exact physicalQ_path outgoing.data.h_pos outgoing.data.h_lt_half
      (distinguishedEta_sq_lt_one nominal.axis.small) ht.1
  have hw : (t, trajectory h (distinguishedEta nominal.axis.small) t) ∈
      MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0) :=
    ⟨ht.1, by rw [hq]; exact ht.2.1⟩
  have haxis : PhysicalGraphBounds.radialProjection
      (t, trajectory h (distinguishedEta nominal.axis.small) t) = 0 := by
    simp [PhysicalGraphBounds.radialProjection, trajectory, coordinateVector]
  have hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ h
      (t, trajectory h (distinguishedEta nominal.axis.small) t)| < 1 / 2 := by
    rw [hq]; exact ht.2.2.1
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · exact minimal_transfer_of_slowBase_germ certificate modulation upper B hs ht.1
      (actual_periodic_eq_slowBase_germ B N0 hN a ha hw haxis hsmall ht.2.2.2.1 ht.2.2.2.2)
  · have he := Set.mem_singleton_iff.mp hu
    subst u
    exact minimal_transfer_of_slowBase_germ certificate modulation upper B hs ht.1
      (actual_compact_eq_slowBase_germ B N0 hN a ha hw haxis hsmall ht.2.2.2.1 ht.2.2.2.2)

/-- Every schedule retained by the actual witness has a common late interval
on which both final velocities meet the minimal transfer conditions. -/
theorem selected_schedule_minimal_transfer_late_interval (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (a : ℕ → ℕ)
    (hsel : MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig B N0)
      (ActualCandidateAssembly.potentialStages B N0 hN)
      (ActualCandidateAssembly.directStages B N0 hN)
      (ActualCandidateAssembly.pressureStages B N0 hN) a)
    {Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : NaturalProfile.IsNaturalSolution h nominal.axis.j Λ P0 a0 f U V Pr) :
    ∃ T < (1 : ℝ), ∀ t ∈ Ioo T 1,
      ∀ u ∈ ({actualPeriodicVelocity B N0 hN a,
        actualCompactVelocity B N0 hN a} : Set VelocityField),
        HasDerivAt (trajectory h (distinguishedEta nominal.axis.small))
          (u (t, trajectory h (distinguishedEta nominal.axis.small) t)) t ∧
        spatialDerivative u t (trajectory h (distinguishedEta nominal.axis.small) t)
          (coordinateVector 2) = (axialExponent nominal.axis.small / (1 - t)) • coordinateVector 2 :=
  mem_nhdsLT_iff_exists_Ioo_subset.mp
    (actual_minimal_transfer_eventually B N0 hN a hsel.2.2.2.2.1 hs)

end Actual
end NavierStokes.MagneticAxisTransfer
