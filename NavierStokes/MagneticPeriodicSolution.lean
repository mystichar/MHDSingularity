import NavierStokes.MagneticPeriodicCompatibility
import Mathlib.Topology.Order.IsLUB

/-! One preterminal magnetic field obtained by compatible finite-slab
construction. No uniform bound at the terminal time is used. -/
noncomputable section
namespace NavierStokes.MagneticPeriodicSolution
open Set Filter ProblemStatement MagneticPeriodicFlow
open scoped Topology ContDiff
private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance

structure Data where
  velocity : VelocityField
  a : ℝ
  ha : a < 1
  smooth : ContDiffOn ℝ ∞ velocity (Iio (1 : ℝ) ×ˢ univ)
  periodic : UnitSpatialPeriodsOn (Iio (1 : ℝ)) velocity
  divergence : ∀ t < 1, ∀ x, spatialDivergence velocity t x = 0

namespace Data
variable (D : Data)

def endpoints : ℕ → ℝ := (exists_seq_strictMono_tendsto' D.ha).choose

theorem endpoints_spec : StrictMono D.endpoints ∧
    (∀ n, D.endpoints n ∈ Ioo D.a 1) ∧ Tendsto D.endpoints atTop (𝓝 1) :=
  (exists_seq_strictMono_tendsto' D.ha).choose_spec

def slab (n : ℕ) : Slab where
  velocity := D.velocity
  a := D.a
  b := D.endpoints n
  hab := (D.endpoints_spec.2.1 n).1
  hb := (D.endpoints_spec.2.1 n).2
  smooth := D.smooth
  periodic := D.periodic

theorem exists_endpoint (t : ℝ) (ht : t < 1) : ∃ n, t < D.endpoints n :=
  (D.endpoints_spec.2.2.eventually (Ioi_mem_nhds ht)).exists

def index (t : ℝ) (ht : t < 1) : ℕ := (D.exists_endpoint t ht).choose

theorem index_spec (t : ℝ) (ht : t < 1) : t < D.endpoints (D.index t ht) :=
  (D.exists_endpoint t ht).choose_spec

/-- A single field is chosen once on the entire preterminal domain. -/
def magnetic (Bz0 : ℝ) (z : SpaceTime) : Space :=
  if ht : z.1 < 1 then (D.slab (D.index z.1 ht)).magnetic Bz0 z else 0

theorem magnetic_eq_slab (Bz0 t : ℝ) (n : ℕ) (ht : t ∈ Icc D.a (D.endpoints n))
    (x : Space) : D.magnetic Bz0 (t,x) = (D.slab n).magnetic Bz0 (t,x) := by
  have ht1 : t < 1 := ht.2.trans_lt (D.endpoints_spec.2.1 n).2
  rw [magnetic, dite_eq_left ht1]
  exact (D.slab (D.index t ht1)).magnetic_overlap (D.slab n) rfl rfl Bz0 t
    ⟨ht.1,(D.index_spec t ht1).le⟩ ht x

theorem magnetic_initial (Bz0 : ℝ) (x : Space) :
    D.magnetic Bz0 (D.a,x) = Bz0 • coordinateVector 2 := by
  rw [D.magnetic_eq_slab Bz0 D.a 0 ⟨le_rfl,(D.endpoints_spec.2.1 0).1.le⟩]
  exact (D.slab 0).magnetic_initial Bz0 x

theorem magnetic_eventuallyEq (Bz0 t : ℝ) (ht : t ∈ Ioo D.a 1) (n : ℕ)
    (hn : t < D.endpoints n) (x : Space) :
    D.magnetic Bz0 =ᶠ[𝓝 (t,x)] (D.slab n).magnetic Bz0 := by
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 hn)] with z hz
  exact D.magnetic_eq_slab Bz0 z.1 n ⟨hz.1.le,hz.2.le⟩ z.2

theorem magnetic_continuousOn (Bz0 : ℝ) :
    ContinuousOn (D.magnetic Bz0) (Ico D.a 1 ×ˢ univ) := by
  intro z hz
  obtain ⟨n,hn⟩ := D.exists_endpoint z.1 hz.1.2
  have hc := (D.slab n).magnetic_continuousOn Bz0 z ⟨⟨hz.1.1,hn.le⟩,mem_univ _⟩
  have he : D.magnetic Bz0 =ᶠ[𝓝[Ico D.a 1 ×ˢ univ] z] (D.slab n).magnetic Bz0 := by
    filter_upwards [self_mem_nhdsWithin,
      (continuous_fst.continuousWithinAt.tendsto).eventually (Iio_mem_nhds hn)] with w hw hwn
    exact D.magnetic_eq_slab Bz0 w.1 n ⟨hw.1.1,hwn.le⟩ w.2
  have hm : (Icc D.a (D.endpoints n) ×ˢ (univ : Set Space)) ∈
      𝓝[Ico D.a 1 ×ˢ univ] z := by
    filter_upwards [self_mem_nhdsWithin,
      (continuous_fst.continuousWithinAt.tendsto).eventually (Iio_mem_nhds hn)] with w hw hwn
    exact ⟨⟨hw.1.1,hwn.le⟩,mem_univ _⟩
  exact (hc.mono_of_mem_nhdsWithin hm).congr_of_eventuallyEq_of_mem he hz

theorem magnetic_contDiffAt (Bz0 t : ℝ) (ht : t ∈ Ioo D.a 1) (x : Space) :
    ContDiffAt ℝ 1 (D.magnetic Bz0) (t,x) := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  exact ((D.slab n).magnetic_contDiffAt Bz0 t ⟨ht.1,hn⟩ x).congr_of_eventuallyEq
    (D.magnetic_eventuallyEq Bz0 t ht n hn x)

theorem magnetic_periodic (Bz0 : ℝ) :
    UnitSpatialPeriodsOn (Ico D.a 1) (D.magnetic Bz0) := by
  intro t ht x i
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  rw [D.magnetic_eq_slab Bz0 t n ⟨ht.1,hn.le⟩,
    D.magnetic_eq_slab Bz0 t n ⟨ht.1,hn.le⟩]
  exact (D.slab n).magnetic_periodic Bz0 t (mem_univ _) x i

/-- All finite spatial orders at each preterminal time; this is not a
claim of joint C-infinity regularity. -/
theorem magnetic_spatial_smooth (Bz0 t : ℝ) (ht : t ∈ Ico D.a 1) :
    ContDiff ℝ ∞ (fun x => D.magnetic Bz0 (t,x)) := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he : (fun x => D.magnetic Bz0 (t,x)) = (fun x => (D.slab n).magnetic Bz0 (t,x)) :=
    funext (D.magnetic_eq_slab Bz0 t n ⟨ht.1,hn.le⟩)
  rw [he]
  exact (D.slab n).magnetic_spatial_smooth Bz0 t ⟨ht.1,hn.le⟩

theorem magnetic_divergence_free (Bz0 t : ℝ) (ht : t ∈ Ico D.a 1) (x : Space) :
    spatialDivergence (D.magnetic Bz0) t x = 0 := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he : (fun y => D.magnetic Bz0 (t,y)) = (fun y => (D.slab n).magnetic Bz0 (t,y)) :=
    funext (D.magnetic_eq_slab Bz0 t n ⟨ht.1,hn.le⟩)
  change (∑ i : Fin 3, (fderiv ℝ (fun y => D.magnetic Bz0 (t,y)) x (coordinateVector i)) i) = 0
  rw [he]
  exact (D.slab n).magnetic_divergence_free
    (fun s hs y => D.divergence s (hs.2.trans_lt (D.endpoints_spec.2.1 n).2) y)
    Bz0 t ⟨ht.1,hn.le⟩ x

theorem magnetic_induction (Bz0 : ℝ) :
    MagneticTransport.IdealInductionOn (Ioo D.a 1) D.velocity (D.magnetic Bz0) := by
  intro t ht x
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he := D.magnetic_eventuallyEq Bz0 t ht n hn x
  have h := (D.slab n).magnetic_induction Bz0 t ⟨ht.1,hn⟩ x
  change temporalDerivative _ _ _ + spatialDerivative _ _ _ _ = spatialDerivative _ _ _ _
  rw [show temporalDerivative (D.magnetic Bz0) t x =
      temporalDerivative ((D.slab n).magnetic Bz0) t x from
    congrArg (fun L : ℝ →L[ℝ] Space => L 1) (ResidualRegularity.time_fderiv_congr he),
    show spatialDerivative (D.magnetic Bz0) t x = spatialDerivative ((D.slab n).magnetic Bz0) t x from
      ResidualRegularity.space_fderiv_congr he, he.self_of_nhds]
  exact h

end Data
end NavierStokes.MagneticPeriodicSolution

namespace NavierStokes.MagneticPeriodicSolution
open Set Filter ProblemStatement MagneticPeriodicFlow MagneticTransport
open MagneticAxisTransfer MagneticAssembledAmplification MagneticSimilarityTrajectory MagneticCoreAmplification
open scoped Topology ContDiff

/-- Precisely the classical regularity used here: joint continuity on the
closed-left domain and joint C¹ in its interior, together with the equations. -/
structure ClassicalSolution (u : VelocityField) (B : MagneticField) (a b Bz0 : ℝ) : Prop where
  continuous : ContinuousOn B (Ico a b ×ˢ univ)
  regular : ∀ t ∈ Ioo a b, ∀ x, ContDiffAt ℝ 1 B (t,x)
  periodic : UnitSpatialPeriodsOn (Ico a b) B
  divergence : ∀ t ∈ Ico a b, ∀ x, spatialDivergence B t x = 0
  induction : IdealInductionOn (Ioo a b) u B
  initial : ∀ x, B (a,x) = Bz0 • coordinateVector 2

theorem Data.classicalSolution (D : Data) (Bz0 : ℝ) :
    ClassicalSolution D.velocity (D.magnetic Bz0) D.a 1 Bz0 :=
  ⟨D.magnetic_continuousOn Bz0, D.magnetic_contDiffAt Bz0,
    D.magnetic_periodic Bz0, D.magnetic_divergence_free Bz0,
    D.magnetic_induction Bz0, D.magnetic_initial Bz0⟩

section Actual
open CorrectionInitialization.ActualPrimary
variable (budget N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (scales : ℕ → ℕ)
    (hsel : MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig budget N0)
      (ActualCandidateAssembly.potentialStages budget N0 hN)
      (ActualCandidateAssembly.directStages budget N0 hN)
      (ActualCandidateAssembly.pressureStages budget N0 hN) scales)

def actualData (a : ℝ) (ha : a < 1) : Data where
  velocity := actualPeriodicVelocity budget N0 hN scales
  a := a
  ha := ha
  smooth := (assembled_velocities_smooth budget N0 hN scales hsel).1
  periodic := MagneticPeriodicCoefficient.actual_periodic budget N0 hN scales
  divergence := MagneticPeriodicCoefficient.actual_divergence budget N0 hN scales hsel

include hsel in
/-- Existence of one classical periodic divergence-free ideal-induction field
for the actual selected assembled velocity, from a constant axial seed. -/
theorem exists_actual_solution (a Bz0 : ℝ) (ha : a < 1) :
    ∃ B : MagneticField, ClassicalSolution (actualPeriodicVelocity budget N0 hN scales) B a 1 Bz0 :=
  ⟨(actualData budget N0 hN scales hsel a ha).magnetic Bz0,
    (actualData budget N0 hN scales hsel a ha).classicalSolution Bz0⟩

variable {Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : NaturalProfile.IsNaturalSolution h nominal.axis.j Λ P0 a0 f U V Pr)

local notation "γ₀" => trajectory h (distinguishedEta nominal.axis.small)
local notation "K₀" => axialExponent nominal.axis.small

/-- Existential amplification for ONE constructed field. The schedule and
natural-solution hypotheses are retained exactly; no coupled MHD or magnetic
energy conclusion is asserted. Physical singular time is still one. -/
theorem exists_actual_amplifying_solution (a Bz0 : ℝ)
    (ha : lateStart budget N0 hN scales hsel hs < a) (ha1 : a < 1) (hseed : Bz0 ≠ 0) :
    ∃ B : MagneticField,
      ClassicalSolution (actualPeriodicVelocity budget N0 hN scales) B a 1 Bz0 ∧
      (∀ t ∈ Ico a 1, B (t,γ₀ t) =
        (Bz0 * ((1-a)/(1-t)) ^ K₀) • coordinateVector 2) ∧
      Tendsto (fun t => ‖B (t,γ₀ t)‖) (𝓝[<] 1) atTop := by
  obtain ⟨B,hB⟩ := exists_actual_solution budget N0 hN scales hsel a Bz0 ha1
  have hg := (lateStart_spec budget N0 hN scales hsel hs).2.1
  have hgc : ContinuousOn γ₀ (Ico a 1) := hg.path_continuous.mono
    (fun _ ht => ⟨ha.trans_le ht.1,ht.2⟩)
  have hBc : ContinuousOn (fun t => B (t,γ₀ t)) (Ico a 1) :=
    hB.continuous.comp (continuousOn_id.prodMk hgc) (fun t ht => ⟨ht,mem_univ _⟩)
  have hBd : ∀ t ∈ Ioo a 1, DifferentiableAt ℝ B (t,γ₀ t) :=
    fun t ht => (hB.regular t ht _).differentiableAt one_ne_zero
  refine ⟨B,hB,?_,?_⟩
  · intro t ht
    exact hg.pure_axial_transport_preterminal ha hB.induction hBc hBd (hB.initial _) ht
  · exact periodic_magnetic_norm_tendsto_atTop budget N0 hN scales hsel hs
      ha ha1 hseed hB.induction hBc hBd (hB.initial _)
end Actual
end NavierStokes.MagneticPeriodicSolution
