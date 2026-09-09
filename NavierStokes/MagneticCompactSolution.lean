import NavierStokes.MagneticCompactSupport
import Mathlib.Topology.Order.IsLUB

/-! One preterminal magnetic field obtained by compatible finite-slab
construction. No uniform bound at the terminal time is used. -/
noncomputable section
namespace NavierStokes.MagneticCompactSolution
open Set Filter ProblemStatement MagneticCompactFlow
open scoped Topology ContDiff ENNReal
private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance

structure Data where
  velocity : VelocityField
  a : ℝ
  ha : a < 1
  smooth : ContDiffOn ℝ ∞ velocity (Iio (1 : ℝ) ×ˢ univ)
  supportSet : Set Space
  support_compact : IsCompact supportSet
  supported : ∀ t < 1, tsupport (fun x => velocity (t,x)) ⊆ supportSet
  divergence : ∀ t ∈ Ico a 1, ∀ x, spatialDivergence velocity t x = 0

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
  supportSet := D.supportSet
  support_compact := D.support_compact
  supported := D.supported

theorem exists_endpoint (t : ℝ) (ht : t < 1) : ∃ n, t < D.endpoints n :=
  (D.endpoints_spec.2.2.eventually (Ioi_mem_nhds ht)).exists

def index (t : ℝ) (ht : t < 1) : ℕ := (D.exists_endpoint t ht).choose

theorem index_spec (t : ℝ) (ht : t < 1) : t < D.endpoints (D.index t ht) :=
  (D.exists_endpoint t ht).choose_spec

/-- A single field is chosen once on the entire preterminal domain. -/
def magnetic (W : Space → Space) (z : SpaceTime) : Space :=
  if ht : z.1 < 1 then (D.slab (D.index z.1 ht)).magnetic W z else 0

theorem magnetic_eq_slab (W : Space → Space) (t : ℝ) (n : ℕ) (ht : t ∈ Icc D.a (D.endpoints n))
    (x : Space) : D.magnetic W (t,x) = (D.slab n).magnetic W (t,x) := by
  have ht1 : t < 1 := ht.2.trans_lt (D.endpoints_spec.2.1 n).2
  rw [magnetic, dite_eq_left ht1]
  exact (D.slab (D.index t ht1)).magnetic_overlap (D.slab n) rfl rfl W t
    ⟨ht.1,(D.index_spec t ht1).le⟩ ht x

theorem magnetic_initial (W : Space → Space) (x : Space) :
    D.magnetic W (D.a,x) = W x := by
  rw [D.magnetic_eq_slab W D.a 0 ⟨le_rfl,(D.endpoints_spec.2.1 0).1.le⟩]
  exact (D.slab 0).magnetic_initial W x

theorem magnetic_eventuallyEq (W : Space → Space) (t : ℝ) (ht : t ∈ Ioo D.a 1) (n : ℕ)
    (hn : t < D.endpoints n) (x : Space) :
    D.magnetic W =ᶠ[𝓝 (t,x)] (D.slab n).magnetic W := by
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 hn)] with z hz
  exact D.magnetic_eq_slab W z.1 n ⟨hz.1.le,hz.2.le⟩ z.2

theorem magnetic_continuousOn (W : Space → Space) (hW : Continuous W) :
    ContinuousOn (D.magnetic W) (Ico D.a 1 ×ˢ univ) := by
  intro z hz
  obtain ⟨n,hn⟩ := D.exists_endpoint z.1 hz.1.2
  have hc := (D.slab n).magnetic_continuousOn W hW z ⟨⟨hz.1.1,hn.le⟩,mem_univ _⟩
  have he : D.magnetic W =ᶠ[𝓝[Ico D.a 1 ×ˢ univ] z] (D.slab n).magnetic W := by
    filter_upwards [self_mem_nhdsWithin,
      (continuous_fst.continuousWithinAt.tendsto).eventually (Iio_mem_nhds hn)] with w hw hwn
    exact D.magnetic_eq_slab W w.1 n ⟨hw.1.1,hwn.le⟩ w.2
  have hm : (Icc D.a (D.endpoints n) ×ˢ (univ : Set Space)) ∈
      𝓝[Ico D.a 1 ×ˢ univ] z := by
    filter_upwards [self_mem_nhdsWithin,
      (continuous_fst.continuousWithinAt.tendsto).eventually (Iio_mem_nhds hn)] with w hw hwn
    exact ⟨⟨hw.1.1,hwn.le⟩,mem_univ _⟩
  exact (hc.mono_of_mem_nhdsWithin hm).congr_of_eventuallyEq_of_mem he hz

theorem magnetic_contDiffAt (W : Space → Space) (hW : ContDiff ℝ ∞ W) (t : ℝ) (ht : t ∈ Ioo D.a 1) (x : Space) :
    ContDiffAt ℝ 1 (D.magnetic W) (t,x) := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  exact ((D.slab n).magnetic_contDiffAt W hW t ⟨ht.1,hn⟩ x).congr_of_eventuallyEq
    (D.magnetic_eventuallyEq W t ht n hn x)

/-- All finite spatial orders at each preterminal time; this is not a
claim of joint C-infinity regularity. -/
theorem magnetic_spatial_smooth (W : Space → Space) (hW : ContDiff ℝ ∞ W) (t : ℝ) (ht : t ∈ Ico D.a 1) :
    ContDiff ℝ ∞ (fun x => D.magnetic W (t,x)) := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he : (fun x => D.magnetic W (t,x)) = (fun x => (D.slab n).magnetic W (t,x)) :=
    funext (D.magnetic_eq_slab W t n ⟨ht.1,hn.le⟩)
  rw [he]
  exact (D.slab n).magnetic_spatial_smooth W hW t ⟨ht.1,hn.le⟩

theorem magnetic_divergence_free (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (hdivW : ∀ x, ∑ i : Fin 3, (fderiv ℝ W x (coordinateVector i)) i = 0) (t : ℝ) (ht : t ∈ Ico D.a 1) (x : Space) :
    spatialDivergence (D.magnetic W) t x = 0 := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he : (fun y => D.magnetic W (t,y)) = (fun y => (D.slab n).magnetic W (t,y)) :=
    funext (D.magnetic_eq_slab W t n ⟨ht.1,hn.le⟩)
  change (∑ i : Fin 3, (fderiv ℝ (fun y => D.magnetic W (t,y)) x (coordinateVector i)) i) = 0
  rw [he]
  exact (D.slab n).magnetic_divergence_free
    (fun s hs y => D.divergence s ⟨hs.1,hs.2.trans_lt (D.endpoints_spec.2.1 n).2⟩ y)
    W hW hdivW t ⟨ht.1,hn.le⟩ x

theorem magnetic_induction (W : Space → Space) (hW : ContDiff ℝ ∞ W) :
    MagneticTransport.IdealInductionOn (Ioo D.a 1) D.velocity (D.magnetic W) := by
  intro t ht x
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he := D.magnetic_eventuallyEq W t ht n hn x
  have h := (D.slab n).magnetic_induction W hW t ⟨ht.1,hn⟩ x
  change temporalDerivative _ _ _ + spatialDerivative _ _ _ _ = spatialDerivative _ _ _ _
  rw [show temporalDerivative (D.magnetic W) t x =
      temporalDerivative ((D.slab n).magnetic W) t x from
    congrArg (fun L : ℝ →L[ℝ] Space => L 1) (ResidualRegularity.time_fderiv_congr he),
    show spatialDerivative (D.magnetic W) t x = spatialDerivative ((D.slab n).magnetic W) t x from
      ResidualRegularity.space_fderiv_congr he, he.self_of_nhds]
  exact h

/-- Actual transported support on every member of the cofinal family. -/
theorem transported_support (W : Space → Space) (hW : HasCompactSupport W)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc D.a (D.endpoints n)) :
    tsupport (fun x => D.magnetic W (t,x)) ⊆ (D.slab n).Phi t '' tsupport W := by
  rw [show (fun x => D.magnetic W (t,x)) = (fun x => (D.slab n).magnetic W (t,x)) from
    funext (D.magnetic_eq_slab W t n ht)]
  exact (D.slab n).transported_support W hW t

theorem uniform_support (W : Space → Space) (hW : HasCompactSupport W)
    (b : ℝ) (hb : b ∈ Ico D.a 1) : ∃ K : Set Space, IsCompact K ∧
      ∀ t ∈ Icc D.a b, tsupport (fun x => D.magnetic W (t,x)) ⊆ K := by
  obtain ⟨n,hn⟩ := D.exists_endpoint b hb.2
  refine ⟨(D.slab n).supportTube W,(D.slab n).supportTube_compact W hW,?_⟩
  intro t ht
  have ht' : t ∈ Icc D.a (D.endpoints n) := ⟨ht.1,ht.2.trans hn.le⟩
  rw [show (fun x => D.magnetic W (t,x)) = (fun x => (D.slab n).magnetic W (t,x)) from
    funext (D.magnetic_eq_slab W t n ht')]
  exact (D.slab n).magnetic_supported_tube W hW t ht'

theorem slab_bounds (W : Space → Space) (hc : Continuous W) (hW : HasCompactSupport W)
    (b : ℝ) (hb : b ∈ Ico D.a 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E : ℝ≥0∞, E < ⊤ ∧ ∀ t ∈ Icc D.a b,
      (∀ x, ‖D.magnetic W (t,x)‖ ≤ C) ∧ MagneticPeriodicNorms.supNorm (D.magnetic W) t ≤ C ∧
      MagneticCompactFlow.energy (D.magnetic W) t ≤ E ∧ MagneticCompactFlow.energy (D.magnetic W) t < ⊤ := by
  obtain ⟨K,hK,hs⟩ := D.uniform_support W hW b hb
  exact MagneticCompactFlow.compact_slab_bounds hK
    ((D.magnetic_continuousOn W hc).mono (prod_subset_prod_left
      (fun t ht => ⟨ht.1,ht.2.trans_lt hb.2⟩)))
    (fun t ht x hx => image_eq_zero_of_notMem_tsupport (f := fun y => D.magnetic W (t,y))
      (fun hm => hx (hs t ht hm)))

end Data
end NavierStokes.MagneticCompactSolution
