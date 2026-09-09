import NavierStokes.ResistivePeriodicClassical

/-! One preterminal field from the existing compatible mild paths. The
same field restricts to every observation slab. Classical conclusions
below concern constant seeds, for which spatial regularity was proved. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
open Set Filter ProblemStatement PeriodicGaussian PeriodicMild PeriodicTranslation
open MagneticPeriodicMain (budget threshold geometry Selected)
open scoped Topology ContDiff

variable (scales : ℕ → ℕ) (hsel : Selected scales) (a : ℝ) (ha : a < 1)
    (eta_m : ℝ) (heta : 0 < eta_m) (B_a : PeriodicC1)

def slabField (b : ℝ) (hab : a < b) (hb : b < 1) : MagneticField :=
  physicalField a (b-a) (sub_nonneg.mpr hab.le)
    (actualPath scales hsel a b hab hb eta_m heta B_a)

theorem slabField_overlap (b c : ℝ) (hab : a < b) (hac : a < c) (hb : b < 1) (hc : c < 1)
    (t : ℝ) (htb : t ∈ Icc a b) (htc : t ∈ Icc a c) (x : Space) :
    slabField scales hsel a eta_m heta B_a b hab hb (t,x) =
      slabField scales hsel a eta_m heta B_a c hac hc (t,x) := by
  have he := actual_overlap scales hsel a b c hab hac hb hc eta_m heta B_a (t-a)
    (sub_nonneg.mpr htb.1) (sub_le_sub_right htb.2 a) (sub_le_sub_right htc.2 a)
  have h := congrArg (fun B : PeriodicC1 => (c1Value B).val x) he
  simpa only [slabField, physicalField, projIcc_of_mem _
    ⟨sub_nonneg.mpr htb.1,sub_le_sub_right htb.2 a⟩, projIcc_of_mem _
    ⟨sub_nonneg.mpr htc.1,sub_le_sub_right htc.2 a⟩] using! h

private abbrev scheduleData := MagneticPeriodicSolution.actualData budget threshold geometry scales hsel a ha

/-- The diffusivity and initial datum are fixed before the endpoint index
is evaluated. Every finite representative is the existing actualPath. -/
def field (p : SpaceTime) : Space :=
  if ht : p.1 < 1 then
    let D := scheduleData scales hsel a ha
    let n := D.index p.1 ht
    slabField scales hsel a eta_m heta B_a (D.endpoints n)
      (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 p
  else 0

theorem field_eq_slab (b : ℝ) (hab : a < b) (hb : b < 1)
    (t : ℝ) (ht : t ∈ Icc a b) (x : Space) :
    field scales hsel a ha eta_m heta B_a (t,x) =
      slabField scales hsel a eta_m heta B_a b hab hb (t,x) := by
  have ht1 := ht.2.trans_lt hb
  rw [field, dite_eq_left ht1]
  let D := scheduleData scales hsel a ha
  exact slabField_overlap scales hsel a eta_m heta B_a _ b _ hab _ hb t
    ⟨ht.1,(D.index_spec t ht1).le⟩ ht x

theorem field_initial (x : Space) :
    field scales hsel a ha eta_m heta B_a (a,x) = (c1Value B_a).val x := by
  let D := scheduleData scales hsel a ha
  rw [field_eq_slab scales hsel a ha eta_m heta B_a (D.endpoints 0)
    (D.endpoints_spec.2.1 0).1 (D.endpoints_spec.2.1 0).2 a
    ⟨le_rfl,(D.endpoints_spec.2.1 0).1.le⟩]
  exact physicalField_initial (actual_mild scales hsel a _ _ _ eta_m heta B_a) x

theorem field_eventuallyEq (b : ℝ) (hab : a < b) (hb : b < 1)
    (t : ℝ) (ht : t ∈ Ioo a b) (x : Space) :
    field scales hsel a ha eta_m heta B_a =ᶠ[𝓝 (t,x)]
      slabField scales hsel a eta_m heta B_a b hab hb := by
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)] with p hp
  exact field_eq_slab scales hsel a ha eta_m heta B_a b hab hb p.1 ⟨hp.1.le,hp.2.le⟩ p.2

theorem field_continuousOn :
    ContinuousOn (field scales hsel a ha eta_m heta B_a) (Ico a 1 ×ˢ univ) := by
  intro p hp
  let D := scheduleData scales hsel a ha
  obtain ⟨n,hn⟩ := D.exists_endpoint p.1 hp.1.2
  let b := D.endpoints n
  have hab := (D.endpoints_spec.2.1 n).1
  have hb := (D.endpoints_spec.2.1 n).2
  have hc : ContinuousWithinAt (slabField scales hsel a eta_m heta B_a b hab hb)
      (Ico a 1 ×ˢ univ) p := (physicalField_continuous a (b-a) (sub_nonneg.mpr hab.le)
    (actualPath scales hsel a b hab hb eta_m heta B_a)).continuousAt.continuousWithinAt
  apply hc.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [self_mem_nhdsWithin,
    (continuous_fst.continuousWithinAt.tendsto).eventually (Iio_mem_nhds hn)] with q hq hqb
  exact field_eq_slab scales hsel a ha eta_m heta B_a b hab hb q.1 ⟨hq.1.1,hqb.le⟩ q.2

theorem field_periodic : UnitSpatialPeriodsOn (Ico a 1) (field scales hsel a ha eta_m heta B_a) := by
  intro t ht x i
  let D := scheduleData scales hsel a ha
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  rw [field_eq_slab scales hsel a ha eta_m heta B_a (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 t ⟨ht.1,hn.le⟩,
    field_eq_slab scales hsel a ha eta_m heta B_a (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 t ⟨ht.1,hn.le⟩]
  exact physicalField_periodic _ _ _ _ univ t (mem_univ _) x i

omit B_a in
theorem field_constant_spatial_smooth (c : Space) (t : ℝ) (ht : t ∈ Ico a 1) :
    ContDiff ℝ ∞ (fun x => field scales hsel a ha eta_m heta (c1Constant c) (t,x)) := by
  let D := scheduleData scales hsel a ha
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he := funext (field_eq_slab scales hsel a ha eta_m heta (c1Constant c) (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 t ⟨ht.1,hn.le⟩)
  rw [he]
  exact actual_constant_spatial_smooth scales hsel a _ _ _ eta_m heta c t

omit B_a in
theorem field_constant_time_differentiable (c : Space) (t : ℝ) (ht : t ∈ Ioo a 1) (x : Space) :
    DifferentiableAt ℝ (fun s => field scales hsel a ha eta_m heta (c1Constant c) (s,x)) t := by
  let D := scheduleData scales hsel a ha
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he := field_eventuallyEq scales hsel a ha eta_m heta (c1Constant c) (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 t ⟨ht.1,hn⟩ x
  have he' := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto t)
  exact (actual_constant_time_differentiable scales hsel a _ _ _ eta_m heta c t ⟨ht.1,hn⟩ x).congr_of_eventuallyEq he'

omit B_a in
theorem field_constant_induction (c : Space) :
    ResistiveInductionOn eta_m (Ioo a 1)
      (MagneticAxisTransfer.actualPeriodicVelocity budget threshold geometry scales)
      (field scales hsel a ha eta_m heta (c1Constant c)) := by
  intro t ht x
  let D := scheduleData scales hsel a ha
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he := field_eventuallyEq scales hsel a ha eta_m heta (c1Constant c) (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 t ⟨ht.1,hn⟩ x
  have hs := funext (field_eq_slab scales hsel a ha eta_m heta (c1Constant c) (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 t ⟨ht.1.le,hn.le⟩)
  have h := actual_constant_induction scales hsel a (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 eta_m heta c t ⟨ht.1,hn⟩ x
  change temporalDerivative _ _ _ + spatialDerivative _ _ _ _ = spatialDerivative _ _ _ _ + eta_m • spatialLaplacian _ _ _
  rw [show temporalDerivative (field scales hsel a ha eta_m heta (c1Constant c)) t x =
      temporalDerivative (slabField scales hsel a eta_m heta (c1Constant c) (D.endpoints n)
        (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2) t x from
      congrArg (fun L : ℝ →L[ℝ] Space => L 1) (ResidualRegularity.time_fderiv_congr he)]
  simp only [spatialDerivative, spatialLaplacian, hs]
  rw [he.self_of_nhds]
  exact h

/-- A single family is fixed after the velocity, reference time, and seed.
The arbitrary zero extension at nonpositive diffusivity has no PDE claim. -/
def family (c : Space) (eta : ℝ) : MagneticField :=
  if heta : 0 < eta then field scales hsel a ha eta heta (c1Constant c) else 0

theorem family_positive (c : Space) {eta : ℝ} (heta' : 0 < eta) :
    family scales hsel a ha c eta = field scales hsel a ha eta heta' (c1Constant c) := by
  simp only [family, dite_eq_left heta']

end NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
