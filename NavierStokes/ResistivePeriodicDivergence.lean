import NavierStokes.ResistivePeriodicSolenoidal

/-! Constant-seed solenoidality, propagated by the forward scalar maximum
principle, and inherited by the one compatible preterminal field. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace NavierStokes.ResistiveMagnetic.PeriodicTranslation
open Set Filter ProblemStatement PeriodicGaussian PeriodicSource PeriodicMild
open EulerVolterraConvolution
open scoped Topology ContDiff
private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

/-- No time derivative or PDE before the initial time is required. -/
theorem constant_mild_divergence_free {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    (hTpos : 0 < T) (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x+coordinateVector i) = A.field t x)
    (hdiv : ∀ t x, spatialDivergence (fun p : SpaceTime => A.field t p.2) 0 x = 0)
    (c : Space) (z : Path T)
    (hz : Mild T hT eta_m heta
      (sourcePaths (periodicPath A hp) (periodicPath A.derivative (derivative_periodic A hp))) (c1Constant c) z)
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) : delta hT z (t,x) = 0 := by
  have hs := constant_seed_translation_contDiff T hT eta_m heta A hp c z hz
  let u : VelocityField := fun p => A.field (projIcc 0 T hT p.1) p.2
  have htd (s : ℝ) (hs : s ∈ Ioo 0 T) (y : Space) :
      DifferentiableAt ℝ (fun r => delta hT z (r,y)) s :=
    (delta_hasDerivAt A hp c z hz ⟨s,hs.1.le,hs.2.le⟩ hs y).differentiableAt
  have hxd (s : ℝ) : ContDiff ℝ 2 (fun y => delta hT z (s,y)) :=
    (delta_spatial_smooth hT z hs s).of_le (by simp)
  have hi (y : Space) : delta hT z (0,y) = 0 := by
    have he : (fun y => physicalField 0 T hT z (0,y)) = fun _ => c :=
      funext (fun y => physicalField_initial hz y)
    simp only [delta,spatialDivergence,spatialDerivative,he]
    rw [(hasFDerivAt_const c y).fderiv]
    simp
  have hn := Slice.nonpos (u := u) hTpos heta.le (delta_continuous hT z).continuousOn
    (fun s _ => delta_periodic hT z s (mem_univ _)) htd (fun s _ => hxd s)
    (fun s hs y => (delta_operator_zero A hp hdiv c z hz s hs y).le)
    (fun y => (hi y).le) ht x
  have hm := Slice.nonpos (q := fun p => -delta hT z p) (u := u) hTpos heta.le
    (delta_continuous hT z).neg.continuousOn
    (fun s _ y i => congrArg Neg.neg (delta_periodic hT z s (mem_univ _) y i))
    (fun s hs y => (htd s hs y).neg) (fun s _ => (hxd s).neg)
    (fun s hs y => by
      have he := Slice.operator_affine (q := delta hT z) (u := u) (eta_m := eta_m)
        (hasDerivAt_const s (-1 : ℝ)) (hasDerivAt_const s (0 : ℝ)) (htd s hs y) (hxd s)
      have hzero : Slice.operator u eta_m (delta hT z) s y = 0 :=
        delta_operator_zero A hp hdiv c z hz s hs y
      simpa only [neg_one_mul,add_zero,zero_mul,hzero,neg_zero] using he.le)
    (fun y => by simp only [hi,neg_zero,le_refl]) ht x
  exact le_antisymm hn (neg_nonpos.mp hm)

open MagneticPeriodicMain (budget threshold geometry Selected)

/-- Divergence preservation for the same actual finite-slab constant-seed
path. The arbitrary constant direction is allowed; amplification below
will still use only the axial direction. -/
theorem actual_constant_divergence_free (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hab : a < b) (hb : b < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space)
    (t : ℝ) (ht : t ∈ Icc a b) (x : Space) :
    spatialDivergence (physicalField a (b-a) (sub_nonneg.mpr hab.le)
      (actualPath scales hsel a b hab hb eta_m heta (c1Constant c))) t x = 0 := by
  let A := MagneticPeriodicCoefficient.actualOnSlab budget threshold geometry scales hsel a b hb
  have hp : ∀ s x i, A.field s (x+coordinateVector i) = A.field s x :=
    fun s x i => MagneticPeriodicCoefficient.actual_periodic budget threshold geometry scales
      (a+s) (by have hh := s.property.2; change a+s.val < 1; linarith) x i
  have hd : ∀ s x, spatialDivergence (fun p : SpaceTime => A.field s p.2) 0 x = 0 := by
    intro s y
    exact MagneticPeriodicCoefficient.actual_divergence budget threshold geometry scales hsel
      (a+s) (by have hh := s.property.2; change a+s.val < 1; linarith) y
  have h := constant_mild_divergence_free (sub_pos.mpr hab) A hp hd c _
    (actual_mild scales hsel a b hab hb eta_m heta (c1Constant c)) (t-a)
    ⟨sub_nonneg.mpr ht.1,sub_le_sub_right ht.2 a⟩ x
  simpa only [delta,spatialDivergence,spatialDerivative,physicalField,sub_zero] using! h

end NavierStokes.ResistiveMagnetic.PeriodicTranslation

namespace NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
open Set ProblemStatement PeriodicGaussian PeriodicMild PeriodicTranslation
open MagneticPeriodicMain (budget threshold geometry Selected)

theorem field_constant_divergence_free (scales : ℕ → ℕ) (hsel : Selected scales)
    (a : ℝ) (ha : a < 1) (eta_m : ℝ) (heta : 0 < eta_m) (c : Space)
    (t : ℝ) (ht : t ∈ Ico a 1) (x : Space) :
    spatialDivergence (field scales hsel a ha eta_m heta (c1Constant c)) t x = 0 := by
  let D := MagneticPeriodicSolution.actualData budget threshold geometry scales hsel a ha
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have he := funext (field_eq_slab scales hsel a ha eta_m heta (c1Constant c) (D.endpoints n)
    (D.endpoints_spec.2.1 n).1 (D.endpoints_spec.2.1 n).2 t ⟨ht.1,hn.le⟩)
  unfold spatialDivergence spatialDerivative
  rw [he]
  exact actual_constant_divergence_free scales hsel a _ _ _ eta_m heta c t ⟨ht.1,hn.le⟩ x

theorem family_divergence_free (scales : ℕ → ℕ) (hsel : Selected scales)
    (a : ℝ) (ha : a < 1) (c : Space) (eta_m : ℝ) (heta : 0 < eta_m)
    (t : ℝ) (ht : t ∈ Ico a 1) (x : Space) :
    spatialDivergence (family scales hsel a ha c eta_m) t x = 0 := by
  rw [family_positive scales hsel a ha c heta]
  exact field_constant_divergence_free scales hsel a ha eta_m heta c t ht x

end NavierStokes.ResistiveMagnetic.PeriodicClassicalGlue
