import NavierStokes.ResistiveMildRightDerivative

/-! The uniform-space mild-to-time-equation bridge. Its C2 and Laplacian
path hypotheses are explicit and are discharged separately for the same
constructed constant-seed mild path. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicMild
open Set Filter MeasureTheory ProblemStatement PeriodicGaussian EulerVolterraConvolution
open scoped Topology BoundedContinuousFunction
private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

theorem integral_of_right_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ} {g q : ℝ → E}
    (hg : ContinuousOn g (Icc 0 T)) (hq : Continuous q)
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (q t) (Ici t) t) :
    ∀ t ∈ Icc 0 T, g t = g 0 + ∫ s in (0 : ℝ)..t, q s := by
  apply eq_of_has_deriv_right_eq hd
  · intro t _
    exact (((hq.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (g 0)).hasDerivWithinAt
  · exact hg
  · exact (show Continuous (fun t => g 0 + ∫ s in (0 : ℝ)..t, q s) from
      (show Differentiable ℝ (fun t => g 0 + ∫ s in (0 : ℝ)..t, q s) from
        fun t => (((hq.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (g 0)).differentiableAt).continuous).continuousOn
  · simp

theorem strong_derivative_of_right_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ} {g q : ℝ → E}
    (hg : ContinuousOn g (Icc 0 T)) (hq : Continuous q)
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (q t) (Ici t) t)
    {t : ℝ} (ht : t ∈ Ioo 0 T) : HasDerivAt g (q t) t := by
  have hi := (((hq.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (g 0))
  apply hi.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact integral_of_right_derivative hg hq hd s ⟨hs.1.le,hs.2.le⟩

def valueEvolution {T : ℝ} (hT : 0 ≤ T) (z : Path T) (t : ℝ) : PeriodicField :=
  c1Inclusion (extendPath T hT z t)

theorem valueEvolution_continuous {T : ℝ} (hT : 0 ≤ T) (z : Path T) :
    Continuous (valueEvolution hT z) :=
  c1Inclusion.continuous.comp (extendPath_continuous T hT z)

theorem mild_right_derivative {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z)
    (hC2 : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ 2 (c1Inclusion (z t)).val)
    (L : C(Icc (0 : ℝ) T,PeriodicField))
    (hL : ∀ t, L t = laplacianField (c1Inclusion (z t)) (hC2 t))
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (valueEvolution hT z)
      (eta_m • extendPath T hT L t + extendPath T hT (valueSource S z) t) (Ici t) t := by
  let tt : Icc (0 : ℝ) T := ⟨t,ht.1,ht.2.le⟩
  let f := valueSource S z
  let w := fun s => heat eta_m s (c1Inclusion B_a) + valueDuhamel eta_m T hT f s
  have he : w t = c1Inclusion (z tt) := (mild_value_equation hz tt).symm
  have hw : ContDiff ℝ 2 (w t).val := he ▸ hC2 tt
  have hd := value_heat_right_derivative eta_m heta.le T hT f (c1Inclusion B_a) t ht.1 hw
  have hl : laplacianField (w t) hw = extendPath T hT L t := by
    rw [laplacianField_congr he hw (hC2 tt)]
    change _ = L (projIcc 0 T hT t)
    rw [projIcc_of_mem hT tt.property, ← hL]
  change uniformLaplacian (w t) hw = extendPath T hT L t at hl
  change HasDerivWithinAt w (eta_m • uniformLaplacian (w t) hw + extendPath T hT f t) (Ici t) t at hd
  rw [hl] at hd
  refine hd.congr_of_eventuallyEq ?_ ?_
  · have hu : ∀ᶠ s : ℝ in 𝓝[Ici t] t, s < T :=
      nhdsWithin_le_nhds (Iio_mem_nhds ht.2)
    filter_upwards [self_mem_nhdsWithin, hu] with s hs hsT
    have hs0 : 0 ≤ s := ht.1.trans hs
    have hm := mild_value_equation hz (⟨s,hs0,hsT.le⟩ : Icc (0 : ℝ) T)
    simpa only [valueEvolution, extendPath, projIcc_of_mem hT ⟨hs0,hsT.le⟩] using! hm
  · simpa only [valueEvolution, extendPath, projIcc_of_mem hT ⟨ht.1,ht.2.le⟩, tt, w, f] using!
      mild_value_equation hz tt

/-- A continuous path of actual Laplacians upgrades the existing mild
path to a strong uniform-space time derivative on the forward interior. -/
theorem mild_hasDerivAt_of_laplacianPath {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z)
    (hC2 : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ 2 (c1Inclusion (z t)).val)
    (L : C(Icc (0 : ℝ) T,PeriodicField))
    (hL : ∀ t, L t = laplacianField (c1Inclusion (z t)) (hC2 t))
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (valueEvolution hT z)
      (eta_m • extendPath T hT L t + extendPath T hT (valueSource S z) t) t :=
  strong_derivative_of_right_derivative (valueEvolution_continuous hT z).continuousOn
    (((extendPath_continuous T hT L).const_smul eta_m).add
      (extendPath_continuous T hT (valueSource S z)))
    (mild_right_derivative hz hC2 L hL) ht

/-- The endpoint assertion is a derivative within the forward slab,
not a derivative of its clamped extension on a backward interval. -/
theorem mild_hasDerivWithinAt_of_laplacianPath {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z)
    (hC2 : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ 2 (c1Inclusion (z t)).val)
    (L : C(Icc (0 : ℝ) T,PeriodicField))
    (hL : ∀ t, L t = laplacianField (c1Inclusion (z t)) (hC2 t))
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (valueEvolution hT z)
      (eta_m • L t + valueSource S z t) (Icc (0 : ℝ) T) t := by
  let q := fun s => eta_m • extendPath T hT L s + extendPath T hT (valueSource S z) s
  have hq : Continuous q := ((extendPath_continuous T hT L).const_smul eta_m).add
    (extendPath_continuous T hT (valueSource S z))
  have he := integral_of_right_derivative (valueEvolution_continuous hT z).continuousOn hq
    (mild_right_derivative hz hC2 L hL)
  have hi := (((hq.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (valueEvolution hT z 0)).hasDerivWithinAt (s := Icc (0 : ℝ) T)
  have hd := hi.congr_mono he (he t t.property) (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T)
  simpa only [q,extendPath,projIcc_of_mem hT t.property] using! hd

end NavierStokes.ResistiveMagnetic.PeriodicMild
