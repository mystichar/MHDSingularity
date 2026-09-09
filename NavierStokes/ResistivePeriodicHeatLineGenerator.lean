import NavierStokes.ResistivePeriodicHeatKernel
import NavierStokes.ResistivePeriodicTranslationDerivative
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! The variance generator of a physical directional Gaussian is one half
of its second strong translation derivative. The Gaussian calculus follows
the inherited directional proof, on the physical periodic uniform space. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement Filter
open EulerGaussianCylinderHeat
open scoped Topology NNReal
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

abbrev translationOrbit (v : Space) (f : PeriodicValue V) (s : ℝ) : PeriodicValue V :=
  translate (s • v) f

theorem translationOrbit_continuous (v : Space) (f : PeriodicValue V) :
    Continuous (translationOrbit v f) :=
  (translate_continuous f).comp (continuous_id.smul continuous_const)

theorem translationOrbit_norm (v : Space) (f : PeriodicValue V) (s : ℝ) :
    ‖translationOrbit v f s‖ = ‖f‖ := translate_norm _ f

theorem translationOrbit_hasDerivAt_all (v : Space) (f g : PeriodicValue V)
    (h : HasDerivAt (translationOrbit v f) g 0) (s : ℝ) :
    HasDerivAt (translationOrbit v f) (translationOrbit v g s) s := by
  have hd := translate_hasFDerivAt_all (ContinuousLinearMap.toSpanSingleton ℝ v) f
    (ContinuousLinearMap.toSpanSingleton ℝ g) h.hasFDerivAt s
  simpa using! hd.hasDerivAt

theorem valueLine_derivative_identity (v : Space) {r : ℝ≥0} (hr : r ≠ 0)
    (f g : PeriodicValue V) (hD : HasDerivAt (translationOrbit v f) g 0) :
    valueLine v r g = valueLineDerivative v r f := by
  have hp := valueKernel_integrable v f (gaussianPDFReal 0 r) (integrable_gaussianPDFReal 0 r)
  have hpg := valueKernel_integrable v g (gaussianPDFReal 0 r) (integrable_gaussianPDFReal 0 r)
  have hdp := valueKernel_integrable v f (fun x => -(x / (r : ℝ)) * gaussianPDFReal 0 r x)
    ((gaussianMomentKernel_integrable r).neg.congr (Eventually.of_forall (fun x => by
      simp only [Pi.neg_apply]; ring)))
  have hIBP := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (fun x _ => gaussianPDF_hasDerivAt r x)
    (fun x _ => translationOrbit_hasDerivAt_all v f g hD x) hpg hdp hp
  change (∫ x, gaussianPDFReal 0 r x • translationOrbit v g x) =
    -(∫ x, (-(x / (r : ℝ)) * gaussianPDFReal 0 r x) • translationOrbit v f x) at hIBP
  change (∫ x, translationOrbit v g x ∂gaussianReal 0 r) =
    (r : ℝ)⁻¹ • ∫ x, x • translationOrbit v f x ∂gaussianReal 0 r
  rw [integral_gaussianReal_eq_integral_smul hr, hIBP,
    integral_gaussianReal_eq_integral_smul hr, ← integral_smul, ← integral_neg]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change -((-(x / (r : ℝ)) * gaussianPDFReal 0 r x) • translationOrbit v f x) =
    (r : ℝ)⁻¹ • (gaussianPDFReal 0 r x • (x • translationOrbit v f x))
  rw [← neg_smul]
  simp only [smul_smul]
  congr 1
  ring

/-- A continuous real-parameter extension of the Gaussian average, constant for negative variance. -/
def realValueLine (a : Space) (t : ℝ) (f : PeriodicValue V) : PeriodicValue V :=
  ∫ x : ℝ, translationOrbit a f (Real.sqrt t * x) ∂gaussianReal 0 1

theorem realValueLine_eq (a : Space) {t : ℝ} (ht : 0 ≤ t) (f : PeriodicValue V) :
    realValueLine a t f = valueLine a ⟨t, ht⟩ f :=
  (valueLine_standard a ⟨t, ht⟩ f).symm

@[simp] theorem realValueLine_zero (a : Space) (f : PeriodicValue V) : realValueLine a 0 f = f := by
  rw [realValueLine_eq a le_rfl]
  exact valueLine_zero a f

theorem realValueLine_continuous (a : Space) (f : PeriodicValue V) :
    Continuous (fun t : ℝ => realValueLine a t f) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro t
    exact ((translationOrbit_continuous a f).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (fun x => (translationOrbit_norm a f _).le)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x =>
      (translationOrbit_continuous a f).comp (Real.continuous_sqrt.mul_const x))

/-- The chain-rule derivative of a scaled orbit, before Gaussian integration. -/
theorem scaledOrbit_hasDerivAt (a : Space) (f g : PeriodicValue V)
    (hD : HasDerivAt (translationOrbit a f) g 0) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => translationOrbit a f (Real.sqrt s * x))
      ((x / (2 * Real.sqrt t)) • translationOrbit a g (Real.sqrt t * x)) t := by
  have ho := translationOrbit_hasDerivAt_all a f g hD (Real.sqrt t * x)
  have hs := (Real.hasDerivAt_sqrt ht.ne').mul_const x
  have h := ho.scomp t hs
  convert! h using 1
  change (x / (2 * Real.sqrt t)) • translationOrbit a g (Real.sqrt t * x) =
    (1 / (2 * Real.sqrt t) * x) • translationOrbit a g (Real.sqrt t * x)
  congr 1
  ring

/-- Differentiation of the Gaussian average at positive variance is justified by an integrable first moment. -/
theorem realValueLine_hasDerivAt_moment (a : Space) (f g : PeriodicValue V)
    (hD : HasDerivAt (translationOrbit a f) g 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realValueLine a s f)
      (∫ x : ℝ, (x / (2 * Real.sqrt t)) • translationOrbit a g (Real.sqrt t * x) ∂gaussianReal 0 1) t := by
  let F : ℝ → ℝ → PeriodicValue V := fun s x => translationOrbit a f (Real.sqrt s * x)
  let F' : ℝ → ℝ → PeriodicValue V := fun s x => (x / (2 * Real.sqrt s)) • translationOrbit a g (Real.sqrt s * x)
  let B : ℝ → ℝ := fun x => (‖x‖ / (2 * Real.sqrt (t/2))) * ‖g‖
  have hhalf : 0 < t/2 := by linarith
  have hder (x s : ℝ) (hs : s ∈ Set.Ioi (t/2)) : HasDerivAt (fun r => F r x) (F' s x) s :=
    scaledOrbit_hasDerivAt a f g hD x s (hhalf.trans hs)
  have hbound : ∀ x s : ℝ, s ∈ Set.Ioi (t/2) → ‖F' s x‖ ≤ B x := by
    intro x s hs
    have hspos : 0 < s := hhalf.trans hs
    change ‖(x / (2 * Real.sqrt s)) • translationOrbit a g (Real.sqrt s * x)‖ ≤
      (‖x‖ / (2 * Real.sqrt (t / 2))) * ‖g‖
    rw [norm_smul, translationOrbit_norm, Real.norm_eq_abs, abs_div,
      abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hspos))]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (abs_nonneg x)
        (mul_pos (by norm_num) (Real.sqrt_pos.mpr hhalf))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs.le) (by norm_num))) (norm_nonneg g)
  have hFint : Integrable (F t) (gaussianReal 0 1) :=
    Integrable.of_bound ((translationOrbit_continuous a f).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      ‖f‖ (Filter.Eventually.of_forall (fun x => (translationOrbit_norm a f _).le))
  have hBint : Integrable B (gaussianReal 0 1) :=
    ((gaussianId_integrable 1).norm.div_const (2 * Real.sqrt (t/2))).mul_const ‖g‖
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B) (Ioi_mem_nhds (by linarith : t/2 < t))
    (Filter.Eventually.of_forall (fun s =>
      ((translationOrbit_continuous a f).comp (continuous_const.mul continuous_id)).aestronglyMeasurable))
    hFint
    (((continuous_id.div_const (2 * Real.sqrt t)).smul
      ((translationOrbit_continuous a g).comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound) hBint (Filter.Eventually.of_forall hder)
  exact h.2

/-- Gaussian scaling rewrites the variance derivative as one half of the averaged orbit derivative. -/
theorem varianceMoment_eq_half_derivative (a : Space) {t : ℝ} (ht : 0 < t) (g : PeriodicValue V) :
    (∫ x : ℝ, (x / (2 * Real.sqrt t)) • translationOrbit a g (Real.sqrt t * x) ∂gaussianReal 0 1) =
      (1/2 : ℝ) • valueLineDerivative a ⟨t, ht.le⟩ g := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hmap : Measure.map (fun x => Real.sqrt t * x) (gaussianReal 0 1) = gaussianReal 0 ⟨t, ht.le⟩ := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt t)
    have he : NNReal.mk (Real.sqrt t ^ 2) (sq_nonneg _) * 1 = (⟨t, ht.le⟩ : ℝ≥0) := by
      apply Subtype.ext
      change Real.sqrt t ^ 2 * 1 = t
      rw [mul_one, Real.sq_sqrt ht.le]
    rw [mul_zero, he] at h
    exact h
  change (∫ x : ℝ, (x / (2 * Real.sqrt t)) • translationOrbit a g (Real.sqrt t * x) ∂gaussianReal 0 1) =
    (1/2 : ℝ) • (t⁻¹ • ∫ x : ℝ, x • translationOrbit a g x ∂gaussianReal 0 ⟨t, ht.le⟩)
  have hm := integral_map_of_stronglyMeasurable
    (μ := gaussianReal 0 1) (φ := fun x : ℝ => Real.sqrt t * x)
    (f := fun x : ℝ => x • translationOrbit a g x) (by fun_prop)
    ((continuous_id.smul (translationOrbit_continuous a g)).stronglyMeasurable)
  rw [← hmap, hm, ← integral_smul, ← integral_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (x / (2 * Real.sqrt t)) • translationOrbit a g (Real.sqrt t * x) =
    (1/2 : ℝ) • t⁻¹ • (Real.sqrt t * x) • translationOrbit a g (Real.sqrt t * x)
  simp only [smul_smul]
  congr 1
  field_simp
  rw [Real.sq_sqrt ht.le]

/-- At every positive variance, the generator is one half of the genuine second translation derivative. -/
theorem realValueLine_generator_pos (a : Space) (f g h : PeriodicValue V)
    (hD : HasDerivAt (translationOrbit a f) g 0)
    (hDD : HasDerivAt (translationOrbit a g) h 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realValueLine a s f) ((1/2 : ℝ) • realValueLine a t h) t := by
  have hd := realValueLine_hasDerivAt_moment a f g hD ht
  rw [varianceMoment_eq_half_derivative a ht g,
    ← valueLine_derivative_identity a (show (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 by intro hz; have hzR := congrArg (fun z : ℝ≥0 => (z : ℝ)) hz; exact ht.ne' hzR) g h hDD,
    ← realValueLine_eq a ht.le h] at hd
  exact hd

/-- The generator formula also holds as a genuine right derivative at zero variance. -/
theorem realValueLine_generator_zero (a : Space) (f g h : PeriodicValue V)
    (hD : HasDerivAt (translationOrbit a f) g 0)
    (hDD : HasDerivAt (translationOrbit a g) h 0) :
    HasDerivWithinAt (fun s => realValueLine a s f) ((1/2 : ℝ) • h) (Set.Ici 0) 0 := by
  have hlim : Filter.Tendsto (fun s => (1/2 : ℝ) • realValueLine a s h)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1/2 : ℝ) • h)) := by
    have hc : ContinuousAt (fun s => (1/2 : ℝ) • realValueLine a s h) 0 :=
      ((realValueLine_continuous a h).const_smul (1/2 : ℝ)).continuousAt
    simpa only [realValueLine_zero] using (hc.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun t ht => (realValueLine_generator_pos a f g h hD hDD ht).differentiableAt.differentiableWithinAt)
    (realValueLine_continuous a f).continuousAt.continuousWithinAt self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realValueLine_generator_pos a f g h hD hDD ht).deriv.symm


end NavierStokes.ResistiveMagnetic.PeriodicGaussian
