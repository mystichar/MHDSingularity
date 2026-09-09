import NavierStokes.ResistivePeriodicHeatGenerator

/-! Positive-time C2 smoothing and the actual heat equation. No all-orders
Banach hierarchy or resistive induction solution is introduced. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set ProblemStatement Filter
open scoped Topology NNReal

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

/-- Two first-derivative gains, with the proved codomain and derivative
commutation adapters, give genuine spatial C2 from C0 input. -/
theorem valueSpatial_contDiff_two {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) :
    ContDiff ℝ 2 (valueSpatial r f).val := by
  let e : ℝ≥0 := r / 2
  have he : 0 < e := div_pos hr (by norm_num)
  have hee : e + e = r := add_halves r
  let g := gainVariance e he f
  let h := spatialC1 e g
  have hv : c1Value h = valueSpatial r f := by
    rw [spatialC1_value, gainVariance_value, valueSpatial_semigroup, hee]
  have hvfun : (c1Value h).val = (valueSpatial r f).val := congrArg Subtype.val hv
  have hD : fderiv ℝ (valueSpatial r f).val = (valueSpatial e (c1Derivative g)).val := by
    funext x
    rw [← hvfun, c1_fderiv h x]
    exact congrArg (fun q : PeriodicValue (Space →L[ℝ] V) => q.val x) (spatialC1_derivative e g)
  have hc1 : ContDiff ℝ 1 (valueSpatial r f).val := by
    rw [← hvfun]
    exact c1_contDiff h
  have hcD : ContDiff ℝ 1 (valueSpatial e (c1Derivative g)).val :=
    c1_contDiff (gainVariance e he (c1Derivative g))
  exact contDiff_succ_iff_fderiv.mpr ⟨hc1.differentiable (by norm_num), by simp, hD ▸ hcD⟩

theorem directional_heat_eq (r : ℝ≥0) (f g : PeriodicC1Value V)
    (hv : c1Value f = valueSpatial r (c1Value g)) (v : Space) :
    directionalField f v = valueSpatial r (directionalField g v) := by
  have he : f = spatialC1 r g := c1Value_injective (hv.trans (spatialC1_value r g).symm)
  subst f
  unfold directionalField
  rw [spatialC1_derivative, valueMap_spatial]

theorem firstField_heat {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) :
    firstField (valueSpatial r f) (valueSpatial_contDiff_two hr f) i = valueSpatial r (firstField f hf i) :=
  directional_heat_eq r _ _ rfl _

theorem secondField_heat {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) :
    secondField (valueSpatial r f) (valueSpatial_contDiff_two hr f) i = valueSpatial r (secondField f hf i) :=
  directional_heat_eq r _ _ (firstField_heat hr f hf i) _

theorem laplacianField_heat {r : ℝ≥0} (hr : 0 < r) (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) :
    laplacianField (valueSpatial r f) (valueSpatial_contDiff_two hr f) = valueSpatial r (laplacianField f hf) := by
  simp only [laplacianField, secondField_heat hr f hf, map_add]

theorem laplacianField_congr {f g : PeriodicValue V} (h : f = g)
    (hf : ContDiff ℝ 2 f.val) (hg : ContDiff ℝ 2 g.val) : laplacianField f hf = laplacianField g hg := by
  subst g
  rfl

/-- A semigroup right generator also determines the two-sided derivative
at positive time. The left limit uses A(s), never a negative heat time. -/
theorem varianceEvolution_hasDerivAt_of_zero (f d : PeriodicValue V)
    (hd : Tendsto (fun h : ℝ => h⁻¹ • (varianceEvolution h f - f)) (𝓝[>] 0) (𝓝 d))
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => varianceEvolution s f) (varianceEvolution r d) r := by
  let q := fun h : ℝ => h⁻¹ • (varianceEvolution h f - f)
  have hright : Tendsto (fun s : ℝ => s - r) (𝓝[>] r) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((show Continuous (fun s : ℝ => s - r) by fun_prop).tendsto r).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < s - r
      exact sub_pos.mpr (show r < s from hs)
  have hleft : Tendsto (fun s : ℝ => r - s) (𝓝[<] r) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((show Continuous (fun s : ℝ => r - s) by fun_prop).tendsto r).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < r - s
      exact sub_pos.mpr (show s < r from hs)
  have hl := varianceEvolution_joint_continuous.continuousAt.tendsto.comp
    (((continuous_id.tendsto r).mono_left nhdsWithin_le_nhds).prodMk_nhds (hd.comp hleft))
  have hu := (varianceEvolution r).continuous.continuousAt.tendsto.comp (hd.comp hright)
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  constructor
  · apply hl.congr'
    have hp : ∀ᶠ s : ℝ in 𝓝[<] r, 0 < s :=
      (show ∀ᶠ s : ℝ in 𝓝 r, 0 < s from Ioi_mem_nhds hr).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hp] with s hs hsp
    have he : varianceEvolution r f = varianceEvolution s (varianceEvolution (r - s) f) := by
      have h := varianceEvolution_semigroup hsp.le (sub_nonneg.mpr hs.le) f
      simpa only [add_sub_cancel] using h
    change varianceEvolution s ((r - s)⁻¹ • (varianceEvolution (r - s) f - f)) =
      (s - r)⁻¹ • (varianceEvolution s f - varianceEvolution r f)
    rw [he, map_smul, map_sub, show s - r = -(r - s) by ring, inv_neg, neg_smul]
    module
  · apply hu.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have he : varianceEvolution s f = varianceEvolution r (varianceEvolution (s - r) f) := by
      have h := varianceEvolution_semigroup hr.le (sub_nonneg.mpr hs.le) f
      simpa only [add_sub_cancel] using h
    change varianceEvolution r ((s - r)⁻¹ • (varianceEvolution (s - r) f - f)) =
      (s - r)⁻¹ • (varianceEvolution s f - varianceEvolution r f)
    rw [he, map_smul, map_sub]

theorem variance_generator_pos_C2 (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => varianceEvolution s f)
      ((1 / 2 : ℝ) • laplacianField (varianceEvolution r f)
        (valueSpatial_contDiff_two (Real.toNNReal_pos.mpr hr) f)) r := by
  have hd := varianceEvolution_hasDerivAt_of_zero f _ (variance_generator_limit f hf) hr
  rw [map_smul] at hd
  have he := laplacianField_heat (Real.toNNReal_pos.mpr hr) f hf
  change laplacianField (varianceEvolution r f) _ = varianceEvolution r (laplacianField f hf) at he
  rw [← he] at hd
  exact hd

/-- Positive-time evolution has a genuine uniform time derivative even
for merely continuous input. Spatial C2 is supplied by the kernel. -/
theorem variance_generator_pos (f : PeriodicValue V) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => varianceEvolution s f)
      ((1 / 2 : ℝ) • laplacianField (varianceEvolution r f)
        (valueSpatial_contDiff_two (Real.toNNReal_pos.mpr hr) f)) r := by
  let e : ℝ := r / 2
  have he : 0 < e := half_pos hr
  let g := varianceEvolution e f
  have hg : ContDiff ℝ 2 g.val := valueSpatial_contDiff_two (Real.toNNReal_pos.mpr he) f
  have hre : 0 < r - e := by dsimp [e]; linarith
  have hd := (variance_generator_pos_C2 g hg hre).scomp_of_eq r ((hasDerivAt_id r).sub_const e) (by simp)
  have hval : varianceEvolution (r - e) g = varianceEvolution r f := by
    have h := varianceEvolution_semigroup hre.le he.le f
    simpa only [sub_add_cancel] using h.symm
  have hlap := laplacianField_congr hval
    (valueSpatial_contDiff_two (Real.toNNReal_pos.mpr hre) g)
    (valueSpatial_contDiff_two (Real.toNNReal_pos.mpr hr) f)
  simp only [one_smul] at hd
  rw [hlap] at hd
  apply hd.congr_of_eventuallyEq
  have hp : ∀ᶠ s : ℝ in 𝓝 r, e < s := Ioi_mem_nhds (by dsimp [e]; linarith)
  filter_upwards [hp] with s hs
  change varianceEvolution s f = varianceEvolution (s - e) (varianceEvolution e f)
  have h := varianceEvolution_semigroup (sub_nonneg.mpr hs.le) he.le f
  simpa only [sub_add_cancel] using h

theorem heat_contDiff_two (eta_m tau : ℝ) (heta : 0 < eta_m) (htau : 0 < tau) (f : PeriodicField) :
    ContDiff ℝ 2 (heat eta_m tau f).val := by
  rw [heat, ← valueSpatial_eq_spatialOperator]
  exact valueSpatial_contDiff_two (Real.toNNReal_pos.mpr (by positivity)) f

/-- Time differentiation in the original periodic uniform Banach space. -/
theorem heat_hasDerivAt (eta_m tau : ℝ) (heta : 0 < eta_m) (htau : 0 < tau) (f : PeriodicField) :
    HasDerivAt (fun s : ℝ => heat eta_m s f)
      (eta_m • laplacianField (heat eta_m tau f) (heat_contDiff_two eta_m tau heta htau f)) tau := by
  have hr : 0 < 2 * eta_m * tau := by positivity
  have hd := (variance_generator_pos f hr).scomp_of_eq tau
    ((hasDerivAt_id tau).const_mul (2 * eta_m)) (by simp)
  have he (s : ℝ) : varianceEvolution (2 * eta_m * s) f = heat eta_m s f :=
    congrArg (fun L => L f) (valueSpatial_eq_spatialOperator _)
  have hlap := laplacianField_congr (he tau)
    (valueSpatial_contDiff_two (Real.toNNReal_pos.mpr hr) f) (heat_contDiff_two eta_m tau heta htau f)
  simp only [mul_one, smul_smul, show 2 * eta_m * (1 / 2 : ℝ) = eta_m by ring] at hd
  rw [hlap] at hd
  change HasDerivAt (fun s : ℝ => varianceEvolution (2 * eta_m * s) f)
    (eta_m • laplacianField (heat eta_m tau f) (heat_contDiff_two eta_m tau heta htau f)) tau at hd
  have hfun : (fun s : ℝ => varianceEvolution (2 * eta_m * s) f) =
      (fun s : ℝ => heat eta_m s f) := funext he
  rw [hfun] at hd
  exact hd

/-- Bounded point evaluation identifies a uniform-space time derivative
with the project's physical temporal derivative. -/
theorem temporalDerivative_of_uniform_derivative {f : ℝ → PeriodicField}
    {d : PeriodicField} {t : ℝ} (hd : HasDerivAt f d t) (x : Space) :
    temporalDerivative (fun p : SpaceTime => (f p.1).val p.2) t x = d.val x := by
  have hx : HasDerivAt (fun s : ℝ => (f s).val x) (d.val x) t :=
    (valueEval x).hasFDerivAt.comp_hasDerivAt t hd
  change deriv (fun s : ℝ => (f s).val x) t = d.val x
  exact hx.deriv

/-- A uniform Laplacian evolution gives the physical pointwise PDE. -/
theorem heat_equation_of_uniform_derivative {f : ℝ → PeriodicField} {eta_m t : ℝ}
    (hf : ContDiff ℝ 2 (f t).val)
    (hd : HasDerivAt f (eta_m • laplacianField (f t) hf) t) (x : Space) :
    temporalDerivative (fun p : SpaceTime => (f p.1).val p.2) t x =
      eta_m • spatialLaplacian (fun p : SpaceTime => (f p.1).val p.2) t x := by
  rw [temporalDerivative_of_uniform_derivative hd x]
  change eta_m • (laplacianField (f t) hf).val x = _
  exact congrArg (fun z : Space => eta_m • z) (laplacianField_eq_spatialLaplacian (f t) hf t x)

/-- The physical heat equation uses precisely the project's temporal
derivative and spatial Laplacian conventions. -/
theorem heat_equation (eta_m tau : ℝ) (heta : 0 < eta_m) (htau : 0 < tau) (f : PeriodicField) (x : Space) :
    temporalDerivative (fun p : SpaceTime => (heat eta_m p.1 f).val p.2) tau x =
      eta_m • spatialLaplacian (fun p : SpaceTime => (heat eta_m p.1 f).val p.2) tau x :=
  heat_equation_of_uniform_derivative (heat_contDiff_two eta_m tau heta htau f)
    (heat_hasDerivAt eta_m tau heta htau f) x

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
