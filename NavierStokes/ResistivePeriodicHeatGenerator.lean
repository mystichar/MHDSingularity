import NavierStokes.ResistivePeriodicHeatLineGenerator
import NavierStokes.ResistivePeriodicHeatDerivatives
import NavierStokes.ResistivePeriodicHeatVolterra

/-! The generator of the actual physical periodic heat operators, in the
uniform function-space norm, identified with the spatial Laplacian. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement Filter
open scoped Topology NNReal

private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

def firstField (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) : PeriodicValue V :=
  directionalField (c1OfContDiff f (hf.of_le (by norm_num))) (coordinateVector i)

theorem firstField_contDiff (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) :
    ContDiff ℝ 1 (firstField f hf i).val :=
  (ContinuousLinearMap.apply ℝ V (coordinateVector i)).contDiff.comp
    (hf.fderiv_right (by norm_num))

def secondField (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) : PeriodicValue V :=
  directionalField (c1OfContDiff (firstField f hf i) (firstField_contDiff f hf i)) (coordinateVector i)

def laplacianField (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) : PeriodicValue V :=
  secondField f hf 0 + secondField f hf 1 + secondField f hf 2

@[simp] theorem firstField_apply (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) (x : Space) :
    (firstField f hf i).val x = fderiv ℝ f.val x (coordinateVector i) := rfl

@[simp] theorem secondField_apply (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) (x : Space) :
    (secondField f hf i).val x = fderiv ℝ (fun y => fderiv ℝ f.val y (coordinateVector i)) x
      (coordinateVector i) := rfl

/-- Equality with the existing spatial Laplacian convention on R3. -/
theorem laplacianField_eq_spatialLaplacian (f : PeriodicField) (hf : ContDiff ℝ 2 f.val) (t : ℝ) (x : Space) :
    (laplacianField f hf).val x = spatialLaplacian (fun p : SpaceTime => f.val p.2) t x := by
  simp [laplacianField, spatialLaplacian, spatialDerivative, Fin.sum_univ_succ, add_assoc]
  rfl

theorem realValueLine_eq_toNNReal (v : Space) (r : ℝ) (f : PeriodicValue V) :
    realValueLine v r f = valueLine v r.toNNReal f := by
  by_cases hr : 0 ≤ r
  · rw [realValueLine_eq v hr]
    congr 2
    exact (Real.toNNReal_of_nonneg hr).symm
  · rw [Real.toNNReal_eq_zero.mpr (le_of_not_ge hr), valueLine_zero]
    simp [realValueLine, Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hr), translationOrbit]

/-- The directional right difference quotient, in the periodic uniform norm. -/
theorem line_generator_limit (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) (i : Fin 3) :
    Tendsto (fun r : ℝ => r⁻¹ • (valueLine (coordinateVector i) r.toNNReal f - f))
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) • secondField f hf i)) := by
  have hD := c1_translation_hasDerivAt (c1OfContDiff f (hf.of_le (by norm_num))) (coordinateVector i)
  have hDD := c1_translation_hasDerivAt
    (c1OfContDiff (firstField f hf i) (firstField_contDiff f hf i)) (coordinateVector i)
  have hd := realValueLine_generator_zero (coordinateVector i) f (firstField f hf i)
    (secondField f hf i) hD hDD
  have hl := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Ici_sdiff_left] at hl
  simpa only [slope_fun_def, vsub_eq_sub, sub_zero, realValueLine_zero, realValueLine_eq_toNNReal,
    Real.toNNReal_zero, valueLine_zero] using! hl

def varianceEvolution (r : ℝ) : PeriodicValue V →L[ℝ] PeriodicValue V := valueSpatial r.toNNReal

@[simp] theorem varianceEvolution_zero (f : PeriodicValue V) : varianceEvolution 0 f = f := by
  simp [varianceEvolution]

theorem varianceEvolution_joint_continuous :
    Continuous (fun p : ℝ × PeriodicValue V => varianceEvolution p.1 p.2) :=
  valueSpatial_joint_continuous.comp ((by fun_prop : Continuous (fun p : ℝ × PeriodicValue V => p.1.toNNReal)).prodMk
    continuous_snd)

theorem varianceEvolution_semigroup {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (f : PeriodicValue V) :
    varianceEvolution (r + s) f = varianceEvolution r (varianceEvolution s f) := by
  rw [varianceEvolution, Real.toNNReal_add hr hs]
  exact (valueSpatial_semigroup _ _ f).symm

/-- The three directional limits add to one half of the actual Laplacian.
Convergence is in the Banach uniform norm, including at zero variance. -/
theorem variance_generator_limit (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) :
    Tendsto (fun r : ℝ => r⁻¹ • (varianceEvolution r f - f))
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) • laplacianField f hf)) := by
  let q := fun i : Fin 3 => fun r : ℝ => r⁻¹ • (valueLine (coordinateVector i) r.toNNReal f - f)
  have hq (i : Fin 3) : Tendsto (q i) (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) • secondField f hf i)) :=
    line_generator_limit f hf i
  have hr : Tendsto (fun r : ℝ => r.toNNReal) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_real_toNNReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have h1 := (valueLine_joint_continuous (coordinateVector 0)).continuousAt.tendsto.comp (hr.prodMk_nhds (hq 1))
  have h2 := (valueLine_joint_continuous (coordinateVector 1)).continuousAt.tendsto.comp (hr.prodMk_nhds (hq 2))
  have h02 := (valueLine_joint_continuous (coordinateVector 0)).continuousAt.tendsto.comp (hr.prodMk_nhds h2)
  have hlim := ((hq 0).add h1).add h02
  have he (r : ℝ) : q 0 r + valueLine (coordinateVector 0) r.toNNReal (q 1 r) +
      valueLine (coordinateVector 0) r.toNNReal (valueLine (coordinateVector 1) r.toNNReal (q 2 r)) =
      r⁻¹ • (varianceEvolution r f - f) := by
    dsimp only [q, varianceEvolution, valueSpatial, ContinuousLinearMap.comp_apply]
    simp only [map_smul, map_sub]
    module
  simp only [Function.comp_def, valueLine_zero] at hlim
  convert! hlim using 1
  · funext r
    exact (he r).symm
  · simp only [laplacianField, smul_add]

theorem variance_generator_zero (f : PeriodicValue V) (hf : ContDiff ℝ 2 f.val) :
    HasDerivWithinAt (fun r : ℝ => varianceEvolution r f)
      ((1 / 2 : ℝ) • laplacianField f hf) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  simpa only [slope_fun_def, vsub_eq_sub, sub_zero, varianceEvolution_zero] using! variance_generator_limit f hf

/-- The exported physical-time generator has diffusivity eta_m, because
the physical Gaussian variance is exactly twice eta_m times elapsed time. -/
theorem heat_generator_zero (eta_m : ℝ) (heta : 0 ≤ eta_m) (f : PeriodicField) (hf : ContDiff ℝ 2 f.val) :
    HasDerivWithinAt (fun tau : ℝ => heat eta_m tau f) (eta_m • laplacianField f hf) (Ici 0) 0 := by
  have hd := variance_generator_zero f hf
  have htime : HasDerivWithinAt (fun tau : ℝ => 2 * eta_m * tau) (2 * eta_m) (Ici 0) 0 :=
    by simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 * eta_m)).hasDerivWithinAt (s := Ici 0)
  have hmap : MapsTo (fun tau : ℝ => 2 * eta_m * tau) (Ici 0) (Ici 0) := by
    intro tau ht
    change 0 ≤ 2 * eta_m * tau
    exact mul_nonneg (mul_nonneg (by norm_num) heta) ht
  have hd' : HasDerivWithinAt (fun r : ℝ => varianceEvolution r f)
      ((1 / 2 : ℝ) • laplacianField f hf) (Ici 0) (2 * eta_m * 0) := by simpa using hd
  have h := hd'.scomp (0 : ℝ) htime hmap
  have he : (fun tau : ℝ => varianceEvolution (2 * eta_m * tau) f) = fun tau : ℝ => heat eta_m tau f := by
    funext tau
    exact congrArg (fun L => L f) (valueSpatial_eq_spatialOperator _)
  change HasDerivWithinAt (fun tau : ℝ => varianceEvolution (2 * eta_m * tau) f)
    ((2 * eta_m) • ((1 / 2 : ℝ) • laplacianField f hf)) (Ici 0) 0 at h
  rw [he] at h
  rw [smul_smul, show 2 * eta_m * (1 / 2 : ℝ) = eta_m by ring] at h
  exact h

theorem heat_generator_limit (eta_m : ℝ) (heta : 0 ≤ eta_m) (f : PeriodicField) (hf : ContDiff ℝ 2 f.val) :
    Tendsto (fun tau : ℝ => tau⁻¹ • (heat eta_m tau f - f)) (𝓝[>] 0)
      (𝓝 (eta_m • laplacianField f hf)) := by
  have h := hasDerivWithinAt_iff_tendsto_slope.mp (heat_generator_zero eta_m heta f hf)
  rw [Ici_sdiff_left] at h
  simpa only [slope_fun_def, vsub_eq_sub, sub_zero, heat_zero, ContinuousLinearMap.id_apply] using! h

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
