import NavierStokes.ResistivePeriodicMildRestart

/-! A forward restart argument differentiates the short Duhamel interval
without differentiating a singular derivative-gain kernel at zero. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicMild
open Set Filter MeasureTheory ProblemStatement PeriodicGaussian EulerVolterraConvolution
open scoped Topology BoundedContinuousFunction
private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance

def shortDuhamel (eta_m T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T,PeriodicField)) (t h : ℝ) : PeriodicField :=
  ∫ s in (0 : ℝ)..h, heat eta_m (h-s) (extendPath T hT f (t+s))

theorem shortDuhamel_hasDerivAt_zero (eta_m T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T,PeriodicField)) (t : ℝ) :
    HasDerivAt (shortDuhamel eta_m T hT f t) (extendPath T hT f t) 0 := by
  let g := fun h s : ℝ => heat eta_m (h-h*s) (extendPath T hT f (t+h*s))
  have hg : Continuous g.uncurry := (heat_joint_continuous eta_m).comp
    ((by fun_prop : Continuous (fun p : ℝ × ℝ => p.1-p.1*p.2)).prodMk
      ((extendPath_continuous T hT f).comp (by fun_prop)))
  have hi : Continuous (fun h => ∫ s in (0 : ℝ)..1, g h s) := by
    have hh := continuous_parametric_integral_of_continuous (μ := volume) hg
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc] using hh
  have he (h : ℝ) : shortDuhamel eta_m T hT f t h = h • ∫ s in (0 : ℝ)..1, g h s := by
    have hh := intervalIntegral.smul_integral_comp_mul_left
      (fun s => heat eta_m (h-s) (extendPath T hT f (t+s))) h (a := 0) (b := 1)
    simpa only [mul_zero, mul_one, shortDuhamel, g] using! hh.symm
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hi0 : (∫ s in (0 : ℝ)..1, g 0 s) = extendPath T hT f t := by
    simp [g]
  have hl := (hi.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [hi0] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [zero_add, he, zero_smul, sub_zero, smul_smul,
    inv_mul_cancel₀ (show h ≠ 0 from hh), one_smul]

theorem value_heat_restart_short (eta_m : ℝ) (heta : 0 ≤ eta_m)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T,PeriodicField)) (u₀ : PeriodicField)
    (t h : ℝ) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    heat eta_m (t+h) u₀ + valueDuhamel eta_m T hT f (t+h) =
      heat eta_m h (heat eta_m t u₀ + valueDuhamel eta_m T hT f t) +
        shortDuhamel eta_m T hT f t h := by
  have hr := value_heat_restart eta_m heta T hT f u₀ t (t+h) ht (by linarith)
  rw [add_sub_cancel_left] at hr
  rw [hr]
  congr 1
  have hi := intervalIntegral.integral_comp_add_left
    (fun s => heat eta_m (t+h-s) (extendPath T hT f s)) t (a := 0) (b := h)
  simp only [add_zero] at hi
  have he : (fun r => heat eta_m (t+h-(t+r)) (extendPath T hT f (t+r))) =
      fun r => heat eta_m (h-r) (extendPath T hT f (t+r)) := by
    funext r
    rw [show t+h-(t+r) = h-r by ring]
  rw [he] at hi
  exact hi.symm

/-- The existing Laplacian specialized to the original physical field space. -/
def uniformLaplacian (f : PeriodicField) (hf : ContDiff ℝ 2 f.val) : PeriodicField :=
  laplacianField f hf

/-- Only a C2 attained state is needed to compute the right time
derivative. The source remains a continuous uniform-space path. -/
theorem value_heat_right_derivative (eta_m : ℝ) (heta : 0 ≤ eta_m)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T,PeriodicField)) (u₀ : PeriodicField)
    (t : ℝ) (ht : 0 ≤ t)
    (hC2 : ContDiff ℝ 2 (heat eta_m t u₀ + valueDuhamel eta_m T hT f t).val) :
    HasDerivWithinAt (fun s => heat eta_m s u₀ + valueDuhamel eta_m T hT f s)
      (eta_m • uniformLaplacian (heat eta_m t u₀ + valueDuhamel eta_m T hT f t) hC2 +
        extendPath T hT f t) (Ici t) t := by
  have hheat : HasDerivWithinAt
      (fun s => heat eta_m s (heat eta_m t u₀ + valueDuhamel eta_m T hT f t))
      (eta_m • uniformLaplacian (heat eta_m t u₀ + valueDuhamel eta_m T hT f t) hC2)
      (Ici 0) 0 := heat_generator_zero eta_m heta _ hC2
  have hd := hheat.add
    (shortDuhamel_hasDerivAt_zero eta_m T hT f t).hasDerivWithinAt
  have hc := hd.scomp_of_eq t ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
    (show MapsTo (fun s : ℝ => s-t) (Ici t) (Ici 0) from by
      intro s hs
      change 0 ≤ s-t
      change t ≤ s at hs
      exact sub_nonneg.mpr hs)
    (sub_self t).symm
  simp only [one_smul] at hc
  refine hc.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hr := value_heat_restart_short eta_m heta T hT f u₀ t (s-t) ht (sub_nonneg.mpr hs)
    simpa only [add_sub_cancel, Function.comp_def] using! hr
  · simp [shortDuhamel]

end NavierStokes.ResistiveMagnetic.PeriodicMild
