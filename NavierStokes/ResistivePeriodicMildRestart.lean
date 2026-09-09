import NavierStokes.ResistivePeriodicMildActual
import NavierStokes.ResistivePeriodicHeatEquation

/-! Exact restart identities for the existing physical periodic heat
operator, in the uniform space. These identities do not select a new
magnetic solution. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicMild
open Set Filter MeasureTheory ProblemStatement PeriodicGaussian EulerVolterraConvolution
open scoped Topology BoundedContinuousFunction
private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance

private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance
private local instance {T : ℝ} : NormedAddCommGroup (Path T) := inferInstance
private local instance {T : ℝ} : NormedSpace ℝ (Path T) := inferInstance

def valueSource {T : ℝ} (S : Coefficient T) (z : Path T) : C(Icc (0 : ℝ) T,PeriodicField) :=
  EulerContinuousTimeIntegral.multiplier S z

theorem shifted_heat_continuous (eta_m T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T,PeriodicField)) (t : ℝ) :
    Continuous (fun s => heat eta_m (t-s) (extendPath T hT f s)) :=
  (heat_joint_continuous eta_m).comp
    ((continuous_const.sub continuous_id).prodMk (extendPath_continuous T hT f))

def valueDuhamel (eta_m T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T,PeriodicField)) (t : ℝ) : PeriodicField :=
  ∫ s in (0 : ℝ)..t, heat eta_m (t-s) (extendPath T hT f s)

theorem valueDuhamel_history (eta_m : ℝ) (heta : 0 ≤ eta_m)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T,PeriodicField))
    (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    heat eta_m (t-a) (valueDuhamel eta_m T hT f a) =
      ∫ s in (0 : ℝ)..a, heat eta_m (t-s) (extendPath T hT f s) := by
  unfold valueDuhamel
  rw [← (heat eta_m (t-a)).intervalIntegral_comp_comm
    ((shifted_heat_continuous eta_m T hT f a).intervalIntegrable 0 a)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  rw [uIoc_of_le ha] at hs
  have h := congrArg (fun L : PeriodicField →L[ℝ] PeriodicField => L (extendPath T hT f s))
    (heat_semigroup heta (sub_nonneg.mpr hat) (sub_nonneg.mpr hs.2))
  simpa only [sub_add_sub_cancel, ContinuousLinearMap.comp_apply] using! h.symm

theorem valueDuhamel_restart (eta_m : ℝ) (heta : 0 ≤ eta_m)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T,PeriodicField))
    (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    valueDuhamel eta_m T hT f t = heat eta_m (t-a) (valueDuhamel eta_m T hT f a) +
      ∫ s in a..t, heat eta_m (t-s) (extendPath T hT f s) := by
  rw [valueDuhamel_history eta_m heta T hT f a t ha hat]
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((shifted_heat_continuous eta_m T hT f t).intervalIntegrable (μ := volume) 0 a)
    ((shifted_heat_continuous eta_m T hT f t).intervalIntegrable (μ := volume) a t)).symm

theorem value_heat_restart (eta_m : ℝ) (heta : 0 ≤ eta_m)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T,PeriodicField)) (u₀ : PeriodicField)
    (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    heat eta_m t u₀ + valueDuhamel eta_m T hT f t =
      heat eta_m (t-a) (heat eta_m a u₀ + valueDuhamel eta_m T hT f a) +
        ∫ s in a..t, heat eta_m (t-s) (extendPath T hT f s) := by
  rw [map_add, ← ContinuousLinearMap.comp_apply, ← heat_semigroup heta (sub_nonneg.mpr hat) ha,
    sub_add_cancel, valueDuhamel_restart eta_m heta T hT f a t ha hat, add_assoc]

theorem mild_value_equation {T eta_m : ℝ} {hT : 0 ≤ T} {heta : 0 < eta_m}
    {S : Coefficient T} {B_a : PeriodicC1} {z : Path T}
    (hz : Mild T hT eta_m heta S B_a z) (t : Icc (0 : ℝ) T) :
    c1Inclusion (z t) = heat eta_m t.val (c1Inclusion B_a) +
      valueDuhamel eta_m T hT (valueSource S z) t.val := by
  have he := congrArg c1Inclusion (mild_equation hz t)
  rw [map_add, heatC1_value] at he
  have hc := c1Inclusion.intervalIntegral_comp_comm (mild_integrable T hT eta_m heta S z t)
  have he' := he.trans (congrArg (fun w : PeriodicField => heat eta_m t.val (c1Inclusion B_a) + w) hc.symm)
  refine he'.trans ?_
  congr 1
  have heq : (∫ r in (0 : ℝ)..t.val, c1Inclusion (heatKernel eta_m heta r
      (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r)))))) =
      ∫ r in (0 : ℝ)..t.val, heat eta_m r (extendPath T hT (valueSource S z) (t.val-r)) := by
    rw [intervalIntegral.integral_of_le t.property.1, intervalIntegral.integral_of_le t.property.1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    exact heatKernel_value eta_m heta hr.1 _
  rw [heq]
  have h := intervalIntegral.integral_comp_sub_left
    (fun s => heat eta_m (t.val-s) (extendPath T hT (valueSource S z) s)) t.val
    (a := 0) (b := t.val)
  simpa only [sub_sub_cancel, sub_self, sub_zero, valueDuhamel] using! h

end NavierStokes.ResistiveMagnetic.PeriodicMild
