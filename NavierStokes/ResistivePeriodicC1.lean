import NavierStokes.ResistivePeriodicHeatSpace
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! The complete physical periodic C1 space is the closed graph of the
actual spatial derivative, with the maximum of the two uniform norms. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set ProblemStatement Filter
open scoped Topology BoundedContinuousFunction

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

def derivativeGraph : Submodule ℝ (PeriodicValue V × PeriodicValue (Space →L[ℝ] V)) where
  carrier := {p | ∀ x, HasFDerivAt p.1.val (p.2.val x) x}
  zero_mem' := by intro x; exact hasFDerivAt_const (0 : V) x
  add_mem' := by
    intro p q hp hq x
    exact (hp x).add (hq x)
  smul_mem' := by
    intro c p hp x
    exact (hp x).const_smul c

/-- Uniform convergence of both entries preserves the genuine derivative
identity. This is an analytic closed-graph proof, not an extra assumption. -/
theorem derivativeGraph_closed :
    IsClosed (derivativeGraph V : Set (PeriodicValue V × PeriodicValue (Space →L[ℝ] V))) := by
  apply isSeqClosed_iff_isClosed.mp
  intro p q hp hpq
  have hfst : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hpq
  have hsnd : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hpq
  have hD : TendstoUniformly (fun n => (p n).2.val) q.2.val atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((continuous_subtype_val.tendsto q.2).comp hsnd)
  intro x
  exact hasFDerivAt_of_tendstoUniformly hD (fun n x => hp n x)
    (fun x => (valueEval x).continuous.continuousAt.tendsto.comp hfst) x

abbrev PeriodicC1Value := derivativeGraph V

instance periodicC1ValueCompleteSpace [CompleteSpace V] : CompleteSpace (PeriodicC1Value V) :=
  (derivativeGraph_closed V).isComplete.completeSpace_coe

abbrev PeriodicC1 := PeriodicC1Value Space

private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance
private local instance : NormedAddCommGroup (PeriodicC1Value V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicC1Value V) := inferInstance

variable {V}

def c1Value : PeriodicC1Value V →L[ℝ] PeriodicValue V :=
  (ContinuousLinearMap.fst ℝ _ _).comp (derivativeGraph V).subtypeL

def c1Derivative : PeriodicC1Value V →L[ℝ] PeriodicValue (Space →L[ℝ] V) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (derivativeGraph V).subtypeL

theorem c1_hasFDerivAt (f : PeriodicC1Value V) (x : Space) :
    HasFDerivAt (c1Value f).val ((c1Derivative f).val x) x := f.property x

theorem c1_fderiv (f : PeriodicC1Value V) (x : Space) :
    fderiv ℝ (c1Value f).val x = (c1Derivative f).val x := (c1_hasFDerivAt f x).fderiv

theorem c1_contDiff (f : PeriodicC1Value V) : ContDiff ℝ 1 (c1Value f).val := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨(c1Derivative f).val, (c1Derivative f).val.continuous, c1_hasFDerivAt f⟩

/-- The product norm is exactly the stated maximum, without a hidden sum
or a homogeneous seminorm that would exclude constant fields. -/
theorem c1_norm (f : PeriodicC1Value V) :
    ‖f‖ = max ‖c1Value f‖ ‖c1Derivative f‖ := rfl

theorem c1Value_norm_le (f : PeriodicC1Value V) : ‖c1Value f‖ ≤ ‖f‖ := le_max_left _ _

theorem c1Derivative_norm_le (f : PeriodicC1Value V) : ‖c1Derivative f‖ ≤ ‖f‖ := le_max_right _ _

theorem c1Value_opNorm_le : ‖c1Value (V := V)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa only [one_mul] using c1Value_norm_le f)

theorem c1Value_injective : Function.Injective (c1Value (V := V)) := by
  intro f g h
  apply Subtype.ext
  apply Prod.ext h
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact (c1_fderiv f x).symm.trans ((congrArg (fun v : PeriodicValue V =>
    fderiv ℝ v.val x) h).trans (c1_fderiv g x))

def c1Constant (c : V) : PeriodicC1Value V :=
  ⟨(valueConstant c, valueConstant (0 : Space →L[ℝ] V)),
    fun x => hasFDerivAt_const c x⟩

@[simp] theorem c1Constant_value (c : V) : c1Value (c1Constant c) = valueConstant c := rfl

@[simp] theorem c1Constant_derivative (c : V) : c1Derivative (c1Constant c) = 0 := rfl

@[simp] theorem c1Constant_norm (c : V) : ‖c1Constant c‖ = ‖c‖ := by
  rw [c1_norm, c1Constant_derivative, norm_zero, max_eq_left (norm_nonneg _)]
  change ‖BoundedContinuousFunction.const Space c‖ = ‖c‖
  simp

/-- The continuous inclusion has exactly the original target space. -/
def c1Inclusion : PeriodicC1 →L[ℝ] PeriodicField := c1Value

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
