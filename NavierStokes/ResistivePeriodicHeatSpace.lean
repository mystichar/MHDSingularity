import NavierStokes.ResistivePeriodicGaussian

/-! Codomain extension of the existing physical periodic uniform space.
The `Space` specialization is definitionally the existing `PeriodicField`.
This also permits continuous-linear-map-valued derivative fields. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set MeasureTheory ProbabilityTheory ProblemStatement
open scoped BoundedContinuousFunction NNReal

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

def periodicValues : ClosedSubmodule ℝ (Space →ᵇ V) where
  carrier := {f | ∀ x i, f (x + coordinateVector i) = f x}
  zero_mem' := by intro x i; rfl
  add_mem' := by
    intro f g hf hg x i
    change f (x + coordinateVector i) + g (x + coordinateVector i) = f x + g x
    rw [hf, hg]
  smul_mem' := by
    intro c f hf x i
    change c • f (x + coordinateVector i) = c • f x
    rw [hf]
  isClosed' := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun i => isClosed_eq
      (BoundedContinuousFunction.evalCLM ℝ (x + coordinateVector i)).continuous
      (BoundedContinuousFunction.evalCLM ℝ x).continuous))

abbrev PeriodicValue := (periodicValues V).toSubmodule

instance periodicValueCompleteSpace [CompleteSpace V] : CompleteSpace (PeriodicValue V) :=
  (periodicValues V).isClosed'.isComplete.completeSpace_coe

/-- No new physical space is substituted for the existing one. -/
theorem periodicValue_space : PeriodicValue Space = PeriodicField := rfl

variable {V}

def valueConstant (c : V) : PeriodicValue V :=
  ⟨BoundedContinuousFunction.const Space c, by intro x i; rfl⟩

def valueEval (x : Space) : PeriodicValue V →L[ℝ] V :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp (periodicValues V).toSubmodule.subtypeL

@[simp] theorem valueEval_apply (x : Space) (f : PeriodicValue V) :
    valueEval x f = f.val x := rfl

/-- Translation on the physical cover, with its original unit periods. -/
def translate (y : Space) : PeriodicValue V →L[ℝ] PeriodicValue V :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨f.val.compContinuous ⟨fun x => x + y, by fun_prop⟩,
        fun x i => by simpa only [BoundedContinuousFunction.compContinuous_apply,
          ContinuousMap.coe_mk, add_right_comm] using f.property (x + y) i⟩
      map_add' := fun f g => by apply Subtype.ext; rfl
      map_smul' := fun c f => by apply Subtype.ext; rfl }
    1 (fun f => by
      change ‖f.val.compContinuous _‖ ≤ 1 * ‖f.val‖
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f.val)).mpr
        (fun x => f.val.norm_coe_le_norm _))

@[simp] theorem translate_apply (y : Space) (f : PeriodicValue V) (x : Space) :
    (translate y f).val x = f.val (x + y) := rfl

@[simp] theorem translate_zero (f : PeriodicValue V) : translate 0 f = f := by
  apply Subtype.ext
  ext x
  simp

theorem translate_add (y z : Space) (f : PeriodicValue V) :
    translate y (translate z f) = translate (y + z) f := by
  apply Subtype.ext
  ext x
  simp [add_assoc]

theorem translate_commute (y z : Space) (f : PeriodicValue V) :
    translate y (translate z f) = translate z (translate y f) := by
  rw [translate_add, translate_add, add_comm y z]

theorem translate_norm_le (y : Space) (f : PeriodicValue V) : ‖translate y f‖ ≤ ‖f‖ := by
  exact (BoundedContinuousFunction.norm_le (norm_nonneg f.val)).mpr
    (fun x => f.val.norm_coe_le_norm _)

@[simp] theorem translate_norm (y : Space) (f : PeriodicValue V) : ‖translate y f‖ = ‖f‖ := by
  apply le_antisymm (translate_norm_le y f)
  have h := translate_norm_le (-y) (translate y f)
  simpa [translate_add] using h

theorem translate_continuous (f : PeriodicValue V) : Continuous (fun y => translate y f) := by
  apply Continuous.subtype_mk
  have h := MagneticPeriodicCoefficient.boundedSlice_continuous
    (fun z : Space × Space => f.val (z.2 + z.1))
    (f.val.continuous.comp (continuous_snd.add continuous_fst))
    (fun y x i => by simpa only [add_right_comm] using f.property (x + y) i)
  convert h using 1
  funext y
  ext x
  rfl

theorem translate_joint_continuous :
    Continuous (fun p : Space × PeriodicValue V => translate p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith'
    (fun p : Space × PeriodicValue V => translate p.1 p.2) 1
  · intro y
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
      translate_norm_le y (f - g)
  · intro f
    exact translate_continuous f

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
