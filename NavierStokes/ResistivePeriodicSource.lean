import NavierStokes.ResistivePeriodicHeatDerivatives
import NavierStokes.ResistivePeriodicCoefficient

/-! The unprojected linear induction source on the completed physical
periodic C1 space. The actual coefficient path retains physical time. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.ResistiveMagnetic.PeriodicSource
open Set ProblemStatement PeriodicGaussian
open scoped Topology BoundedContinuousFunction

abbrev DerivativeField := PeriodicValue (Space →L[ℝ] Space)
private local instance : NormedAddCommGroup PeriodicField := inferInstance
private local instance : NormedSpace ℝ PeriodicField := inferInstance
private local instance : NormedAddCommGroup DerivativeField := inferInstance
private local instance : NormedSpace ℝ DerivativeField := inferInstance
private local instance : NormedAddCommGroup PeriodicC1 := inferInstance
private local instance : NormedSpace ℝ PeriodicC1 := inferInstance

def applyField (G : DerivativeField) (f : PeriodicField) : PeriodicField :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun x => G.val x (f.val x))
    (G.val.continuous.clm_apply f.val.continuous) (‖G‖ * ‖f‖)
    (fun x => ((G.val x).le_opNorm (f.val x)).trans
      (mul_le_mul (G.val.norm_coe_le_norm x) (f.val.norm_coe_le_norm x)
        (norm_nonneg _) (norm_nonneg _))),
    fun x i => by change G.val (x + coordinateVector i) (f.val (x + coordinateVector i)) = G.val x (f.val x)
                  rw [G.property, f.property]⟩

@[simp] theorem applyField_apply (G : DerivativeField) (f : PeriodicField) (x : Space) :
    (applyField G f).val x = G.val x (f.val x) := rfl

theorem applyField_norm_le (G : DerivativeField) (f : PeriodicField) :
    ‖applyField G f‖ ≤ ‖G‖ * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg G) (norm_nonneg f))).mpr
  intro x
  exact ((G.val x).le_opNorm (f.val x)).trans
    (mul_le_mul (G.val.norm_coe_le_norm x) (f.val.norm_coe_le_norm x)
      (norm_nonneg _) (norm_nonneg _))

/-- Bounded pointwise application, with both inputs in periodic uniform spaces. -/
def pairing : DerivativeField →L[ℝ] PeriodicField →L[ℝ] PeriodicField :=
  LinearMap.mkContinuous₂
    { toFun := fun G =>
        { toFun := applyField G
          map_add' := fun f g => by
            apply Subtype.ext
            apply BoundedContinuousFunction.ext
            intro x
            change G.val x (f.val x + g.val x) = G.val x (f.val x) + G.val x (g.val x)
            exact map_add _ _ _
          map_smul' := fun c f => by
            apply Subtype.ext
            apply BoundedContinuousFunction.ext
            intro x
            change G.val x (c • f.val x) = c • G.val x (f.val x)
            exact map_smul _ _ _ }
      map_add' := fun G H => by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply BoundedContinuousFunction.ext
        intro x
        rfl
      map_smul' := fun c G => by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply BoundedContinuousFunction.ext
        intro x
        rfl }
    1 (fun G f => by simpa only [one_mul] using! applyField_norm_le G f)

@[simp] theorem pairing_apply (G : DerivativeField) (f : PeriodicField) (x : Space) :
    (pairing G f).val x = G.val x (f.val x) := rfl

/-- This formula acts on every genuine C1 field; it requires no second
derivative, projection, or zero-mean condition. -/
def sourceOperator (u : PeriodicField) (G : DerivativeField) : PeriodicC1 →L[ℝ] PeriodicField :=
  -((pairing.flip u).comp c1Derivative) + (pairing G).comp c1Value

@[simp] theorem sourceOperator_apply (u : PeriodicField) (G : DerivativeField)
    (B : PeriodicC1) (x : Space) :
    (sourceOperator u G B).val x =
      -(c1Derivative B).val x (u.val x) + G.val x ((c1Value B).val x) := rfl

theorem sourceOperator_bound (u : PeriodicField) (G : DerivativeField) (B : PeriodicC1) :
    ‖sourceOperator u G B‖ ≤ (‖u‖ + ‖G‖) * ‖B‖ := by
  change ‖-applyField (c1Derivative B) u + applyField G (c1Value B)‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  have h1 := (applyField_norm_le (c1Derivative B) u).trans
    (mul_le_mul_of_nonneg_right (c1Derivative_norm_le B) (norm_nonneg u))
  have h2 := (applyField_norm_le G (c1Value B)).trans
    (mul_le_mul_of_nonneg_left (c1Value_norm_le B) (norm_nonneg G))
  nlinarith

theorem sourceOperator_opNorm_le (u : PeriodicField) (G : DerivativeField)
    {U L : ℝ} (hU : ‖u‖ ≤ U) (hL : ‖G‖ ≤ L) : ‖sourceOperator u G‖ ≤ U + L := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg ((norm_nonneg _).trans hU) ((norm_nonneg _).trans hL))
  intro B
  exact (sourceOperator_bound u G B).trans
    (mul_le_mul_of_nonneg_right (add_le_add hU hL) (norm_nonneg B))

theorem sourceOperator_lipschitz (u : PeriodicField) (G : DerivativeField)
    {U L : ℝ} (hU : ‖u‖ ≤ U) (hL : ‖G‖ ≤ L) (B C : PeriodicC1) :
    ‖sourceOperator u G B - sourceOperator u G C‖ ≤ (U + L) * ‖B - C‖ := by
  rw [← map_sub]
  exact (sourceOperator u G).le_of_opNorm_le (sourceOperator_opNorm_le u G hU hL) _

theorem sourceOperator_continuous :
    Continuous (fun p : PeriodicField × DerivativeField => sourceOperator p.1 p.2) := by
  exact (((pairing.flip.continuous.comp continuous_fst).clm_comp continuous_const).neg).add
    ((pairing.continuous.comp continuous_snd).clm_comp continuous_const)

/-- The stored magnetic derivative is identified before comparison with
the existing physical source. Only a spatial C1 magnetic field is used. -/
theorem sourceOperator_eq_source (u : VelocityField) (t : ℝ) (v : PeriodicField)
    (G : DerivativeField) (hv : ∀ x, v.val x = u (t,x))
    (hG : ∀ x, G.val x = spatialDerivative u t x) (B : PeriodicC1) (x : Space) :
    (sourceOperator v G B).val x =
      Comparison.source u (fun p : SpaceTime => (c1Value B).val p.2) t x := by
  rw [sourceOperator_apply, hv, hG, Comparison.source]
  change -(c1Derivative B).val x (u (t,x)) + _ =
    -fderiv ℝ (c1Value B).val x (u (t,x)) + _
  rw [c1_fderiv]

def ofSmoothTimeField (T : ℝ) (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x + coordinateVector i) = A.field t x) :
    C(Icc (0 : ℝ) T, PeriodicC1) := by
  let v : Icc (0 : ℝ) T → PeriodicValue Space := fun t => ⟨A.field t, hp t⟩
  let G : Icc (0 : ℝ) T → DerivativeField := fun t =>
    ⟨A.derivative.field t, fun x i => by
      change A.derivativeField t (x + coordinateVector i) = A.derivativeField t x
      rw [A.derivativeField_eq, A.derivativeField_eq]
      exact value_fderiv_periodic (v t) x i⟩
  refine ⟨fun t => ⟨(v t,G t), fun x => ?_⟩, ?_⟩
  · change HasFDerivAt (A.field t) (A.derivativeField t x) x
    rw [A.derivativeField_eq]
    exact ((A.smooth t).differentiable (by simp) x).hasFDerivAt
  · apply Continuous.subtype_mk
    exact (Continuous.subtype_mk A.field.continuous _).prodMk
      (Continuous.subtype_mk A.derivative.field.continuous _)

@[simp] theorem ofSmoothTimeField_value (T : ℝ) (A : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (hp : ∀ t x i, A.field t (x + coordinateVector i) = A.field t x)
    (t : Icc (0 : ℝ) T) (x : Space) :
    (c1Value (ofSmoothTimeField T A hp t)).val x = A.field t x := rfl

open MagneticPeriodicMain (budget threshold geometry Selected)
open MagneticAxisTransfer

/-- The same selected periodic velocity as Paper I, viewed as a continuous
C1 path on one fixed elapsed-time slab. All jets come from actualOnSlab. -/
def actualVelocityPath (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hb : b < 1) : C(Icc (0 : ℝ) (b-a), PeriodicC1) :=
  ofSmoothTimeField (b-a)
    (MagneticPeriodicCoefficient.actualOnSlab budget threshold geometry scales hsel a b hb)
    (fun t x i => MagneticPeriodicCoefficient.actual_periodic budget threshold geometry scales
      (a+t) (by have ht := t.property.2; change a + t.val < 1; linarith) x i)

@[simp] theorem actualVelocityPath_value (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hb : b < 1) (t : Icc (0 : ℝ) (b-a)) (x : Space) :
    (c1Value (actualVelocityPath scales hsel a b hb t)).val x =
      actualPeriodicVelocity budget threshold geometry scales (a+t,x) := rfl

theorem actualVelocityPath_derivative (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hb : b < 1) (t : Icc (0 : ℝ) (b-a)) (x : Space) :
    (c1Derivative (actualVelocityPath scales hsel a b hb t)).val x =
      spatialDerivative (actualPeriodicVelocity budget threshold geometry scales) (a+t) x := by
  rw [← c1_fderiv]
  rfl

def actualSourcePath (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hb : b < 1) : C(Icc (0 : ℝ) (b-a), PeriodicC1 →L[ℝ] PeriodicField) :=
  ⟨fun t => sourceOperator (c1Value (actualVelocityPath scales hsel a b hb t))
      (c1Derivative (actualVelocityPath scales hsel a b hb t)),
    sourceOperator_continuous.comp
      ((c1Value.continuous.comp (actualVelocityPath scales hsel a b hb).continuous).prodMk
        (c1Derivative.continuous.comp (actualVelocityPath scales hsel a b hb).continuous))⟩

theorem actualSourcePath_eq_source (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hb : b < 1) (t : Icc (0 : ℝ) (b-a)) (B : PeriodicC1) (x : Space) :
    (actualSourcePath scales hsel a b hb t B).val x =
      Comparison.source (actualPeriodicVelocity budget threshold geometry scales)
        (fun p : SpaceTime => (c1Value B).val p.2) (a+t) x :=
  sourceOperator_eq_source _ _ _ _ (actualVelocityPath_value scales hsel a b hb t)
    (actualVelocityPath_derivative scales hsel a b hb t) B x

/-- This finite coefficient is chosen before eta_m and the initial field. -/
theorem actualSourcePath_bound (scales : ℕ → ℕ) (hsel : Selected scales)
    (a b : ℝ) (hb : b < 1) (t : Icc (0 : ℝ) (b-a)) (B : PeriodicC1) :
    ‖actualSourcePath scales hsel a b hb t B‖ ≤ ‖actualSourcePath scales hsel a b hb‖ * ‖B‖ :=
  ((actualSourcePath scales hsel a b hb t).le_opNorm B).trans
    (mul_le_mul_of_nonneg_right ((actualSourcePath scales hsel a b hb).norm_coe_le_norm t)
      (norm_nonneg B))

end NavierStokes.ResistiveMagnetic.PeriodicSource
