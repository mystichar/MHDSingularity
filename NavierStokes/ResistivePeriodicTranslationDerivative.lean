import NavierStokes.ResistivePeriodicC1
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Strong translation derivatives and the actual derivative graph on the
physical three-dimensional cover. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.PeriodicGaussian
open Set ProblemStatement Filter
open scoped Topology BoundedContinuousFunction

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
private local instance : NormedAddCommGroup (PeriodicValue V) := inferInstance
private local instance : NormedSpace ℝ (PeriodicValue V) := inferInstance

section Parameters
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem translate_hasFDerivAt_all (A : E →L[ℝ] Space) (f : PeriodicValue V)
    (G : E →L[ℝ] PeriodicValue V)
    (h : HasFDerivAt (fun y => translate (A y) f) G 0) (x : E) :
    HasFDerivAt (fun y => translate (A y) f) ((translate (A x)).comp G) x := by
  have h0 := (translate (A x)).hasFDerivAt.comp 0 h
  have h0' : HasFDerivAt (fun y => translate (A x) (translate (A y) f))
      ((translate (A x)).comp G) (x - x) := by simpa using! h0
  have hd := h0'.comp (f := fun y : E => y - x) x ((hasFDerivAt_id x).sub_const x)
  have he : (fun y => translate (A x) (translate (A (y - x)) f)) =
      fun y => translate (A y) f := by
    funext y
    rw [translate_add, ← map_add, add_sub_cancel]
  simpa only [Function.comp_def, id_eq, sub_self, he, ContinuousLinearMap.comp_id] using! hd

/-- Combining two genuine translation derivatives uses continuity of the
partial derivatives, justified by finite dimensionality of their domains. -/
theorem translate_hasFDerivAt_coprod [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    (A : E →L[ℝ] Space) (C : H →L[ℝ] Space) (f : PeriodicValue V)
    (G : E →L[ℝ] PeriodicValue V) (J : H →L[ℝ] PeriodicValue V)
    (hG : HasFDerivAt (fun y => translate (A y) f) G 0)
    (hJ : HasFDerivAt (fun y => translate (C y) f) J 0) :
    HasFDerivAt (fun y : E × H => translate ((A.coprod C) y) f) (G.coprod J) 0 := by
  let F := fun x : E => fun y : H => translate (A x + C y) f
  let F₁ := fun x : E => fun y : H => (translate (A x + C y)).comp G
  let F₂ := fun x : E => fun y : H => (translate (A x + C y)).comp J
  have h1 (p : E × H) : HasFDerivAt (fun x => F x p.2) (F₁ p.1 p.2) p.1 := by
    have hd := (translate (C p.2)).hasFDerivAt.comp p.1
      (translate_hasFDerivAt_all A f G hG p.1)
    convert! hd using 1
    · funext x
      simp [F, translate_add, add_comm]
    · ext w
      simp [F₁, translate_add, add_comm]
  have h2 (p : E × H) : HasFDerivAt (F p.1) (F₂ p.1 p.2) p.2 := by
    have hd := (translate (A p.1)).hasFDerivAt.comp p.2
      (translate_hasFDerivAt_all C f J hJ p.2)
    convert! hd using 1
    · funext y
      simp [F, translate_add]
    · ext w
      simp [F₂, translate_add]
  have hc1 : Continuous (Function.uncurry F₁) := by
    apply continuous_clm_apply.mpr
    intro w
    exact (translate_continuous (G w)).comp
      ((A.continuous.comp continuous_fst).add (C.continuous.comp continuous_snd))
  have hc2 : Continuous (Function.uncurry F₂) := by
    apply continuous_clm_apply.mpr
    intro w
    exact (translate_continuous (J w)).comp
      ((A.continuous.comp continuous_fst).add (C.continuous.comp continuous_snd))
  have hd := (hasStrictFDerivAt_uncurry_coprod (u := (0 : E × H)) (f := F) (f₁ := F₁) (f₂ := F₂)
    (Eventually.of_forall h1) (Eventually.of_forall h2) hc1.continuousAt hc2.continuousAt).hasFDerivAt
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro w
  change G w.1 + J w.2 = translate (A 0 + C 0) (G w.1) + translate (A 0 + C 0) (J w.2)
  simp

end Parameters

def coordinateGradient (g : Fin 3 → PeriodicValue V) : Space →L[ℝ] PeriodicValue V :=
  (EuclideanSpace.proj 0).smulRight (g 0) +
    (EuclideanSpace.proj 1).smulRight (g 1) + (EuclideanSpace.proj 2).smulRight (g 2)

theorem translate_hasFDerivAt_coordinates (f : PeriodicValue V) (g : Fin 3 → PeriodicValue V)
    (hg : ∀ i, HasDerivAt (fun s : ℝ => translate (s • coordinateVector i) f) (g i) 0) :
    HasFDerivAt (fun y : Space => translate y f) (coordinateGradient g) 0 := by
  let A (i : Fin 3) : ℝ →L[ℝ] Space := ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector i)
  let G (i : Fin 3) : ℝ →L[ℝ] PeriodicValue V := ContinuousLinearMap.toSpanSingleton ℝ (g i)
  let P : Space →L[ℝ] ℝ × (ℝ × ℝ) :=
    (EuclideanSpace.proj 0).prod ((EuclideanSpace.proj 1).prod (EuclideanSpace.proj 2))
  have hD (i : Fin 3) : HasFDerivAt (fun s => translate (A i s) f) (G i) 0 := (hg i).hasFDerivAt
  have h12 := translate_hasFDerivAt_coprod (A 1) (A 2) f (G 1) (G 2) (hD 1) (hD 2)
  have h012 := translate_hasFDerivAt_coprod (A 0) ((A 1).coprod (A 2)) f
    (G 0) ((G 1).coprod (G 2)) (hD 0) h12
  have h012' : HasFDerivAt (fun y : ℝ × (ℝ × ℝ) => translate ((A 0).coprod ((A 1).coprod (A 2)) y) f)
      ((G 0).coprod ((G 1).coprod (G 2))) (P 0) := by simpa using h012
  have hd := h012'.comp (0 : Space) P.hasFDerivAt
  have he (x : Space) : (A 0).coprod ((A 1).coprod (A 2)) (P x) = x := by
    change x 0 • coordinateVector 0 + (x 1 • coordinateVector 1 + x 2 • coordinateVector 2) = x
    simpa [Fin.sum_univ_succ, add_assoc] using PeriodicUniqueness.sum_coordinates x
  convert! hd using 1
  · funext x
    dsimp only [Function.comp_def]
    rw [he]
  · ext x
    simp [coordinateGradient, P, G, add_assoc]

/-- The transpose of a bounded linear map into periodic uniform fields.
Its values are actual continuous linear maps at each physical point. -/
def derivativeTranspose : (Space →L[ℝ] PeriodicValue V) →L[ℝ] PeriodicValue (Space →L[ℝ] V) :=
  LinearMap.mkContinuous
    { toFun := fun G => ⟨BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => (valueEval x).comp G)
        (continuous_clm_apply.mpr (fun w => (G w).val.continuous)) ‖G‖
        (fun x => ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G)
          (fun w => ((G w).val.norm_coe_le_norm x).trans (G.le_opNorm w))),
        fun x i => by ext w; exact (G w).property x i⟩
      map_add' := fun G J => by apply Subtype.ext; ext x w; rfl
      map_smul' := fun c G => by apply Subtype.ext; ext x w; rfl }
    1 (fun G => by
      apply (BoundedContinuousFunction.norm_le (show 0 ≤ 1 * ‖G‖ by positivity)).mpr
      intro x
      change ‖(valueEval x).comp G‖ ≤ 1 * ‖G‖
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G)
        (fun w => ((G w).val.norm_coe_le_norm x).trans (G.le_opNorm w)))

@[simp] theorem derivativeTranspose_apply (G : Space →L[ℝ] PeriodicValue V) (x w : Space) :
    (derivativeTranspose G).val x w = (G w).val x := rfl

theorem derivativeTranspose_norm_le (G : Space →L[ℝ] PeriodicValue V) :
    ‖derivativeTranspose G‖ ≤ ‖G‖ := by
  exact (BoundedContinuousFunction.norm_le (norm_nonneg G)).mpr
    (fun x => ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G)
      (fun w => ((G w).val.norm_coe_le_norm x).trans (G.le_opNorm w)))

theorem hasFDerivAt_of_translation (f : PeriodicValue V) (G : Space →L[ℝ] PeriodicValue V)
    (hG : HasFDerivAt (fun y : Space => translate y f) G 0) (x : Space) :
    HasFDerivAt f.val ((derivativeTranspose G).val x) x := by
  have h0 := (valueEval x).hasFDerivAt.comp 0 hG
  have h0' : HasFDerivAt (fun y => valueEval x (translate y f))
      ((valueEval x).comp G) (x - x) := by simpa using! h0
  have hd := h0'.comp (f := fun y : Space => y - x) x ((hasFDerivAt_id x).sub_const x)
  convert! hd using 1
  · funext y
    change f.val y = f.val (x + (y - x))
    rw [add_sub_cancel]

theorem coordinateGradient_norm_le (g : Fin 3 → PeriodicValue V) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ i, ‖g i‖ ≤ C) : ‖coordinateGradient g‖ ≤ 3 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hw (i : Fin 3) : |w i| ≤ ‖w‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w i
  have hi (i : Fin 3) : ‖w i • g i‖ ≤ C * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (hw i) (hg i) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  change ‖w 0 • g 0 + w 1 • g 1 + w 2 • g 2‖ ≤ _
  have h := (norm_add_le (w 0 • g 0 + w 1 • g 1) (w 2 • g 2)).trans
    (add_le_add_left (norm_add_le _ _) _)
  nlinarith [hi 0, hi 1, hi 2]

end NavierStokes.ResistiveMagnetic.PeriodicGaussian
