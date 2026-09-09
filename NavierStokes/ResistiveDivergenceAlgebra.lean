import NavierStokes.ResistiveDifferentialCalculus

noncomputable section
namespace NavierStokes.ResistiveMagnetic.Calculus
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Div (e : Fin 3 → E) (F : Fin 3 → E → ℝ) (x : E) := ∑ i, P (e i) (F i) x
def Adv (e : Fin 3 → E) (U : Fin 3 → E → ℝ) (f : E → ℝ) (x : E) := ∑ j, U j x * P (e j) f x
def Lap (e : Fin 3 → E) (f : E → ℝ) (x : E) := ∑ j, P (e j) (P (e j) f) x

variable {O : Set E} (hO : IsOpen O) {e : Fin 3 → E} {U B : Fin 3 → E → ℝ}
  (hU : ∀ i, ContDiffOn ℝ ∞ (U i) O) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) O)
  {x : E} (hx : x ∈ O)

include hO hB in
theorem Div_smooth : ContDiffOn ℝ ∞ (Div e B) O :=
  ContDiffOn.sum (fun i _ => P_smooth hO (hB i) _)

include hO hU hB hx in
theorem Div_Adv : Div e (fun i => Adv e U (B i)) x =
    (∑ i, ∑ j, P (e i) (U j) x * P (e j) (B i) x) + Adv e U (Div e B) x := by
  unfold Div Adv
  simp_rw [P_sum hO hx Finset.univ _ (fun j _ => (hU j).mul (P_smooth hO (hB _) _)),
    P_mul hO (hU _) (P_smooth hO (hB _) _) hx,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [P_sum hO hx Finset.univ _ (fun i _ => P_smooth hO (hB i) _)]
  exact Finset.sum_congr rfl (fun i _ => P_comm hO (hB i) hx _ _)

include hO hB hx in
theorem Div_time (v : E) : Div e (fun i => P v (B i)) x = P v (Div e B) x := by
  unfold Div
  rw [P_sum hO hx Finset.univ _ (fun i _ => P_smooth hO (hB i) _)]
  exact Finset.sum_congr rfl (fun i _ => P_comm hO (hB i) hx _ _)

include hO hB hx in
theorem Div_Lap : Div e (fun i => Lap e (B i)) x = Lap e (Div e B) x := by
  unfold Div Lap
  simp_rw [P_sum hO hx Finset.univ _ (fun j _ => P_smooth hO (P_smooth hO (hB _) _) _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : P (e j) (fun x => ∑ i, P (e i) (B i) x) =ᶠ[𝓝 x]
      (fun y => ∑ i, P (e j) (P (e i) (B i)) y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact P_sum hO hy Finset.univ _ (fun i _ => P_smooth hO (hB i) _) _
  rw [show P (e j) (P (e j) (fun x => ∑ i, P (e i) (B i) x)) x =
      P (e j) (fun y => ∑ i, P (e j) (P (e i) (B i)) y) x from
    congrArg (fun L : E →L[ℝ] ℝ => L (e j)) he.fderiv_eq]
  rw [P_sum hO hx Finset.univ _ (fun i _ => P_smooth hO (P_smooth hO (hB i) _) _)]
  exact Finset.sum_congr rfl (fun i _ => P_comm_three hO (hB i) hx _ _)

/-- The two quadratic derivative contractions cancel by interchanging indices. -/
theorem cross_contraction :
    (∑ i, ∑ j, P (e i) (U j) x * P (e j) (B i) x) =
    (∑ i, ∑ j, P (e i) (B j) x * P (e j) (U i) x) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))
include hO hB in
theorem Lap_smooth (i : Fin 3) : ContDiffOn ℝ ∞ (Lap e (B i)) O :=
  ContDiffOn.sum (fun _j _ => P_smooth hO (P_smooth hO (hB i) _) _)

include hO hU hB in
theorem Adv_smooth (i : Fin 3) : ContDiffOn ℝ ∞ (Adv e U (B i)) O :=
  ContDiffOn.sum (fun j _ => (hU j).mul (P_smooth hO (hB i) _))

include hO hU hB hx in
/-- Divergence of stretching-form induction is scalar advection-diffusion.
Quadratic first-derivative terms cancel; third derivatives commute by C3. -/
theorem divergence_transport (v : E) (eta_m : ℝ)
    (heq : ∀ y ∈ O, ∀ i, P v (B i) y + Adv e U (B i) y =
      Adv e B (U i) y + eta_m*Lap e (B i) y)
    (hdiv : ∀ y ∈ O, Div e U y = 0) :
    P v (Div e B) x + Adv e U (Div e B) x = eta_m*Lap e (Div e B) x := by
  have hi (i : Fin 3) : P (e i) (P v (B i)) x + P (e i) (Adv e U (B i)) x =
      P (e i) (Adv e B (U i)) x + eta_m*P (e i) (Lap e (B i)) x := by
    have he : (fun y => P v (B i) y + Adv e U (B i) y) =ᶠ[𝓝 x]
        (fun y => Adv e B (U i) y + eta_m*Lap e (B i) y) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact heq y hy i
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L (e i)) he.fderiv_eq
    change P (e i) _ x = P (e i) _ x at hh
    rw [P_add hO (P_smooth hO (hB i) v) (Adv_smooth hO hU hB i) hx,
      P_add hO (Adv_smooth hO hB hU i) (contDiffOn_const.mul (Lap_smooth hO hB i)) hx,
      P_const_mul hO (Lap_smooth hO hB i) hx] at hh
    exact hh
  have hh := congrArg (fun f : Fin 3 → ℝ => ∑ i, f i) (funext hi)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  change Div e (fun i => P v (B i)) x + Div e (fun i => Adv e U (B i)) x =
    Div e (fun i => Adv e B (U i)) x + eta_m*Div e (fun i => Lap e (B i)) x at hh
  rw [Div_time hO hB hx, Div_Adv hO hU hB hx, Div_Adv hO hB hU hx,
    Div_Lap hO hB hx, cross_contraction] at hh
  have he : Div e U =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hdiv y hy
  have hz : Adv e B (Div e U) x = 0 := by
    unfold Adv P
    rw [he.fderiv_eq]
    simp
  rw [hz] at hh
  linarith
end NavierStokes.ResistiveMagnetic.Calculus
