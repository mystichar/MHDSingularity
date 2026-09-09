import NavierStokes.ResistiveMagneticInduction

/-! Local directional calculus used to commute divergence with transport and
diffusion. All derivatives are actual Frechet derivatives on an open set. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Calculus
open Set Filter
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def P (v : E) (f : E → ℝ) (x : E) := fderiv ℝ f x v

variable {O : Set E} (hO : IsOpen O) {f g : E → ℝ}
  (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
  {x : E} (hx : x ∈ O)

include hO hf in
theorem P_smooth (v : E) : ContDiffOn ℝ ∞ (P v f) O :=
  (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

include hO hf hx in
theorem P_comm (v w : E) : P v (P w f) x = P w (P v f) x := by
  have h := hf.contDiffAt (hO.mem_nhds hx)
  have hd := (h.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  unfold P
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using (h.isSymmSndFDerivAt (by simp)).eq v w

include hO hf hg hx in
theorem P_mul (v : E) : P v (fun x => f x*g x) x = P v f x*g x + f x*P v g x := by
  have hdf := (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdg := (hg.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  unfold P
  rw [fderiv_fun_mul hdf hdg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

include hO hf hg hx in
theorem P_add (v : E) : P v (fun x => f x+g x) x = P v f x+P v g x := by
  unfold P
  rw [fderiv_fun_add ((hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    ((hg.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))]
  rfl

include hO hf hx in
theorem P_const_mul (c : ℝ) (v : E) : P v (fun x => c*f x) x = c*P v f x := by
  unfold P
  rw [fderiv_const_mul ((hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))]
  rfl

include hO hx in
theorem P_sum {ι : Type*} (s : Finset ι) (F : ι → E → ℝ)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ∞ (F i) O) (v : E) :
    P v (fun x => ∑ i ∈ s, F i x) x = ∑ i ∈ s, P v (F i) x := by
  unfold P
  rw [fderiv_fun_sum (fun i hi => (hF i hi |>.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))]
  simp

include hO hf hx in
/-- Commutation with a repeated directional derivative, using C3 rather
than silently commuting the third derivatives. -/
theorem P_comm_three (v w : E) :
    P v (P w (P w f)) x = P w (P w (P v f)) x := by
  rw [P_comm hO (P_smooth hO hf w) hx v w]
  have he : P v (P w f) =ᶠ[𝓝 x] P w (P v f) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact P_comm hO hf hy v w
  exact congrArg (fun L : E →L[ℝ] ℝ => L w) he.fderiv_eq
end NavierStokes.ResistiveMagnetic.Calculus
