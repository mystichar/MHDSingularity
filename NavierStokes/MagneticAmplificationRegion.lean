import NavierStokes.MagneticCompactMain
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative label-space high-field balls. The radius is well-defined
also when the derivative bound H is zero. -/
noncomputable section
namespace NavierStokes.MagneticAmplificationRegion
open Set Metric

def radius (r0 M H : ℝ) : ℝ := r0*M/(2*(M+r0*H))

theorem radius_bounds {r0 M H : ℝ} (hr : 0 < r0) (hM : 0 < M) (hH : 0 ≤ H) :
    0 < radius r0 M H ∧ radius r0 M H ≤ r0/2 ∧ H*radius r0 M H ≤ M/2 := by
  have hp : 0 < 2*(M+r0*H) := by positivity
  refine ⟨div_pos (mul_pos hr hM) hp,?_,?_⟩
  · apply (div_le_iff₀ hp).2
    nlinarith [mul_nonneg hr.le hH]
  · unfold radius
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hp).2
    nlinarith [sq_nonneg M]

theorem high_field_ball {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Q : E → V} {xi : E} {r0 M H : ℝ}
    (hr : 0 < r0) (hM : 0 < M) (hH : 0 ≤ H) (hcenter : ‖Q xi‖ = M)
    (hd : ∀ x ∈ closedBall xi r0, DifferentiableAt ℝ Q x)
    (hbound : ∀ x ∈ closedBall xi r0, ‖fderiv ℝ Q x‖ ≤ H)
    {x : E} (hx : x ∈ ball xi (radius r0 M H)) : M/2 ≤ ‖Q x‖ := by
  have hb := radius_bounds hr hM hH
  have hx0 : x ∈ closedBall xi r0 := by
    exact (mem_closedBall.mpr ((mem_ball.mp hx).le.trans (hb.2.1.trans (by linarith))))
  have hl := (convex_closedBall xi r0).norm_image_sub_le_of_norm_fderiv_le hd hbound
    (mem_closedBall_self hr.le) hx0
  have hdist : ‖x-xi‖ ≤ radius r0 M H := by simpa only [← dist_eq_norm] using (mem_ball.mp hx).le
  have hdiff : ‖Q x-Q xi‖ ≤ M/2 :=
    hl.trans ((mul_le_mul_of_nonneg_left hdist hH).trans hb.2.2)
  have hn := norm_sub_norm_le (Q xi) (Q x)
  rw [norm_sub_rev, hcenter] at hn
  linarith
end NavierStokes.MagneticAmplificationRegion
