import NavierStokes.ResistiveModeCutoff
import NavierStokes.MagneticEnergyLowerBounds

/-! Paper I's geometric lower bound remains valid for a supplied smooth
resistive field. Its central norm and variation bound must be recomputed;
flux freezing and a diffusion-imposed minimum radius are not asserted. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set Metric MeasureTheory ProblemStatement MagneticAmplificationRegion MagneticEnergyLowerBounds
open scoped ContDiff ENNReal

theorem material_high_field_region (S : MagneticCompactFlow.Slab) (B : MagneticField)
    (hd : ∀ t ∈ Icc S.a S.b, ∀ x, spatialDivergence S.velocity t x = 0)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (hB : ContDiff ℝ ∞ (fun x => B (t,x)))
    (xi : Space) {r0 M : ℝ} (hr : 0 < r0) (hM : 0 < M)
    (hcenter : ‖B (t,S.Phi t xi)‖ = M) :
    ∃ H : ℝ, 0 ≤ H ∧
    let r := radius r0 M H
    0 < r ∧ IsOpen (S.region t xi r) ∧
    volume (S.region t xi r) = ENNReal.ofReal (c3*r^3) ∧
    (∀ x ∈ S.region t xi r, M/2 ≤ ‖B (t,x)‖) ∧
    ENNReal.ofReal ((c3/8)*M^2*r^3) ≤ MagneticCompactFlow.energy B t := by
  let Q : Space → Space := fun x => B (t,S.Phi t x)
  have hQ : ContDiff ℝ ∞ Q := hB.comp (S.Phi_smooth t ht)
  obtain ⟨H,hH,hbound⟩ := ((isCompact_closedBall xi r0).image
    (hQ.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  have hb : ∀ x ∈ closedBall xi r0, ‖fderiv ℝ Q x‖ ≤ H :=
    fun x hx => hbound _ ⟨x,hx,rfl⟩
  let r := radius r0 M H
  have hrp : 0 < r := (radius_bounds hr hM hH.le).1
  have hv : volume (S.region t xi r) = ENNReal.ofReal (c3*r^3) :=
    (S.region_volume hd t ht xi r).trans (ball_volume xi hrp.le)
  have hhigh : ∀ x ∈ S.region t xi r, M/2 ≤ ‖B (t,x)‖ := by
    rintro x ⟨y,hy,rfl⟩
    exact high_field_ball (Q := Q) (xi := xi) (x := y) hr hM hH.le hcenter (fun x _ => hQ.differentiable (by simp) x) hb hy
  refine ⟨H,hH.le,hrp,S.region_open t xi r,hv,hhigh,?_⟩
  have he := energy_of_region B t M hM.le _ (S.region_open t xi r).measurableSet hhigh
  rw [hv,← ENNReal.ofReal_mul (by positivity : 0 ≤ M^2/8)] at he
  convert! he using 1
  congr 1
  ring
end NavierStokes.ResistiveMagnetic
