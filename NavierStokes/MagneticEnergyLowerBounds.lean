import NavierStokes.MagneticDeformationBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Actual image-volume preservation and normalized magnetic-energy lower
bounds. No integrability assumption is needed for these nonnegative integrals. -/
noncomputable section
namespace NavierStokes.MagneticEnergyLowerBounds
open Set Filter Metric MeasureTheory ProblemStatement MagneticAmplificationRegion
open scoped Topology ENNReal ContDiff

def c3 : ℝ := Real.pi*4/3

theorem c3_pos : 0 < c3 := by unfold c3; positivity

theorem unit_ball_volume : volume (ball (0 : Space) 1) = ENNReal.ofReal c3 := by
  simp [EuclideanSpace.volume_ball_fin_three,c3]

theorem unit_ball_finite_positive : 0 < volume (ball (0 : Space) 1) ∧ volume (ball (0 : Space) 1) < ⊤ := by
  rw [unit_ball_volume]
  exact ⟨ENNReal.ofReal_pos.mpr c3_pos,ENNReal.ofReal_lt_top⟩

theorem ball_volume (xi : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball xi r) = ENNReal.ofReal (c3*r^3) := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_mul c3_pos.le, ENNReal.ofReal_pow hr]
  exact mul_comm _ _

theorem energy_of_region (B : MagneticField) (t M : ℝ) (hM : 0 ≤ M)
    (U : Set Space) (hU : MeasurableSet U) (hB : ∀ x ∈ U, M/2 ≤ ‖B (t,x)‖) :
    ENNReal.ofReal (M^2/8) * volume U ≤ MagneticCompactFlow.energy B t := by
  have hl : ENNReal.ofReal ((M/2)^2) * volume U ≤ ∫⁻ x, ENNReal.ofReal (‖B (t,x)‖^2) := by
    rw [← lintegral_indicator_const hU]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (hB x hx) 2)
    · simp only [indicator_of_notMem hx]; exact zero_le
  have hh := mul_le_mul_right hl (2 : ℝ≥0∞)⁻¹
  unfold MagneticCompactFlow.energy
  convert hh using 1
  rw [← mul_assoc]
  congr 1
  have he : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/2 : ℝ) := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]; simp
  rw [he,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  ring

end NavierStokes.MagneticEnergyLowerBounds

namespace NavierStokes.MagneticCompactFlow.Slab
open Set Filter Metric MeasureTheory ProblemStatement EulerSmoothBanachFlow
open MagneticAmplificationRegion MagneticEnergyLowerBounds
open scoped Topology ENNReal ContDiff
variable (S : Slab)

def flowHomeomorph (t : ℝ) : Space ≃ₜ Space := S.data.flowHomeomorph 0 (t-S.a)

theorem Phi_measurePreserving
    (hd : ∀ t ∈ Icc S.a S.b, ∀ x, spatialDivergence S.velocity t x = 0)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) : MeasurePreserving (S.Phi t) volume volume := by
  apply forward_measurePreserving _ _ S.coefficient _ volume (S.slabTime t ht)
  intro s y
  change EulerSmoothLimit.divergence (fun x => S.velocity (S.a+s,x)) y = 0
  rw [EulerSmoothLimit.divergence_eq_coordinate_sum]
  apply hd (S.a+s) ⟨by linarith [s.property.1],by linarith [s.property.2]⟩ y

def region (t : ℝ) (xi : Space) (r : ℝ) : Set Space := S.Phi t '' ball xi r

theorem region_open (t : ℝ) (xi : Space) (r : ℝ) : IsOpen (S.region t xi r) :=
  (S.flowHomeomorph t).isOpenMap _ isOpen_ball

theorem region_volume
    (hd : ∀ t ∈ Icc S.a S.b, ∀ x, spatialDivergence S.velocity t x = 0)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (xi : Space) (r : ℝ) :
    volume (S.region t xi r) = volume (ball xi r) := by
  have hh := (S.Phi_measurePreserving hd t ht).measure_preimage
    (S.region_open t xi r).measurableSet.nullMeasurableSet
  change volume (S.Phi t ⁻¹' (S.Phi t '' ball xi r)) = _ at hh
  rw [preimage_image_eq _ (show Function.Injective (S.Phi t) from (S.flowHomeomorph t).injective)] at hh
  exact hh.symm

theorem quantitative_region (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (hd : ∀ t ∈ Icc S.a S.b, ∀ x, spatialDivergence S.velocity t x = 0)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (xi : Space) {r0 M H : ℝ}
    (hr : 0 < r0) (hM : 0 < M) (hH : 0 ≤ H) (hcenter : ‖S.Q W t xi‖ = M)
    (hbound : ∀ x ∈ closedBall xi r0, ‖fderiv ℝ (S.Q W t) x‖ ≤ H) :
    let r := radius r0 M H
    IsOpen (S.region t xi r) ∧
    volume (S.region t xi r) = ENNReal.ofReal (c3*r^3) ∧
    (∀ x ∈ S.region t xi r, M/2 ≤ ‖S.magnetic W (t,x)‖) ∧
    ENNReal.ofReal ((c3/8)*M^2*r^3) ≤ MagneticCompactFlow.energy (S.magnetic W) t := by
  let r := radius r0 M H
  have hrp : 0 < r := (radius_bounds hr hM hH).1
  have hv : volume (S.region t xi r) = ENNReal.ofReal (c3*r^3) :=
    (S.region_volume hd t ht xi r).trans (ball_volume xi hrp.le)
  have hb : ∀ x ∈ S.region t xi r, M/2 ≤ ‖S.magnetic W (t,x)‖ := by
    rintro x ⟨y,hy,rfl⟩
    rw [S.magnetic_Phi_Q]
    exact high_field_ball hr hM hH hcenter
      (fun x _ => (S.Q_smooth W hW t ht).differentiable (by simp) x) hbound hy
  refine ⟨S.region_open t xi r,hv,hb,?_⟩
  have he := energy_of_region (S.magnetic W) t M hM.le _ (S.region_open t xi r).measurableSet hb
  rw [hv,← ENNReal.ofReal_mul (by positivity : 0 ≤ M^2/8)] at he
  convert he using 1
  congr 1
  ring
end NavierStokes.MagneticCompactFlow.Slab
