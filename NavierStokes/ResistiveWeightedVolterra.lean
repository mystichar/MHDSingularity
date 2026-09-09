import NavierStokes.ResistivePeriodicHeatVolterra
import Euler.VolterraUniqueness

/-! Exponential weights for the actual singular Volterra integral. They
change neither the path space nor the recovered physical equation. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.WeightedVolterra
open Set MeasureTheory Filter EulerVolterraConvolution
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def weightedKernel (K : ℝ → Y →L[ℝ] X) (lambda r : ℝ) : Y →L[ℝ] X :=
  Real.exp (-lambda * r) • K r

def weightedMajorant (k : ℝ → ℝ) (lambda r : ℝ) : ℝ := Real.exp (-lambda * r) * k r

theorem weightedKernel_continuous (K : ℝ → Y →L[ℝ] X)
    (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ univ)) (lambda : ℝ) :
    ContinuousOn (fun p : ℝ × Y => weightedKernel K lambda p.1 p.2) (Ioi 0 ×ˢ univ) :=
  (show Continuous (fun p : ℝ × Y => Real.exp (-lambda * p.1)) by fun_prop).continuousOn.smul hK

theorem weightedKernel_bound (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
    (lambda r : ℝ) (hbound : ∀ y, ‖K r y‖ ≤ k r * ‖y‖) (y : Y) :
    ‖weightedKernel K lambda r y‖ ≤ weightedMajorant k lambda r * ‖y‖ := by
  change ‖Real.exp (-lambda * r) • K r y‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (hbound y) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm

theorem weightedMajorant_nonneg (k : ℝ → ℝ) (lambda r : ℝ) (hk : 0 ≤ k r) :
    0 ≤ weightedMajorant k lambda r := mul_nonneg (Real.exp_pos _).le hk

theorem weightedMajorant_norm_le (k : ℝ → ℝ) {lambda r : ℝ}
    (hlambda : 0 ≤ lambda) (hr : 0 ≤ r) :
    ‖weightedMajorant k lambda r‖ ≤ ‖k r‖ := by
  rw [weightedMajorant, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have he : Real.exp (-lambda * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)

theorem weightedMajorant_integrable (k : ℝ → ℝ) {T lambda : ℝ}
    (hk : IntegrableOn k (Ioc 0 T)) (hlambda : 0 ≤ lambda) :
    IntegrableOn (weightedMajorant k lambda) (Ioc 0 T) := by
  apply hk.norm.mono'
    ((show Continuous (fun r : ℝ => Real.exp (-lambda * r)) by fun_prop).aestronglyMeasurable.mul
      hk.aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  exact weightedMajorant_norm_le k hlambda hr.1.le

/-- An integer sequence of weights makes the kernel mass tend to zero.
Dominated convergence uses only positive integration times. -/
theorem weightedMass_tendsto_zero (k : ℝ → ℝ) {T : ℝ}
    (hk : IntegrableOn k (Ioc 0 T)) :
    Tendsto (fun n : ℕ => kernelMass T (weightedMajorant k n)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc 0 T)) (F := fun n : ℕ => weightedMajorant k n)
    (f := fun _ : ℝ => (0 : ℝ)) (fun r => ‖k r‖)
    (fun n => (weightedMajorant_integrable k hk (Nat.cast_nonneg n)).aestronglyMeasurable)
    hk.norm
    (fun n => by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
      exact weightedMajorant_norm_le k (Nat.cast_nonneg n) hr.1.le)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
      have hn : Tendsto (fun n : ℕ => (n : ℝ) * r) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hr.1
      have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
      simpa only [weightedMajorant, neg_mul, zero_mul, Function.comp_def] using! he.mul_const (k r))
  simpa only [integral_zero, kernelMass] using h

/-- The weight depends on the kernel, slab, and source bound, not the
initial datum. This argument also includes A=0 without division by A. -/
theorem exists_weight (k : ℝ → ℝ) {T : ℝ} (hk : IntegrableOn k (Ioc 0 T)) (A : ℝ) :
    ∃ n : ℕ, kernelMass T (weightedMajorant k n) * A ≤ (1 / 2 : ℝ) := by
  have h : Tendsto (fun n : ℕ => kernelMass T (weightedMajorant k n) * A) atTop (𝓝 0) := by
    simpa only [zero_mul] using (weightedMass_tendsto_zero k hk).mul_const A
  obtain ⟨n, hn⟩ := (h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  exact ⟨n, hn.le⟩

def weightPath {T : ℝ} (lambda : ℝ) (z : C(Icc (0 : ℝ) T, X)) : C(Icc (0 : ℝ) T, X) :=
  ⟨fun t => Real.exp (lambda * t.val) • z t,
    (show Continuous (fun t : Icc (0 : ℝ) T => Real.exp (lambda * t.val)) by fun_prop).smul z.continuous⟩

@[simp] theorem weightPath_apply {T : ℝ} (lambda : ℝ) (z : C(Icc (0 : ℝ) T, X))
    (t : Icc (0 : ℝ) T) : weightPath lambda z t = Real.exp (lambda * t.val) • z t := rfl

theorem weightPath_neg_norm_le {T lambda : ℝ} (hlambda : 0 ≤ lambda)
    (z : C(Icc (0 : ℝ) T, X)) : ‖weightPath (-lambda) z‖ ≤ ‖z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).mpr
  intro t
  rw [weightPath_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have he : Real.exp (-lambda * t.val) ≤ 1 := Real.exp_le_one_iff.mpr
    (by nlinarith [mul_nonneg hlambda t.property.1])
  exact (mul_le_mul he (z.norm_coe_le_norm t) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem weightPath_norm_le {T lambda : ℝ} (hlambda : 0 ≤ lambda)
    (z : C(Icc (0 : ℝ) T, X)) : ‖weightPath lambda z‖ ≤ Real.exp (lambda * T) * ‖z‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro t
  rw [weightPath_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 hlambda))
    (z.norm_coe_le_norm t) (norm_nonneg _) (Real.exp_pos _).le

@[simp] theorem weightPath_cancel {T : ℝ} (lambda : ℝ) (z : C(Icc (0 : ℝ) T, X)) :
    weightPath lambda (weightPath (-lambda) z) = z := by
  ext t
  simp only [weightPath_apply, smul_smul, ← Real.exp_add]
  rw [show lambda * t.val + -lambda * t.val = 0 by ring, Real.exp_zero, one_smul]

theorem weightedKernel_cancel (K : ℝ → Y →L[ℝ] X) (lambda : ℝ) :
    weightedKernel (weightedKernel K lambda) (-lambda) = K := by
  funext r
  simp only [weightedKernel, neg_neg, smul_smul, ← Real.exp_add]
  rw [show lambda * r + -lambda * r = 0 by ring, Real.exp_zero, one_smul]

end NavierStokes.ResistiveMagnetic.WeightedVolterra
