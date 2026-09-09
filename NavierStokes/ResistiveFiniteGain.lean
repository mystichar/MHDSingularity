import NavierStokes.ResistiveIdealComparison
import NavierStokes.MagneticPeriodicMain

/-! Observation times and finite-gain transfer from an explicit comparison
estimate. This module does not construct resistive solutions or assert the
comparison estimate for them. It uses no resistive axial invariance. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Comparison
open Set Filter ProblemStatement
open scoped Topology

def observationTime (a K G : ℝ) : ℝ := 1-(1-a)*(2*G)^(-K⁻¹)

theorem observationTime_bounds {a K G : ℝ} (ha : a < 1) (hK : 0 < K) (hG : 1 < G) :
    a < observationTime a K G ∧ observationTime a K G < 1 := by
  have hbase : 1 < 2*G := by linarith
  have hp := Real.rpow_pos_of_pos (by linarith : 0 < 2*G) (-K⁻¹)
  have hl : (2*G)^(-K⁻¹) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hbase (neg_neg_of_pos (inv_pos.mpr hK))
  unfold observationTime
  constructor <;> nlinarith [mul_pos (sub_pos.mpr ha) hp]

theorem observationTime_gain {a K G : ℝ} (ha : a < 1) (hK : 0 < K) (hG : 1 < G) :
    ((1-a)/(1-observationTime a K G))^K = 2*G := by
  have hs : 1-a ≠ 0 := (sub_pos.mpr ha).ne'
  have hp : 0 < 2*G := by linarith
  have he : (1-a)/(1-observationTime a K G) = (2*G)^K⁻¹ := by
    unfold observationTime
    rw [sub_sub_cancel,Real.rpow_neg hp.le]
    field_simp
  rw [he,Real.rpow_inv_rpow hp.le hK.ne']

/-- A threshold that also covers a zero comparison constant. -/
def diffusivityThreshold (G Bz0 C : ℝ) : ℝ := G*|Bz0|/(1+C)

theorem diffusivityThreshold_pos {G Bz0 C : ℝ} (hG : 0 < G) (hB : Bz0 ≠ 0) (hC : 0 ≤ C) :
    0 < diffusivityThreshold G Bz0 C := by
  exact div_pos (mul_pos hG (abs_pos.mpr hB)) (by linarith)

/-- Triangle-inequality transfer for arbitrary vectors. -/
theorem finite_gain_of_error {v ideal : Space} {G Bz0 C eta_m : ℝ}
    (_hG : 0 < G) (_hB : Bz0 ≠ 0) (hC : 0 ≤ C) (heta : 0 < eta_m)
    (hsmall : eta_m < diffusivityThreshold G Bz0 C)
    (hideal : ‖ideal‖ = 2*G*|Bz0|) (herror : ‖v-ideal‖ ≤ eta_m*C) :
    G*|Bz0| ≤ ‖v‖ := by
  have hc : 0 < 1+C := by linarith
  have hh : eta_m*(1+C) < G*|Bz0| := (lt_div_iff₀ hc).mp hsmall
  rw [norm_sub_rev] at herror
  have htri : ‖ideal‖ ≤ ‖ideal-v‖+‖v‖ := by simpa using norm_add_le (ideal-v) v
  nlinarith

/-- Correct family quantifier order, conditional on a single family's
explicit fixed-slab comparison. The family, a and Bz0 precede every G.
This theorem is not the requested closed PDE existence theorem. -/
theorem family_finite_gain {a K Bz0 : ℝ} {gamma : ℝ → Space}
    (ha : a < 1) (hK : 0 < K) (hB : Bz0 ≠ 0)
    (ideal : MagneticField) (family : ℝ → MagneticField)
    (hideal : ∀ t ∈ Ico a 1, ‖ideal (t,gamma t)‖ =
      |Bz0| * ((1-a)/(1-t))^K)
    (hcomparison : ∀ b ∈ Ioo a 1, ∃ C : ℝ, 0 ≤ C ∧
      ∀ eta_m > 0, ∀ t ∈ Icc a b, ∀ x,
        ‖family eta_m (t,x)-ideal (t,x)‖ ≤ eta_m*C) :
    ∀ G > 1, ∃ t ∈ Ioo a 1, ∃ eta_G > 0,
      ∀ eta_m ∈ Ioo 0 eta_G, G*|Bz0| ≤ ‖family eta_m (t,gamma t)‖ := by
  intro G hG
  let t := observationTime a K G
  have ht : t ∈ Ioo a 1 := observationTime_bounds ha hK hG
  obtain ⟨C,hC,herror⟩ := hcomparison t ht
  refine ⟨t,ht,diffusivityThreshold G Bz0 C,diffusivityThreshold_pos (by linarith) hB hC,?_⟩
  intro eta_m heta
  apply finite_gain_of_error (by linarith : 0 < G) hB hC heta.1 heta.2 _
    (herror eta_m heta.1 t ⟨ht.1.le,le_rfl⟩ (gamma t))
  rw [hideal t ⟨ht.1.le,ht.2⟩,observationTime_gain ha hK hG]
  ring

/-- Fixed-slab vanishing-diffusivity convergence follows from the stated
uniform error estimate. This is uniform in t,x through that same bound. -/
theorem error_tendsto_zero {C : ℝ} (_hC : 0 ≤ C) {error : ℝ → ℝ}
    (hnonneg : ∀ eta_m > 0, 0 ≤ error eta_m)
    (hbound : ∀ eta_m > 0, error eta_m ≤ eta_m*C) :
    Tendsto error (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hh : Tendsto (fun eta_m : ℝ => eta_m*C) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const C
  apply squeeze_zero' _ _ hh
  · filter_upwards [self_mem_nhdsWithin] with eta_m heta
    exact hnonneg eta_m heta
  · filter_upwards [self_mem_nhdsWithin] with eta_m heta
    exact hbound eta_m heta
end NavierStokes.ResistiveMagnetic.Comparison
