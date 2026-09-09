import NavierStokes.MagneticEnergyLowerBounds

/-! Conditional terminal estimates. No power bound on the actual label
variation is assumed elsewhere or asserted by this file. -/
noncomputable section
namespace NavierStokes.MagneticEnergyLowerBounds
open Set Filter MagneticAmplificationRegion
open scoped Topology ENNReal

/-- Algebraic radius bound valid also when H=0. -/
theorem radius_lower {r0 M H L R : ℝ} (hr : 0 < r0) (hM : 0 < M)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 1 ≤ R) (hb : H ≤ L*M*R) :
    r0 / (2*(1+r0*L)) / R ≤ radius r0 M H := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hp : 0 < 1+r0*L := by positivity
  have hden : 0 < 2*(M+r0*H) := by positivity
  rw [radius, div_le_div_iff₀ hRp hden]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2*(1+r0*L))]
  have h1 : M ≤ M*R := le_mul_of_one_le_right hM.le hR
  nlinarith [mul_le_mul_of_nonneg_left hb hr.le,
    mul_le_mul_of_nonneg_left h1 hr.le]

/-- The exponent in the lower bound is negative under the stated criterion. -/
theorem energy_exponent_negative {K p : ℝ} (hK : 0 < K) (hp : p < 5*K/3) :
    -2*K + 3*max (p-K) 0 < 0 := by
  rcases le_total (p-K) 0 with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- Explicit power-law lower bound from an additional power bound on H. -/
theorem power_lower {r0 m C K p s H : ℝ}
    (hr : 0 < r0) (hm : 0 < m) (hC : 0 < C)
    (hs : 0 < s) (hs1 : s ≤ 1) (hH : 0 ≤ H) (hb : H ≤ C*s^(-p)) :
    let q := max (p-K) 0
    let d := r0/(2*(1+r0*(C/m)))
    (c3/8)*m^2*d^3*s^(-2*K+3*q) ≤
      (c3/8)*(m*s^(-K))^2*(radius r0 (m*s^(-K)) H)^3 := by
  let q := max (p-K) 0
  let d := r0/(2*(1+r0*(C/m)))
  have hq : 0 ≤ q := le_max_right _ _
  have hqp : p-K ≤ q := le_max_left _ _
  have hpow := Real.rpow_pos_of_pos hs (-K)
  have hR : 1 ≤ s^(-q) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (neg_nonpos.mpr hq)
  have hb' : H ≤ (C/m)*(m*s^(-K))*s^(-q) := by
    calc
      H ≤ C*s^(-p) := hb
      _ ≤ C*s^(-K + -q) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)) hC.le
      _ = _ := by rw [Real.rpow_add hs]; field_simp
  have hrl := radius_lower hr (mul_pos hm hpow) hH (div_pos hC hm).le hR hb'
  have he : d / s^(-q) = d*s^q := by rw [Real.rpow_neg hs.le, div_inv_eq_mul]
  change d / s^(-q) ≤ _ at hrl
  rw [he] at hrl
  have hd : 0 < d := by dsimp [d]; positivity
  have hc3 := c3_pos
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ d*s^q) hrl 3)
    (show 0 ≤ (c3/8)*(m*s^(-K))^2 by positivity)
  convert! hh using 1
  have h2 : (s^(-K))^2 = s^((-K)*2) := by rw [Real.rpow_mul hs.le, Real.rpow_two]
  have h3 : (s^q)^3 = s^(q*3) := by simp [Real.rpow_mul hs.le]
  rw [mul_pow, mul_pow, h2, h3]
  rw [show -2*K+3*q = (-K)*2+q*3 by ring, Real.rpow_add hs]
  ring
/-- A sufficiently late H-bound implies an eventual energy power lower bound.
All hypotheses refer to single functions H and E on the preterminal interval. -/
theorem eventual_power_lower (E : ℝ → ℝ≥0∞) (H : ℝ → ℝ)
    {r0 m C K p : ℝ} (hr : 0 < r0) (hm : 0 < m) (hC : 0 < C)
    (hH : ∀ᶠ t in 𝓝[<] (1:ℝ), 0 ≤ H t)
    (hb : ∀ᶠ t in 𝓝[<] (1:ℝ), H t ≤ C*(1-t)^(-p))
    (hE : ∀ᶠ t in 𝓝[<] (1:ℝ),
      ENNReal.ofReal ((c3/8)*(m*(1-t)^(-K))^2*
        (radius r0 (m*(1-t)^(-K)) (H t))^3) ≤ E t) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in 𝓝[<] (1:ℝ),
      ENNReal.ofReal (c*(1-t)^(-2*K+3*max (p-K) 0)) ≤ E t := by
  let d := r0/(2*(1+r0*(C/m)))
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨(c3/8)*m^2*d^3, mul_pos (mul_pos (div_pos c3_pos (by norm_num)) (sq_pos_of_pos hm)) (pow_pos hd 3),?_⟩
  filter_upwards [hH,hb,hE,Ioo_mem_nhdsLT (show (0:ℝ)<1 by norm_num)] with t htH htb htE ht
  exact (ENNReal.ofReal_le_ofReal (power_lower hr hm hC (sub_pos.mpr ht.2)
    (by linarith [ht.1] : 1-t ≤ 1) htH htb)).trans htE

/-- Sufficient, conditional energy divergence. This does not discharge hb
for the actual compact velocity. -/
theorem conditional_energy_divergence (E : ℝ → ℝ≥0∞) (H : ℝ → ℝ)
    {r0 m C K p : ℝ} (hr : 0 < r0) (hm : 0 < m) (hC : 0 < C)
    (hK : 0 < K) (_hp : 0 ≤ p) (hcrit : p < 5*K/3)
    (hH : ∀ᶠ t in 𝓝[<] (1:ℝ), 0 ≤ H t)
    (hb : ∀ᶠ t in 𝓝[<] (1:ℝ), H t ≤ C*(1-t)^(-p))
    (hE : ∀ᶠ t in 𝓝[<] (1:ℝ),
      ENNReal.ofReal ((c3/8)*(m*(1-t)^(-K))^2*
        (radius r0 (m*(1-t)^(-K)) (H t))^3) ≤ E t) :
    Tendsto E (𝓝[<] (1:ℝ)) (𝓝 ⊤) := by
  obtain ⟨c,hc,he⟩ := eventual_power_lower E H hr hm hC hH hb hE
  have hn := energy_exponent_negative hK hcrit
  have hl := (BlowupImplication.negative_power_tendsto_atTop (neg_pos.mpr hn)
    (BlowupImplication.remaining_time_tendsto 1)).atTop_mul_pos hc tendsto_const_nhds
  simp only [neg_neg] at hl
  apply tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hl)
  filter_upwards [he] with t ht
  simpa only [Function.comp_apply, mul_comm] using ht
end NavierStokes.MagneticEnergyLowerBounds
