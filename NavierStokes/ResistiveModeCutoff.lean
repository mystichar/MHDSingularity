import NavierStokes.ResistiveAxialModel

/-! A damped scalar mode with an explicitly assumed inverse-power curvature.
Finite diffusivity cuts off this mode when r>0. This is not a cutoff theorem
for an unconstructed assembled-flow magnetic profile. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Mode
open Set Filter
open scoped Topology

def profile (A b x : ℝ) := x^A * Real.exp (-b*x)

theorem profile_pos {A b x : ℝ} (hx : 0 < x) : 0 < profile A b x :=
  mul_pos (Real.rpow_pos_of_pos hx A) (Real.exp_pos _)

theorem profile_deriv {A b x : ℝ} (hx : 0 < x) :
    HasDerivAt (profile A b) (x^(A-1)*Real.exp (-b*x)*(A-b*x)) x := by
  have hd := (Real.hasDerivAt_rpow_const (p := A) (Or.inl hx.ne')).mul
    (((hasDerivAt_id x).const_mul (-b)).exp)
  have he : x^A = x^(A-1)*x := by
    calc
      x^A = x^((A-1)+1) := by congr 1; ring
      _ = x^(A-1)*x := by rw [Real.rpow_add hx,Real.rpow_one]
  simp only [id_eq] at hd
  convert! hd using 1
  rw [he]
  ring

/-- Exact global maximum of the damped mode profile on positive x. -/
theorem profile_le_peak {A b x : ℝ} (hA : 0 < A) (hb : 0 < b) (hx : 0 < x) :
    profile A b x ≤ profile A b (A/b) := by
  have hp : 0 < A/b := div_pos hA hb
  by_cases hxp : x ≤ A/b
  · have hm : MonotoneOn (profile A b) (Icc x (A/b)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      · intro y hy
        exact (profile_deriv (hx.trans_le hy.1)).continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Ioo x (A/b) := by simpa only [interior_Icc] using hy
        exact (profile_deriv (hx.trans hy'.1)).hasDerivWithinAt
      · intro y hy
        have hy' : y ∈ Ioo x (A/b) := by simpa only [interior_Icc] using hy
        have hby : b*y ≤ A := by nlinarith [(le_div_iff₀ hb).mp hy'.2.le]
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hx.trans hy'.1).le _) (Real.exp_pos _).le) (sub_nonneg.mpr hby)
    exact hm ⟨le_rfl,hxp⟩ ⟨hxp,le_rfl⟩ hxp
  · have hpx := le_of_not_ge hxp
    have hm : AntitoneOn (profile A b) (Icc (A/b) x) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      · intro y hy
        exact (profile_deriv (hp.trans_le hy.1)).continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Ioo (A/b) x := by simpa only [interior_Icc] using hy
        exact (profile_deriv (hp.trans hy'.1)).hasDerivWithinAt
      · intro y hy
        have hy' : y ∈ Ioo (A/b) x := by simpa only [interior_Icc] using hy
        have hby : A ≤ b*y := by nlinarith [(div_le_iff₀ hb).mp hy'.1.le]
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (Real.rpow_nonneg (hp.trans hy'.1).le _) (Real.exp_pos _).le) (sub_nonpos.mpr hby)
    exact hm ⟨le_rfl,hpx⟩ ⟨hpx,le_rfl⟩ hpx

def gain (K d r s0 s : ℝ) :=
  s0^K * Real.exp ((d/r)*s0^(-r)) * profile (K/r) (d/r) (s^(-r))

def peakRemaining (K d r : ℝ) := (d/K)^(r⁻¹)
def peakGain (K d r s0 : ℝ) :=
  s0^K * Real.exp ((d/r)*s0^(-r)) * profile (K/r) (d/r) (K/d)

theorem gain_pos {K d r s0 s : ℝ} (hs0 : 0 < s0) (hs : 0 < s) :
    0 < gain K d r s0 s :=
  mul_pos (mul_pos (Real.rpow_pos_of_pos hs0 _) (Real.exp_pos _))
    (profile_pos (Real.rpow_pos_of_pos hs _))

theorem gain_le_peak {K d r s0 s : ℝ} (hK : 0 < K) (hd : 0 < d) (hr : 0 < r)
    (hs0 : 0 < s0) (hs : 0 < s) : gain K d r s0 s ≤ peakGain K d r s0 := by
  have he : (K/r)/(d/r) = K/d := by field_simp
  have hb := profile_le_peak (div_pos hK hr) (div_pos hd hr) (Real.rpow_pos_of_pos hs (-r))
  rw [he] at hb
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem gain_tendsto_zero {K d r s0 : ℝ} (hd : 0 < d) (hr : 0 < r) :
    Tendsto (gain K d r s0) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hx := BlowupImplication.negative_power_tendsto_atTop hr
    (tendsto_id : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝[>] 0))
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K/r) (d/r) (div_pos hd hr)).comp hx
  have hh' := hh.const_mul (s0^K * Real.exp ((d/r)*s0^(-r)))
  convert! hh' using 1; simp
theorem gain_as_power {K d r s0 s : ℝ} (hr : r ≠ 0) (hs : 0 < s) :
    gain K d r s0 s = (s0^K * Real.exp ((d/r)*s0^(-r))) *
      s^(-K) * Real.exp (-(d/r)*s^(-r)) := by
  unfold gain profile
  rw [← Real.rpow_mul hs.le]
  have he : -r*(K/r) = -K := by field_simp
  rw [he]
  ring

theorem gain_initial {K d r s0 : ℝ} (hr : r ≠ 0) (hs0 : 0 < s0) :
    gain K d r s0 s0 = 1 := by
  rw [gain_as_power hr hs0,Real.rpow_neg hs0.le K]
  rw [show -(d/r)*s0^(-r) = -((d/r)*s0^(-r)) by ring,Real.exp_neg]
  field_simp

theorem gain_deriv {K d r s0 s : ℝ} (hr : r ≠ 0) (hs : 0 < s) :
    HasDerivAt (gain K d r s0) (((-K+d*s^(-r))/s)*gain K d r s0 s) s := by
  let c := s0^K * Real.exp ((d/r)*s0^(-r))
  have he : gain K d r s0 =ᶠ[𝓝 s] (fun y => c*y^(-K)*Real.exp (-(d/r)*y^(-r))) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    exact gain_as_power hr hy
  have hd := ((Real.hasDerivAt_rpow_const (p := -K) (Or.inl hs.ne')).const_mul c).mul
    (((Real.hasDerivAt_rpow_const (p := -r) (Or.inl hs.ne')).const_mul (-(d/r))).exp)
  have hd' := hd.congr_of_eventuallyEq he
  convert! hd' using 1
  rw [gain_as_power hr hs]
  rw [Real.rpow_sub hs, Real.rpow_sub hs, Real.rpow_one]
  dsimp [c]
  field_simp

/-- Exact remaining-time law with stretching K/s and curvature damping
 d*s^(-(r+1)). Here d=eta_m*lambda/L^2 in an eigenmode closure. -/
theorem physical_time_mode {K d r a B0 t : ℝ} (hr : r ≠ 0) (ht : t < 1) :
    HasDerivAt (fun s => B0*gain K d r (1-a) (1-s))
      ((K/(1-t)-d*(1-t)^(-(r+1)))*(B0*gain K d r (1-a) (1-t))) t := by
  have hd := ((gain_deriv (K := K) (d := d) (s0 := 1-a) hr (sub_pos.mpr ht)).comp t
    ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))).const_mul B0
  convert! hd using 1
  rw [show -(r+1) = -r-1 by ring,Real.rpow_sub (sub_pos.mpr ht),Real.rpow_one]
  ring

theorem gain_at_peak {K d r s0 : ℝ} (hK : 0 < K) (hd : 0 < d) (hr : r ≠ 0) :
    gain K d r s0 (peakRemaining K d r) = peakGain K d r s0 := by
  have hs : 0 < peakRemaining K d r := Real.rpow_pos_of_pos (div_pos hd hK) _
  unfold gain peakGain
  congr 2
  rw [Real.rpow_neg hs.le]
  unfold peakRemaining
  rw [Real.rpow_inv_rpow (div_pos hd hK).le hr,inv_div]

theorem peakGain_formula {K d r s0 : ℝ} (hd : d ≠ 0) (hr : r ≠ 0) :
    peakGain K d r s0 = s0^K * (K/d)^(K/r) *
      Real.exp ((d/r)*s0^(-r)-K/r) := by
  unfold peakGain profile
  rw [Real.exp_sub]
  have he : -(d/r)*(K/d) = -(K/r) := by field_simp
  rw [he,Real.exp_neg]
  ring
/-- Conditional finite-diffusivity amplification law for a single supplied
induction solution. The additional eigen-curvature closure is explicit. -/
theorem trajectory_mode {eta_m a b B0 K d r t : ℝ}
    {u : ProblemStatement.VelocityField} {B : ProblemStatement.MagneticField}
    {gamma : ℝ → ProblemStatement.Space} {x0 : ProblemStatement.Space}
    (heta : 0 < eta_m) (hr : 0 < r) (hb : b < 1)
    (hg : MagneticTransport.IsLagrangianTrajectoryOn u gamma a b x0)
    (hind : ResistiveInductionOn eta_m (Ioo a b) u B)
    (hBc : ContinuousOn (fun s => B (s,gamma s)) (Icc a b))
    (hBd : ∀ s ∈ Ioo a b, DifferentiableAt ℝ B (s,gamma s))
    (hA : ContinuousOn (fun s => ProblemStatement.spatialDerivative u s (gamma s)) (Icc a b))
    (haxis : ∀ s ∈ Ioo a b, ProblemStatement.spatialDerivative u s (gamma s)
      (ProblemStatement.coordinateVector 2) = (K/(1-s)) • ProblemStatement.coordinateVector 2)
    (hcurvature : ∀ s ∈ Ioo a b, ProblemStatement.spatialLaplacian B s (gamma s) =
      -((d/eta_m)*(1-s)^(-(r+1))) • B (s,gamma s))
    (hseed : B (a,gamma a) = B0 • ProblemStatement.coordinateVector 2)
    (ht : t ∈ Icc a b) :
    B (t,gamma t) = (B0*gain K d r (1-a) (1-t)) • ProblemStatement.coordinateVector 2 := by
  have ha : a < 1 := hg.ordered.trans_lt hb
  have hmu : ContinuousOn (fun s : ℝ => (d/eta_m)*(1-s)^(-(r+1))) (Icc a b) :=
    continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).rpow_const
      (fun s hs => Or.inl (sub_pos.mpr (hs.2.trans_lt hb)).ne'))
  apply pure_axial_of_curvature_closure hg hind hBc hBd hA hmu haxis hcurvature
    (fun s hs => (physical_time_mode (K := K) (d := d) (a := a) (B0 := B0) hr.ne'
      (hs.2.trans_lt hb)).continuousAt.continuousWithinAt) _ _ hseed ht
  · intro s hs
    convert! physical_time_mode (K := K) (d := d) (a := a) (B0 := B0) hr.ne' (hs.2.le.trans_lt hb) using 1
    field_simp
  · rw [gain_initial hr.ne' (sub_pos.mpr ha),mul_one]

/-- The rate-equality peak is reached inside the chosen forward interval
exactly when its remaining time belongs to that interval. -/
theorem trajectory_peak_time {a b K d r : ℝ}
    (hleft : 1-b ≤ peakRemaining K d r) (hright : peakRemaining K d r ≤ 1-a) :
    1-peakRemaining K d r ∈ Icc a b := by constructor <;> linarith
/-- A bound for the vector mode in trajectory_mode. It is independent of
remaining time; it becomes an actual field bound only under that theorem's
PDE, trajectory, regularity, axial-column, and curvature premises. -/
theorem axial_mode_norm_le_peak {K d r s0 s B0 : ℝ}
    (hK : 0 < K) (hd : 0 < d) (hr : 0 < r) (hs0 : 0 < s0) (hs : 0 < s) :
    ‖(B0*gain K d r s0 s) • ProblemStatement.coordinateVector 2‖ ≤
      |B0| *peakGain K d r s0 := by
  simp only [norm_smul,ProblemStatement.coordinateVector,PiLp.norm_single,norm_one,mul_one,
    Real.norm_eq_abs,abs_mul,abs_of_pos (gain_pos hs0 hs)]
  exact mul_le_mul_of_nonneg_left (gain_le_peak hK hd hr hs0 hs) (abs_nonneg B0)
end NavierStokes.ResistiveMagnetic.Mode
