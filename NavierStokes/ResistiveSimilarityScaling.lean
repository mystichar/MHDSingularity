import NavierStokes.ResistiveMagneticInduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact moving-coordinate identities and dimensionless rate ratios.
The magnetic length ell is an independent input, never the core radius. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set Filter ProblemStatement PeriodicIntegration PeriodicUniqueness
open scoped Topology ContDiff

def pullback (gamma : ℝ → Space) (ell : ℝ → ℝ) (B : MagneticField) : MagneticField :=
  fun z => B (z.1,gamma z.1 + ell z.1 • z.2)

theorem partial_rescale {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (c : Space) (ell : ℝ) (i : Fin 3) (y : Space) :
    spatialPartial i (fun x => f (c+ell • x)) y =
      ell • spatialPartial i f (c+ell • y) := by
  have hd := (hf.differentiable (by simp) _).hasFDerivAt.comp y
    ((hasFDerivAt_const c y).add ((hasFDerivAt_id y).const_smul ell))
  change HasFDerivAt (fun x => f (c+ell • x)) _ y at hd
  rw [spatialPartial,hd.fderiv]
  simp [spatialPartial]

theorem laplacian_pullback {B : MagneticField} {t : ℝ}
    (hB : ContDiff ℝ ∞ (fun x => B (t,x))) (gamma : ℝ → Space) (ell : ℝ → ℝ) (y : Space) :
    spatialLaplacian (pullback gamma ell B) t y =
      (ell t)^2 • spatialLaplacian B t (gamma t+ell t • y) := by
  change (∑ i, spatialPartial i (spatialPartial i (fun x => B (t,gamma t+ell t • x))) y) = _
  have he (i : Fin 3) : spatialPartial i (fun x => B (t,gamma t+ell t • x)) =
      fun x => ell t • spatialPartial i (fun x => B (t,x)) (gamma t+ell t • x) :=
    funext (partial_rescale hB (gamma t) (ell t) i)
  simp_rw [he]
  have hi (i : Fin 3) : spatialPartial i
      (fun x => ell t • spatialPartial i (fun x => B (t,x)) (gamma t+ell t • x)) y =
      (ell t)^2 • spatialPartial i (spatialPartial i (fun x => B (t,x))) (gamma t+ell t • y) := by
    have hg : ContDiff ℝ ∞ (fun x : Space => spatialPartial i (fun x => B (t,x)) (gamma t+ell t • x)) := (spatial_partial_contDiff hB i).comp
      (contDiff_const.add (contDiff_id.const_smul (ell t)))
    change fderiv ℝ (fun x => ell t • spatialPartial i (fun x => B (t,x)) (gamma t+ell t • x)) y
      (coordinateVector i) = _
    rw [fderiv_fun_const_smul (hg.differentiable (by simp) y)]
    change ell t • spatialPartial i (fun x => spatialPartial i (fun x => B (t,x))
      (gamma t+ell t • x)) y = _
    have hp := partial_rescale (f := spatialPartial i (fun x => B (t,x)))
      (spatial_partial_contDiff hB i) (gamma t) (ell t) i y
    convert! congrArg (fun v : Space => ell t • v) hp using 1
    simp [smul_smul,pow_two]
  simp_rw [hi]
  rw [← Finset.smul_sum]
  rfl

/-- Exact equation at a moving and dilating probe, before any terms are
neglected. In particular advection and all components of the assembled
stretching operator remain present. -/
theorem moving_probe_equation {eta_m t ell ell' : ℝ} {u : VelocityField} {B : MagneticField}
    {gamma : ℝ → Space} {gamma' y : Space} {length : ℝ → ℝ} {times : Set ℝ}
    (hB : DifferentiableAt ℝ B (t,gamma t+ell • y))
    (hg : HasDerivAt gamma gamma' t) (hl : HasDerivAt length ell' t) (he : length t = ell)
    (hind : ResistiveInductionOn eta_m times u B) (ht : t ∈ times) :
    HasDerivAt (fun s => pullback gamma length B (s,y))
      (spatialDerivative u t (gamma t+ell • y) (B (t,gamma t+ell • y)) +
       eta_m • spatialLaplacian B t (gamma t+ell • y) +
       spatialDerivative B t (gamma t+ell • y) (gamma'+ell' • y-u (t,gamma t+ell • y))) t := by
  have hpath : HasDerivAt (fun s => (s,gamma s+length s • y)) (1,gamma'+ell' • y) t :=
    (hasDerivAt_id t).prodMk (hg.add (hl.smul_const y))
  have hB' : DifferentiableAt ℝ B (t,gamma t+length t • y) := by simpa only [he] using hB
  have hd := hB'.hasFDerivAt.comp_hasDerivAt t hpath
  simp only [he] at hd
  have hmat := MagneticTransport.joint_fderiv_material hB (gamma'+ell' • y)
  have hpde := hind t ht (gamma t+ell • y)
  convert! hd using 1
  rw [hmat, map_sub]
  rw [eq_sub_of_add_eq hpde]
  abel

theorem derivative_pullback_apply {B : MagneticField} {t : ℝ}
    (hB : ContDiff ℝ ∞ (fun x => B (t,x))) (gamma : ℝ → Space) (ell : ℝ → ℝ) (y v : Space) :
    spatialDerivative (pullback gamma ell B) t y v =
      ell t • spatialDerivative B t (gamma t+ell t • y) v := by
  have hd := (hB.differentiable (by simp) _).hasFDerivAt.comp y
    ((hasFDerivAt_const (gamma t) y).add ((hasFDerivAt_id y).const_smul (ell t)))
  change HasFDerivAt (fun x => B (t,gamma t+ell t • x)) _ y at hd
  change fderiv ℝ (fun x => B (t,gamma t+ell t • x)) y v = _
  rw [hd.fderiv]
  simp [spatialDerivative]

/-- Full transformed resistive PDE. U and C are spatial pullbacks of the
actual velocity and field. Translation, dilation, advection, and every
stretching component are retained, and diffusion has coefficient eta_m/ell². -/
theorem rescaled_induction {eta_m t ell' : ℝ} {u : VelocityField} {B : MagneticField}
    {gamma : ℝ → Space} {gamma' y : Space} {ell : ℝ → ℝ} {times : Set ℝ}
    (hB : DifferentiableAt ℝ B (t,gamma t+ell t • y))
    (hu : ContDiff ℝ ∞ (fun x => u (t,x))) (hsB : ContDiff ℝ ∞ (fun x => B (t,x)))
    (hg : HasDerivAt gamma gamma' t) (hl : HasDerivAt ell ell' t) (hell : 0 < ell t)
    (hind : ResistiveInductionOn eta_m times u B) (ht : t ∈ times) :
    temporalDerivative (pullback gamma ell B) t y +
      (ell t)⁻¹ • spatialDerivative (pullback gamma ell B) t y
        (pullback gamma ell u (t,y)-gamma'-ell' • y) =
      (ell t)⁻¹ • spatialDerivative (pullback gamma ell u) t y (pullback gamma ell B (t,y)) +
        (eta_m/(ell t)^2) • spatialLaplacian (pullback gamma ell B) t y := by
  have hd := moving_probe_equation hB hg hl rfl hind ht
  have htime : temporalDerivative (pullback gamma ell B) t y =
      spatialDerivative u t (gamma t+ell t • y) (B (t,gamma t+ell t • y)) +
      eta_m • spatialLaplacian B t (gamma t+ell t • y) +
      spatialDerivative B t (gamma t+ell t • y) (gamma'+ell' • y-u (t,gamma t+ell t • y)) := hd.deriv
  rw [htime,derivative_pullback_apply hsB,derivative_pullback_apply hu,laplacian_pullback hsB]
  simp only [smul_smul, inv_mul_cancel₀ hell.ne',one_smul,
    div_mul_cancel₀ _ (pow_ne_zero 2 hell.ne'),pullback]
  simp only [map_sub,map_add]
  module

def stretchingRate (K remaining : ℝ) := K/remaining
def diffusionRate (eta_m ell : ℝ) := eta_m/ell^2
def effectiveRm (K remaining eta_m ell : ℝ) := stretchingRate K remaining / diffusionRate eta_m ell

theorem effectiveRm_eq {K s eta_m ell : ℝ} (hs : 0 < s) (heta : 0 < eta_m) (hl : 0 < ell) :
    effectiveRm K s eta_m ell = K*ell^2/(eta_m*s) := by
  unfold effectiveRm stretchingRate diffusionRate
  field_simp

theorem effectiveRm_power {K L s eta_m beta : ℝ} (hL : 0 < L) (hs : 0 < s) (heta : 0 < eta_m) :
    effectiveRm K s eta_m (L*s^beta) = (K*L^2/eta_m)*s^(2*beta-1) := by
  rw [effectiveRm_eq hs heta (mul_pos hL (Real.rpow_pos_of_pos hs beta)),mul_pow]
  rw [Real.rpow_sub hs,Real.rpow_one,show 2*beta = beta*2 by ring,
    Real.rpow_mul hs.le,Real.rpow_two]
  ring
/-- Below the square-root length exponent the rate ratio grows without bound. -/
theorem effectiveRm_tendsto_infinity {K L eta_m beta : ℝ}
    (hK : 0 < K) (hL : 0 < L) (heta : 0 < eta_m) (hb : beta < 1/2) :
    Tendsto (fun s => effectiveRm K s eta_m (L*s^beta)) (𝓝[>] (0:ℝ)) atTop := by
  have hp : 0 < K*L^2/eta_m := by positivity
  have hh := (BlowupImplication.negative_power_tendsto_atTop (by linarith : 0 < 1-2*beta)
    (tendsto_id : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝[>] 0))).atTop_mul_pos hp tendsto_const_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0:ℝ)) (s := Ioi 0)] with s hs
  rw [effectiveRm_power hL hs heta]
  simp only [id_eq]
  rw [show -(1-2*beta) = 2*beta-1 by ring]
  exact mul_comm _ _

theorem effectiveRm_tendsto_zero {K L eta_m beta : ℝ}
    (hL : 0 < L) (heta : 0 < eta_m) (hb : 1/2 < beta) :
    Tendsto (fun s => effectiveRm K s eta_m (L*s^beta)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hh := ((tendsto_id.mono_left nhdsWithin_le_nhds :
    Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).rpow_const_nhds_zero
      (by linarith : 0 < 2*beta-1)).const_mul (K*L^2/eta_m)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0:ℝ)) (s := Ioi 0)] with s hs
  exact (effectiveRm_power hL hs heta).symm

theorem effectiveRm_critical {K L eta_m s : ℝ}
    (hL : 0 < L) (hs : 0 < s) (heta : 0 < eta_m) :
    effectiveRm K s eta_m (L*s^(1/2:ℝ)) = K*L^2/eta_m := by
  rw [effectiveRm_power hL hs heta]
  norm_num

/-- A rate-equality scale, not a proved cutoff for an unspecified field. -/
def cutoffRemaining (K L eta_m beta : ℝ) := (eta_m/(K*L^2))^((2*beta-1)⁻¹)

theorem cutoffRemaining_pos {K L eta_m beta : ℝ}
    (hK : 0 < K) (hL : 0 < L) (heta : 0 < eta_m) :
    0 < cutoffRemaining K L eta_m beta := Real.rpow_pos_of_pos (by positivity) _

theorem effectiveRm_cutoff {K L eta_m beta : ℝ}
    (hK : 0 < K) (hL : 0 < L) (heta : 0 < eta_m) (hb : beta ≠ 1/2) :
    let s := cutoffRemaining K L eta_m beta
    effectiveRm K s eta_m (L*s^beta) = 1 := by
  dsimp only
  rw [effectiveRm_power hL (cutoffRemaining_pos hK hL heta) heta]
  unfold cutoffRemaining
  rw [Real.rpow_inv_rpow (by positivity) (by intro h; apply hb; linarith)]
  field_simp

/-- The ideal gain evaluated at the rate-equality scale. It is a comparison
quantity; the actual resistive maximum requires a magnetic profile estimate. -/
def idealGainAtCutoff (K L eta_m beta initialRemaining : ℝ) :=
  (initialRemaining/cutoffRemaining K L eta_m beta)^K
end NavierStokes.ResistiveMagnetic
