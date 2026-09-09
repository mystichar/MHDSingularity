import NavierStokes.ResistiveMagneticDivergence
import NavierStokes.ResistiveMagneticEnergy

/-! Exact ideal/resistive difference algebra. These are local PDE lemmas;
no resistive existence or parabolic maximum principle is assumed or claimed. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Comparison
open Set ProblemStatement MagneticTransport PeriodicUniqueness
open scoped ContDiff InnerProductSpace

/-- The unprojected induction source, in physical coordinates. -/
def source (u : VelocityField) (B : MagneticField) (t : ℝ) (x : Space) : Space :=
  -spatialDerivative B t x (u (t,x)) + spatialDerivative u t x (B (t,x))

theorem source_norm_le (u B : VelocityField) (t : ℝ) (x : Space) :
    ‖source u B t x‖ ≤ ‖spatialDerivative B t x‖ * ‖u (t,x)‖ +
      ‖spatialDerivative u t x‖ * ‖B (t,x)‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa using (spatialDerivative B t x).le_opNorm (u (t,x)))
    ((spatialDerivative u t x).le_opNorm (B (t,x))))

theorem source_sub {u B I : VelocityField} {t : ℝ}
    (hB : ContDiff ℝ ∞ (fun x => B (t,x))) (hI : ContDiff ℝ ∞ (fun x => I (t,x))) (x : Space) :
    source u (B-I) t x = source u B t x-source u I t x := by
  simp only [source,spatialDerivative_sub hB hI,sub_apply,Pi.sub_apply,map_sub]
  module

/-- Subtraction of the two supplied PDEs, retaining the ideal Laplacian
forcing. No direction of the resistive field is prescribed. -/
theorem difference_equation {u B I : VelocityField} {eta_m t : ℝ} {x : Space}
    (hB : ContDiff ℝ ∞ (fun x => B (t,x))) (hI : ContDiff ℝ ∞ (fun x => I (t,x)))
    (hBt : DifferentiableAt ℝ (fun s => B (s,x)) t)
    (hIt : DifferentiableAt ℝ (fun s => I (s,x)) t)
    (hres : temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x)
    (hideal : temporalDerivative I t x + spatialDerivative I t x (u (t,x)) =
      spatialDerivative u t x (I (t,x))) :
    temporalDerivative (B-I) t x + spatialDerivative (B-I) t x (u (t,x)) =
      spatialDerivative u t x ((B-I) (t,x)) + eta_m • spatialLaplacian (B-I) t x +
        eta_m • spatialLaplacian I t x := by
  rw [temporalDerivative_sub hBt hIt,spatialDerivative_sub hB hI,
    spatialLaplacian_sub hB hI]
  simp only [sub_apply,Pi.sub_apply,map_sub,smul_sub]
  rw [eq_sub_of_add_eq hres,eq_sub_of_add_eq hideal]
  module

theorem difference_initial {B I : VelocityField} {a : ℝ}
    (hinit : ∀ x, B (a,x) = I (a,x)) : ∀ x, (B-I) (a,x) = 0 := by
  intro x
  exact sub_eq_zero.mpr (hinit x)

/-- Young's inequality for the exact squared-norm residual. Constants L,D
are independent of diffusivity whenever their input bounds are. -/
theorem squared_residual_bound {A : Space →L[ℝ] Space} {w f : Space} {eta_m L D diss : ℝ}
    (heta : 0 ≤ eta_m) (hL : ‖A‖ ≤ L) (hD : ‖f‖ ≤ D) (hdiss : 0 ≤ diss) :
    2*⟪w,A w⟫_ℝ - 2*eta_m*diss + 2*eta_m*⟪w,f⟫_ℝ ≤
      (2*L+1)*‖w‖^2 + eta_m^2*D^2 := by
  have hstretch : ⟪w,A w⟫_ℝ ≤ L*‖w‖^2 := calc
    _ ≤ ‖w‖*‖A w‖ := real_inner_le_norm _ _
    _ ≤ ‖w‖*(L*‖w‖) := mul_le_mul_of_nonneg_left
      ((A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring
  have hforce : ⟪w,f⟫_ℝ ≤ ‖w‖*D :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg _))
  have hy := sq_nonneg (‖w‖-eta_m*D)
  have hf := mul_le_mul_of_nonneg_left hforce (show 0 ≤ 2*eta_m by positivity)
  have hn := mul_nonneg heta hdiss
  nlinarith

/-- The candidate comparison constant. It contains no diffusivity. -/
def constant (L D a b : ℝ) : ℝ :=
  D * Real.sqrt ((Real.exp ((2*L+1)*(b-a))-1)/(2*L+1))

theorem constant_nonneg {L D a b : ℝ} (hD : 0 ≤ D) : 0 ≤ constant L D a b :=
  mul_nonneg hD (Real.sqrt_nonneg _)

@[simp] theorem constant_zero (L a b : ℝ) : constant L 0 a b = 0 := by simp [constant]

theorem barrier_nonneg {L a b : ℝ} (hL : 0 ≤ L) (hab : a ≤ b) :
    0 ≤ (Real.exp ((2*L+1)*(b-a))-1)/(2*L+1) := by
  have hc : 0 < 2*L+1 := by linarith
  exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc.le (sub_nonneg.mpr hab)))) hc.le

/-- The exact square-root step, including D=0. The scalar barrier estimate
is an explicit premise; a maximum principle must establish it separately. -/
theorem norm_le_of_squared_barrier {w : Space} {eta_m L D a b : ℝ}
    (heta : 0 ≤ eta_m) (hL : 0 ≤ L) (hD : 0 ≤ D) (hab : a ≤ b)
    (hq : ‖w‖^2 ≤ eta_m^2*D^2*((Real.exp ((2*L+1)*(b-a))-1)/(2*L+1))) :
    ‖w‖ ≤ eta_m*constant L D a b := by
  have hsq := Real.sq_sqrt (barrier_nonneg hL hab)
  have hc := constant_nonneg (L := L) (a := a) (b := b) hD
  have he : (eta_m*constant L D a b)^2 =
      eta_m^2*D^2*((Real.exp ((2*L+1)*(b-a))-1)/(2*L+1)) := by
    unfold constant
    rw [mul_pow,mul_pow,hsq]
    ring
  have hn := mul_nonneg heta hc
  nlinarith [norm_nonneg w]
/-- The exact scalar barrier ODE behind the proposed comparison constant. -/
theorem barrier_hasDerivAt {L a t : ℝ} (hL : 0 ≤ L) :
    HasDerivAt (fun s => (Real.exp ((2*L+1)*(s-a))-1)/(2*L+1))
      ((2*L+1)*((Real.exp ((2*L+1)*(t-a))-1)/(2*L+1))+1) t := by
  have hc : 2*L+1 ≠ 0 := by linarith
  have hd := ((((hasDerivAt_id t).sub_const a).const_mul (2*L+1)).exp.sub_const 1).div_const (2*L+1)
  simp only [id_eq] at hd
  convert! hd using 1
  field_simp
  ring

theorem barrier_initial (L a : ℝ) : (Real.exp ((2*L+1)*(a-a))-1)/(2*L+1) = 0 := by simp
end NavierStokes.ResistiveMagnetic.Comparison
