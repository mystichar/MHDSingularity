import NavierStokes.ResistiveSquaredNorm
import NavierStokes.ResistivePeriodicMaximum

/-! The squared-norm identity with forward time differentiability and C²
spatial slices. No joint smoothness of higher derivatives is assumed. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set Filter ProblemStatement
open scoped ContDiff InnerProductSpace Topology

namespace Slice

/-- Bridge from the existing joint scalar time operator, when that joint
derivative exists, to the slice operator used by the maximum principle. -/
theorem scalarTime_eq {q : SpaceTime → ℝ} {t : ℝ} {x : Space}
    (hq : DifferentiableAt ℝ q (t,x)) : scalarTime q (t,x) = time q t x := by
  have hd := hq.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hd.deriv.symm

theorem scalarPartial_eq {q : SpaceTime → ℝ} {t : ℝ} {x : Space}
    (hq : DifferentiableAt ℝ q (t,x)) (i : Fin 3) :
    scalarPartial i q (t,x) = gradient q t x (coordinateVector i) := by
  have hd := hq.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  exact (congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector i)) hd.fderiv).symm

/-- The second-derivative bridge explicitly requires differentiability of
the joint scalar partials. The slice-based comparison does not require
these additional joint derivatives. -/
theorem scalarLaplacian_eq {q : SpaceTime → ℝ} {t : ℝ} {x : Space}
    (hq : ∀ y, DifferentiableAt ℝ q (t,y))
    (hdq : ∀ i, DifferentiableAt ℝ (scalarPartial i q) (t,x)) :
    scalarLaplacian q (t,x) = laplacian q t x := by
  unfold scalarLaplacian Calculus.Lap laplacian
  apply Finset.sum_congr rfl
  intro i _
  change scalarPartial i (scalarPartial i q) (t,x) = _
  rw [scalarPartial_eq (hdq i)]
  have he : (fun y => scalarPartial i q (t,y)) = fun y => gradient q t y (coordinateVector i) :=
    funext (fun y => scalarPartial_eq (hq y) i)
  change fderiv ℝ (fun y => scalarPartial i q (t,y)) x (coordinateVector i) = _
  rw [he]


theorem norm_sq_time {W : MagneticField} {t : ℝ} {x : Space}
    (ht : DifferentiableAt ℝ (fun s => W (s,x)) t) :
    time (fun z => ‖W z‖^2) t x = 2*⟪W (t,x),temporalDerivative W t x⟫_ℝ :=
  ht.hasDerivAt.norm_sq.deriv

theorem norm_sq_gradient {W : MagneticField} {t : ℝ} {x : Space}
    (hx : DifferentiableAt ℝ (fun y => W (t,y)) x) (v : Space) :
    gradient (fun z => ‖W z‖^2) t x v = 2*⟪W (t,x),spatialDerivative W t x v⟫_ℝ := by
  rw [gradient,hx.hasFDerivAt.norm_sq.fderiv]
  simp [spatialDerivative]

theorem norm_sq_second {W : MagneticField} {t : ℝ}
    (hx : ContDiff ℝ 2 (fun y => W (t,y))) (x v : Space) :
    fderiv ℝ (fun y => gradient (fun z => ‖W z‖^2) t y v) x v =
      2*‖spatialDerivative W t x v‖^2 +
      2*⟪W (t,x),fderiv ℝ (fun y => spatialDerivative W t y v) x v⟫_ℝ := by
  have he : (fun y => gradient (fun z => ‖W z‖^2) t y v) =
      (fun y => 2*⟪W (t,y),spatialDerivative W t y v⟫_ℝ) :=
    funext (fun y => norm_sq_gradient (hx.differentiable (by norm_num) y) v)
  have hD : Differentiable ℝ (fun y => spatialDerivative W t y v) :=
    ((hx.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num)
  have hd := (((hx.differentiable (by norm_num) x).hasFDerivAt.inner ℝ
    (hD x).hasFDerivAt).const_mul 2)
  rw [he,hd.fderiv]
  simp [fderivInnerCLM_apply,spatialDerivative,mul_add,add_comm]

theorem norm_sq_laplacian {W : MagneticField} {t : ℝ}
    (hx : ContDiff ℝ 2 (fun y => W (t,y))) (x : Space) :
    laplacian (fun z => ‖W z‖^2) t x =
      2*(∑ i : Fin 3, ‖spatialDerivative W t x (coordinateVector i)‖^2) +
      2*⟪W (t,x),spatialLaplacian W t x⟫_ℝ := by
  simp only [laplacian,norm_sq_second hx,Finset.sum_add_distrib,← Finset.mul_sum,
    ← inner_sum,spatialLaplacian]

/-- Exact squared-norm PDE, with all diffusion and forcing terms. -/
theorem squared_equation {W u : VelocityField} {t eta_m : ℝ} {x f : Space}
    (ht : DifferentiableAt ℝ (fun s => W (s,x)) t)
    (hx : ContDiff ℝ 2 (fun y => W (t,y)))
    (heq : temporalDerivative W t x + spatialDerivative W t x (u (t,x)) =
      spatialDerivative u t x (W (t,x)) + eta_m • spatialLaplacian W t x + eta_m • f) :
    operator u eta_m (fun z => ‖W z‖^2) t x =
      2*⟪W (t,x),spatialDerivative u t x (W (t,x))⟫_ℝ -
      2*eta_m*(∑ i : Fin 3, ‖spatialDerivative W t x (coordinateVector i)‖^2) +
      2*eta_m*⟪W (t,x),f⟫_ℝ := by
  rw [operator,norm_sq_time ht,norm_sq_gradient (hx.differentiable (by norm_num) x),
    norm_sq_laplacian hx,← mul_add,← inner_add_right,heq]
  simp only [inner_add_right,inner_smul_right]
  ring

theorem squared_inequality {W u : VelocityField} {t eta_m L D : ℝ} {x f : Space}
    (ht : DifferentiableAt ℝ (fun s => W (s,x)) t)
    (hx : ContDiff ℝ 2 (fun y => W (t,y)))
    (heta : 0 ≤ eta_m) (hL : ‖spatialDerivative u t x‖ ≤ L) (hD : ‖f‖ ≤ D)
    (heq : temporalDerivative W t x + spatialDerivative W t x (u (t,x)) =
      spatialDerivative u t x (W (t,x)) + eta_m • spatialLaplacian W t x + eta_m • f) :
    operator u eta_m (fun z => ‖W z‖^2) t x ≤ (2*L+1)*‖W (t,x)‖^2+eta_m^2*D^2 := by
  rw [squared_equation ht hx heq]
  exact Comparison.squared_residual_bound heta hL hD
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))

end Slice

namespace Comparison

theorem spatialDerivative_sub_of_differentiable {B I : MagneticField} {t : ℝ}
    (hB : Differentiable ℝ (fun y => B (t,y)))
    (hI : Differentiable ℝ (fun y => I (t,y))) (x : Space) :
    spatialDerivative (B-I) t x = spatialDerivative B t x - spatialDerivative I t x :=
  ((hB x).hasFDerivAt.sub (hI x).hasFDerivAt).fderiv

theorem spatialLaplacian_sub_of_contDiff_two {B I : MagneticField} {t : ℝ}
    (hB : ContDiff ℝ 2 (fun y => B (t,y)))
    (hI : ContDiff ℝ 2 (fun y => I (t,y))) (x : Space) :
    spatialLaplacian (B-I) t x = spatialLaplacian B t x - spatialLaplacian I t x := by
  have hd := spatialDerivative_sub_of_differentiable
    (hB.differentiable (by norm_num)) (hI.differentiable (by norm_num))
  simp only [spatialLaplacian,hd,sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hBd := (((hB.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
    (contDiff_const (c := coordinateVector i))).differentiable (by norm_num) x).hasFDerivAt
  have hId := (((hI.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
    (contDiff_const (c := coordinateVector i))).differentiable (by norm_num) x).hasFDerivAt
  exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i)) (hBd.sub hId).fderiv

/-- Difference equation with just the time and spatial regularity used by
the PDE. This also supports future forward parabolic constructions. -/
theorem difference_equation_of_slices {u B I : VelocityField} {eta_m t : ℝ} {x : Space}
    (hB : ContDiff ℝ 2 (fun y => B (t,y))) (hI : ContDiff ℝ 2 (fun y => I (t,y)))
    (hBt : DifferentiableAt ℝ (fun s => B (s,x)) t)
    (hIt : DifferentiableAt ℝ (fun s => I (s,x)) t)
    (hres : temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x)
    (hideal : temporalDerivative I t x + spatialDerivative I t x (u (t,x)) =
      spatialDerivative u t x (I (t,x))) :
    temporalDerivative (B-I) t x + spatialDerivative (B-I) t x (u (t,x)) =
      spatialDerivative u t x ((B-I) (t,x)) + eta_m • spatialLaplacian (B-I) t x +
        eta_m • spatialLaplacian I t x := by
  rw [PeriodicUniqueness.temporalDerivative_sub hBt hIt,
    spatialDerivative_sub_of_differentiable (hB.differentiable (by norm_num))
      (hI.differentiable (by norm_num)),spatialLaplacian_sub_of_contDiff_two hB hI]
  simp only [Pi.sub_apply,sub_apply,map_sub,smul_sub]
  rw [eq_sub_of_add_eq hres,eq_sub_of_add_eq hideal]
  module

end Comparison
end NavierStokes.ResistiveMagnetic
