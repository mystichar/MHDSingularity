import NavierStokes.MagneticSimilarityTrajectory
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Exact Cartesian gradient on the axis of the natural similarity core.
No flow derivative or magnetic amplification is asserted. -/

noncomputable section
namespace NavierStokes.MagneticSimilarityGradient

open Set Filter ProblemStatement AxisymmetricFields NaturalCore
open MagneticSimilarityTrajectory
open scoped Topology ContDiff

/-- Axial strain `α` and counterclockwise angular speed `rot`. -/
def axisOperator (α rot : ℝ) : Space →L[ℝ] Space :=
  ((-α / 2) • projection 0 - rot • projection 1).smulRight (coordinateVector 0) +
  (rot • projection 0 + (-α / 2) • projection 1).smulRight (coordinateVector 1) +
  (α • projection 2).smulRight (coordinateVector 2)

theorem axisOperator_apply (α rot : ℝ) (v : Space) :
    axisOperator α rot v =
      (-α / 2 * v 0 - rot * v 1) • coordinateVector 0 +
      (rot * v 0 - α / 2 * v 1) • coordinateVector 1 +
      (α * v 2) • coordinateVector 2 := by
  simp [axisOperator, sub_eq_add_neg, neg_div]

/-- Basis matrix, with rows and columns in the standard coordinate order. -/
theorem axisOperator_matrix (α rot : ℝ) :
    (fun i j : Fin 3 => (axisOperator α rot (coordinateVector j)) i) =
      !![-α / 2, -rot, 0; rot, -α / 2, 0; 0, 0, α] := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [axisOperator, coordinateVector]

theorem axisOperator_trace (α rot : ℝ) :
    ∑ i : Fin 3, (axisOperator α rot (coordinateVector i)) i = 0 := by
  simp [axisOperator, coordinateVector, Fin.sum_univ_succ]
  ring

/-- At an axis point the gradient depends only on two first profile derivatives.
All four axial/transverse entries vanish. -/
theorem spatialDerivative_velocity_on_axis (H K : Profile) (t : ℝ) (x : Space)
    (hH : ContDiffAt ℝ 2 H (profilePoint t x))
    (hK : ContDiffAt ℝ 2 K (profilePoint t x))
    (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    spatialDerivative (velocity H K) t x =
      axisOperator (partialZ H (profilePoint t x)) (-partialS K (profilePoint t x)) := by
  have hprofile := hasFDerivAt_profilePoint t x
  have hHv := hasFDerivAt_profile_composition H t x (hH.differentiableAt (by norm_num))
  have hHZ : HasFDerivAt (fun y => partialZ H (profilePoint t y)) _ x := (((hH.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasFDerivAt.comp x hprofile
  have hHS : HasFDerivAt (fun y => partialS H (profilePoint t y)) _ x := (((hH.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasFDerivAt.comp x hprofile
  have hKS : HasFDerivAt (fun y => partialS K (profilePoint t y)) _ x := (((hK.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasFDerivAt.comp x hprofile
  let V : Space → Space := fun y =>
    (-y 0 * partialZ H (profilePoint t y) / 2 + y 1 * partialS K (profilePoint t y)) • coordinateVector 0 +
    (-y 1 * partialZ H (profilePoint t y) / 2 - y 0 * partialS K (profilePoint t y)) • coordinateVector 1 +
    (H (profilePoint t y) + radialEnergy y * partialS H (profilePoint t y)) • coordinateVector 2
  have h0 := (((((projection 0).hasFDerivAt (x := x)).neg.mul hHZ).mul_const (1 / 2 : ℝ)).add
    ((projection 1).hasFDerivAt.mul hKS)).smul_const (coordinateVector 0)
  have h1 := (((((projection 1).hasFDerivAt (x := x)).neg.mul hHZ).mul_const (1 / 2 : ℝ)).sub
    ((projection 0).hasFDerivAt.mul hKS)).smul_const (coordinateVector 1)
  have h2 := (hHv.add ((hasFDerivAt_radialEnergy x).mul hHS)).smul_const (coordinateVector 2)
  have hd := (h0.add h1).add h2
  have he : (fun y => velocity H K (t, y)) =ᶠ[𝓝 x] V := by
    have heH := (contDiff_profilePoint_slice (n := 2) t).continuous.continuousAt.eventually (hH.eventually (by norm_num))
    have heK := (contDiff_profilePoint_slice (n := 2) t).continuous.continuousAt.eventually (hK.eventually (by norm_num))
    filter_upwards [heH, heK] with y hyH hyK
    have hyHd := hyH.differentiableAt (by norm_num)
    have hyKd := hyK.differentiableAt (by norm_num)
    ext i
    fin_cases i <;> simp [V, coordinateVector, velocity_zero H K t y hyHd hyKd,
      velocity_one H K t y hyHd hyKd, velocity_two H K t y hyHd hyKd]
  unfold spatialDerivative
  rw [he.fderiv_eq (𝕜 := ℝ)]
  have hdV : HasFDerivAt V
      (axisOperator (partialZ H (profilePoint t x)) (-partialS K (profilePoint t x))) x := by
    convert! hd using 1
    · funext y
      simp [V, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext
      intro v
      have hpv : profileDerivative H t x v = v 2 * partialZ H (profilePoint t x) := by
        simp only [profileDerivative_apply, hx0, hx1, zero_mul, zero_add]
      simp [axisOperator, hpv, radialLinear, radialEnergy, hx0, hx1]
      module
  exact hdV.fderiv

/-- Profile form of the exact axial strain along the distinguished path. -/
def axialStrain (h η : ℝ) (V : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  partialZ (meridionalPotential h V) (t, (0, pathZ h η t))

/-- Positive angular speed, so the `(0,1)` matrix entry is its negative. -/
def swirlRate (h η : ℝ) (f : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  -partialS (swirlPotential h f) (t, (0, pathZ h η t))

theorem spatialDerivative_naturalCore_on_trajectory
    {h j Λ η t : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    spatialDerivative (coreVelocity h f V) t (trajectory h η t) =
      axisOperator (axialStrain h η V t) (swirlRate h η f t) := by
  have hx := trajectory_mem_core hh hh1 hη ht Λ
  have he := spatialDerivative_velocity_on_axis (meridionalPotential h V) (swirlPotential h f)
    t (trajectory h η t)
    ((meridionalPotential_contDiffAt hh hh1 hs.average_smooth hx).of_le (by simp))
    ((swirlPotential_contDiffAt hh hh1 hs.f_smooth hx).of_le (by simp))
    (by simp [trajectory, coordinateVector]) (by simp [trajectory, coordinateVector])
  simpa only [profilePoint_trajectory, coreVelocity, axialStrain, swirlRate] using he

/-- The dimensionless coefficient multiplying `q⁻¹` in the axial strain.
This definition is a velocity-gradient coefficient, not a magnetic exponent. -/
def axialCoefficientExact (h j η : ℝ) : ℝ :=
  (4 * NaturalAxisData.d η - 2 * NaturalAxisData.A h * η * NaturalAxisData.U j η) /
    NaturalAxisData.L h η

theorem swirlRate_eq
    {h j Λ η t : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    swirlRate h η f t = pathQ η t ^ (-h) / pathQ η t * a0 η := by
  have hp := trajectory_mem_core hh hh1 hη ht Λ
  rw [coreDomain, mem_ofPred_eq, profilePoint_trajectory] at hp
  have hwin : η ∈ Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right := by
    change -11 / 10 < η ∧ η < 11 / 10
    constructor <;> nlinarith [sq_nonneg (η + 1), sq_nonneg (η - 1)]
  unfold swirlRate
  rw [swirlPotential_partialS hh hh1 hs.f_smooth hp]
  simp only [similarityPoint, zero_div, physicalQ_path hh hh1 hη ht,
    physicalEta_path hh hh1 hη ht, hs.f_axis η hwin, neg_mul, neg_neg]

/-- The meridional potential restricted to the whole spatial axis is fixed by
its prescribed axis data. This identity can legitimately be differentiated in z. -/
theorem meridionalPotential_axis
    {h j Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    {t : ℝ} (ht : t < 1) (z : ℝ) :
    meridionalPotential h V (t, (0, z)) =
      physicalQ h (t, (0, z)) ^ (-NaturalAxisData.A h) *
        NaturalAxisData.U j (physicalEta h (t, (0, z))) := by
  have he := SimilarityCoordinates.coordinateEta_abs_lt_one (a := 2 * h)
    (by linarith) (by linarith) (p := (1 - t, z)) (sub_pos.mpr ht)
  have hwin : physicalEta h (t, (0, z)) ∈
      Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right := by
    have hb := abs_lt.mp he
    change -11 / 10 < physicalEta h (t, (0, z)) ∧ physicalEta h (t, (0, z)) < 11 / 10
    change -1 < physicalEta h (t, (0, z)) ∧ physicalEta h (t, (0, z)) < 1 at hb
    constructor <;> linarith [hb.1, hb.2]
  simp only [meridionalPotential, similarityPoint, zero_div, hs.average_axis _ hwin]

theorem axialStrain_eq
    {h j Λ η t : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    axialStrain h η V t = (pathQ η t)⁻¹ * axialCoefficientExact h j η := by
  let z := pathZ h η t
  have hp := trajectory_mem_core hh hh1 hη ht Λ
  rw [coreDomain, mem_ofPred_eq, profilePoint_trajectory] at hp
  have hH := (meridionalPotential_contDiffAt hh hh1 hs.average_smooth hp).differentiableAt (by simp)
  have hHderiv : HasDerivAt (fun y => meridionalPotential h V (t, (0, y)))
      (axialStrain h η V t) z := by
    have hd := hH.hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_const z t).prodMk ((hasDerivAt_const z (0 : ℝ)).prodMk (hasDerivAt_id z)))
    simpa only [Function.comp_def, id_eq, axialStrain, partialZ] using hd
  have hq := SimilarityCoordinates.coordinateQ_hasDerivAt_z_L (a := 2 * h)
    (by linarith) (by linarith) (τ := 1 - t) (z := z) (sub_pos.mpr ht)
  have he := SimilarityCoordinates.coordinateEta_hasDerivAt_z_L (a := 2 * h)
    (by linarith) (by linarith) (τ := 1 - t) (z := z) (sub_pos.mpr ht)
  have hpos := pathQ_pos hη ht
  have hqe : SimilarityCoordinates.coordinateQ (2 * h) (1 - t, z) = pathQ η t :=
    physicalQ_path hh hh1 hη ht
  have hee : SimilarityCoordinates.coordinateEta (2 * h) (1 - t, z) = η :=
    physicalEta_path hh hh1 hη ht
  rw [hqe, hee] at hq he
  have hd := (hq.rpow_const (p := -NaturalAxisData.A h) (Or.inl (by rw [hqe]; exact hpos.ne'))).mul
    ((he.const_mul 4).add (hasDerivAt_const z j))
  have hfun : (fun y => meridionalPotential h V (t, (0, y))) =
      (fun y => SimilarityCoordinates.coordinateQ (2 * h) (1 - t, y) ^ (-NaturalAxisData.A h) *
        (4 * SimilarityCoordinates.coordinateEta (2 * h) (1 - t, y) + j)) :=
    funext (meridionalPotential_axis hh hh1 hs ht)
  rw [hfun] at hHderiv
  have hv := hHderiv.unique hd
  simp only [Pi.add_apply, hqe, hee, add_zero] at hv
  rw [hv]
  have hD : (1 - 2 * h) / 2 = NaturalAxisData.D h := by unfold NaturalAxisData.D; ring
  rw [hD]
  have hp1 : pathQ η t ^ (1 - NaturalAxisData.D h) * pathQ η t ^ (-NaturalAxisData.A h - 1) =
      (pathQ η t)⁻¹ := by
    rw [← Real.rpow_add hpos]
    have hpow : (1 - NaturalAxisData.D h) + (-NaturalAxisData.A h - 1) = -1 := by
      unfold NaturalAxisData.D NaturalAxisData.A; ring
    rw [hpow, Real.rpow_neg_one]
  have hp2 : pathQ η t ^ (-NaturalAxisData.A h) / pathQ η t ^ NaturalAxisData.D h =
      (pathQ η t)⁻¹ := by
    rw [← Real.rpow_sub hpos]
    have hpow : -NaturalAxisData.A h - NaturalAxisData.D h = -1 := by
      unfold NaturalAxisData.D NaturalAxisData.A; ring
    rw [hpow, Real.rpow_neg_one]
  unfold axialCoefficientExact NaturalAxisData.U NaturalAxisData.d NaturalAxisData.L
  calc
    _ = (-2 * NaturalAxisData.A h * η * (4 * η + j) *
        (pathQ η t ^ (1 - NaturalAxisData.D h) * pathQ η t ^ (-NaturalAxisData.A h - 1)) +
        4 * (1 - η ^ 2) * (pathQ η t ^ (-NaturalAxisData.A h) / pathQ η t ^ NaturalAxisData.D h)) /
        (1 - 2 * h * η ^ 2) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    _ = _ := by rw [hp1, hp2]; ring

/-- Closed-form core gradient; the only remaining profile datum is axis swirl `a0`. -/
theorem spatialDerivative_naturalCore_on_trajectory_exact
    {h j Λ η t : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    spatialDerivative (coreVelocity h f V) t (trajectory h η t) =
      axisOperator ((pathQ η t)⁻¹ * axialCoefficientExact h j η)
        (pathQ η t ^ (-h) / pathQ η t * a0 η) := by
  rw [spatialDerivative_naturalCore_on_trajectory hh hh1 hs hη ht,
    axialStrain_eq hh hh1 hs hη ht, swirlRate_eq hh hh1 hs hη ht]

/-- Specialization to the root that defines the Lagrangian core trajectory. -/
theorem spatialDerivative_naturalCore_on_distinguishedTrajectory
    {h j Λ t : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (p : NaturalAxisData.SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr) (ht : t < 1) :
    spatialDerivative (coreVelocity h f V) t (trajectory h (distinguishedEta p) t) =
      axisOperator ((pathQ (distinguishedEta p) t)⁻¹ *
        axialCoefficientExact h j (distinguishedEta p))
        (pathQ (distinguishedEta p) t ^ (-h) / pathQ (distinguishedEta p) t *
          a0 (distinguishedEta p)) :=
  spatialDerivative_naturalCore_on_trajectory_exact p.h_pos (by linarith [p.h_le]) hs
    (distinguishedEta_sq_lt_one p) ht

/-- The diagonal strain block has zero trace, independently of the swirl. -/
theorem axisOperator_strain_trace (α : ℝ) :
    ∑ i : Fin 3, (axisOperator α 0 (coordinateVector i)) i = 0 :=
  axisOperator_trace α 0

end NavierStokes.MagneticSimilarityGradient
