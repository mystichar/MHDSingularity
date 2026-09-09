import NavierStokes.NaturalCore
import NavierStokes.CoordinateAlgebra
import NavierStokes.MagneticTrajectory

/-! The constant-eta trajectory of the natural similarity core. Transfer to an
assembled velocity requires explicit agreement along the path. -/

noncomputable section

namespace NavierStokes.MagneticSimilarityTrajectory

open Set ProblemStatement NaturalAxisData NaturalCore AxisymmetricFields
open scoped ContDiff

/-- Similarity scale on a path with fixed eta. -/
def pathQ (η t : ℝ) : ℝ := (1 - t) / d η

/-- Axial physical position of the constant-eta path. -/
def pathZ (h η t : ℝ) : ℝ := pathQ η t ^ D h * η

def trajectory (h η t : ℝ) : Space := pathZ h η t • coordinateVector 2

theorem pathQ_pos {η t : ℝ} (hη : η ^ 2 < 1) (ht : t < 1) :
    0 < pathQ η t := div_pos (sub_pos.mpr ht) (sub_pos.mpr hη)

theorem physicalQ_path {h η t : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    physicalQ h (t, (0, pathZ h η t)) = pathQ η t := by
  apply (SimilarityCoordinates.eq_coordinateQ (by linarith) (by linarith)
    (sub_pos.mpr ht) (pathQ_pos hη ht) ?_).symm
  have hf := CoordinateAlgebra.forward_coordinate_identity (pathQ_pos hη ht) h η
  change pathQ η t - (pathQ η t ^ D h * η) ^ 2 * pathQ η t ^ (2 * h) = 1 - t
  change pathQ η t * d η = pathQ η t - (pathQ η t ^ D h * η) ^ 2 * pathQ η t ^ (2 * h) at hf
  rw [← hf]
  exact div_mul_cancel₀ (1 - t) (ne_of_gt (sub_pos.mpr hη))

theorem physicalEta_path {h η t : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    physicalEta h (t, (0, pathZ h η t)) = η := by
  change pathZ h η t / physicalQ h (t, (0, pathZ h η t)) ^ ((1 - 2 * h) / 2) = η
  rw [physicalQ_path hh hh1 hη ht]
  have he : (1 - 2 * h) / 2 = D h := by unfold D; ring
  rw [he]
  exact mul_div_cancel_left₀ η (Real.rpow_pos_of_pos (pathQ_pos hη ht) _).ne'

theorem profilePoint_trajectory (h η t : ℝ) :
    profilePoint t (trajectory h η t) = (t, (0, pathZ h η t)) := by
  simp [profilePoint, radialEnergy, trajectory, coordinateVector]

theorem similarityPoint_trajectory {h η t : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    similarityPoint h (profilePoint t (trajectory h η t)) = (0, η) := by
  rw [profilePoint_trajectory]
  simp only [similarityPoint, zero_div, physicalEta_path hh hh1 hη ht]

theorem trajectory_mem_core {h η t : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hη : η ^ 2 < 1) (ht : t < 1) (Λ : ℝ) :
    (t, trajectory h η t) ∈ coreDomain h Λ := by
  refine ⟨ht, ?_⟩
  rw [similarityPoint_trajectory hh hh1 hη ht]
  have hleft : -1 < η := by nlinarith [sq_nonneg (η + 1)]
  have hright : η < 1 := by nlinarith [sq_nonneg (η - 1)]
  change (0, η) ∈ NaturalProfile.domain Λ
  norm_num [NaturalProfile.domain, NaturalProfile.rescalePoint,
    AxisEvaluation.strip, NaturalAxisCoefficients.window]
  constructor <;> linarith

theorem coreVelocity_trajectory {h j Λ η t : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hη : η ^ 2 < 1) (ht : t < 1) :
    coreVelocity h f V (t, trajectory h η t) =
      (pathQ η t ^ (-A h) * NaturalAxisData.U j η) • coordinateVector 2 := by
  have hx := trajectory_mem_core hh hh1 hη ht Λ
  have hH := (meridionalPotential_contDiffAt hh hh1 hs.average_smooth hx).differentiableAt (by simp)
  have hK := (swirlPotential_contDiffAt hh hh1 hs.f_smooth hx).differentiableAt (by simp)
  change velocity _ _ _ = _
  rw [velocity_on_axis _ _ _ _ hH hK (by simp [trajectory, coordinateVector])
    (by simp [trajectory, coordinateVector])]
  have hwin : η ∈ Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right := by
    change -11 / 10 < η ∧ η < 11 / 10
    constructor <;> nlinarith [sq_nonneg (η + 1), sq_nonneg (η - 1)]
  have hz : trajectory h η t 2 = pathZ h η t := by simp [trajectory, coordinateVector]
  rw [hz]
  change (physicalQ h (t, (0, pathZ h η t)) ^ (-A h) *
    V (0 / physicalQ h (t, (0, pathZ h η t)), physicalEta h (t, (0, pathZ h η t)))) • _ = _
  rw [physicalQ_path hh hh1 hη ht, physicalEta_path hh hh1 hη ht, zero_div,
    hs.average_axis η hwin]

theorem pathZ_hasDerivAt {h j η t : ℝ} (hη : η ^ 2 < 1) (ht : t < 1)
    (hroot : H h j η = 0) :
    HasDerivAt (pathZ h η) (pathQ η t ^ (-A h) * NaturalAxisData.U j η) t := by
  have hq : HasDerivAt (pathQ η) (-1 / d η) t := by
    convert! ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).div_const (d η) using 1
    simp
  have hd := (hq.rpow_const (p := D h) (Or.inl (pathQ_pos hη ht).ne')).mul_const η
  have he : D h - 1 = -A h := by unfold D A; ring
  have hcoef : -(D h * η) / d η = NaturalAxisData.U j η := by
    apply (div_eq_iff (ne_of_gt (sub_pos.mpr hη))).mpr
    dsimp [H, d] at hroot
    nlinarith
  convert! hd using 1
  rw [he]
  calc
    pathQ η t ^ (-A h) * NaturalAxisData.U j η =
        pathQ η t ^ (-A h) * (-(D h * η) / d η) := by rw [hcoef]
    _ = _ := by ring

theorem trajectory_hasDerivAt {h j Λ η t : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hη : η ^ 2 < 1) (hroot : H h j η = 0) (ht : t < 1) :
    HasDerivAt (trajectory h η) (coreVelocity h f V (t, trajectory h η t)) t := by
  rw [coreVelocity_trajectory hh hh1 hs hη ht]
  exact (pathZ_hasDerivAt hη ht hroot).smul_const (coordinateVector 2)

theorem trajectory_isLagrangian {h j Λ η a b : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hη : η ^ 2 < 1) (hroot : H h j η = 0) (hab : a ≤ b) (hb : b < 1) :
    MagneticTransport.IsLagrangianTrajectoryOn (coreVelocity h f V)
      (trajectory h η) a b (trajectory h η a) := by
  refine ⟨hab, rfl, ?_, ?_⟩
  · intro t ht
    exact (trajectory_hasDerivAt hh hh1 hs hη hroot (ht.2.trans_lt hb)).continuousAt.continuousWithinAt
  · intro t ht
    exact trajectory_hasDerivAt hh hh1 hs hη hroot (ht.2.trans hb)

/-- The distinguished eta is chosen from the inherited proved unique-root theorem. -/
def distinguishedEta {h j : ℝ} (p : SmallParameters h j) : ℝ :=
  Classical.choose (exists_unique_root p)

theorem distinguishedEta_spec {h j : ℝ} (p : SmallParameters h j) :
    distinguishedEta p ∈ Ioo (-j / 4) (-j / 5) ∧
    H h j (distinguishedEta p) = 0 ∧
    ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = distinguishedEta p :=
  Classical.choose_spec (exists_unique_root p)

theorem distinguishedEta_sq_lt_one {h j : ℝ} (p : SmallParameters h j) :
    distinguishedEta p ^ 2 < 1 := by
  have hs := (distinguishedEta_spec p).1
  have hlo : -1 < distinguishedEta p := by linarith [hs.1, p.j_le]
  have hhi : distinguishedEta p < 1 := by linarith [hs.2, p.j_pos]
  nlinarith [mul_pos (sub_pos.mpr hhi) (show 0 < distinguishedEta p + 1 by linarith)]

/-- The distinguished path is a genuine particle trajectory of the natural core
on every finite closed interval lying strictly before time one. -/
theorem distinguished_trajectory_isLagrangian
    {h j Λ a b : ℝ} {P0 a0 : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (p : SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hab : a ≤ b) (hb : b < 1) :
    MagneticTransport.IsLagrangianTrajectoryOn (coreVelocity h f V)
      (trajectory h (distinguishedEta p)) a b (trajectory h (distinguishedEta p) a) :=
  trajectory_isLagrangian p.h_pos (by linarith [p.h_le]) hs
    (distinguishedEta_sq_lt_one p) (distinguishedEta_spec p).2.1 hab hb

/-- Transfer to an assembled velocity requires equality of velocity values along
this path. This hypothesis alone makes no assertion about spatial gradients. -/
theorem distinguished_trajectory_isLagrangian_of_agrees
    {u : VelocityField} {h j Λ a b : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (p : SmallParameters h j)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    (hab : a ≤ b) (hb : b < 1)
    (heq : ∀ t ∈ Ioo a b,
      u (t, trajectory h (distinguishedEta p) t) =
        coreVelocity h f V (t, trajectory h (distinguishedEta p) t)) :
    MagneticTransport.IsLagrangianTrajectoryOn u
      (trajectory h (distinguishedEta p)) a b (trajectory h (distinguishedEta p) a) := by
  have hc := distinguished_trajectory_isLagrangian p hs hab hb
  refine ⟨hc.ordered, hc.initial, hc.continuous, ?_⟩
  intro t ht
  rw [heq t ht]
  exact hc.hasDerivAt t ht

end NavierStokes.MagneticSimilarityTrajectory
