import NavierStokes.MagneticAmplificationRegion

/-! Label derivatives of the actual magnetic transport. Compact-slab bounds
come from smooth maps into continuous path spaces, not separate smoothness. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.MagneticCompactFlow.Slab
open Set Filter Metric ProblemStatement EulerSmoothBanachFlow EulerSmoothPathJoint
open scoped Topology ContDiff
private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
variable (S : Slab)

def Q (W : Space → Space) (t : ℝ) (xi : Space) : Space := S.F t xi (W xi)

theorem magnetic_Phi_Q (W : Space → Space) (t : ℝ) (xi : Space) :
    S.magnetic W (t,S.Phi t xi) = S.Q W t xi := S.magnetic_Phi W t xi

def qPath (W : Space → Space) (xi : Space) : C(Icc (0 : ℝ) (S.b-S.a),Space) :=
  EulerContinuousTimeIntegral.multiplier
    (EulerSmoothPathJoint.spatialDerivative _ (pathFamily _ (sub_nonneg.mpr S.hab.le) S.coefficient) xi)
    ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) (S.b-S.a))) (W xi))

theorem qPath_smooth (W : Space → Space) (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (S.qPath W) := by
  apply EulerContinuousPathCalculus.contDiff_apply _ _
    (spatialDerivative_contDiff _ _ (pathFamily_contDiff _ _ _))
  let L : Space →L[ℝ] C(Icc (0 : ℝ) (S.b-S.a),Space) := ContinuousLinearMap.const ℝ _
  change ContDiff ℝ ∞ (L ∘ W)
  exact L.contDiff.comp hW

theorem qPath_apply (W : Space → Space) (t : ℝ) (ht : t ∈ Icc S.a S.b) (xi : Space) :
    S.qPath W xi (S.slabTime t ht) = S.Q W t xi := by
  change spatialDerivative _ (pathFamily _ _ S.coefficient) xi (S.slabTime t ht) (W xi) = _
  rw [spatialDerivative_apply _ _ (pathFamily_contDiff _ _ _)]
  rfl

theorem Q_smooth (W : Space → Space) (hW : ContDiff ℝ ∞ W) (t : ℝ) (ht : t ∈ Icc S.a S.b) :
    ContDiff ℝ ∞ (S.Q W t) :=
  ((S.Phi_smooth t ht).fderiv_right (by simp)).clm_apply hW

def extendedDQ (W : Space → Space) (z : SpaceTime) : Space →L[ℝ] Space :=
  timeSlice (S.b-S.a) (sub_nonneg.mpr S.hab.le)
    (spatialDerivative _ (S.qPath W)) (z.1-S.a) z.2

theorem extendedDQ_continuous (W : Space → Space) (hW : ContDiff ℝ ∞ W) :
    Continuous (S.extendedDQ W) :=
  (timeSlice_joint_continuous _ _ _ (spatialDerivative_contDiff _ _ (S.qPath_smooth W hW)).continuous).comp
    ((continuous_fst.sub continuous_const).prodMk continuous_snd)

theorem extendedDQ_eq (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (xi : Space) :
    S.extendedDQ W (t,xi) = fderiv ℝ (S.Q W t) xi := by
  unfold extendedDQ timeSlice EulerVolterraConvolution.extendPath
  dsimp only
  rw [projIcc_of_mem _ (show t-S.a ∈ Icc 0 (S.b-S.a) from (S.slabTime t ht).property)]
  rw [spatialDerivative_apply _ _ (S.qPath_smooth W hW)]
  congr 1
  exact funext (S.qPath_apply W t ht)

/-- A uniform bound on a fixed compact slab and a fixed label ball. -/
theorem exists_uniform_DQ_bound (W : Space → Space) (hW : ContDiff ℝ ∞ W) (xi : Space) (r0 : ℝ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t ∈ Icc S.a S.b, ∀ x ∈ closedBall xi r0,
      ‖fderiv ℝ (S.Q W t) x‖ ≤ H := by
  obtain ⟨H,hH,hb⟩ := (((isCompact_Icc (a := S.a) (b := S.b)).prod
    (isCompact_closedBall xi r0)).image (S.extendedDQ_continuous W hW)).isBounded.exists_pos_norm_le
  refine ⟨H,hH.le,?_⟩
  intro t ht x hx
  rw [← S.extendedDQ_eq W hW t ht x]
  exact hb _ ⟨(t,x),⟨ht,hx⟩,rfl⟩

/-- Exact label derivative: DQ[v] = (DF[v]) W + F (DW[v]). -/
theorem Q_fderiv_apply (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (xi v : Space) :
    fderiv ℝ (S.Q W t) xi v = (fderiv ℝ (S.F t) xi v) (W xi) + S.F t xi (fderiv ℝ W xi v) := by
  have hF : DifferentiableAt ℝ (S.F t) xi :=
    ((S.Phi_smooth t ht).fderiv_right (by simp : ∞ + 1 ≤ ∞)).differentiable (by simp) xi
  have hd := hF.hasFDerivAt.clm_apply (hW.differentiable (by simp) xi).hasFDerivAt
  convert! congrArg (fun L : Space →L[ℝ] Space => L v) hd.fderiv using 1
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_comm]
/-- On the constant-seed plateau, the seed derivative term vanishes. -/
theorem Q_fderiv_plateau (center : Space) (Bz0 : ℝ)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (xi v : Space)
    (hxi : xi-center ∈ SpatialLocalization.plateau) :
    fderiv ℝ (S.Q (MagneticCompactSeed.seed center Bz0) t) xi v =
      (fderiv ℝ (S.F t) xi v) (Bz0 • coordinateVector 2) := by
  have he : MagneticCompactSeed.seed center Bz0 =ᶠ[𝓝 xi] (fun _ => Bz0 • coordinateVector 2) := by
    filter_upwards [(continuous_id.sub continuous_const).continuousAt.eventually
      (SpatialLocalization.isOpen_plateau.mem_nhds hxi)] with x hx
    exact MagneticCompactSeed.seed_eq_on_plateau center Bz0 hx
  rw [S.Q_fderiv_apply _ (MagneticCompactSeed.seed_smooth _ _) t ht xi v,
    he.self_of_nhds, he.fderiv_eq]
  simp

end NavierStokes.MagneticCompactFlow.Slab
