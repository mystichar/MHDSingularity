import NavierStokes.MagneticPeriodicCoefficient
import Euler.SmoothFlowJoint
import Euler.SmoothFlowVolume
import Euler.BoundedFlowPeriodicity
import Euler.PacketVolumeDivergence

/-! Compactly supported smooth coefficients and varying-seed transport.
Physical-time adapters reuse the existing Euler flow and Jacobian machinery. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NavierStokes.MagneticCompactFlow
open Set Filter ProblemStatement EulerSmoothBanachFlow
open scoped Topology ContDiff
private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

structure Slab where
  velocity : VelocityField
  a : ℝ
  b : ℝ
  hab : a < b
  hb : b < 1
  smooth : ContDiffOn ℝ ∞ velocity (Iio (1 : ℝ) ×ˢ univ)
  supportSet : Set Space
  support_compact : IsCompact supportSet
  supported : ∀ t < 1, tsupport (fun x => velocity (t,x)) ⊆ supportSet

namespace Slab
variable (S : Slab)

def coefficient := SmoothTimeField.ofContDiffOnCompactSupport (Icc (0 : ℝ) (S.b-S.a))
  (MagneticPeriodicCoefficient.shiftedField S.a S.velocity)
  (MagneticPeriodicCoefficient.shifted_smooth S.smooth S.hb)
  S.supportSet S.support_compact (fun t ht => S.supported (S.a+t) (by
    have hh : t ≤ S.b-S.a := ht.2
    linarith [S.hb]))

@[simp] theorem coefficient_apply (s : Icc (0 : ℝ) (S.b-S.a)) (x : Space) :
    S.coefficient.field s x = S.velocity (S.a+s,x) := rfl

/-- One uniform spatial Lipschitz constant on this finite slab. Its size
may depend on the slab endpoint through the derivative coefficient path. -/
theorem coefficient_lipschitz (s : Icc (0 : ℝ) (S.b-S.a)) :
    LipschitzWith ‖S.coefficient.derivative.field‖₊ (S.coefficient.field s : Space → Space) :=
  velocity_lipschitz _ S.coefficient s

def data := flowData (S.b-S.a) (sub_nonneg.mpr S.hab.le) S.coefficient

def Phi (t : ℝ) (x : Space) : Space := S.data.forward (t-S.a) x

def Y (t : ℝ) (x : Space) : Space := S.data.backward (t-S.a) x

/-- The actual spatial derivative, not independently postulated matrix data. -/
def F (t : ℝ) (x : Space) : Space →L[ℝ] Space := fderiv ℝ (S.Phi t) x

def magnetic (W : Space → Space) (z : SpaceTime) : Space :=
  S.F z.1 (S.Y z.1 z.2) (W (S.Y z.1 z.2))

@[simp] theorem Phi_initial (x : Space) : S.Phi S.a x = x := by
  simp [Phi, S.data.forward_zero]
@[simp] theorem Y_initial (x : Space) : S.Y S.a x = x := by
  simp [Y, S.data.backward_zero]
@[simp] theorem Y_Phi (t : ℝ) (x : Space) : S.Y t (S.Phi t x) = x :=
  S.data.backward_forward (t-S.a) x
@[simp] theorem Phi_Y (t : ℝ) (x : Space) : S.Phi t (S.Y t x) = x :=
  S.data.forward_backward (t-S.a) x
@[simp] theorem F_initial (x : Space) : S.F S.a x = ContinuousLinearMap.id ℝ Space := by
  simp [F, show S.Phi S.a = id from funext (S.Phi_initial)]
@[simp] theorem magnetic_initial (W : Space → Space) (x : Space) :
    S.magnetic W (S.a,x) = W x := by simp [magnetic]

theorem Phi_continuous : Continuous (Function.uncurry S.Phi) :=
  S.data.forward_joint_continuous.comp
    ((continuous_fst.sub continuous_const).prodMk continuous_snd)
theorem Y_continuous : Continuous (Function.uncurry S.Y) :=
  S.data.backward_joint_continuous.comp
    ((continuous_fst.sub continuous_const).prodMk continuous_snd)

def slabTime (t : ℝ) (ht : t ∈ Icc S.a S.b) : Icc (0 : ℝ) (S.b-S.a) :=
  ⟨t-S.a, sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 _⟩

theorem data_velocity (t : ℝ) (ht : t ∈ Icc S.a S.b) (x : Space) :
    S.data.velocity (t-S.a) x = S.velocity (t,x) := by
  change (flowData _ _ S.coefficient).velocity (S.slabTime t ht) x = _
  rw [flowData, EulerBoundedLipschitzFlow.ofTimeInterval_velocity]
  change S.velocity (S.a + (t-S.a),x) = _
  rw [add_sub_cancel]

theorem Phi_hasDerivAt (t : ℝ) (ht : t ∈ Icc S.a S.b) (x : Space) :
    HasDerivAt (fun s => S.Phi s x) (S.velocity (t,S.Phi t x)) t := by
  have hs : HasDerivAt (fun s : ℝ => s-S.a) 1 t := (hasDerivAt_id t).sub_const S.a
  have hd := (S.data.forward_hasDerivAt (t-S.a) x).scomp t hs
  convert! hd using 1
  simp [one_smul, S.data_velocity t ht, Phi]

theorem F_eq_evolution (t : ℝ) (ht : t ∈ Icc S.a S.b) (x : Space) :
    S.F t x = (jacobianEvolution (S.b-S.a) (sub_nonneg.mpr S.hab.le)
      S.coefficient x).forward (S.slabTime t ht) :=
  forward_fderiv _ _ _ (S.slabTime t ht) x

theorem magnetic_Phi (W : Space → Space) (t : ℝ) (x : Space) :
    S.magnetic W (t,S.Phi t x) = S.F t x (W x) := by simp [magnetic]

/-- A continuous extension of the spatial Jacobian, using path-space
label differentiation. Only its restriction to the slab represents F. -/
def extendedF (z : SpaceTime) : Space →L[ℝ] Space :=
  EulerSmoothPathJoint.timeSlice (S.b-S.a) (sub_nonneg.mpr S.hab.le)
    (EulerSmoothPathJoint.spatialDerivative (S.b-S.a)
      (pathFamily (S.b-S.a) (sub_nonneg.mpr S.hab.le) S.coefficient)) (z.1-S.a) z.2

theorem extendedF_continuous : Continuous S.extendedF :=
  (EulerSmoothPathJoint.timeSlice_joint_continuous _ _ _
    (EulerSmoothPathJoint.spatialDerivative_contDiff _ _
      (pathFamily_contDiff _ _ _)).continuous).comp
    ((continuous_fst.sub continuous_const).prodMk continuous_snd)

theorem extendedF_eq (t : ℝ) (ht : t ∈ Icc S.a S.b) (x : Space) :
    S.extendedF (t,x) = S.F t x := by
  unfold extendedF EulerSmoothPathJoint.timeSlice EulerVolterraConvolution.extendPath
  dsimp only
  rw [projIcc_of_mem _ (show t-S.a ∈ Icc 0 (S.b-S.a) from (S.slabTime t ht).property)]
  exact EulerSmoothPathJoint.spatialDerivative_apply _ _ (pathFamily_contDiff _ _ _) x
    (S.slabTime t ht)

theorem F_continuousOn : ContinuousOn (Function.uncurry S.F) (Icc S.a S.b ×ˢ univ) :=
  S.extendedF_continuous.continuousOn.congr
    (fun z hz => (S.extendedF_eq z.1 hz.1 z.2).symm)

theorem magnetic_continuousOn (W : Space → Space) (hW : Continuous W) :
    ContinuousOn (S.magnetic W) (Icc S.a S.b ×ˢ univ) := by
  exact (S.F_continuousOn.comp (continuousOn_fst.prodMk S.Y_continuous.continuousOn)
    (fun z hz => ⟨hz.1, mem_univ _⟩)).clm_apply (hW.comp S.Y_continuous).continuousOn

theorem Phi_smooth (t : ℝ) (ht : t ∈ Icc S.a S.b) : ContDiff ℝ ∞ (S.Phi t) :=
  forward_contDiff _ _ _ (S.slabTime t ht)

theorem Y_smooth (t : ℝ) (ht : t ∈ Icc S.a S.b) : ContDiff ℝ ∞ (S.Y t) :=
  backward_contDiff _ _ _ (S.slabTime t ht)

/-- Spatial smoothness is proved at each slab time. This does not assert
joint smoothness across the endpoints. -/
theorem magnetic_spatial_smooth (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) :
    ContDiff ℝ ∞ (fun x => S.magnetic W (t,x)) :=
  (((S.Phi_smooth t ht).fderiv_right (by simp)).comp
    (S.Y_smooth t ht)).clm_apply (hW.comp (S.Y_smooth t ht))

theorem F_det_one
    (hd : ∀ t ∈ Icc S.a S.b, ∀ x, spatialDivergence S.velocity t x = 0)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (x : Space) : (S.F t x).det = 1 := by
  apply forward_det_one _ _ S.coefficient _ (S.slabTime t ht) x
  intro s y
  change EulerSmoothLimit.divergence (fun x => S.velocity (S.a+s,x)) y = 0
  rw [EulerSmoothLimit.divergence_eq_coordinate_sum]
  apply hd (S.a+s) ⟨by linarith [s.property.1], by linarith [s.property.2]⟩ y

theorem magnetic_divergence_free
    (hd : ∀ t ∈ Icc S.a S.b, ∀ x, spatialDivergence S.velocity t x = 0)
    (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (hdivW : ∀ x, ∑ i : Fin 3, (fderiv ℝ W x (coordinateVector i)) i = 0)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (x : Space) :
    spatialDivergence (S.magnetic W) t x = 0 := by
  have hh := EulerPacketVolumeDivergence.divergence_pushforward (S.Phi t) (S.Y t)
    W (S.Y t x) (jacobianEquiv _ _ S.coefficient (S.slabTime t ht) (S.Y t x))
    ((S.Phi_smooth t ht).of_le (by simp)).contDiffAt
    (S.F_eq_evolution t ht (S.Y t x))
    (Eventually.of_forall (fun y => by
      simp only [EulerPacketVolumeDivergence.operatorMatrix_det]
      exact S.F_det_one hd t ht y))
    (S.Y_Phi t) ((S.Y_smooth t ht).differentiable (by simp) _) (hW.differentiable (by simp) _)
  rw [S.Phi_Y, EulerSmoothLimit.divergence_eq_coordinate_sum,
    EulerSmoothLimit.divergence_eq_coordinate_sum] at hh
  exact hh.trans (hdivW _)

/-- C¹ inverse regularity needs only the C¹ forward map and its already
proved invertible derivative. No time derivative of the velocity is assumed. -/
theorem Y_contDiffAt (t : ℝ) (ht : t ∈ Ioo S.a S.b) (x : Space) :
    ContDiffAt ℝ 1 (Function.uncurry S.Y) (t,x) := by
  let T := S.b-S.a
  let hT := sub_nonneg.mpr S.hab.le
  let A := S.coefficient
  let s := t-S.a
  have hs : s ∈ Ioo 0 T := ⟨sub_pos.mpr ht.1, sub_lt_sub_right ht.2 _⟩
  let y := (flowData T hT A).backward s x
  have hg : ContDiffAt ℝ 1 (liftForward T hT A) (s,y) :=
    contDiffAt_fst.prodMk (forward_joint_contDiffAt_one T hT A s hs y)
  have hi : ContDiffAt ℝ 1 (liftBackward T hT A) (s,x) := by
    apply EulerSmoothImplicitLift.contDiffAt_of_identity
      (liftBackward T hT A) (liftForward T hT A) id (s,x) 1 (by norm_num)
      ((continuous_fst.prodMk (flowData T hT A).backward_joint_continuous).continuousAt)
      hg contDiff_id.contDiffAt
      (timeLiftEquiv (jacobianEquiv T hT A ⟨s,hs.1.le,hs.2.le⟩ y)
        (velocityFamily T hT A y ⟨s,hs.1.le,hs.2.le⟩))
    · exact liftForward_hasFDerivAt T hT A s hs y
    · intro p
      exact Prod.ext rfl ((flowData T hT A).forward_backward p.1 p.2)
  exact hi.snd.comp (t,x) ((contDiffAt_fst.sub contDiffAt_const).prodMk contDiffAt_snd)

theorem extendedF_contDiffAt (t : ℝ) (ht : t ∈ Ioo S.a S.b) (x : Space) :
    ContDiffAt ℝ 1 S.extendedF (t,x) := by
  have hj := EulerSmoothPathJoint.joint_contDiffAt_one (S.b-S.a) (sub_nonneg.mpr S.hab.le)
    (EulerSmoothPathJoint.spatialDerivative _ (pathFamily _ _ S.coefficient))
    (EulerSmoothPathJoint.spatialDerivative _ (velocityFamily _ _ S.coefficient))
    (EulerSmoothPathJoint.spatialDerivative_contDiff _ _ (pathFamily_contDiff _ _ _))
    (EulerSmoothPathJoint.spatialDerivative_contDiff _ _ (velocityFamily_contDiff _ _ _))
    (EulerSmoothPathJoint.spatialDerivative_time _ _ _ _
      (pathFamily_contDiff _ _ _) (velocityFamily_contDiff _ _ _)
      (pathFamily_time_derivative _ _ _))
    (t-S.a) ⟨sub_pos.mpr ht.1, sub_lt_sub_right ht.2 _⟩ x
  exact hj.comp (t,x) ((contDiffAt_fst.sub contDiffAt_const).prodMk contDiffAt_snd)

theorem F_contDiffAt (t : ℝ) (ht : t ∈ Ioo S.a S.b) (x : Space) :
    ContDiffAt ℝ 1 (Function.uncurry S.F) (t,x) := by
  apply (S.extendedF_contDiffAt t ht x).congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)] with z hz
  exact (S.extendedF_eq z.1 ⟨hz.1.le,hz.2.le⟩ z.2).symm

theorem magnetic_contDiffAt (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (ht : t ∈ Ioo S.a S.b) (x : Space) :
    ContDiffAt ℝ 1 (S.magnetic W) (t,x) := by
  have hc : ContDiffAt ℝ 1 (fun z : SpaceTime => (z.1,S.Y z.1 z.2)) (t,x) :=
    contDiffAt_fst.prodMk (S.Y_contDiffAt t ht x)
  have hJ : ContDiffAt ℝ 1 (fun z : SpaceTime => S.F z.1 (S.Y z.1 z.2)) (t,x) := by
    convert! (S.F_contDiffAt t ht (S.Y t x)).comp (t,x) hc using 1
  exact hJ.clm_apply ((hW.of_le (by simp)).contDiffAt.comp (t,x) (S.Y_contDiffAt t ht x))

/-- The variational ODE for the actual spatial Jacobian in physical time. -/
theorem F_hasDerivAt (t : ℝ) (ht : t ∈ Ioo S.a S.b) (x : Space) :
    HasDerivAt (fun s => S.F s x)
      ((spatialDerivative S.velocity t (S.Phi t x)).comp (S.F t x)) t := by
  let U := jacobianEvolution (S.b-S.a) (sub_nonneg.mpr S.hab.le) S.coefficient x
  have hi : t-S.a ∈ Ioo 0 (S.b-S.a) := ⟨sub_pos.mpr ht.1, sub_lt_sub_right ht.2 _⟩
  have hu := (U.derivative (S.slabTime t ⟨ht.1.le,ht.2.le⟩)).hasDerivAt
    (Icc_mem_nhds hi.1 hi.2)
  have hs : HasDerivAt (fun s : ℝ => s-S.a) 1 t := (hasDerivAt_id t).sub_const S.a
  have he : (fun s => EulerVolterraConvolution.extendPath (S.b-S.a)
      (sub_nonneg.mpr S.hab.le) U.forward (s-S.a)) =ᶠ[𝓝 t] (fun s => S.F s x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [S.F_eq_evolution s ⟨hs.1.le,hs.2.le⟩ x]
    unfold EulerVolterraConvolution.extendPath
    rw [projIcc_of_mem _ (show s-S.a ∈ Icc 0 (S.b-S.a) from
      (S.slabTime s ⟨hs.1.le,hs.2.le⟩).property)]
    rfl
  have hd := (hu.scomp t hs).congr_of_eventuallyEq he.symm
  simp only [one_smul] at hd
  convert! hd using 1
  rw [S.F_eq_evolution t ⟨ht.1.le,ht.2.le⟩ x]
  congr 1
  change spatialDerivative S.velocity t (S.Phi t x) =
    S.coefficient.derivativeField (S.slabTime t ⟨ht.1.le,ht.2.le⟩) (S.Phi t x)
  rw [SmoothTimeField.derivativeField_eq]
  change fderiv ℝ (fun y => S.velocity (t,y)) _ =
    fderiv ℝ (fun y => S.velocity (S.a+(t-S.a),y)) _
  rw [add_sub_cancel]

/-- Stretching-form induction is proved for the constructed field. -/
theorem magnetic_induction (W : Space → Space) (hW : ContDiff ℝ ∞ W) :
    MagneticTransport.IdealInductionOn (Ioo S.a S.b) S.velocity (S.magnetic W) := by
  intro t ht x
  let xi := S.Y t x
  have hphi := S.Phi_hasDerivAt t ⟨ht.1.le,ht.2.le⟩ xi
  have hB := (S.magnetic_contDiffAt W hW t ht (S.Phi t xi)).differentiableAt one_ne_zero
  have hchain := hB.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hphi)
  have hF := (S.F_hasDerivAt t ht xi).clm_apply (hasDerivAt_const t (W xi))
  have he : (fun s => S.magnetic W (s,S.Phi s xi)) = (fun s => S.F s xi (W xi)) :=
    funext (fun s => S.magnetic_Phi W s xi)
  change HasDerivAt (fun s => S.magnetic W (s,S.Phi s xi)) _ t at hchain
  rw [he] at hchain
  have hh := hchain.unique hF
  rw [MagneticTransport.joint_fderiv_material hB] at hh
  simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero, xi, S.Phi_Y, magnetic] using hh

end Slab
end NavierStokes.MagneticCompactFlow
