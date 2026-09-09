import NavierStokes.ResistiveLinearMild
import Euler.ContinuousPathCalculus
import Mathlib.Analysis.Normed.Ring.Units

/-! Parameter regularity of an already supplied mild path. The existing
Volterra convolution is bundled linearly; no new fixed-point construction
or parabolic derivative gain is asserted in this module. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.LinearMild
open Set Filter MeasureTheory EulerVolterraConvolution EulerContinuousPathCalculus
open scoped Topology ContDiff

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (T : ℝ) (hT : 0 ≤ T) (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
  (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ univ))
  (hk : IntegrableOn k (Ioc 0 T)) (hk0 : ∀ r ∈ Ioc 0 T, 0 ≤ k r)
  (hb : ∀ r ∈ Ioc 0 T, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)

private local instance : NormedAddCommGroup (C(Icc (0 : ℝ) T,X) →L[ℝ] C(Icc (0 : ℝ) T,X)) := inferInstance
private local instance : NormedSpace ℝ (C(Icc (0 : ℝ) T,X) →L[ℝ] C(Icc (0 : ℝ) T,X)) := inferInstance

def convolutionCLM : C(Icc (0 : ℝ) T,Y) →L[ℝ] C(Icc (0 : ℝ) T,X) :=
  LinearMap.mkContinuous
    { toFun := convolution T hT K k hK hk hk0 hb
      map_add' := fun f g => by
        apply ContinuousMap.ext
        intro t
        change (∫ r in Ioc 0 T, causalIntegrand T hT K (f+g) t r) =
          (∫ r in Ioc 0 T, causalIntegrand T hT K f t r) +
          (∫ r in Ioc 0 T, causalIntegrand T hT K g t r)
        rw [← integral_add (causalIntegrand_integrable T hT K k hK hk hk0 hb f t)
          (causalIntegrand_integrable T hT K k hK hk hk0 hb g t)]
        apply integral_congr_ae
        filter_upwards [] with r
        by_cases hr : r ≤ t.val <;> simp [causalIntegrand,hr,extendPath,map_add]
      map_smul' := fun c f => by
        apply ContinuousMap.ext
        intro t
        change (∫ r in Ioc 0 T, causalIntegrand T hT K (c • f) t r) =
          c • (∫ r in Ioc 0 T, causalIntegrand T hT K f t r)
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [] with r
        by_cases hr : r ≤ t.val <;> simp [causalIntegrand,hr,extendPath,map_smul] }
    (kernelMass T k) (convolution_bound T hT K k hK hk hk0 hb)

theorem convolutionCLM_norm : ‖convolutionCLM T hT K k hK hk hk0 hb‖ ≤ kernelMass T k :=
  (convolutionCLM T hT K k hK hk hk0 hb).opNorm_le_bound
    (kernelMass_nonneg T k hk0) (convolution_bound T hT K k hK hk hk0 hb)

def responseMap (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)) :
    C(Icc (0 : ℝ) T,X) →L[ℝ] C(Icc (0 : ℝ) T,X) :=
  (convolutionCLM T hT K k hK hk hk0 hb).comp (coefficientMap S)

theorem responseMap_norm (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)) :
    ‖responseMap T hT K k hK hk hk0 hb S‖ ≤ kernelMass T k * ‖S‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (convolutionCLM_norm T hT K k hK hk hk0 hb)
      (EulerContinuousTimeIntegral.multiplier_norm S) (norm_nonneg _) (kernelMass_nonneg T k hk0))

def residualMap (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)) :
    C(Icc (0 : ℝ) T,X) →L[ℝ] C(Icc (0 : ℝ) T,X) :=
  ContinuousLinearMap.id ℝ _ - responseMap T hT K k hK hk hk0 hb S

theorem residualMap_mild {S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)}
    {f z : C(Icc (0 : ℝ) T,X)} (hz : IsMild T hT K S f z) :
    residualMap T hT K k hK hk hk0 hb S z = f := by
  apply ContinuousMap.ext
  intro t
  change z t - convolution T hT K k hK hk hk0 hb _ t = f t
  rw [convolution_eq_interval]
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using! hz t)

theorem one_sub_invertible [CompleteSpace X] (L : X →L[ℝ] X) (hL : ‖L‖ < 1) :
    (ContinuousLinearMap.id ℝ X - L).IsInvertible := by
  let e := (ContinuousLinearEquiv.unitsEquiv ℝ X) (Units.oneSub L hL)
  exact ⟨e,rfl⟩

include hK hk hk0 hb in
theorem mild_family_contDiffAt [CompleteSpace X]
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞ω} (S : P → C(Icc (0 : ℝ) T, X →L[ℝ] Y))
    (f z : P → C(Icc (0 : ℝ) T,X)) (hS : ContDiff ℝ n S) (hf : ContDiff ℝ n f)
    (hz : ∀ p, IsMild T hT K (S p) (f p) (z p)) (p : P)
    (hsmall : kernelMass T k * ‖S p‖ < 1) : ContDiffAt ℝ n z p := by
  let R := fun q => responseMap T hT K k hK hk hk0 hb (S q)
  let L := fun q => residualMap T hT K k hK hk hk0 hb (S q)
  have hR : ContDiff ℝ n R :=
    contDiff_const.clm_comp (contDiff_multiplier S hS)
  have hL : ContDiff ℝ n L := contDiff_const.sub hR
  have hp : ‖R p‖ < 1 := (responseMap_norm T hT K k hK hk hk0 hb (S p)).trans_lt hsmall
  have hInv : (L p).IsInvertible := one_sub_invertible _ hp
  have hc : ContDiffAt ℝ n (fun q => (L q).inverse (f q)) p :=
    (hInv.contDiffAt_map_inverse.comp p hL.contDiffAt).clm_apply hf.contDiffAt
  apply hc.congr_of_eventuallyEq
  have hRn : Continuous (fun q : P => ‖R q‖) := by
    simpa only using! hR.continuous.norm
  have hn : ∀ᶠ q in 𝓝 p, ‖R q‖ < 1 :=
    (hRn.tendsto p).eventually (Iio_mem_nhds hp)
  filter_upwards [hn] with q hq
  have hqInv : (L q).IsInvertible := one_sub_invertible _ hq
  have he := residualMap_mild T hT K k hK hk hk0 hb (hz q)
  exact (hqInv.inverse_apply_self (z q)).symm.trans (congrArg (L q).inverse he)

end NavierStokes.ResistiveMagnetic.LinearMild
