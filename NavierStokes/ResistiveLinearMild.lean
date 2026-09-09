import NavierStokes.ResistiveWeightedVolterra

/-! Globally linear Volterra equations on an entire compact time slab.
Existence uses the existing fixed-point theorem and a temporary exponential
weight. Uniqueness is in the whole continuous path class. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.LinearMild
open Set MeasureTheory EulerVolterraConvolution WeightedVolterra
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (T : ℝ) (hT : 0 ≤ T)

/-- The unweighted equation, with only the standard clamped path extension
inside its Bochner integral. No analytic existence is part of this predicate. -/
def IsMild (K : ℝ → Y →L[ℝ] X) (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y))
    (f z : C(Icc (0 : ℝ) T, X)) : Prop :=
  ∀ t : Icc (0 : ℝ) T, z t = f t + ∫ r in (0 : ℝ)..t.val,
    K r (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r))))

theorem source_continuous (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)) :
    Continuous (fun p : Icc (0 : ℝ) T × X => S p.1 p.2) :=
  (S.continuous.comp continuous_fst).clm_apply continuous_snd

theorem initial {K : ℝ → Y →L[ℝ] X} {S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)}
    {f z : C(Icc (0 : ℝ) T, X)} (hz : IsMild T hT K S f z) :
    z ⟨0,le_rfl,hT⟩ = f ⟨0,le_rfl,hT⟩ := by
  simpa only [intervalIntegral.integral_same, add_zero] using hz ⟨0,le_rfl,hT⟩

/-- Weighting uses the actual source and kernel linearity. The projection
is the identity at all integration times, including the endpoints. -/
theorem weight {K : ℝ → Y →L[ℝ] X} {S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)}
    {f z : C(Icc (0 : ℝ) T, X)} (hz : IsMild T hT K S f z) (lambda : ℝ) :
    IsMild T hT (weightedKernel K lambda) S (weightPath (-lambda) f) (weightPath (-lambda) z) := by
  intro t
  change Real.exp (-lambda*t.val) • z t = Real.exp (-lambda*t.val) • f t + _
  rw [hz t, smul_add, ← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 t.val := by simpa only [uIcc_of_le t.property.1] using hr
  have hp : t.val-r ∈ Icc 0 T := ⟨sub_nonneg.mpr hr'.2, by have ht := t.property.2; linarith [hr'.1]⟩
  have he : (projIcc 0 T hT (t.val-r)).val = t.val-r := by rw [projIcc_of_mem hT hp]
  change Real.exp (-lambda*t.val) • K r (S _ (z _)) =
    Real.exp (-lambda*r) • K r (S _ (Real.exp (-lambda*(projIcc 0 T hT (t.val-r)).val) • z _))
  simp only [map_smul, smul_smul, ← Real.exp_add]
  congr 1
  congr 1
  rw [he]
  ring

theorem unweight {K : ℝ → Y →L[ℝ] X} {S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)}
    {f Z : C(Icc (0 : ℝ) T, X)} (lambda : ℝ)
    (hZ : IsMild T hT (weightedKernel K lambda) S (weightPath (-lambda) f) Z) :
    IsMild T hT K S f (weightPath lambda Z) := by
  have h := weight T hT hZ (-lambda)
  simpa only [weightedKernel_cancel, neg_neg, weightPath_cancel] using h

variable (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ univ))
variable (hk : IntegrableOn k (Ioc 0 T)) (hk0 : ∀ r ∈ Ioc 0 T, 0 ≤ k r)
variable (hbound : ∀ r ∈ Ioc 0 T, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)

include hK hk hk0 hbound in
/-- The original shifted integral is genuinely Bochner integrable in X. -/
theorem duhamel_integrable (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y))
    (z : C(Icc (0 : ℝ) T, X)) (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun r : ℝ => K r
      (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r))))) volume 0 t.val := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.property.1]
  have hs : Ioc (0 : ℝ) t.val ⊆ Ioc 0 T := fun r hr => ⟨hr.1,hr.2.trans t.property.2⟩
  have hp : Continuous (fun r : ℝ => projIcc 0 T hT (t.val-r)) :=
    continuous_projIcc.comp (continuous_const.sub continuous_id)
  have hc : ContinuousOn (fun r : ℝ => K r
      (S (projIcc 0 T hT (t.val-r)) (z (projIcc 0 T hT (t.val-r))))) (Ioc 0 t.val) :=
    hK.comp (continuous_id.prodMk ((S.continuous.comp hp).clm_apply (z.continuous.comp hp))).continuousOn
      (fun r hr => ⟨hr.1,mem_univ _⟩)
  apply (((hk.mono_set hs).mul_const (‖S‖ * ‖z‖))).mono'
    (hc.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  apply (hbound r (hs hr) _).trans
  apply mul_le_mul_of_nonneg_left _ (hk0 r (hs hr))
  exact ((S _).le_opNorm (z _)).trans
    (mul_le_mul (S.norm_coe_le_norm _) (z.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg S))

include hK hk hk0 hbound in
theorem fixedPoint_iff (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y))
    (f z : C(Icc (0 : ℝ) T, X)) :
    IsMild T hT K S f z ↔
      z = picard T hT K k hK hk hk0 hbound f (fun t => S t) (source_continuous T S) z := by
  constructor
  · intro hz
    ext t
    change z t = f t + convolution T hT K k hK hk hk0 hbound _ t
    rw [convolution_eq_interval]
    exact hz t
  · intro hz t
    have he := congrArg (fun z : C(Icc (0 : ℝ) T, X) => z t) hz
    change z t = f t + convolution T hT K k hK hk hk0 hbound _ t at he
    rw [convolution_eq_interval] at he
    exact he

include hK hk hk0 hbound in
/-- A global linear coefficient gives uniqueness in the entire path class,
using a radius chosen only after the two arbitrary paths are supplied. -/
theorem unique_of_small (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y))
    (A : ℝ) (hA : 0 ≤ A) (hS : ∀ t, ‖S t‖ ≤ A) (hsmall : kernelMass T k * A < 1)
    (f u v : C(Icc (0 : ℝ) T, X))
    (hu : IsMild T hT K S f u) (hv : IsMild T hT K S f v) : u = v := by
  apply mild_solution_unique T hT K k hK hk hk0 hbound f (fun t => S t) (source_continuous T S)
    (max ‖u‖ ‖v‖) A hA _ hsmall u v (le_max_left _ _) (le_max_right _ _) hu hv
  intro t x y _ _
  rw [← map_sub]
  exact (S t).le_of_opNorm_le (hS t) _

include hK hk hk0 hbound in
theorem mild_norm_le (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y))
    (A : ℝ) (hA : 0 ≤ A) (hS : ∀ t, ‖S t‖ ≤ A)
    (f z : C(Icc (0 : ℝ) T, X)) (hz : IsMild T hT K S f z) :
    ‖z‖ ≤ ‖f‖ + kernelMass T k * A * ‖z‖ := by
  have hs : ‖pathNonlinearity T (fun t => S t) (source_continuous T S) z‖ ≤ A * ‖z‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hA (norm_nonneg z))).mpr
    intro t
    exact ((S t).le_of_opNorm_le (hS t) (z t)).trans
      (mul_le_mul_of_nonneg_left (z.norm_coe_le_norm t) hA)
  have hc := (convolution_bound T hT K k hK hk hk0 hbound _).trans
    (mul_le_mul_of_nonneg_left hs (kernelMass_nonneg T k hk0))
  have he := (fixedPoint_iff T hT K k hK hk hk0 hbound S f z).mp hz
  calc
    ‖z‖ = ‖f + convolution T hT K k hK hk hk0 hbound
        (pathNonlinearity T (fun t => S t) (source_continuous T S) z)‖ := congrArg norm he
    _ ≤ ‖f‖ + ‖convolution T hT K k hK hk hk0 hbound _‖ := norm_add_le _ _
    _ ≤ ‖f‖ + kernelMass T k * (A * ‖z‖) := add_le_add le_rfl hc
    _ = _ := by ring

include hK hk hk0 hbound in
/-- The weight is fixed before the free path. The invariant ball is only
used for construction; the returned uniqueness quantifies over all paths. -/
theorem exists_unique_of_weight [CompleteSpace X]
    (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)) (A : ℝ) (hA : 0 ≤ A) (hS : ∀ t, ‖S t‖ ≤ A)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hhalf : kernelMass T (weightedMajorant k lambda) * A ≤ (1 / 2 : ℝ))
    (f : C(Icc (0 : ℝ) T, X)) :
    ∃ z : C(Icc (0 : ℝ) T, X), IsMild T hT K S f z ∧
      ‖z‖ ≤ 2 * Real.exp (lambda*T) * ‖f‖ ∧
      ∀ w, IsMild T hT K S f w → w = z := by
  let Kw := weightedKernel K lambda
  let kw := weightedMajorant k lambda
  have hKw := weightedKernel_continuous K hK lambda
  have hkw := weightedMajorant_integrable k hk hlambda
  have hkw0 : ∀ r ∈ Ioc 0 T, 0 ≤ kw r := fun r hr => weightedMajorant_nonneg k lambda r (hk0 r hr)
  have hwb : ∀ r ∈ Ioc 0 T, ∀ y, ‖Kw r y‖ ≤ kw r * ‖y‖ :=
    fun r hr y => weightedKernel_bound K k lambda r (hbound r hr) y
  let fw := weightPath (-lambda) f
  let N := ‖f‖
  let R := 2*N+1
  have hR : 0 ≤ R := by dsimp [R,N]; positivity
  have hsmall : kernelMass T kw * A < 1 := lt_of_le_of_lt hhalf (by norm_num)
  have hfree : ‖fw‖ ≤ N := weightPath_neg_norm_le hlambda f
  have hbudget : ‖fw‖ + kernelMass T kw * (A*R) ≤ R := by
    have hprod := mul_le_mul_of_nonneg_right hhalf hR
    dsimp [R,N] at *
    nlinarith
  obtain ⟨Z, _, hZ⟩ := exists_mild_solution T hT Kw kw hKw hkw hkw0 hwb fw
    (fun t => S t) (source_continuous T S) R (A*R) A hR (mul_nonneg hA hR) hA
    (fun t x hx => ((S t).le_of_opNorm_le (hS t) x).trans (mul_le_mul_of_nonneg_left hx hA))
    (fun t x y _ _ => by rw [← map_sub]; exact (S t).le_of_opNorm_le (hS t) _)
    hbudget hsmall
  have hZn : ‖Z‖ ≤ 2*N := by
    have hn := mild_norm_le T hT Kw kw hKw hkw hkw0 hwb S A hA hS fw Z hZ
    have hm := mul_le_mul_of_nonneg_right hhalf (norm_nonneg Z)
    nlinarith
  refine ⟨weightPath lambda Z, unweight T hT lambda hZ, ?_, ?_⟩
  · exact (weightPath_norm_le hlambda Z).trans
      ((mul_le_mul_of_nonneg_left hZn (Real.exp_pos _).le).trans_eq (by dsimp [N]; ring))
  · intro w hw
    have he := unique_of_small T hT Kw kw hKw hkw hkw0 hwb S A hA hS hsmall fw
      (weightPath (-lambda) w) Z (weight T hT hw lambda) hZ
    have he' := congrArg (weightPath lambda) he
    simpa only [weightPath_cancel] using he'

include hK hk hk0 hbound in
theorem exists_unique [CompleteSpace X]
    (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)) (A : ℝ) (hA : 0 ≤ A) (hS : ∀ t, ‖S t‖ ≤ A) :
    ∃ n : ℕ, kernelMass T (weightedMajorant k n) * A ≤ (1 / 2 : ℝ) ∧
      ∀ f : C(Icc (0 : ℝ) T, X), ∃ z : C(Icc (0 : ℝ) T, X),
        IsMild T hT K S f z ∧ ‖z‖ ≤ 2 * Real.exp ((n:ℝ)*T) * ‖f‖ ∧
        ∀ w, IsMild T hT K S f w → w = z := by
  obtain ⟨n,hn⟩ := exists_weight k hk A
  exact ⟨n,hn,fun f => exists_unique_of_weight T hT K k hK hk hk0 hbound S A hA hS n
    (Nat.cast_nonneg n) hn f⟩

include hK hk hk0 hbound in
/-- No construction radius or weight is a hypothesis of this uniqueness theorem. -/
theorem unique [CompleteSpace X]
    (S : C(Icc (0 : ℝ) T, X →L[ℝ] Y))
    (f u v : C(Icc (0 : ℝ) T, X))
    (hu : IsMild T hT K S f u) (hv : IsMild T hT K S f v) : u = v := by
  obtain ⟨_,_,hh⟩ := exists_unique T hT K k hK hk hk0 hbound S ‖S‖ (norm_nonneg S)
    S.norm_coe_le_norm
  obtain ⟨z,_,_,hz⟩ := hh f
  exact (hz u hu).trans (hz v hv).symm

def restrictPath {T T' : ℝ} (h : T' ≤ T) (z : C(Icc (0 : ℝ) T, X)) :
    C(Icc (0 : ℝ) T', X) :=
  ⟨fun t => z ⟨t.val,t.property.1,t.property.2.trans h⟩,
    z.continuous.comp (Continuous.subtype_mk continuous_subtype_val _)⟩

omit [NormedSpace ℝ X] in
@[simp] theorem restrictPath_apply {T T' : ℝ} (h : T' ≤ T) (z : C(Icc (0 : ℝ) T, X))
    (t : Icc (0 : ℝ) T') : restrictPath h z t = z ⟨t.val,t.property.1,t.property.2.trans h⟩ := rfl

/-- Restriction preserves the original equation, regardless of any weights
used to construct the paths. The two clamps agree throughout integration. -/
theorem restrict {T' : ℝ} (hT' : 0 ≤ T') (h : T' ≤ T)
    {S : C(Icc (0 : ℝ) T, X →L[ℝ] Y)} {f z : C(Icc (0 : ℝ) T, X)}
    (hz : IsMild T hT K S f z) :
    IsMild T' hT' K (restrictPath h S) (restrictPath h f) (restrictPath h z) := by
  intro t
  have he := hz ⟨t.val,t.property.1,t.property.2.trans h⟩
  change z ⟨t.val,t.property.1,t.property.2.trans h⟩ = f ⟨t.val,t.property.1,t.property.2.trans h⟩ + _
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 t.val := by simpa only [uIcc_of_le t.property.1] using hr
  have hp' : t.val-r ∈ Icc 0 T' := ⟨sub_nonneg.mpr hr'.2, by have ht := t.property.2; linarith [hr'.1]⟩
  have hp : t.val-r ∈ Icc 0 T := ⟨hp'.1,hp'.2.trans h⟩
  simp only [projIcc_of_mem hT hp, projIcc_of_mem hT' hp', restrictPath_apply]

end NavierStokes.ResistiveMagnetic.LinearMild
