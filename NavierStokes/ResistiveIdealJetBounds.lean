import NavierStokes.ResistivePeriodicCoefficient
import Euler.InverseMapJetContinuity

/-! Joint continuity of the actual periodic ideal field's spatial jets.
The parameter is closed-slab physical time. Smoothness into continuous
path spaces supplies forward jets; the inverse derivative identity supplies
inverse jets. No joint C-infinity assertion is made. -/
noncomputable section
set_option maxHeartbeats 200000
namespace NavierStokes.ResistiveMagnetic.Jets
open Set Filter ProblemStatement EulerSmoothBanachFlow
open scoped ContDiff Topology

section Families
variable {K E V Z : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Parameter continuity of composition jets, from the actual chain rule. -/
theorem composition (f : K → V → Z) (g : K → E → V)
    (hf : ∀ t x, ContDiffAt ℝ ∞ (f t) (g t x))
    (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfj : ∀ n, Continuous (fun p : K × E => iteratedFDeriv ℝ n (f p.1) (g p.1 p.2)))
    (hgj : ∀ n, Continuous (fun p : K × E => iteratedFDeriv ℝ n (g p.1) p.2))
    (n : ℕ) : Continuous (fun p : K × E => iteratedFDeriv ℝ n (f p.1 ∘ g p.1) p.2) := by
  have he : (fun p : K × E => iteratedFDeriv ℝ n (f p.1 ∘ g p.1) p.2) =
      (fun p => ∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (f p.1) (g p.1 p.2))
          (fun i => iteratedFDeriv ℝ (c.partSize i) (g p.1) p.2)) := by
    funext p
    exact iteratedFDeriv_comp (hf p.1 p.2) (hg p.1).contDiffAt (by simp)
  rw [he]
  apply continuous_finsetSum
  intro c _
  exact (c.compAlongOrderedFinpartitionL ℝ E V Z).continuous_uncurry_of_multilinear.comp
    ((hfj c.length).prodMk (continuous_pi (fun i => hgj (c.partSize i))))

end Families

/-- Smooth dependence into the uniform continuous-path Banach space
implies joint continuity of every evaluated spatial jet. -/
theorem path_jets {K E V : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyCompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : E → C(K,V)) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Continuous (fun p : K × E => iteratedFDeriv ℝ n (fun y => f y p.1) p.2) := by
  have hj : Continuous (fun x => EulerFinitePathTensor.tensorPathMap (K := K) n
      (iteratedFDeriv ℝ n f x)) :=
    (EulerFinitePathTensor.tensorPathMap n).continuous.comp
      (hf.iteratedFDeriv_right (m := ∞) (by simp)).continuous
  have hc : Continuous (fun p : K × E =>
      EulerFinitePathTensor.tensorPathMap n (iteratedFDeriv ℝ n f p.2) p.1) := by
    exact continuous_eval.comp ((hj.comp continuous_snd).prodMk continuous_fst)
  exact hc.congr (fun p => EulerFinitePathTensor.tensorPath_iteratedFDeriv f hf n p.2 p.1)

/-- A topological closed-time restriction adapter; no extension of the
PDE or of its derivatives is involved. -/
theorem closed_time_continuity {V : Type*} [TopologicalSpace V]
    {a b : ℝ} (hab : a ≤ b) {f : SpaceTime → V}
    (hf : Continuous (fun p : Icc a b × Space => f (p.1,p.2))) :
    ContinuousOn f (Icc a b ×ˢ univ) := by
  let lift : SpaceTime → Icc a b × Space := fun z => (projIcc a b hab z.1,z.2)
  have hl : Continuous lift :=
    (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous (fun z : SpaceTime => f (projIcc a b hab z.1,z.2)) := hf.comp hl
  apply hc.continuousOn.congr
  intro z hz
  dsimp only
  rw [projIcc_of_mem hab hz.1]

private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

namespace Slab
variable (S : MagneticPeriodicFlow.Slab)

theorem F_jets (n : ℕ) :
    Continuous (fun p : Icc S.a S.b × Space => iteratedFDeriv ℝ n (S.F p.1) p.2) := by
  let fp := EulerSmoothPathJoint.spatialDerivative (S.b-S.a)
    (pathFamily (S.b-S.a) (sub_nonneg.mpr S.hab.le) S.coefficient)
  have hfp : ContDiff ℝ ∞ fp := EulerSmoothPathJoint.spatialDerivative_contDiff _ _
    (pathFamily_contDiff _ _ _)
  have hc := (path_jets fp hfp n).comp
    (show Continuous (fun p : Icc S.a S.b × Space =>
      (S.slabTime p.1 p.1.property,p.2)) from
      (((continuous_subtype_val.comp continuous_fst).sub continuous_const).subtype_mk
        (fun p : Icc S.a S.b × Space => (S.slabTime p.1 p.1.property).property)).prodMk continuous_snd)
  have he (t : Icc S.a S.b) : (fun y => fp y (S.slabTime t t.property)) = S.F t := by
    funext y
    exact EulerSmoothPathJoint.spatialDerivative_apply _ _ (pathFamily_contDiff _ _ _)
      y (S.slabTime t t.property)
  exact hc.congr (fun p => by dsimp only [Function.comp_def]; rw [he])

theorem F_smooth (t : Icc S.a S.b) : ContDiff ℝ ∞ (S.F t) :=
  (S.Phi_smooth t t.property).fderiv_right (by simp)

theorem F_joint : Continuous (fun p : Icc S.a S.b × Space => S.F p.1 p.2) := by
  exact S.extendedF_continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) |>.congr
      (fun p => S.extendedF_eq p.1 p.1.property p.2)

theorem inverseF_smooth_at (t : Icc S.a S.b) (x : Space) :
    ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (S.F t x) := by
  rw [S.F_eq_evolution t t.property x]
  exact contDiffAt_map_inverse (jacobianEquiv (S.b-S.a) (sub_nonneg.mpr S.hab.le) S.coefficient (S.slabTime t t.property) x)

theorem inverseF_jets (n : ℕ) : Continuous (fun p : Icc S.a S.b × Space =>
    iteratedFDeriv ℝ n (fun y => (S.F p.1 y).inverse) p.2) := by
  apply composition (fun _ => ContinuousLinearMap.inverse) (fun t : Icc S.a S.b => S.F t)
    (inverseF_smooth_at S) (F_smooth S) _ (F_jets S) n
  intro m
  rw [continuous_iff_continuousAt]
  intro p
  have hi : ContinuousAt (iteratedFDeriv ℝ m
      (ContinuousLinearMap.inverse : (Space →L[ℝ] Space) → Space →L[ℝ] Space))
      (S.F p.1 p.2) := (inverseF_smooth_at S p.1 p.2).continuousAt_iteratedFDeriv (by simp)
  exact hi.comp (f := fun p : Icc S.a S.b × Space => S.F p.1 p.2) (F_joint S).continuousAt

theorem Y_derivative (t : Icc S.a S.b) (x : Space) :
    fderiv ℝ (S.Y t) x = (S.F t (S.Y t x)).inverse := by
  rw [S.F_eq_evolution t t.property]
  have he : (jacobianEvolution (S.b-S.a) (sub_nonneg.mpr S.hab.le) S.coefficient (S.Y t x)).forward (S.slabTime t t.property) =
      (jacobianEquiv (S.b-S.a) (sub_nonneg.mpr S.hab.le) S.coefficient (S.slabTime t t.property) (S.Y t x) : Space →L[ℝ] Space) := rfl
  rw [he,ContinuousLinearMap.inverse_equiv]
  exact (backward_hasFDerivAt_label _ _ S.coefficient (S.slabTime t t.property) x).fderiv

/-- The generic inverse-jet theorem is instantiated with the inverse of
the actual forward Jacobian, including all its coefficient-jet premises. -/
theorem Y_jets (n : ℕ) :
    Continuous (fun p : Icc S.a S.b × Space => iteratedFDeriv ℝ n (S.Y p.1) p.2) := by
  apply EulerGevreyComposition.continuous_iteratedFDeriv_of_fderiv_eq_comp
    (fun t : Icc S.a S.b => S.Y t) (fun t y => (S.F t y).inverse)
  · exact S.Y_continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · exact fun t => (S.Y_smooth t t.property).differentiable (by simp)
  · intro t
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (inverseF_smooth_at S t x).comp x (F_smooth S t).contDiffAt
  · exact inverseF_jets S
  · exact Y_derivative S

/-- Every spatial jet of the Eulerian ideal witness is jointly continuous
on the closed slab, including its initial time. -/
theorem magnetic_jets (Bz0 : ℝ) (n : ℕ) : Continuous (fun p : Icc S.a S.b × Space =>
    iteratedFDeriv ℝ n (fun x => S.magnetic Bz0 (p.1,x)) p.2) := by
  let G (t : Icc S.a S.b) (x : Space) := S.F t (S.Y t x)
  have hY : Continuous (fun p : Icc S.a S.b × Space => S.Y p.1 p.2) :=
    S.Y_continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hGj (m : ℕ) : Continuous (fun p : Icc S.a S.b × Space => iteratedFDeriv ℝ m (G p.1) p.2) :=
    composition (fun t : Icc S.a S.b => S.F t) (fun t => S.Y t)
      (fun t _ => (F_smooth S t).contDiffAt) (fun t => S.Y_smooth t t.property)
      (fun k => (F_jets S k).comp (continuous_fst.prodMk hY)) (Y_jets S) m
  have hGc : Continuous (fun p : Icc S.a S.b × Space => G p.1 p.2) :=
    (F_joint S).comp (continuous_fst.prodMk hY)
  have hGs (t : Icc S.a S.b) : ContDiff ℝ ∞ (G t) :=
    (F_smooth S t).comp (S.Y_smooth t t.property)
  let C : (Space →L[ℝ] Space) →L[ℝ] Space :=
    (ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)).flip (Bz0 • coordinateVector 2)
  have hC : ContDiff ℝ ∞ C := C.contDiff
  have hc := composition (fun _ => C) G (fun _ _ => hC.contDiffAt) hGs
    (fun m => (hC.iteratedFDeriv_right (m := ∞) (by simp)).continuous.comp hGc) hGj n
  have he (t : Icc S.a S.b) : C ∘ G t = fun x => S.magnetic Bz0 (t,x) := by
    funext x
    simp [C,G,MagneticPeriodicFlow.Slab.magnetic]
  exact hc.congr (fun p => by rw [he])

end Slab

/-- The Laplacian is the trace of the genuine second spatial derivative. -/
theorem laplacian_eq_jet {B : MagneticField} {t : ℝ}
    (hB : ContDiff ℝ 2 (fun x => B (t,x))) (x : Space) :
    spatialLaplacian B t x = ∑ i : Fin 3,
      iteratedFDeriv ℝ 2 (fun y => B (t,y)) x (fun _ => coordinateVector i) := by
  simp only [spatialLaplacian,spatialDerivative]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  have hd := (hB.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

namespace Slab
variable (S : MagneticPeriodicFlow.Slab)

theorem magnetic_laplacian_continuous (Bz0 : ℝ) : Continuous
    (fun p : Icc S.a S.b × Space => spatialLaplacian (S.magnetic Bz0) p.1 p.2) := by
  have hc : Continuous (fun p : Icc S.a S.b × Space => ∑ i : Fin 3,
      iteratedFDeriv ℝ 2 (fun y => S.magnetic Bz0 (p.1,y)) p.2 (fun _ => coordinateVector i)) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_eval.comp ((magnetic_jets S Bz0 2).prodMk continuous_const)
  exact hc.congr (fun p => (laplacian_eq_jet
    ((S.magnetic_spatial_smooth Bz0 p.1 p.1.property).of_le (by norm_num)) p.2).symm)

theorem magnetic_laplacian_continuousOn (Bz0 : ℝ) : ContinuousOn
    (fun z => spatialLaplacian (S.magnetic Bz0) z.1 z.2) (Icc S.a S.b ×ˢ univ) := by
  exact closed_time_continuity S.hab.le (magnetic_laplacian_continuous S Bz0)

end Slab
/-- Periodicity passes to the Laplacian via actual derivative identities. -/
theorem laplacian_periodic {B : MagneticField} {s : Set ℝ}
    (hp : UnitSpatialPeriodsOn s B)
    (hx : ∀ t ∈ s, ContDiff ℝ 2 (fun y => B (t,y))) :
    UnitSpatialPeriodsOn s (fun z => spatialLaplacian B z.1 z.2) := by
  intro t ht x i
  dsimp only
  rw [laplacian_eq_jet (hx t ht),laplacian_eq_jet (hx t ht),
    MagneticPeriodicCoefficient.spatial_jet_periodic hp 2 ⟨t,ht⟩ x i]

theorem laplacian_eq_of_slice_eq {B I : MagneticField} {t : ℝ}
    (he : ∀ x, B (t,x) = I (t,x)) (x : Space) :
    spatialLaplacian B t x = spatialLaplacian I t x := by
  unfold spatialLaplacian spatialDerivative
  rw [show (fun y => B (t,y)) = (fun y => I (t,y)) from funext he]

end NavierStokes.ResistiveMagnetic.Jets

namespace NavierStokes.MagneticPeriodicSolution.Data
open Set ProblemStatement
open scoped ContDiff
variable (D : MagneticPeriodicSolution.Data)

/-- Closed-slab joint Laplacian continuity for the SAME glued witness.
Overlap compatibility identifies entire spatial slices with one larger
finite-slab representative, also at the initial time. -/
theorem magnetic_laplacian_continuousOn (Bz0 : ℝ) {b : ℝ} (hb : b < 1) :
    ContinuousOn (fun z => spatialLaplacian (D.magnetic Bz0) z.1 z.2)
      (Icc D.a b ×ˢ univ) := by
  obtain ⟨n,hn⟩ := D.exists_endpoint b hb
  have hc := (ResistiveMagnetic.Jets.Slab.magnetic_laplacian_continuousOn (D.slab n) Bz0).mono
    (show Icc D.a b ×ˢ (univ : Set Space) ⊆ Icc (D.slab n).a (D.slab n).b ×ˢ univ from
      fun z hz => ⟨⟨hz.1.1,hz.1.2.trans hn.le⟩,mem_univ _⟩)
  apply hc.congr
  intro z hz
  exact ResistiveMagnetic.Jets.laplacian_eq_of_slice_eq
    (D.magnetic_eq_slab Bz0 z.1 n ⟨hz.1.1,hz.1.2.trans hn.le⟩) z.2

theorem magnetic_laplacian_periodic (Bz0 : ℝ) :
    UnitSpatialPeriodsOn (Ico D.a 1) (fun z => spatialLaplacian (D.magnetic Bz0) z.1 z.2) :=
  ResistiveMagnetic.Jets.laplacian_periodic (D.magnetic_periodic Bz0)
    (fun t ht => (D.magnetic_spatial_smooth Bz0 t ht).of_le (by norm_num))

/-- A finite Laplacian bound, independent of magnetic diffusivity, for
the actual ideal field on each fixed compact preterminal slab. -/
theorem magnetic_laplacian_bound (Bz0 : ℝ) {b : ℝ} (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc D.a b, ∀ x, ‖spatialLaplacian (D.magnetic Bz0) t x‖ ≤ C :=
  ResistiveMagnetic.Comparison.laplacian_bound_of_joint_continuity
    (D.magnetic_laplacian_continuousOn Bz0 hb)
    (fun t ht => D.magnetic_laplacian_periodic Bz0 t ⟨ht.1,ht.2.trans_lt hb⟩)

end NavierStokes.MagneticPeriodicSolution.Data
