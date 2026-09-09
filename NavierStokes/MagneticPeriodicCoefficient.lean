import NavierStokes.MagneticAssembledAmplification
import Euler.CompactSmoothTimeField
import Euler.SmoothTimeFieldJoint

/-! A compact-cell adapter for smooth periodic velocities. All uniform bounds
are on one finite time slab; no terminal-time bound is assumed. -/

noncomputable section
namespace NavierStokes.MagneticPeriodicCoefficient
open Set Filter ProblemStatement
open scoped Topology ContDiff BoundedContinuousFunction

variable {P V : Type} [TopologicalSpace P] [NormedAddCommGroup V]

omit [TopologicalSpace P] [NormedAddCommGroup V] in
theorem fractional_eq (u : P × Space → V)
    (hp : ∀ t x i, u (t, x + coordinateVector i) = u (t, x)) (t : P) (x : Space) :
    u (t, CompactForceDecay.fractionalPoint x) = u (t, x) :=
  CompactForceDecay.periodic_fractionalPoint
    (g := fun z : SpaceTime => u (t, z.2)) (fun _ _ y i => hp t y i) 0 x

def boundedSlice (u : P × Space → V) (hc : Continuous u)
    (hp : ∀ t x i, u (t, x + coordinateVector i) = u (t, x)) (t : P) : Space →ᵇ V where
  toFun x := u (t, x)
  continuous_toFun := hc.comp (continuous_const.prodMk continuous_id)
  map_bounded' := Metric.isBounded_range_iff.mp
    ((CompactForceDecay.isCompact_unitCube.image
      (hc.comp (continuous_const.prodMk continuous_id))).isBounded.subset (by
        rintro _ ⟨x, rfl⟩
        exact ⟨CompactForceDecay.fractionalPoint x, CompactForceDecay.fractionalPoint_mem_unitCube x,
          fractional_eq u hp t x⟩))

theorem boundedSlice_continuous (u : P × Space → V) (hc : Continuous u)
    (hp : ∀ t x i, u (t, x + coordinateVector i) = u (t, x)) :
    Continuous (boundedSlice u hc hp) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨U, hU, hclose⟩ := CompactForceDecay.isCompact_unitCube.mem_uniformity_of_prod
    (f := fun t x => u (t, x)) (s := univ) hc.continuousOn (mem_univ t)
    (Metric.dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hU
  filter_upwards [hU] with s hs
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.dist_le (half_pos hε).le).mpr
  intro x
  change dist (u (s, x)) (u (t, x)) ≤ ε / 2
  rw [← fractional_eq u hp s x, ← fractional_eq u hp t x]
  exact (hclose s hs _ (CompactForceDecay.fractionalPoint_mem_unitCube x)).le

def boundedPath (u : P × Space → V) (hc : Continuous u)
    (hp : ∀ t x i, u (t, x + coordinateVector i) = u (t, x)) : C(P, Space →ᵇ V) :=
  ⟨boundedSlice u hc hp, boundedSlice_continuous u hc hp⟩

variable [NormedSpace ℝ V]

theorem spatial_jet_periodic {u : SpaceTime → V} {s : Set ℝ}
    (hp : UnitSpatialPeriodsOn s u) (n : ℕ) (t : s) (x : Space) (i : Fin 3) :
    iteratedFDeriv ℝ n (fun y => u (t, y)) (x + coordinateVector i) =
      iteratedFDeriv ℝ n (fun y => u (t, y)) x := by
  have he : (fun y => u (t, y + coordinateVector i)) = (fun y => u (t, y)) :=
    funext (fun y => hp t t.property y i)
  have hd := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => u (t, y)) n
    (coordinateVector i) x
  rw [he] at hd
  exact hd.symm

private local instance (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] V) := inferInstance

/-- The actual field and all its spatial jets, bounded by the periodic cell. -/
def ofPeriodicSlab (s : Set ℝ) [CompactSpace s] (u : SpaceTime → V)
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ)) (hp : UnitSpatialPeriodsOn s u) :
    SmoothTimeField s Space V where
  field := boundedPath (fun z : s × Space => u (z.1, z.2))
    (hu.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.property, mem_univ _⟩)) (fun t x i => hp t t.property x i)
  smooth t := by
    change ContDiff ℝ ∞ (fun x : Space => u ((t : ℝ), x))
    exact contDiffOn_univ.mp
      (hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ => ⟨t.property, mem_univ _⟩))
  jet n := boundedPath (fun z : s × Space => iteratedFDeriv ℝ n (fun y => u (z.1, y)) z.2)
    ((EulerCompactSmoothTimeField.contDiffOn_spatial_jet hu n).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.property, mem_univ _⟩)) (spatial_jet_periodic hp n)
  jet_eq _ _ _ := rfl

@[simp] theorem ofPeriodicSlab_apply (s : Set ℝ) [CompactSpace s] (u : SpaceTime → V)
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ)) (hp : UnitSpatialPeriodsOn s u)
    (t : s) (x : Space) : (ofPeriodicSlab s u hu hp).field t x = u (t, x) := rfl

end NavierStokes.MagneticPeriodicCoefficient

namespace NavierStokes.MagneticPeriodicCoefficient
open Set ProblemStatement
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Physical time is shifted only inside the finite-interval coefficient API. -/
def shiftedField (a : ℝ) (u : SpaceTime → V) : SpaceTime → V :=
  fun z => u (a + z.1, z.2)

theorem shifted_smooth {u : SpaceTime → V} {a b : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Iio (1 : ℝ) ×ˢ univ)) (hb : b < 1) :
    ContDiffOn ℝ ∞ (shiftedField a u) (Icc 0 (b-a) ×ˢ univ) := by
  apply hu.comp ((contDiffOn_const.add contDiffOn_fst).prodMk contDiffOn_snd)
  intro z hz
  exact ⟨by change a + z.1 < 1; have hh : z.1 ≤ b-a := hz.1.2; linarith, mem_univ _⟩

def onSlab (u : SpaceTime → V) (a b : ℝ)
    (hu : ContDiffOn ℝ ∞ u (Iio (1 : ℝ) ×ˢ univ)) (hb : b < 1)
    (hp : UnitSpatialPeriodsOn (Iio (1 : ℝ)) u) :
    SmoothTimeField (Icc (0 : ℝ) (b-a)) Space V :=
  ofPeriodicSlab _ (shiftedField a u) (shifted_smooth hu hb)
    (fun t ht x i => hp (a+t) (by change a+t < 1; have hh : t ≤ b-a := ht.2; linarith) x i)

@[simp] theorem onSlab_apply (u : SpaceTime → V) (a b : ℝ)
    (hu : ContDiffOn ℝ ∞ u (Iio (1 : ℝ) ×ˢ univ)) (hb : b < 1)
    (hp : UnitSpatialPeriodsOn (Iio (1 : ℝ)) u)
    (t : Icc (0 : ℝ) (b-a)) (x : Space) :
    (onSlab u a b hu hb hp).field t x = u (a+t,x) := rfl

section Actual
open CorrectionInitialization.ActualPrimary MagneticAxisTransfer
variable (budget N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (scales : ℕ → ℕ)
    (hsel : MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig budget N0)
      (ActualCandidateAssembly.potentialStages budget N0 hN)
      (ActualCandidateAssembly.directStages budget N0 hN)
      (ActualCandidateAssembly.pressureStages budget N0 hN) scales)

theorem actual_periodic : UnitSpatialPeriodsOn (Iio (1 : ℝ))
    (actualPeriodicVelocity budget N0 hN scales) :=
  TimeLocalization.activatedVelocity_periodic _ _
    (MixedPeriodicAssembly.periodicVelocity_periodic _ _ _)

/-- The actual selected assembled velocity, with no assumed flow wrapper. -/
def actualOnSlab (a b : ℝ) (hb : b < 1) :
    SmoothTimeField (Icc (0 : ℝ) (b-a)) Space Space :=
  onSlab (actualPeriodicVelocity budget N0 hN scales) a b
    (MagneticAssembledAmplification.assembled_velocities_smooth budget N0 hN scales hsel).1
    hb (actual_periodic budget N0 hN scales)

@[simp] theorem actualOnSlab_apply (a b : ℝ) (hb : b < 1)
    (t : Icc (0 : ℝ) (b-a)) (x : Space) :
    (actualOnSlab budget N0 hN scales hsel a b hb).field t x =
      actualPeriodicVelocity budget N0 hN scales (a+t,x) := rfl
include hsel in
/-- Incompressibility of the selected assembled periodic velocity, including
the localized direct angular series and time activation. -/
theorem actual_divergence (t : ℝ) (ht : t < 1) (x : Space) :
    spatialDivergence (actualPeriodicVelocity budget N0 hN scales) t x = 0 := by
  have hsum := hsel.2.2.2.2.2.2.1
  have hp : ContDiffOn ℝ ∞ (actualPotentialSum budget N0 hN scales)
      (Iio (1 : ℝ) ×ˢ univ) := hsum.potential.mono (fun _ hw => hw.1)
  have hv : ContDiffOn ℝ ∞ (actualDirectSum budget N0 hN scales)
      (Iio (1 : ℝ) ×ˢ univ) := hsum.direct.mono (fun _ hw => hw.1)
  have hc : ∀ s ∈ Iio (1 : ℝ), ∀ y,
      spatialDivergence (SpatialLocalization.cutPotential
        (actualDirectSum budget N0 hN scales)) s y = 0 := by
    apply LocalAngularDiagonal.spatialCut_angularSum_divergence
      outgoing.data.h_pos outgoing.data.h_lt_half (ActualCandidateAssembly.directData budget N0 hN)
      hsel.2.2.2.2.1
    · exact_mod_cast hsel.2.1 0
    · intro j
      exact_mod_cast hsel.2.2.2.1.monotone (Nat.zero_le j)
    · exact hsel.2.2.2.2.2.1 0
  have hd := MixedPeriodicAssembly.periodicVelocity_divergence_free hp hv hc ht x
  change spatialDivergence (fun z => SmoothCutoffs.timeSwitch t •
    MixedPeriodicAssembly.periodicVelocity (actualPotentialSum budget N0 hN scales)
      (actualDirectSum budget N0 hN scales) z) t x = 0
  rw [ResidualCalculus.spatialDivergence_const_smul _ t x _
    ((SpatialCurl.contDiff_spatialSlice
      (MixedPeriodicAssembly.periodicVelocity_smoothOn hp hv) ht).differentiable (by simp) x), hd,
    mul_zero]

end Actual
end NavierStokes.MagneticPeriodicCoefficient
