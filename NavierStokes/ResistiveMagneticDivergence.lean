import NavierStokes.ResistiveDivergenceAlgebra
import NavierStokes.ResidualRegularity

noncomputable section
namespace NavierStokes.ResistiveMagnetic
open Set Filter ProblemStatement Calculus
open scoped Topology ContDiff

def spaceDirection (i : Fin 3) : SpaceTime := (0,coordinateVector i)
def timeDirection : SpaceTime := (1,0)
def component (B : MagneticField) (i : Fin 3) (z : SpaceTime) := B z i

def scalarTime (f : SpaceTime → ℝ) (z : SpaceTime) := P timeDirection f z
def scalarPartial (i : Fin 3) (f : SpaceTime → ℝ) (z : SpaceTime) := P (spaceDirection i) f z
def scalarLaplacian (f : SpaceTime → ℝ) := Lap spaceDirection f
def divergenceScalar (B : MagneticField) := Div spaceDirection (component B)

variable {O : Set SpaceTime} (hO : IsOpen O) {B : MagneticField}
  (hB : ContDiffOn ℝ ∞ B O) {z : SpaceTime} (hz : z ∈ O)

include hB in
theorem component_smooth (i : Fin 3) : ContDiffOn ℝ ∞ (component B i) O :=
  ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hB)

include hO hB hz in
theorem P_component (v : SpaceTime) (i : Fin 3) :
    P v (component B i) z = (fderiv ℝ B z v) i := by
  have hd := (EuclideanSpace.proj i).hasFDerivAt.comp z
    ((hB.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (component B i) _ z at hd
  rw [P,hd.fderiv]
  rfl

include hO hB hz in
theorem component_time (i : Fin 3) :
    P timeDirection (component B i) z = (temporalDerivative B z.1 z.2) i := by
  rw [P_component hO hB hz]
  have hp : HasFDerivAt (fun s : ℝ => (s,z.2)) ((ContinuousLinearMap.id ℝ ℝ).prod 0) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd := ((hB.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.comp z.1 hp
  change HasFDerivAt (fun s => B (s,z.2)) _ z.1 at hd
  unfold temporalDerivative
  rw [hd.fderiv]
  rfl

include hO hB hz in
theorem component_space (i j : Fin 3) :
    P (spaceDirection j) (component B i) z = (spatialDerivative B z.1 z.2 (coordinateVector j)) i := by
  rw [P_component hO hB hz]
  have hp : HasFDerivAt (fun x : Space => (z.1,x)) ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hd := ((hB.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.comp z.2 hp
  change HasFDerivAt (fun x => B (z.1,x)) _ z.2 at hd
  unfold spatialDerivative
  rw [hd.fderiv]
  rfl

include hO hB hz in
theorem divergenceScalar_eq : divergenceScalar B z = spatialDivergence B z.1 z.2 := by
  unfold divergenceScalar Calculus.Div spatialDivergence
  exact Finset.sum_congr rfl (fun i _ => component_space hO hB hz i i)

include hO hB hz in
theorem component_advection (u : Space) (i : Fin 3) :
    (∑ j, u j * P (spaceDirection j) (component B i) z) = (spatialDerivative B z.1 z.2 u) i := by
  simp_rw [component_space hO hB hz]
  change _ = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (spatialDerivative B z.1 z.2 u)
  conv_rhs => rw [← PeriodicUniqueness.sum_coordinates u, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

include hO hB hz in
theorem component_laplacian (i : Fin 3) :
    Lap spaceDirection (component B i) z = (spatialLaplacian B z.1 z.2) i := by
  unfold Lap spatialLaplacian
  change _ = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (∑ j,
    fderiv ℝ (fun y => spatialDerivative B z.1 y (coordinateVector j)) z.2 (coordinateVector j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  let G : MagneticField := fun w => spatialDerivative B w.1 w.2 (coordinateVector j)
  have hG : ContDiffOn ℝ ∞ G O :=
    (ResidualRegularity.contDiffOn_spatialDerivative hO hB).clm_apply contDiffOn_const
  have he : P (spaceDirection j) (component B i) =ᶠ[𝓝 z] component G i := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact component_space hO hB hw i j
  have he' : P (spaceDirection j) (P (spaceDirection j) (component B i)) z =
      P (spaceDirection j) (component G i) z :=
    congrArg (fun L : SpaceTime →L[ℝ] ℝ => L (spaceDirection j)) he.fderiv_eq
  rw [he', component_space hO hG hz]
  rfl

/-- Local divergence transport, expressed in canonical time and spatial
coordinate derivatives. divergenceScalar_eq identifies the scalar exactly
with the existing spatialDivergence; there is no assumed solenoidality of B. -/
theorem divergence_transport {times : Set ℝ} (htimes : IsOpen times) {eta_m : ℝ}
    {u : VelocityField} {B : MagneticField}
    (hu : ContDiffOn ℝ ∞ u (times ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (times ×ˢ univ))
    (hind : ResistiveInductionOn eta_m times u B)
    (hdiv : ∀ t ∈ times, ∀ x, spatialDivergence u t x = 0)
    {t : ℝ} (ht : t ∈ times) (x : Space) :
    scalarTime (divergenceScalar B) (t,x) +
      Adv spaceDirection (component u) (divergenceScalar B) (t,x) =
      eta_m*scalarLaplacian (divergenceScalar B) (t,x) := by
  have hO : IsOpen (times ×ˢ (univ : Set Space)) := htimes.prod isOpen_univ
  apply Calculus.divergence_transport hO (fun i => component_smooth hu i)
    (fun i => component_smooth hB i) ⟨ht,mem_univ x⟩ timeDirection eta_m
  · intro z hz i
    have he := congrArg (fun v : Space => v i) (hind z.1 hz.1 z.2)
    change (temporalDerivative B z.1 z.2) i + (spatialDerivative B z.1 z.2 (u z)) i =
      (spatialDerivative u z.1 z.2 (B z)) i + eta_m*(spatialLaplacian B z.1 z.2) i at he
    simpa only [component_time hO hB hz, Adv, component,
      component_advection hO hB hz, component_advection hO hu hz, component_laplacian hO hB hz] using he
  · intro z hz
    exact (divergenceScalar_eq hO hu hz).trans (hdiv z.1 hz.1 z.2)
end NavierStokes.ResistiveMagnetic
