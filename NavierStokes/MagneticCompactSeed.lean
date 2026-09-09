import NavierStokes.MagneticPeriodicMain

/-! A compact smooth solenoidal seed, equal to a prescribed axial constant
near its center. The potential uses the project's right-handed curl. -/
noncomputable section
namespace NavierStokes.MagneticCompactSeed
open Set Filter ProblemStatement SpatialLocalization
open scoped Topology ContDiff

def linearPotential (Bz0 : ℝ) : Space →L[ℝ] Space :=
  (Bz0/2) • ((EuclideanSpace.proj 0).smulRight (coordinateVector 1) -
    (EuclideanSpace.proj 1).smulRight (coordinateVector 0))

/-- One half of Bz0 e2 cross (x-center), multiplied by the smooth cutoff. -/
def potential (center : Space) (Bz0 : ℝ) (x : Space) : Space :=
  spatialCutoff (x-center) • linearPotential Bz0 (x-center)

def seed (center : Space) (Bz0 : ℝ) : Space → Space := SpatialCurl.curl (potential center Bz0)

def seedSupport (center : Space) : Set Space := (fun x => x+center) '' supportCylinder

theorem support_compact (center : Space) : IsCompact (seedSupport center) :=
  isCompact_supportCylinder.image (continuous_id.add continuous_const)

theorem potential_smooth (center : Space) (Bz0 : ℝ) : ContDiff ℝ ∞ (potential center Bz0) :=
  (spatialCutoff_contDiff.comp (contDiff_id.sub contDiff_const)).smul
    ((linearPotential Bz0).contDiff.comp (contDiff_id.sub contDiff_const))

theorem seed_smooth (center : Space) (Bz0 : ℝ) : ContDiff ℝ ∞ (seed center Bz0) :=
  SpatialCurl.contDiff_curl (potential_smooth center Bz0) (by simp)

theorem seed_divergence (center : Space) (Bz0 : ℝ) (x : Space) :
    (∑ i : Fin 3, (fderiv ℝ (seed center Bz0) x (coordinateVector i)) i) = 0 :=
  SpatialCurl.divergence_curl ((potential_smooth center Bz0).contDiffAt.of_le (by simp))

theorem seed_supported (center : Space) (Bz0 : ℝ) : tsupport (seed center Bz0) ⊆ seedSupport center := by
  apply (SpatialCurl.tsupport_curl_cutoff_subset _ _).trans
  apply closure_minimal _ (support_compact center).isClosed
  intro x hx
  refine ⟨x-center, spatialCutoff_support_subset hx, sub_add_cancel _ _⟩

theorem seed_compact (center : Space) (Bz0 : ℝ) : HasCompactSupport (seed center Bz0) :=
  (support_compact center).of_isClosed_subset (isClosed_tsupport _) (seed_supported center Bz0)

theorem curl_linear (center : Space) (Bz0 : ℝ) (x : Space) :
    SpatialCurl.curl (fun y => linearPotential Bz0 (y-center)) x = Bz0 • coordinateVector 2 := by
  have hd := (linearPotential Bz0).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const center)
  change HasFDerivAt (fun y => linearPotential Bz0 (y-center)) _ x at hd
  rw [SpatialCurl.curl, hd.fderiv]
  ext i
  fin_cases i <;> simp [SpatialCurl.curlLinear, linearPotential, coordinateVector]
  all_goals ring

theorem seed_eq_on_plateau (center : Space) (Bz0 : ℝ) {x : Space} (hx : x-center ∈ plateau) :
    seed center Bz0 x = Bz0 • coordinateVector 2 := by
  have he : potential center Bz0 =ᶠ[𝓝 x] (fun y => linearPotential Bz0 (y-center)) := by
    filter_upwards [(spatialCutoff_eventually_one hx).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt] with y hy
    change spatialCutoff (y-center) = 1 at hy
    simp only [potential, hy, one_smul]
  exact (congrArg SpatialCurl.curlLinear he.fderiv_eq).trans (curl_linear center Bz0 x)

theorem seed_local_constant (center : Space) (Bz0 : ℝ) :
    seed center Bz0 =ᶠ[𝓝 center] (fun _ => Bz0 • coordinateVector 2) := by
  have hh : (fun x : Space => x-center) center ∈ plateau := by simpa using zero_mem_plateau
  filter_upwards [(continuous_id.sub continuous_const).continuousAt.eventually
    (isOpen_plateau.mem_nhds hh)] with x hx
  exact seed_eq_on_plateau center Bz0 hx

@[simp] theorem seed_at_center (center : Space) (Bz0 : ℝ) :
    seed center Bz0 center = Bz0 • coordinateVector 2 :=
  (seed_local_constant center Bz0).self_of_nhds
end NavierStokes.MagneticCompactSeed
