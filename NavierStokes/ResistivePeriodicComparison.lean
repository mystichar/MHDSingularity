import NavierStokes.ResistiveSquaredNormSlices

/-! Fixed-slab O(eta_m) comparison and uniqueness for supplied periodic
classical solutions. These theorems construct the scalar barrier from the
PDE; they do not construct resistive solutions. -/
noncomputable section
namespace NavierStokes.ResistiveMagnetic.Comparison
open Set Filter ProblemStatement
open scoped ContDiff Topology

/-- Inhomogeneous vector estimate. The reaction constant includes the
Young-inequality term; the nonnegative diffusivity can also be zero. -/
theorem forced_estimate {u W f : VelocityField} {a b eta_m L D : ℝ}
    (hab : a < b) (heta : 0 ≤ eta_m) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hc : ContinuousOn W (Icc a b ×ˢ univ))
    (hp : UnitSpatialPeriodsOn (Icc a b) W)
    (htd : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => W (s,x)) t)
    (hxd : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => W (t,x)))
    (hu : ∀ t ∈ Ioo a b, ∀ x, ‖spatialDerivative u t x‖ ≤ L)
    (hf : ∀ t ∈ Ioo a b, ∀ x, ‖f (t,x)‖ ≤ D)
    (heq : ∀ t ∈ Ioo a b, ∀ x,
      temporalDerivative W t x + spatialDerivative W t x (u (t,x)) =
      spatialDerivative u t x (W (t,x)) + eta_m • spatialLaplacian W t x + eta_m • f (t,x))
    (hi : ∀ x, W (a,x) = 0) {t : ℝ} (ht : t ∈ Icc a b) (x : Space) :
    ‖W (t,x)‖ ≤ eta_m * constant L D a b := by
  have hcpos : 0 < 2*L+1 := by linarith
  have hbar := Slice.comparison (q := fun z => ‖W z‖^2) (u := u)
    (c := 2*L+1) (F0 := eta_m^2*D^2) hab heta hcpos (by positivity)
    (hc.norm.pow 2) (fun s hs y i => by dsimp only; rw [hp s hs y i])
    (fun s hs y => (htd s hs y).hasDerivAt.norm_sq.differentiableAt)
    (fun s hs => (hxd s hs).norm_sq (𝕜 := ℝ))
    (fun s hs y => Slice.squared_inequality (htd s hs y) (hxd s hs) heta
      (hu s hs y) (hf s hs y) (heq s hs y))
    (fun y => by simp [hi y]) ht x
  apply norm_le_of_squared_barrier heta hL hD hab.le
  calc
    ‖W (t,x)‖^2 ≤ eta_m^2*D^2*(Real.exp ((2*L+1)*(t-a))-1)/(2*L+1) := hbar
    _ = eta_m^2*D^2*((Real.exp ((2*L+1)*(t-a))-1)/(2*L+1)) := by ring
    _ ≤ eta_m^2*D^2*((Real.exp ((2*L+1)*(b-a))-1)/(2*L+1)) := by gcongr; exact ht.2

/-- The uniform ideal/resistive comparison derived from their two PDEs.
The ideal field needs no joint C-infinity regularity. L and D are explicit
fixed-slab bounds, and the scalar barrier is a conclusion, not a premise. -/
theorem ideal_resistive {u B I : VelocityField} {a b eta_m L D : ℝ}
    (hab : a < b) (heta : 0 ≤ eta_m) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hBc : ContinuousOn B (Icc a b ×ˢ univ)) (hIc : ContinuousOn I (Icc a b ×ˢ univ))
    (hBp : UnitSpatialPeriodsOn (Icc a b) B) (hIp : UnitSpatialPeriodsOn (Icc a b) I)
    (hBt : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t)
    (hIt : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => I (s,x)) t)
    (hBx : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => B (t,x)))
    (hIx : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => I (t,x)))
    (hu : ∀ t ∈ Ioo a b, ∀ x, ‖spatialDerivative u t x‖ ≤ L)
    (hΔ : ∀ t ∈ Ioo a b, ∀ x, ‖spatialLaplacian I t x‖ ≤ D)
    (hres : ResistiveInductionOn eta_m (Ioo a b) u B)
    (hideal : MagneticTransport.IdealInductionOn (Ioo a b) u I)
    (hi : ∀ x, B (a,x) = I (a,x)) :
    ∀ t ∈ Icc a b, ∀ x, ‖B (t,x)-I (t,x)‖ ≤ eta_m * constant L D a b := by
  apply forced_estimate (W := B-I) (f := fun z => spatialLaplacian I z.1 z.2)
    hab heta hL hD (hBc.sub hIc)
  · intro t ht x i
    simp only [Pi.sub_apply,hBp t ht x i,hIp t ht x i]
  · exact fun t ht x => (hBt t ht x).sub (hIt t ht x)
  · exact fun t ht => (hBx t ht).sub (hIx t ht)
  · exact hu
  · exact hΔ
  · exact fun t ht x => difference_equation_of_slices (hBx t ht) (hIx t ht)
      (hBt t ht x) (hIt t ht x) (hres t ht x) (hideal t ht x)
  · exact difference_initial hi

/-- Forward uniqueness in the explicitly stated classical periodic class.
Neither divergence freedom nor evolution before the initial time is used. -/
theorem resistive_unique {u B I : VelocityField} {a b eta_m L : ℝ}
    (hab : a < b) (heta : 0 ≤ eta_m) (hL : 0 ≤ L)
    (hBc : ContinuousOn B (Icc a b ×ˢ univ)) (hIc : ContinuousOn I (Icc a b ×ˢ univ))
    (hBp : UnitSpatialPeriodsOn (Icc a b) B) (hIp : UnitSpatialPeriodsOn (Icc a b) I)
    (hBt : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => B (s,x)) t)
    (hIt : ∀ t ∈ Ioo a b, ∀ x, DifferentiableAt ℝ (fun s => I (s,x)) t)
    (hBx : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => B (t,x)))
    (hIx : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (fun x => I (t,x)))
    (hu : ∀ t ∈ Ioo a b, ∀ x, ‖spatialDerivative u t x‖ ≤ L)
    (hres : ResistiveInductionOn eta_m (Ioo a b) u B)
    (hres' : ResistiveInductionOn eta_m (Ioo a b) u I)
    (hi : ∀ x, B (a,x) = I (a,x)) :
    ∀ t ∈ Icc a b, ∀ x, B (t,x) = I (t,x) := by
  intro t₀ ht₀ x₀
  have hh := forced_estimate (W := B-I) (f := 0) (D := 0)
    hab heta hL le_rfl (hBc.sub hIc)
    (fun t ht x i => by simp only [Pi.sub_apply,hBp t ht x i,hIp t ht x i])
    (fun t ht x => (hBt t ht x).sub (hIt t ht x))
    (fun t ht => (hBx t ht).sub (hIx t ht)) hu
    (fun _ _ _ => by simp) (fun t ht x => ?_) (difference_initial hi) ht₀ x₀
  · simpa only [constant_zero,mul_zero,norm_le_zero_iff,Pi.sub_apply,sub_eq_zero] using hh
  · rw [PeriodicUniqueness.temporalDerivative_sub (hBt t ht x) (hIt t ht x),
      spatialDerivative_sub_of_differentiable ((hBx t ht).differentiable (by norm_num))
        ((hIx t ht).differentiable (by norm_num)),
      spatialLaplacian_sub_of_contDiff_two (hBx t ht) (hIx t ht)]
    simp only [Pi.sub_apply,sub_apply,map_sub,smul_sub,Pi.zero_apply,smul_zero,add_zero]
    rw [eq_sub_of_add_eq (hres t ht x),eq_sub_of_add_eq (hres' t ht x)]
    module

end NavierStokes.ResistiveMagnetic.Comparison
