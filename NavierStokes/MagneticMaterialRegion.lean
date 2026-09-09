import NavierStokes.MagneticEnergyLowerBounds

/-! The fixed-start flow and material high-field regions for the single
preterminal compact magnetic field. -/
noncomputable section
namespace NavierStokes.MagneticCompactSolution.Data
open Set Filter Metric MeasureTheory ProblemStatement MagneticCompactFlow
open MagneticAmplificationRegion MagneticEnergyLowerBounds
open scoped Topology ContDiff ENNReal
variable (D : Data)

def Phi (t : ℝ) (xi : Space) : Space :=
  if ht : t < 1 then (D.slab (D.index t ht)).Phi t xi else xi

theorem Phi_eq_slab (t : ℝ) (n : ℕ) (ht : t ∈ Icc D.a (D.endpoints n)) :
    D.Phi t = (D.slab n).Phi t := by
  funext x
  have ht1 := ht.2.trans_lt (D.endpoints_spec.2.1 n).2
  rw [Phi, dite_eq_left ht1]
  exact (D.slab (D.index t ht1)).Phi_overlap (D.slab n) rfl rfl t
    ⟨ht.1,(D.index_spec t ht1).le⟩ ht x

/-- The actual spatial Jacobian, not an independently chosen evolution. -/
def F (t : ℝ) := fderiv ℝ (D.Phi t)
def Q (W : Space → Space) (t : ℝ) (xi : Space) := D.F t xi (W xi)

theorem Q_eq_slab (W : Space → Space) (t : ℝ) (n : ℕ)
    (ht : t ∈ Icc D.a (D.endpoints n)) : D.Q W t = (D.slab n).Q W t := by
  unfold Q F
  rw [D.Phi_eq_slab t n ht]
  rfl

theorem magnetic_Phi_Q (W : Space → Space) (t : ℝ) (ht : t ∈ Ico D.a 1) (xi : Space) :
    D.magnetic W (t,D.Phi t xi) = D.Q W t xi := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have hs : t ∈ Icc D.a (D.endpoints n) := ⟨ht.1,hn.le⟩
  rw [D.Phi_eq_slab t n hs,D.Q_eq_slab W t n hs,D.magnetic_eq_slab W t n hs]
  exact (D.slab n).magnetic_Phi_Q W t xi

theorem exists_uniform_DQ_bound (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (xi : Space) (r0 b : ℝ) (hb : b ∈ Ico D.a 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t ∈ Icc D.a b, ∀ x ∈ closedBall xi r0,
      ‖fderiv ℝ (D.Q W t) x‖ ≤ H := by
  obtain ⟨n,hn⟩ := D.exists_endpoint b hb.2
  obtain ⟨H,hH,hbound⟩ := (D.slab n).exists_uniform_DQ_bound W hW xi r0
  refine ⟨H,hH,?_⟩
  intro t ht x hx
  have hs : t ∈ Icc D.a (D.endpoints n) := ⟨ht.1,ht.2.trans hn.le⟩
  rw [D.Q_eq_slab W t n hs]
  exact hbound t hs x hx

/-- The least upper bound of the label derivative on the fixed closed ball. -/
def derivativeBound (W : Space → Space) (xi : Space) (r0 t : ℝ) : ℝ :=
  sSup ((fun x => ‖fderiv ℝ (D.Q W t) x‖) '' closedBall xi r0)

theorem derivativeBound_spec (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (xi : Space) {r0 t : ℝ} (hr : 0 ≤ r0) (ht : t ∈ Ico D.a 1) :
    0 ≤ D.derivativeBound W xi r0 t ∧
      ∀ x ∈ closedBall xi r0, ‖fderiv ℝ (D.Q W t) x‖ ≤ D.derivativeBound W xi r0 t := by
  obtain ⟨H,_,hH⟩ := D.exists_uniform_DQ_bound W hW xi r0 t ht
  have hb : BddAbove ((fun x => ‖fderiv ℝ (D.Q W t) x‖) '' closedBall xi r0) :=
    ⟨H,by rintro _ ⟨x,hx,rfl⟩; exact hH t ⟨ht.1,le_rfl⟩ x hx⟩
  have hbound : ∀ x ∈ closedBall xi r0, ‖fderiv ℝ (D.Q W t) x‖ ≤ D.derivativeBound W xi r0 t :=
    fun x hx => le_csSup hb ⟨x,hx,rfl⟩
  exact ⟨(norm_nonneg _).trans (hbound xi (mem_closedBall_self hr)),hbound⟩

theorem derivativeBound_uniform (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (xi : Space) {r0 : ℝ} (hr : 0 ≤ r0) (b : ℝ) (hb : b ∈ Ico D.a 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t ∈ Icc D.a b, D.derivativeBound W xi r0 t ≤ H := by
  obtain ⟨H,hH,hbound⟩ := D.exists_uniform_DQ_bound W hW xi r0 b hb
  refine ⟨H,hH,fun t ht => csSup_le ?_ ?_⟩
  · exact ⟨_,xi,mem_closedBall_self hr,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact hbound t ht x hx

def region (t : ℝ) (xi : Space) (r : ℝ) := D.Phi t '' ball xi r

theorem quantitative_region (W : Space → Space) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (ht : t ∈ Ico D.a 1) (xi : Space) {r0 M H : ℝ}
    (hr : 0 < r0) (hM : 0 < M) (hH : 0 ≤ H) (hcenter : ‖D.Q W t xi‖ = M)
    (hbound : ∀ x ∈ closedBall xi r0, ‖fderiv ℝ (D.Q W t) x‖ ≤ H) :
    let r := radius r0 M H
    IsOpen (D.region t xi r) ∧
    volume (D.region t xi r) = ENNReal.ofReal (c3*r^3) ∧
    (∀ x ∈ D.region t xi r, M/2 ≤ ‖D.magnetic W (t,x)‖) ∧
    ENNReal.ofReal ((c3/8)*M^2*r^3) ≤ MagneticCompactFlow.energy (D.magnetic W) t := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  have hs : t ∈ Icc D.a (D.endpoints n) := ⟨ht.1,hn.le⟩
  have he : (fun x => D.magnetic W (t,x)) = (fun x => (D.slab n).magnetic W (t,x)) :=
    funext (D.magnetic_eq_slab W t n hs)
  have hu : D.region t = (D.slab n).region t := by
    funext xi r
    unfold region Slab.region
    rw [D.Phi_eq_slab t n hs]
  rw [D.Q_eq_slab W t n hs] at hcenter hbound
  have hh := (D.slab n).quantitative_region W hW
    (fun s hs x => D.divergence s ⟨hs.1,hs.2.trans_lt (D.endpoints_spec.2.1 n).2⟩ x)
    t hs xi hr hM hH hcenter hbound
  have hep : ∀ x, D.magnetic W (t,x) = (D.slab n).magnetic W (t,x) := congrFun he
  simpa only [hu, MagneticCompactFlow.energy, hep] using hh
/-- Nonlinear trajectory uniqueness identifies the distinguished label. -/
theorem Phi_eq_trajectory (gamma : ℝ → Space)
    (hc : ContinuousOn gamma (Ico D.a 1))
    (hd : ∀ t ∈ Ico D.a 1, HasDerivAt gamma (D.velocity (t,gamma t)) t)
    (t : ℝ) (ht : t ∈ Ico D.a 1) : D.Phi t (gamma D.a) = gamma t := by
  obtain ⟨n,hn⟩ := D.exists_endpoint t ht.2
  let S := D.slab n
  have hs : t ∈ Icc S.a S.b := ⟨ht.1,hn.le⟩
  rw [D.Phi_eq_slab t n hs]
  have hSc : Continuous (fun s => S.Phi s (gamma D.a)) := S.Phi_continuous.comp
    (continuous_id.prodMk continuous_const)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun s => S.Phi s (gamma D.a)-gamma s)
    (f' := fun s => D.velocity (s,S.Phi s (gamma D.a))-D.velocity (s,gamma s))
    (K := (S.data.lipschitzConstant : ℝ))
    (a := D.a) (b := t)
    (hSc.continuousOn.sub (hc.mono (fun s hs => ⟨hs.1,hs.2.trans_lt ht.2⟩)))
    (fun s hs => by
      exact ((S.Phi_hasDerivAt s ⟨hs.1,hs.2.le.trans hn.le⟩ _).sub
        (hd s ⟨hs.1,hs.2.trans ht.2⟩)).hasDerivWithinAt)
    (by rw [show D.a = S.a from rfl, S.Phi_initial, sub_self])
    (fun s hs => by
      have hS : s ∈ Icc S.a S.b := ⟨hs.1,hs.2.le.trans hn.le⟩
      have hl := (S.data.lipschitz (s-D.a)).dist_le_mul (S.Phi s (gamma D.a)) (gamma s)
      change ‖S.data.velocity (s-S.a) _ - S.data.velocity (s-S.a) _‖ ≤ _ at hl
      rw [S.data_velocity s hS, S.data_velocity s hS] at hl
      convert! hl using 1)
    t ⟨ht.1,le_rfl⟩
  exact sub_eq_zero.mp hz

end NavierStokes.MagneticCompactSolution.Data
