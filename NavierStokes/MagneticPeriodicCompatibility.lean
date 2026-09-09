import NavierStokes.MagneticPeriodicFlow

/-! Finite constructions with the same physical initial time agree wherever
both are defined. The proof compares the actual nonlinear flows first. -/
noncomputable section
namespace NavierStokes.MagneticPeriodicFlow.Slab
open Set ProblemStatement
open scoped Topology
private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance

variable (S R : Slab)

theorem Phi_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.Phi t x = R.Phi t x := by
  have hSc : Continuous (fun s => S.Phi s x) := S.Phi_continuous.comp
    (continuous_id.prodMk continuous_const)
  have hRc : Continuous (fun s => R.Phi s x) := R.Phi_continuous.comp
    (continuous_id.prodMk continuous_const)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun s => S.Phi s x-R.Phi s x)
    (f' := fun s => S.velocity (s,S.Phi s x)-S.velocity (s,R.Phi s x))
    (K := (S.data.lipschitzConstant : ℝ))
    (a := S.a) (b := t) (hSc.sub hRc).continuousOn
    (fun s hs => by
      have hS : s ∈ Icc S.a S.b := ⟨hs.1, hs.2.le.trans htS.2⟩
      have hR : s ∈ Icc R.a R.b := ⟨ha ▸ hs.1, hs.2.le.trans htR.2⟩
      convert! ((S.Phi_hasDerivAt s hS x).sub
        (R.Phi_hasDerivAt s hR x)).hasDerivWithinAt using 1
      simp only [hu])
    (by rw [S.Phi_initial, ha, R.Phi_initial, sub_self])
    (fun s hs => by
      have hS : s ∈ Icc S.a S.b := ⟨hs.1, hs.2.le.trans htS.2⟩
      have hl := (S.data.lipschitz (s-S.a)).dist_le_mul (S.Phi s x) (R.Phi s x)
      simpa only [S.data_velocity s hS, dist_eq_norm] using hl)
    t ⟨htS.1,le_rfl⟩
  exact sub_eq_zero.mp hz

theorem F_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.F t x = R.F t x := by
  unfold F
  rw [show S.Phi t = R.Phi t from funext (S.Phi_overlap R hu ha t htS htR)]

theorem Y_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.Y t x = R.Y t x := by
  have he := S.Phi_overlap R hu ha t htS htR (R.Y t x)
  rw [R.Phi_Y] at he
  have hh := congrArg (S.Y t) he
  simpa only [S.Y_Phi] using hh.symm

theorem magnetic_overlap (hu : S.velocity = R.velocity) (ha : S.a = R.a)
    (Bz0 t : ℝ) (htS : t ∈ Icc S.a S.b) (htR : t ∈ Icc R.a R.b) (x : Space) :
    S.magnetic Bz0 (t,x) = R.magnetic Bz0 (t,x) := by
  unfold magnetic
  rw [S.Y_overlap R hu ha t htS htR x, S.F_overlap R hu ha t htS htR]

end NavierStokes.MagneticPeriodicFlow.Slab
