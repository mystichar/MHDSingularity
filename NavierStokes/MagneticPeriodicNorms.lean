import NavierStokes.MagneticPeriodicSolution

/-! Supremum norm divergence and finite-cell energy bounds. Bounds are only
on fixed compact preterminal slabs, never uniform up to the singular time. -/
noncomputable section
namespace NavierStokes.MagneticPeriodicNorms
open Set Filter MeasureTheory ProblemStatement
open scoped Topology ENNReal

/-- The global spatial supremum norm (not an essential supremum). -/
def supNorm (B : MagneticField) (t : ℝ) : ℝ := sSup (Set.range (fun x => ‖B (t,x)‖))

/-- Magnetic energy per unit cell, as a nonnegative extended integral. -/
def cellEnergy (B : MagneticField) (t : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ x in CompactForceDecay.unitCube, ENNReal.ofReal (‖B (t,x)‖ ^ 2)

variable {B : MagneticField} {a b : ℝ}

theorem slab_bound (hc : ContinuousOn B (Icc a b ×ˢ univ))
    (hp : UnitSpatialPeriodsOn (Icc a b) B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x, ‖B (t,x)‖ ≤ C := by
  have hk := (isCompact_Icc (a := a) (b := b)).prod CompactForceDecay.isCompact_unitCube
  have hh := (hk.image_of_continuousOn (hc.mono (prod_subset_prod_right (subset_univ _)))).isBounded
  obtain ⟨C,hC,hbound⟩ := hh.exists_pos_norm_le
  refine ⟨C,hC.le,?_⟩
  intro t ht x
  have he := MagneticPeriodicCoefficient.fractional_eq
    (fun z : (Icc a b) × Space => B (z.1,z.2))
    (fun s y i => hp s s.property y i) ⟨t,ht⟩ x
  rw [← he]
  exact hbound _ ⟨(t,CompactForceDecay.fractionalPoint x),
    ⟨ht,CompactForceDecay.fractionalPoint_mem_unitCube x⟩,rfl⟩

theorem supNorm_bounds {C : ℝ} (_hC : 0 ≤ C) (h : ∀ x, ‖B (a,x)‖ ≤ C) :
    0 ≤ supNorm B a ∧ supNorm B a ≤ C ∧ ∀ x, ‖B (a,x)‖ ≤ supNorm B a := by
  have hb : BddAbove (Set.range (fun x => ‖B (a,x)‖)) := ⟨C,by rintro _ ⟨x,rfl⟩; exact h x⟩
  have hl : ∀ x, ‖B (a,x)‖ ≤ supNorm B a := fun x => le_csSup hb ⟨x,rfl⟩
  exact ⟨(norm_nonneg _).trans (hl 0), csSup_le (Set.range_nonempty _) (by rintro _ ⟨x,rfl⟩; exact h x), hl⟩

theorem energy_bound {C : ℝ} (_hC : 0 ≤ C) (h : ∀ x, ‖B (a,x)‖ ≤ C) :
    cellEnergy B a ≤ (2 : ℝ≥0∞)⁻¹ *
      (ENNReal.ofReal (C^2) * volume CompactForceDecay.unitCube) := by
  unfold cellEnergy
  apply mul_le_mul_right
  calc
    _ ≤ ∫⁻ _x in CompactForceDecay.unitCube, ENNReal.ofReal (C^2) :=
      lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h x) 2))
    _ = _ := by simp

theorem slab_norm_energy_bound (hc : ContinuousOn B (Icc a b ×ˢ univ))
    (hp : UnitSpatialPeriodsOn (Icc a b) B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E : ℝ≥0∞, E < ⊤ ∧
      ∀ t ∈ Icc a b, supNorm B t ≤ C ∧ cellEnergy B t ≤ E ∧ cellEnergy B t < ⊤ := by
  obtain ⟨C,hC,hbound⟩ := slab_bound hc hp
  let E := (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (C^2) * volume CompactForceDecay.unitCube)
  have hE : E < ⊤ := ENNReal.mul_lt_top (by norm_num)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top CompactForceDecay.isCompact_unitCube.measure_lt_top)
  refine ⟨C,hC,E,hE,?_⟩
  intro t ht
  exact ⟨(supNorm_bounds hC (hbound t ht)).2.1,
    energy_bound hC (hbound t ht), (energy_bound hC (hbound t ht)).trans_lt hE⟩

theorem supNorm_tendsto {γ : ℝ → Space}
    (hc : ContinuousOn B (Ico a 1 ×ˢ univ))
    (hp : UnitSpatialPeriodsOn (Ico a 1) B) (ha : a < 1)
    (hg : Tendsto (fun t => ‖B (t,γ t)‖) (𝓝[<] 1) atTop) :
    Tendsto (supNorm B) (𝓝[<] 1) atTop := by
  apply tendsto_atTop_mono' _ _ hg
  filter_upwards [Ioo_mem_nhdsLT ha] with t ht
  have hs : Icc a t ⊆ Ico a 1 := fun s hs => ⟨hs.1,hs.2.trans_lt ht.2⟩
  obtain ⟨C,hC,hbound⟩ := slab_bound
    (hc.mono (prod_subset_prod_left hs)) (fun s hs' x i => hp s (hs hs') x i)
  exact (supNorm_bounds hC (hbound t ⟨ht.1.le,le_rfl⟩)).2.2 (γ t)
end NavierStokes.MagneticPeriodicNorms
