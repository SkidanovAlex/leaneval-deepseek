import Mathlib.Topology.Algebra.Valued.WithVal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Topology.Algebra.Valued

open Filter MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

theorem uniformContinuous_withVal_of_valuation_eq_of_cofinal {K L : Type*} [Ring K] [Ring L]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {w : Valuation L Γ₀}
    (f : WithVal v →+* WithVal w)
    (hf : ∀ x : WithVal v, WithVal.valuation w (f x) = WithVal.valuation v x)
    (hc : ∀ γ : Γ₀, 0 < γ → ∃ x : WithVal v, 0 < WithVal.valuation v x ∧
        WithVal.valuation v x ≤ γ) :
    UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero (WithVal v) Γ₀).tendsto_iff
    (Valued.hasBasis_nhds_zero (WithVal w) Γ₀)]
  intro γ _
  let γ' : Γ₀ := embedding γ.1
  have hpos : 0 < γ' := ValueGroup₀.embedding_unit_pos γ
  obtain ⟨x₀, hx₀pos, hx₀le⟩ := hc γ' hpos
  refine ⟨Units.mk0 ((Valued.v : Valuation (WithVal v) Γ₀).restrict x₀) ?_, trivial, ?_⟩
  · exact ne_of_gt ((Valuation.restrict_pos_iff
      (v := (Valued.v : Valuation (WithVal v) Γ₀)) x₀).mpr hx₀pos)
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding]
    rw [Units.val_mk0] at hx
    have hkey : (Valued.v : Valuation (WithVal w) Γ₀) (f x)
        = (Valued.v : Valuation (WithVal v) Γ₀) x := hf x
    rw [hkey]
    calc (Valued.v : Valuation (WithVal v) Γ₀) x
        < (Valued.v : Valuation (WithVal v) Γ₀) x₀ := by
          rw [← Valuation.restrict_lt_iff]
          exact hx
      _ ≤ embedding γ.1 := hx₀le

end Commons.Topology.Algebra.Valued