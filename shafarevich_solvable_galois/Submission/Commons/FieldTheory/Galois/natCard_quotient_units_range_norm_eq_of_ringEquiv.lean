import Mathlib.RingTheory.Norm.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Galois

/-- **The norm quotient of units is transported along a compatible pair of ring isomorphisms.**

For ring isomorphisms `eB : B ≃+* B₀`, `eE : E ≃+* E₀` compatible with the algebra maps, the
quotients `Bˣ ⧸ N_{E/B}(Eˣ)` and `B₀ˣ ⧸ N_{E₀/B₀}(E₀ˣ)` have the same cardinality. -/
theorem natCard_quotient_units_range_norm_eq_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E]
    [Field B₀] [Field E₀] [Algebra B E] [Algebra B₀ E₀]
    (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))) := by
  -- The compatibility of `eB` and `eE` with the algebra maps, as an equality of ring homs.
  have he : (algebraMap B₀ E₀).comp (eB : B →+* B₀) = (eE : E →+* E₀).comp (algebraMap B E) := by
    ext x
    exact (h x).symm
  -- Mathlib's general transport lemma for the norm along a *compatible pair* of ring isos.
  have key : ∀ x : E, eB (Algebra.norm B x) = Algebra.norm B₀ (eE x) := by
    intro x
    rw [Algebra.norm_eq_of_equiv_equiv eB eE he x, RingEquiv.apply_symm_apply]
  let f : Eˣ →* Bˣ := Units.map (Algebra.norm B : E →* B)
  let g : E₀ˣ →* B₀ˣ := Units.map (Algebra.norm B₀ : E₀ →* B₀)
  let Φ : Bˣ ≃* B₀ˣ := Units.mapEquiv eB.toMulEquiv
  let Ψ : Eˣ ≃* E₀ˣ := Units.mapEquiv eE.toMulEquiv
  -- On units, the two norm maps correspond under `Φ` and `Ψ`.
  have hΦΨ : ∀ u : Eˣ, Φ (f u) = g (Ψ u) := by
    intro u
    apply Units.ext
    change eB (Algebra.norm B (u : E)) = Algebra.norm B₀ (eE (u : E))
    exact key (u : E)
  -- Consequently the two norm ranges correspond under `Φ`.
  have hrange : Subgroup.map (Φ : Bˣ →* B₀ˣ) f.range = g.range := by
    apply le_antisymm
    · rintro z ⟨y, hy, rfl⟩
      obtain ⟨u, rfl⟩ := hy
      exact ⟨Ψ u, (hΦΨ u).symm⟩
    · rintro z ⟨v, rfl⟩
      refine ⟨f (Ψ.symm v), ⟨Ψ.symm v, rfl⟩, ?_⟩
      have hv := hΦΨ (Ψ.symm v)
      simp only [MulEquiv.apply_symm_apply] at hv
      simpa using hv
  have e : (Bˣ ⧸ f.range) ≃* (B₀ˣ ⧸ g.range) := QuotientGroup.congr f.range g.range Φ hrange
  calc Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B)))
      = Nat.card (Bˣ ⧸ f.range) := rfl
    _ = Nat.card (B₀ˣ ⧸ g.range) := Nat.card_congr e.toEquiv
    _ = Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))) := rfl

end Commons.FieldTheory.Galois