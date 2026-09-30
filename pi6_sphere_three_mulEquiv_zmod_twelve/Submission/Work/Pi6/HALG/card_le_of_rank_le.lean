import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false

namespace Work.Pi6.HALG

/-- A vector space over a finite field whose (Cardinal) rank is at most `k` has at most `|𝕜|^k`
elements. Write `Submission/Work/Pi6/HALG/card_le_of_rank_le.lean`, module
`Submission.Work.Pi6.HALG.card_le_of_rank_le`, namespace `Work.Pi6.HALG`.
Hints: `h : Module.rank 𝕜 V ≤ (k : Cardinal)` gives `Module.rank 𝕜 V < ℵ₀`, hence
`Module.Finite 𝕜 V` via `Module.rank_lt_aleph0_iff` (use `Module.Free.of_divisionRing` and the
`StrongRankCondition` instance for a division ring), then `Finite V` via `Module.finite_of_finite`
(𝕜 is finite), then `Module.finrank_eq_rank` and `Module.card_eq_pow_finrank`
(`Fintype.card V = Fintype.card 𝕜 ^ Module.finrank 𝕜 V`) with `Nat.card_eq_fintype_card`; conclude
with monotonicity of `x ↦ b ^ x` for `b = Nat.card 𝕜 ≥ 2`. -/
theorem card_le_of_rank_le {𝕜 : Type} [Field 𝕜] [Fintype 𝕜] {V : Type} [AddCommGroup V]
    [Module 𝕜 V] (k : ℕ) (h : Module.rank 𝕜 V ≤ k) :
    Nat.card V ≤ (Nat.card 𝕜) ^ k := by
  -- `k` is a natural number, hence `< ℵ₀`, so the rank is finite.
  have hfree : Module.Free 𝕜 V := Module.Free.of_divisionRing 𝕜 V
  have hfin : Module.Finite 𝕜 V := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt h (Cardinal.natCast_lt_aleph0 (n := k))
  -- A finite module over a finite ring is finite.
  have hfinV : Finite V := Module.finite_of_finite 𝕜
  haveI : Fintype V := Fintype.ofFinite V
  -- The finrank is exactly the truncated rank, in particular `≤ k`.
  have hfr : Module.finrank 𝕜 V ≤ k := by
    have hc : (Module.finrank 𝕜 V : Cardinal) ≤ (k : Cardinal) := by
      rw [Module.finrank_eq_rank]; exact h
    exact_mod_cast hc
  -- Now count: `|V| = |𝕜| ^ finrank 𝕜 V ≤ |𝕜| ^ k`.
  have hcardV : Nat.card V = Fintype.card V := @Nat.card_eq_fintype_card V _
  have hcardk : Nat.card 𝕜 = Fintype.card 𝕜 := @Nat.card_eq_fintype_card 𝕜 _
  rw [hcardV, hcardk]
  rw [Module.card_eq_pow_finrank (K := 𝕜) (V := V)]
  exact Nat.pow_le_pow_right (Fintype.card_pos_iff.mpr ⟨(0 : 𝕜)⟩) hfr

end Work.Pi6.HALG
