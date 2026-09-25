import Mathlib
import Submission.Work.RelatorRank.Defs

namespace Work.RelatorRank.Counterexample

/-!
# The automorphism group does not act transitively on generating pairs

`G := Multiplicative (ZMod 4 × ZMod 2)` is the abelian group `Z/4 × Z/2` (order `8`), written
multiplicatively.  It is not cyclic (`x ^ 4 = 1` for every `x`, while `|G| = 8`), but it is
`2`-generated.  However its automorphism group is **not** transitive on (unordered) generating
pairs: the *order profile* of a generating pair is preserved by every automorphism, and both
profiles occur.

Concretely we take
* `u  = (1,1)`, `v  = (0,1)` in additive coordinates: `v` has order `2`;
* `u' = (1,0)`, `v' = (3,1)`: both have order `4`.

Both `{u,v}` and `{u',v'}` generate `G`, but no automorphism can carry `{u,v}` onto `{u',v'}`,
because `v ^ 2 = 1` forces the square of its image to be `1`, whereas `(u') ^ 2 ≠ 1` and
`(v') ^ 2 ≠ 1`.
-/

/-- If `u` and `v` enumerate `G = Z/4 × Z/2` through the normal form `u^i * v^j` (`i < 4`,
`j < 2`), then they generate `G`. -/
private lemma closure_pair_eq_top_of_generators
    (u v : Multiplicative (ZMod 4 × ZMod 2))
    (h : ∀ x, ∃ p : Fin 4 × Fin 2, u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ) = x) :
    Subgroup.closure ({u, v} : Set (Multiplicative (ZMod 4 × ZMod 2))) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨p, hp⟩ := h x
  rw [← hp]
  exact mul_mem (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem aut_not_transitive_on_generating_pairs :
    ∃ (u v u' v' : Multiplicative (ZMod 4 × ZMod 2)),
      Subgroup.closure ({u, v} : Set (Multiplicative (ZMod 4 × ZMod 2))) = ⊤ ∧
      Subgroup.closure ({u', v'} : Set (Multiplicative (ZMod 4 × ZMod 2))) = ⊤ ∧
      (¬ ∃ x : Multiplicative (ZMod 4 × ZMod 2),
        Subgroup.closure ({x} : Set (Multiplicative (ZMod 4 × ZMod 2))) = ⊤) ∧
      ¬ (∃ e : Multiplicative (ZMod 4 × ZMod 2) ≃* Multiplicative (ZMod 4 × ZMod 2),
          (e u = u' ∧ e v = v') ∨ (e u = v' ∧ e v = u')) := by
  refine ⟨Multiplicative.ofAdd (1, 1), Multiplicative.ofAdd (0, 1),
          Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (3, 1), ?_, ?_, ?_, ?_⟩
  · -- `(1,1)` and `(0,1)` generate `Z/4 × Z/2`
    apply closure_pair_eq_top_of_generators
    decide
  · -- `(1,0)` and `(3,1)` generate `Z/4 × Z/2`
    apply closure_pair_eq_top_of_generators
    decide
  · -- `G` is not cyclic: every element has order dividing `4`, but `|G| = 8`
    have hexp : ∀ y : Multiplicative (ZMod 4 × ZMod 2), y ^ 4 = 1 := by decide
    rintro ⟨x, hx⟩
    have htop :
        Nat.card ↥(Subgroup.closure ({x} : Set (Multiplicative (ZMod 4 × ZMod 2)))) = 8 := by
      rw [hx, Subgroup.card_top]
      simp [Nat.card_eq_fintype_card]
    have hle :
        Nat.card ↥(Subgroup.closure ({x} : Set (Multiplicative (ZMod 4 × ZMod 2)))) ≤ 4 := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hexp x))
    omega
  · -- no automorphism can match the two generating pairs: they have different order profiles
    rintro ⟨e, hcases⟩
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv2 : (Multiplicative.ofAdd (0, 1) : Multiplicative (ZMod 4 × ZMod 2)) ^ 2 = 1 := by
        decide
      have hsq : (Multiplicative.ofAdd (3, 1) : Multiplicative (ZMod 4 × ZMod 2)) ^ 2 = 1 := by
        rw [← h2, ← map_pow, hv2, map_one]
      exact absurd hsq (by decide)
    · have hv2 : (Multiplicative.ofAdd (0, 1) : Multiplicative (ZMod 4 × ZMod 2)) ^ 2 = 1 := by
        decide
      have hsq : (Multiplicative.ofAdd (1, 0) : Multiplicative (ZMod 4 × ZMod 2)) ^ 2 = 1 := by
        rw [← h2, ← map_pow, hv2, map_one]
      exact absurd hsq (by decide)

end Work.RelatorRank.Counterexample
