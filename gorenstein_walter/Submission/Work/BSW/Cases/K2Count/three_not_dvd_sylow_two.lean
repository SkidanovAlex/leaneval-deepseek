import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Char.three_special_characters
import Submission.Work.BSW.Char.no_bad_arithmetic_two
import Submission.Work.BSW.Cases.sylow_number_and_ncard

namespace Work.BSW.Cases.K2Count

/-- **The `3`-part of the Sylow-`2` counting** (Bender 1974, §1, the `|K| = 2` case).

`n₂ = Nat.card (Sylow 2 G)` is not divisible by `3`.  The proof is the character-theoretic
computation of Bender–Suzuki–Wall (Bender 1974 §2, Case B for `a = 2`), fed by the two conjugacy
class identities of `Work.BSW.Char`:

* `Work.BSW.Char.three_special_characters h hk hsimple hnab` (already proved, import it) supplies
  three non-trivial irreducible characters `χᵢ`, degrees `dᵢ ≥ 2` and signs `eᵢ = ±1` with
  `χᵢ(t) = eᵢ`, `χᵢ(1) = dᵢ`, `1 + e₁/d₁ + e₂/d₂ + e₃/d₃ = 32/|G|` and `1 + d₁² + d₂² + d₃² ≤ |G|`;
* `Work.BSW.Cases.sylow_number_and_ncard` (already proved, import it) supplies `12 * n₂ = |G|`,
  `n₂ % 4 = 1` and `5 ≤ n₂`, so `32/|G| = 8/(3 n₂)`;
* then `Work.BSW.Char.no_bad_arithmetic_two n₂ hge5 hmod4` (already proved, import it) rules out
  the configuration when `3 ∣ n₂`.

So the whole proof is a short assembly of the three imports: rewrite `32/|G|` as `8/(3 * n₂)`
(this needs `field_simp` plus `Nat.card_eq_fintype_card`, not just `norm_num`), turn the degree
inequality into `1 + Σ dᵢ² ≤ 12 * n₂` (needs `exact_mod_cast` from the `ℚ` form; note `hineq` is
an inequality of natural numbers, so rewriting a `ℚ` equality into it needs `Nat.cast_le`), and
apply `no_bad_arithmetic_two`.

Do NOT import `Submission.Work.BSW.Cases.three_not_dvd_sylow_two` (a sibling copy of this
statement whose proof attempt does not compile). -/
theorem three_not_dvd_sylow_two {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (t s : G) (K : Subgroup G)
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    ¬ (3 ∣ Nat.card (Sylow 2 G)) := by
  classical
  -- The Sylow `2`-structure of the `|K| = 2` case: `12 * n₂ = |G|`, `n₂ ≡ 1 (mod 4)`, `n₂ ≥ 5`.
  obtain ⟨hcardG, hmod4, hge5⟩ :=
    Work.BSW.Cases.sylow_number_and_ncard hsimple hnab t s K h hk
  have : Fintype G := Fintype.ofFinite G
  -- The character-theoretic input (Bender–Suzuki–Wall).
  obtain ⟨χ1, χ2, χ3, d1, d2, d3, e1, e2, e3, hd1, hd2, hd3, he1, he2, he3,
      hχ1t, hχ2t, hχ3t, hχ1d, hχ2d, hχ3d, hrat, hineq⟩ :=
    Work.BSW.Char.three_special_characters h hk hsimple hnab
  intro h3
  -- Reduce to the arithmetic contract, at `n = n₂`.
  refine Work.BSW.Char.no_bad_arithmetic_two (Nat.card (Sylow 2 G)) hge5 hmod4 ⟨h3, ?_⟩
  refine ⟨d1, d2, d3, hd1, hd2, hd3, e1, e2, e3, he1, he2, he3, ?_, ?_⟩
  · -- `32/|G| = 8/(3 n₂)`, using `|G| = 12 n₂` and `n₂ ≠ 0`.
    have hnpos : (0 : ℕ) < Nat.card (Sylow 2 G) := by omega
    have hn0 : (Nat.card (Sylow 2 G) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
    have hcardG' : (Nat.card G : ℚ) = 12 * (Nat.card (Sylow 2 G) : ℚ) := by
      rw [← hcardG]; push_cast; ring
    rw [hrat, hcardG']
    field_simp
    ring
  · -- `1 + Σ dᵢ² ≤ |G| = 12 n₂`.
    rw [← hcardG] at hineq
    exact hineq

end Work.BSW.Cases.K2Count
