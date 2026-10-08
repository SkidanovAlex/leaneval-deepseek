/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# The character-theoretic identity `∑_χ χ(t)² = |C_G(t)|` at an involution `t`

Bender's §2 counting (`Submission/Work/BSW/NOTES_BSW_order.md`) needs the value of the
involution-product sum `∑_χ χ(t)²` when the centralizer of the involution `t` has order `4`.
The identity proved here is the diagonal case of the second (column) orthogonality relation
together with the **reality of character values at an involution**:

* for an involution `t` and an irreducible character `χ`, `χ(t) = star (χ(t))`, because
  `t = t⁻¹` and irreducible character values satisfy `χ(g⁻¹) = star (χ(g))`
  (`OddOrder.RepresentationTheory.irreducibleCharacter_apply_inv`);
* hence `∑_χ χ(t)² = ∑_χ χ(t) · star (χ(t)) = |C_G(t)|`
  (`OddOrder.RepresentationTheory.column_orthogonality_diagonal`).

The hypotheses `hconj` (all involutions are conjugate to `t`) and `|C_G(t)| = 4` are those of the
BSW setting; only the latter enters the calculation (the identity holds for every involution of
every finite group, so `hconj` is not needed).
-/
import Mathlib
import Submission.Work.BSW.Char.Setup
import Submission.Work.BSW.Char.invPairCount_eq_sum_characters
import Submission.Work.BSW.Vocab

namespace Work.BSW.Char

open OddOrder.RepresentationTheory

/-- At an involution `t`, the value of an irreducible character is real: `χ(t) = star (χ(t))`.

Indeed `t⁻¹ = t` and `χ(g⁻¹) = star (χ(g))` for every `g` (complex conjugation of the eigenvalues
of `ρ(g)`, whose product with those of `ρ(g)⁻¹` is `1`). -/
theorem chi_apply_eq_star_of_orderOf_eq_two {G : Type} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (χ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) t = star ((χ : ClassFunction G ℂ) t) := by
  have ht2 : t * t = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h := irreducibleCharacter_apply_inv χ t
  rwa [htinv] at h

/-- **Bender's value of `∑_χ χ(t)²` at an involution with `|C_G(t)| = 4`.**

If `t` is an involution whose centralizer has order `4` — as in the BSW setting, where
`C_G(t) = K⟨s⟩` with `|K| = 2` — then `∑_χ χ(t)² = 4`.  The sum runs over the irreducible
complex characters of `G`.

This is the diagonal second-orthogonality identity `∑_χ χ(t) · star (χ(t)) = |C_G(t)|`
combined with reality of `χ(t)` at the involution `t`. -/
theorem sum_chi_t_sq {G : Type} [Group G] [Fintype G] {t : G} (ht : orderOf t = 2)
    (hconj : ∀ x : G, orderOf x = 2 → IsConj x t)
    (hcard : Nat.card (Subgroup.centralizer ({t} : Set G)) = 4) :
    ∑ χ : OddOrder.RepresentationTheory.IrreducibleCharacter G,
      ((χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) t) ^ 2 = 4 := by
  -- `χ(t)` is real, so the squared character value is `χ(t) · star (χ(t))`.
  have hsum :
      ∑ χ : IrreducibleCharacter G, ((χ : ClassFunction G ℂ) t) ^ 2
        = ∑ χ : IrreducibleCharacter G,
            (χ : ClassFunction G ℂ) t * star ((χ : ClassFunction G ℂ) t) := by
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [← chi_apply_eq_star_of_orderOf_eq_two ht χ]
    ring
  rw [hsum, column_orthogonality_diagonal t, hcard]
  norm_num

end Work.BSW.Char
