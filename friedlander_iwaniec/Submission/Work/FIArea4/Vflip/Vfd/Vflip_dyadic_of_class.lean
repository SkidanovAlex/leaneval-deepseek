import Mathlib
import Submission.Work.FIArea4.Vflip.VflipAux
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface

/-!
# From the single-residue-class estimate to the unrestricted dyadic estimate

FI §12 ("by splitting into four residue classes we can assume without loss of generality that `r`
is fixed modulo eight") proves the large-moduli estimate only for arrays supported on a single
residue class `r ≡ i (mod 8)`, because that is the hypothesis under which the reciprocity flip
`(r₁|d')(r₂|d')` applies.  This file records the (constant-only) reduction that removes the class
hypothesis:

if the estimate `Vvar R S D α ≤ C · p14T12 D R S ε · p14Ener R S α` holds for every array whose
nonzero entries all have `r ≡ i (mod 8)` for the *same* `i`, then the same estimate holds — with
some positive constant `C'` — for an *arbitrary* array, with the same hypotheses on `D,R,S`.

The proof is the mod-8 splitting `Work.FIArea4.Vflip.Vvar_mod8`:

`Vvar R S D α ≤ 8 · Σ_{i<8} Vvar R S D (clsMod8 i α)`,

each `clsMod8 i α` being supported in a single class mod 8, together with the exact additivity of
the energies `Σ_i p14Ener R S (clsMod8 i α) = p14Ener R S α` and the nonnegativity of
`p14T12 · p14Ener`.  The constant is `C' = 8|C| + 1`.
-/

namespace Work.FIArea4.Vflip.Vfd

open scoped BigOperators

theorem Vflip_dyadic_of_class (ε : ℝ) (C : ℝ)
    (hC : ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      (∀ r s, α r s ≠ 0 → ∀ r' s', α r' s' ≠ 0 → r % 8 = r' % 8) →
      Work.FIPlan.Vvar R S D α ≤ C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D ≤ R * S → R * S < D * D →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      Work.FIPlan.Vvar R S D α ≤ C' * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
  classical
  refine ⟨8 * |C| + 1, by positivity, ?_⟩
  intro D R S α hD hR hS hRS hRSD hcop hbox
  -- each truncation `clsMod8 i α` is supported in the single class `r % 8 = i`, so `hC` applies
  have hstep : ∀ i : Fin 8,
      Work.FIPlan.Vvar R S D (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α)
        ≤ C * Work.FIArea4.p14T12 D R S ε
            * Work.FIArea4.p14Ener R S (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α) := by
    intro i
    refine hC D R S (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α) hD hR hS hRS hRSD ?_ ?_ ?_
    · intro r s h
      exact hcop r s (fun h0 => h (by simp [Work.FIArea4.Vflip.clsMod8, h0]))
    · intro r s h
      exact hbox r s (fun h0 => h (by simp [Work.FIArea4.Vflip.clsMod8, h0]))
    · intro r s h r' s' h'
      exact (Work.FIArea4.Vflip.clsMod8_support h).trans
        (Work.FIArea4.Vflip.clsMod8_support h').symm
  -- the energies add up over the eight classes
  have hsum_le : ∑ i : Fin 8, Work.FIPlan.Vvar R S D (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α)
      ≤ C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
    calc ∑ i : Fin 8, Work.FIPlan.Vvar R S D (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α)
        ≤ ∑ i : Fin 8, C * Work.FIArea4.p14T12 D R S ε
            * Work.FIArea4.p14Ener R S (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α) :=
          Finset.sum_le_sum (fun i _ => hstep i)
      _ = C * Work.FIArea4.p14T12 D R S ε
            * ∑ i : Fin 8, Work.FIArea4.p14Ener R S (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α) := by
          rw [Finset.mul_sum]
      _ = C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
          rw [Work.FIArea4.Vflip.sum_p14Ener_clsMod8]
  have hT : 0 ≤ Work.FIArea4.p14T12 D R S ε := by
    rw [Work.FIArea4.p14T12]; positivity
  have hE : 0 ≤ Work.FIArea4.p14Ener R S α := by
    rw [Work.FIArea4.p14Ener]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)))
  calc Work.FIPlan.Vvar R S D α
      ≤ 8 * ∑ i : Fin 8, Work.FIPlan.Vvar R S D (Work.FIArea4.Vflip.clsMod8 (i : ℕ) α) :=
        Work.FIArea4.Vflip.Vvar_mod8 R S D α
    _ ≤ 8 * (C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α) :=
        mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    _ ≤ (8 * |C| + 1) * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
        have h1 : 8 * C ≤ 8 * |C| + 1 := by nlinarith [le_abs_self C]
        have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hT) hE
        linarith [h2]

end Work.FIArea4.Vflip.Vfd
