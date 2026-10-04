import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.commutator_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_pd_le`: the `H^{k-1}` energy of `∂ᵣf` is bounded by the `L²` energies of the
order-`k` jets of `f`

The `Hᵏ` energy of the STE development is

  `ENormSq k f = Σ_{β : Fin k → ι} ∫_{unitCube} ‖∂^β f‖²`

(`Submission/Work/Diff/STE/Torus.lean`), the sum of the `L²` norms squared of *all* iterated
partial derivatives of order `k` indexed by tuples `β : Fin k → ι`.

The lemma proved here is a purely combinatorial regrouping of that sum:

  `ENormSq (k-1) (∂ᵣ f) ≤ (card ι)^{k-1} · KA`  whenever `ENormSq 0 (∂^β f) ≤ KA`
  for every `β : Fin k → ι` and `1 ≤ k`.

The point is that the `k`-fold derivative `∂^{l}∂ᵣ` (`l : Fin (k-1) → ι`) is *literally* one of
the `k`-fold derivatives `∂^β` with `β = Fin.snoc l r` — no commutation (Clairaut) and hence no
smoothness hypothesis is needed, because `pdList` is a `List.foldr` and appending the direction
`r` at the *end* of the list of directions is exactly `foldr`-composition
(`List.foldr_append`).  Consequently `ENormSq (k-1) (∂ᵣ f)` is the sub-sum of
`Σ_{β : Fin (k-1) → ι} ENormSq 0 (∂^{snoc l r} f)` over the `(card ι)^{k-1}` tuples `Fin.snoc l r`,
and each of those summands is `≤ KA` by hypothesis.

The auxiliary lemmas (kept local to this file, to avoid clashing with the sibling copies in
`Submission/Work/Diff/STE/B3/tmA_clause9.lean`) are:

* `ENormSq_zero_eq_loc` : `ENormSq 0 g = ∫_{unitCube} ‖g‖²`;
* `ofFn_snoc_append`   : `List.ofFn (Fin.snoc l r) = List.ofFn l ++ [r]`;
* `pdVec_pd_snoc`      : `pdVec m l (∂ᵣ g) = pdVec (m+1) (Fin.snoc l r) g` (definitional, no
  smoothness).
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.Lead.GalTame

/-- `ENormSq 0` is the `L²` norm squared. -/
private lemma ENormSq_zero_eq_loc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 g = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2 := by
  rw [Work.Diff.STE.ENormSq, Finset.univ_unique, Finset.sum_singleton]
  congr 1

/-- Appending the last entry of a `Fin`-tuple corresponds to concatenating the associated lists. -/
private lemma ofFn_snoc_append {α : Type*} {n : ℕ} (l : Fin n → α) (r : α) :
    List.ofFn (Fin.snoc l r) = List.ofFn l ++ [r] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

/-- **Peeling the last partial derivative out of a `pdVec`.**  This is a definitional identity:
`pdVec` is a `List.foldr` of `pd` over the list of directions, and appending the direction `r` at
the end of that list composes the corresponding `pdList` on the right.  No smoothness is needed. -/
private lemma pdVec_pd_snoc {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (l : Fin m → ι) (r : ι)
    (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec m l (Work.Diff.STE.pd r f)
      = Work.Diff.STE.pdVec (m + 1) (Fin.snoc l r) f := by
  simp only [Work.Diff.STE.pdVec]
  rw [ofFn_snoc_append]
  rw [Work.Diff.STE.cm_pdList_append]
  rfl

/-- **The `H^{k-1}` energy of a single partial derivative is controlled by the `L²` energies of the
order-`k` jets.**  Since `∂^{l}∂ᵣ f = ∂^{Fin.snoc l r} f` definitionally (`pdVec_pd_snoc`), the
left hand side is the sum of `(card ι)^{k-1}` of the hypotheses' terms, of which
`k - 1 = m` derivatives are taken by `l` and the last by `r`. -/
theorem ENormSq_pd_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (hk : 1 ≤ k)
    (f : (ι → ℝ) → ℂ) (r : ι) (KA : ℝ) (hKA : 0 ≤ KA)
    (h : ∀ (β : Fin k → ι), Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k β f) ≤ KA) :
    Work.Diff.STE.ENormSq (k - 1) (Work.Diff.STE.pd r f)
      ≤ (Fintype.card ι : ℝ) ^ (k - 1) * KA := by
  cases k with
  | zero => exact absurd hk (by omega)
  | succ m =>
    have key : Work.Diff.STE.ENormSq m (Work.Diff.STE.pd r f)
        ≤ (Fintype.card ι : ℝ) ^ m * KA := by
      have hpt : ∀ l : Fin m → ι,
          (∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec m l (Work.Diff.STE.pd r f) x‖ ^ 2)
            = Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (m + 1) (Fin.snoc l r) f) := by
        intro l
        rw [pdVec_pd_snoc m l r f, ← ENormSq_zero_eq_loc]
      have hsum : Work.Diff.STE.ENormSq m (Work.Diff.STE.pd r f)
          = ∑ l : Fin m → ι,
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (m + 1) (Fin.snoc l r) f) := by
        show (∑ l : Fin m → ι,
              ∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec m l (Work.Diff.STE.pd r f) x‖ ^ 2) = _
        exact Finset.sum_congr rfl (fun l _ => hpt l)
      rw [hsum]
      calc ∑ l : Fin m → ι,
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (m + 1) (Fin.snoc l r) f)
          ≤ ∑ _l : Fin m → ι, KA := Finset.sum_le_sum (fun l _ => h (Fin.snoc l r))
        _ = (Fintype.card ι : ℝ) ^ m * KA := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_pow]
    exact key

end Work.Diff.STE.Lead.GalTame
