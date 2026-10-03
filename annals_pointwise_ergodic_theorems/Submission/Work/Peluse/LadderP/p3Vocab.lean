import Mathlib
import Submission.Work.Peluse.Holds.LadderP
import Submission.Work.Peluse.Ulower.gap_defs

/-! # P3: the vocabulary of the induction step

The objects appearing in every brick of the induction step of Peluse's Lemma 5.1
(`Work.Peluse.LadderP.lemma51P_succ`), named once so that the statements of the later bricks stay
readable:

* `p3good t M₁ b η a` — the frozen statement's *good*-`a` predicate (the negation of its exceptional
  set: all pairwise `gcd(a+b_i, a+b_k) ≤ 1/η` for distinct `i,k`, and `ηM₁ ≤ |a+b_i|` for all `i`);
* `p3lastPair t c M₂ b a` — the last *pair* of direction sets
  `c(a+b_{t-1})[M₂], c(a+b_t)[M₂]` (the pair handed to the two-dimensional inverse theorem);
* `p3Sh t c M₂ b a` — the index type of the iterated peel at `a`: a tuple of pairs of shifts, one
  pair for each of the first `t-1` direction sets;
* `p3raw sh` — the underlying tuple of integer shift pairs of an element of `p3Sh`;
* `p3comp t f sh` — the *translated* iterated difference `x ↦ Δ'_{sh}f (x - Σ_j (sh j).1)`, which is
  supported in `symIcc N` when `f` is (see `Work.Peluse.LadderP.iterDelta_shift_support`).

These are definitionally the expressions written out in `Work.Peluse.LadderP.peel_avg` /
`Work.Peluse.LadderP.peel_mass`, so the bricks there apply directly. -/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.LadderP

open Work.Peluse

noncomputable section

/-- The frozen statement's good-`a` predicate at level `t`. -/
def p3good (t : ℕ) (M₁ : ℕ) (b : Fin t → ℤ) (η : ℝ) (a : ℕ) : Prop :=
  (∀ i k : Fin t, i ≠ k →
      ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b k) : ℕ) : ℝ) ≤ 1 / η) ∧
    ∀ i : Fin t, η * (M₁ : ℝ) ≤ ((|((a : ℤ) + b i)| : ℤ) : ℝ)

noncomputable instance instDecidableP3good (t M₁ : ℕ) (b : Fin t → ℤ) (η : ℝ) :
    DecidablePred (p3good t M₁ b η) := fun _ => Classical.propDecidable _

/-- The last pair of direction sets `c(a+b_{t-1})[M₂]`, `c(a+b_t)[M₂]`. -/
abbrev p3lastPair (t : ℕ) (ht : 2 ≤ t) (c : ℤ) (M₂ : ℕ) (b : Fin (t + 1) → ℤ) (a : ℕ) :
    Fin 2 → Finset ℤ :=
  fun i => arithIcc (c * ((a : ℤ) + b (Fin.cast (by omega) (Fin.natAdd (t - 1) i)))) M₂

/-- The index type of the iterated peel at `a` (one pair of shifts per direction set). -/
abbrev p3Sh (t : ℕ) (c : ℤ) (M₂ : ℕ) (b : Fin (t + 1) → ℤ) (a : ℕ) : Type :=
  (j : Fin (t - 1)) →
    ↥(arithIcc (c * ((a : ℤ) + b (Fin.castLE (by omega : t - 1 ≤ t + 1) j))) M₂) ×
      ↥(arithIcc (c * ((a : ℤ) + b (Fin.castLE (by omega : t - 1 ≤ t + 1) j))) M₂)

/-- The underlying tuple of integer shift pairs. -/
abbrev p3raw {t : ℕ} {c : ℤ} {M₂ : ℕ} {b : Fin (t + 1) → ℤ} {a : ℕ}
    (sh : p3Sh t c M₂ b a) : Fin (t - 1) → ℤ × ℤ :=
  fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))

/-- The translated iterated difference `x ↦ Δ'_{sh}f (x - Σ_j (sh j).1)`. -/
abbrev p3comp (t : ℕ) (f : ℤ → ℂ) (sh : Fin (t - 1) → ℤ × ℤ) : ℤ → ℂ :=
  fun x => Ulower.iterDelta (t - 1) sh f (x - ∑ j : Fin (t - 1), (sh j).1)

@[simp] lemma p3comp_apply (t : ℕ) (f : ℤ → ℂ) (sh : Fin (t - 1) → ℤ × ℤ) (x : ℤ) :
    p3comp t f sh x = Ulower.iterDelta (t - 1) sh f (x - ∑ j : Fin (t - 1), (sh j).1) := rfl

/-- The disjointness of the two halves of `p3Sh`: an element is a tuple of pairs. -/
lemma p3raw_injective {t : ℕ} {c : ℤ} {M₂ : ℕ} {b : Fin (t + 1) → ℤ} {a : ℕ} :
    Function.Injective (p3raw (t := t) (c := c) (M₂ := M₂) (b := b) (a := a)) := by
  intro s s' h
  funext j
  have h1 : (((s j).1 : ℤ), ((s j).2 : ℤ)) = (((s' j).1 : ℤ), ((s' j).2 : ℤ)) :=
    congrFun h j
  have h2 : ((s j).1 : ℤ) = ((s' j).1 : ℤ) := congrArg Prod.fst h1
  have h3 : ((s j).2 : ℤ) = ((s' j).2 : ℤ) := congrArg Prod.snd h1
  exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)

/-- The composite of the peel, in the vocabulary above: `peel_avg`'s summand. -/
lemma p3comp_sh {t : ℕ} {c : ℤ} {M₂ : ℕ} {b : Fin (t + 1) → ℤ} {a : ℕ} {f : ℤ → ℂ}
    (sh : p3Sh t c M₂ b a) :
    p3comp t f (p3raw sh)
      = fun x : ℤ => Ulower.iterDelta (t - 1)
          (fun j : Fin (t - 1) => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f
          (x - ∑ j : Fin (t - 1), ((sh j).1 : ℤ)) := rfl

end

end Work.Peluse.LadderP
