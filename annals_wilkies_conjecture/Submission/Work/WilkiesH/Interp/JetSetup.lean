import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# Jet fibers: the vocabulary of the Siegel–Wilkie interpolation step

This file fixes the combinatorial vocabulary used by
`Work.WilkiesH.Interp.siegel_poly_exists` (and by the lemmas delegated for it).

For a chart `ψ : (Fin μ → ℝ) → (Fin (μ+1) → ℝ)` and a point `t₀`, the polynomial `P` produced
by Siegel's lemma is required to have small *jets* of order `≤ b` at `t₀`.  The jet of order `n`
of a function `F` at `t₀` is a symmetric `n`-multilinear form; to write it down using only the
finite data available we evaluate it on `n`-tuples of coordinate basis vectors.  The tuples are
indexed by their *multiplicity vector* `α : Fin μ → ℕ`, `∑ i, α i = n`:

* `multFun g i` — the multiplicity of the value `i` in the tuple `g`;
* `multVecE hn g` — the multiplicity vector of `g`, as an element of `ExpVec μ b` (for `n ≤ b`);
* `jetFiberSum n α F t₀` — the sum of `(D^n F t₀) (e_{g 1}, …, e_{g n})` over the tuples `g` with
  multiplicity vector `α`.  These are the rows of the "jet matrix" (the linear functionals of the
  polynomial `P` that Siegel's lemma makes small);
* `jetFiberCard μ n α` — the number of such tuples, i.e. the multinomial coefficient
  `n! / ∏ i, (α i)!` (`0` when `∑ i, α i ≠ n`).
-/

set_option autoImplicit false
noncomputable section

open Classical
open Finset

namespace Work.WilkiesH.Interp

open Work.WilkiesH

/-- The multiplicity of the value `i` among the entries of the tuple `g : Fin n → Fin μ`. -/
def multFun {μ n : ℕ} (g : Fin n → Fin μ) (i : Fin μ) : ℕ :=
  (Finset.univ.filter (fun l : Fin n => g l = i)).card

lemma multFun_eq_card {μ n : ℕ} (g : Fin n → Fin μ) (i : Fin μ) :
    multFun g i = Fintype.card {l : Fin n // g l = i} := by
  rw [Fintype.card_subtype]
  rfl

lemma sum_multFun {μ n : ℕ} (g : Fin n → Fin μ) : ∑ i, multFun g i = n := by
  calc ∑ i, multFun g i
      = ∑ i, ∑ l ∈ (Finset.univ : Finset (Fin n)) with g l = i, (1 : ℕ) := by
        simp [multFun]
    _ = ∑ l ∈ (Finset.univ : Finset (Fin n)), (1 : ℕ) := Finset.sum_fiberwise _ _ _
    _ = n := by simp

lemma multFun_le {μ n : ℕ} (g : Fin n → Fin μ) (i : Fin μ) : multFun g i ≤ n := by
  simpa [multFun] using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun l => g l = i)

/-- The multiplicity vector of a tuple, as an exponent vector of total degree `≤ b`,
when the length `n` of the tuple is at most `b`. -/
def multVecE {μ n b : ℕ} (hn : n ≤ b) (g : Fin n → Fin μ) : ExpVec μ b :=
  let f : Fin μ → Fin (b + 1) := fun i => ⟨multFun g i, by have := multFun_le g i; omega⟩
  ⟨f, by
     have hsum : ∑ i, multFun g i = n := sum_multFun g
     have hcast : ∑ i, ((f i : Fin (b + 1)) : ℕ) = ∑ i, multFun g i := rfl
     rw [hcast, hsum]
     exact hn⟩

lemma multVecE_toFun {μ n b : ℕ} (hn : n ≤ b) (g : Fin n → Fin μ) (i : Fin μ) :
    (multVecE hn g).toFun i = multFun g i := rfl

/-- The sum of the `n`-th jet of `F` at `t₀` over the tuples whose multiplicity vector is `α`:
`∑_{g : mult(g) = α} (D^n F t₀) (e_{g 1}, …, e_{g n})`. -/
def jetFiberSum {μ : ℕ} (n : ℕ) (α : Fin μ → ℕ) (F : (Fin μ → ℝ) → ℝ)
    (t₀ : Fin μ → ℝ) : ℝ :=
  ∑ g : {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i},
    (iteratedFDeriv ℝ n F t₀) (fun k => Pi.single (g.1 k) 1)

/-- The number of tuples `Fin n → Fin μ` with multiplicity vector `α`. -/
def jetFiberCard (μ n : ℕ) (α : Fin μ → ℕ) : ℕ :=
  Fintype.card {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i}

lemma jetFiberCard_eq {μ n : ℕ} (α : Fin μ → ℕ) :
    jetFiberCard μ n α = Fintype.card {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i} :=
  rfl

/-- The fiber sum does not depend on the way the arity is written. -/
lemma jetFiberSum_congr_arity {μ : ℕ} {n n' : ℕ} (h : n = n') (α : Fin μ → ℕ)
    (F : (Fin μ → ℝ) → ℝ) (t₀ : Fin μ → ℝ) :
    jetFiberSum n α F t₀ = jetFiberSum n' α F t₀ := by
  subst h
  rfl

/-- The fiber cardinality does not depend on the way the arity is written. -/
lemma jetFiberCard_congr_arity {μ : ℕ} {n n' : ℕ} (h : n = n') (α : Fin μ → ℕ) :
    jetFiberCard μ n α = jetFiberCard μ n' α := by
  subst h
  rfl

/-- If two functions agree as functions, so do their fiber sums. -/
lemma jetFiberSum_congr_fun {μ : ℕ} {n : ℕ} {α : Fin μ → ℕ} {F G : (Fin μ → ℝ) → ℝ}
    (h : F = G) (t₀ : Fin μ → ℝ) : jetFiberSum n α F t₀ = jetFiberSum n α G t₀ := by
  rw [h]

end Work.WilkiesH.Interp
