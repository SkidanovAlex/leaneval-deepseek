import Submission.EFL.Comm.LovaszGfFactorNat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# Lovász's `(g,f)`-factor theorem

For a finite simple graph `G` and integer-valued functions `g ≤ f` (with `g < f` pointwise,
`0 ≤ g` and `f ≤ d_G`), there is a subgraph `R ≤ G` with `g(x) ≤ d_R(x) ≤ f(x)` for every vertex
`x`, provided that for all disjoint `S, T`,

`e_G(S,T) ≤ ∑_{s ∈ S} f(s) + ∑_{t ∈ T} (d_G(t) - g(t))`.

This is exactly the form of the theorem stated (and attributed to Lovász) in

* D. Y. Kang, T. Kelly, D. Kühn, A. Methuku, D. Osthus, *A proof of the Erdős–Faber–Lovász
  conjecture*, Annals of Math. **198** (2023), Theorem 7.3 (special case of Lovász's `(g,f)`-factor
  theorem; see also Schrijver, *Combinatorial Optimization*, Corollary 35.1b).

The proof here reduces the `ℤ`-valued statement to the `ℕ`-valued statement
`Commons.Combinatorics.Factor.lovasz_gf_factor_nat` (which is proved in the shared commons on top
of Tutte's `f`-factor theorem `Commons.Combinatorics.Factor.tutte_f_factor`).
-/

open scoped BigOperators

namespace Commons.Combinatorics.LovaszGFactor

/-- **Lovász's `(g,f)`-factor theorem** (Kang–Kelly–Kühn–Methuku–Osthus, Theorem 7.3 / Schrijver,
Corollary 35.1b), in the `ℤ`-valued form used in the proof of the Erdős–Faber–Lovász conjecture. -/
theorem lovasz_gf_factor {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f g : V → ℤ)
    (hg0 : ∀ x, 0 ≤ g x) (hgf : ∀ x, g x < f x)
    (hf : ∀ x, f x ≤ (Nat.card {y : V // G.Adj x y} : ℤ))
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℤ) ≤
        (∑ s ∈ S, f s) + ∑ t ∈ T, ((Nat.card {y : V // G.Adj t y} : ℤ) - g t)) :
    ∃ R : G.Subgraph, ∀ x, g x ≤ (Nat.card {y : V // R.Adj x y} : ℤ) ∧
      (Nat.card {y : V // R.Adj x y} : ℤ) ≤ f x := by
  classical
  have hf0 : ∀ x, 0 ≤ f x := fun x => le_trans (hg0 x) (le_of_lt (hgf x))
  set fN : V → ℕ := fun v => (f v).toNat with hfN
  set gN : V → ℕ := fun v => (g v).toNat with hgN
  have hfc : ∀ v, ((fN v : ℕ) : ℤ) = f v := fun v => Int.toNat_of_nonneg (hf0 v)
  have hgc : ∀ v, ((gN v : ℕ) : ℤ) = g v := fun v => Int.toNat_of_nonneg (hg0 v)
  have hgf' : ∀ v, gN v < fN v := by
    intro v
    have h1 : (gN v : ℤ) < (fN v : ℤ) := by rw [hgc v, hfc v]; exact hgf v
    exact_mod_cast h1
  have hf' : ∀ v, fN v ≤ Nat.card {w : V // G.Adj v w} := by
    intro v
    have h1 : (fN v : ℤ) ≤ (Nat.card {w : V // G.Adj v w} : ℤ) := by
      rw [hfc v]; exact hf v
    exact_mod_cast h1
  have hlov' : ∀ S T : Finset V, Disjoint S T →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℤ) ≤
        (S.sum (fun s => (fN s : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (gN t : ℤ))) := by
    intro S T hST
    have h := hlov S T hST
    have h1 : (S.sum (fun s => (fN s : ℤ))) = ∑ s ∈ S, f s := by
      apply Finset.sum_congr rfl; intro s _; exact hfc s
    have h2 : T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (gN t : ℤ)))
        = ∑ t ∈ T, ((Nat.card {y : V // G.Adj t y} : ℤ) - g t) := by
      apply Finset.sum_congr rfl; intro t _; rw [hgc t]
    rw [h1, h2]; exact h
  obtain ⟨R, hR⟩ :=
    Commons.Combinatorics.Factor.lovasz_gf_factor_nat G fN gN hgf' hf' hlov'
  exact ⟨R, fun x => ⟨by rw [← hgc x]; exact (hR x).1, by rw [← hfc x]; exact (hR x).2⟩⟩

end Commons.Combinatorics.LovaszGFactor
