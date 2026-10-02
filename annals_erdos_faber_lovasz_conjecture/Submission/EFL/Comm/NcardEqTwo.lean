import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.Ring
import Mathlib.Order.Basic
import Submission.Commons.Combinatorics.Hypergraph.eq_univ_pairs_of_degree

/-!
# Port of `Commons.Combinatorics.Hypergraph.ncard_eq_two_of_mem_ncard_pred`

Used by §12 Step 1 to turn the `¬ IsFull` bound on
`VeqNat 𝓗 (n-1) = {v : d_G(v) = n-1}` into the bound on
`V^{(n-1)}(𝓗) = {v : d_𝓗(v) = n-1}` needed by `(eqn:rs)` in the Type A₁ case.
-/

namespace Commons.Combinatorics.Hypergraph

theorem ncard_eq_two_of_mem_ncard_pred {n : ℕ} {𝓗 : Set (Set (Fin n))} {v : Fin n}
    (hlin : 𝓗.Pairwise fun e₁ e₂ => (e₁ ∩ e₂).Subsingleton)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ e.ncard)
    (hv : ({e ∈ 𝓗 | v ∈ e} : Set (Set (Fin n))).ncard = n - 1)
    {e₀ : Set (Fin n)} (he₀ : e₀ ∈ 𝓗) (hv₀ : v ∈ e₀) : e₀.ncard = 2 := by
  -- Invoke the companion lemma, rewriting `Fintype.card (Fin n)` to `n`.
  have hdeg : ({e ∈ 𝓗 | v ∈ e} : Set (Set (Fin n))).ncard = Fintype.card (Fin n) - 1 := by
    rw [Fintype.card_fin]; exact hv
  have hpairs : ∀ w : Fin n, w ≠ v → ({v, w} : Set (Fin n)) ∈ 𝓗 :=
    eq_univ_pairs_of_degree (Fin n) 𝓗 hlin hbig hdeg
  -- `e₀` has at least two elements, and contains `v`, so it contains some `w ≠ v`.
  have h1 : 1 < e₀.ncard := by have := hbig e₀ he₀; omega
  obtain ⟨w, hw₀, hwv⟩ := Set.exists_ne_of_one_lt_ncard h1 v
  have hpair : ({v, w} : Set (Fin n)) ∈ 𝓗 := hpairs w hwv
  -- Linearity forces `e₀ = {v, w}`.
  have heq : e₀ = {v, w} := by
    by_contra hne
    have hsub : (e₀ ∩ ({v, w} : Set (Fin n))).Subsingleton := hlin he₀ hpair hne
    have hv1 : v ∈ e₀ ∩ ({v, w} : Set (Fin n)) := ⟨hv₀, by simp⟩
    have hw1 : w ∈ e₀ ∩ ({v, w} : Set (Fin n)) := ⟨hw₀, by simp⟩
    exact hwv (hsub hv1 hw1).symm
  rw [heq]
  exact Set.ncard_pair (Ne.symm hwv)


end Commons.Combinatorics.Hypergraph
