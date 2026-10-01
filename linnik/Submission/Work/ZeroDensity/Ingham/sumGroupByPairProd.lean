import Mathlib
import Submission.Work.ZeroDensity.Ingham.fourthMomentDefs

/-!
# Grouping the quadruple index sum by the pair product

The sharp truncated approximate functional equation rewrites the fourth moment of the Dirichlet
polynomial as a quadruple sum over index pairs `(m,n)` in the box `[1,M]²`, and the kernel attached
to such a quadruple depends only on the two **products** `K = mn` and `K' = m'n'`.  This file
performs that bookkeeping: the double sum over pairs of pairs is regrouped by the fibres of the
product map `pairProd`.

The mathematical content is the elementary reindexing `sum_fiber_reindex`: if `f : α → ℕ` maps a
finite set `S` into a finite set `I`, then `∑_{p ∈ S} Φ (f p)` is the sum over `K ∈ I` of
`#(f⁻¹ K) · Φ K` (the fibres over `K ∉ f(S)` being empty and contributing `0`).  Applying it twice
produces `sum_pair_reindex`, and the target `sumGroupByPairProd` is the case `S = pairBox M`,
`f = pairProd`, `I = [1, M·M]`.
-/

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

open Finset

/-- For `M : ℕ`, the product of the entries of a pair in `pairBox M` lies in `[1, M·M]`. -/
lemma pairProd_mem_Icc (M : ℕ) {p : ℕ × ℕ} (hp : p ∈ pairBox M) :
    pairProd p ∈ Finset.Icc 1 (M * M) := by
  rw [pairBox_apply, Finset.mem_product] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [Finset.mem_Icc] at h1 h2 ⊢
  obtain ⟨ha1, ha2⟩ := h1
  obtain ⟨hb1, hb2⟩ := h2
  rw [pairProd_apply]
  refine ⟨?_, Nat.mul_le_mul ha2 hb2⟩
  have h := Nat.mul_le_mul ha1 hb1
  simpa using h

/-- **Reindexing a sum by the fibres of a map.**  If `f : α → ℕ` maps the finite set `S` into the
finite set `I`, then `∑_{p ∈ S} Φ (f p) = ∑_{K ∈ I} #(S ∩ f⁻¹{K}) · Φ K`; the fibres over points
of `I` that are not attained are empty and contribute `0`. -/
lemma sum_fiber_reindex {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (I : Finset ℕ) (hI : ∀ p ∈ S, f p ∈ I) (Φ : ℕ → ℝ) :
    (∑ p ∈ S, Φ (f p)) = ∑ K ∈ I, ((S.filter (fun p => f p = K)).card : ℝ) * Φ K := by
  have h1 : ∀ K : ℕ, ((S.filter (fun p => f p = K)).card : ℝ) * Φ K
      = ∑ p ∈ S.filter (fun p => f p = K), Φ K := by
    intro K
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun K _ => h1 K)]
  have h2 : ∀ K : ℕ, (∑ p ∈ S.filter (fun p => f p = K), Φ K)
      = ∑ p ∈ S, if f p = K then Φ K else 0 := by
    intro K
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun K _ => h2 K)]
  show (∑ p ∈ S, Φ (f p)) = ∑ K ∈ I, ∑ p ∈ S, if f p = K then Φ K else (0:ℝ)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.sum_ite_eq, if_pos (hI p hp)]

/-- **The double reindexing.**  The sum over pairs of pairs `(p, q) ∈ S × S` of a kernel
`Ψ (f p) (f q)` that depends only on the two values of `f` is the double sum over `K, K' ∈ I`
weighted by the products of the fibre cardinalities. -/
lemma sum_pair_reindex {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (I : Finset ℕ) (hI : ∀ p ∈ S, f p ∈ I) (Ψ : ℕ → ℕ → ℝ) :
    (∑ p ∈ S, ∑ q ∈ S, Ψ (f p) (f q))
      = ∑ K ∈ I, ∑ K' ∈ I,
          (((S.filter (fun p => f p = K)).card : ℝ) *
            ((S.filter (fun p => f p = K')).card : ℝ)) * Ψ K K' := by
  calc
    _ = ∑ p ∈ S, ∑ K' ∈ I, ((S.filter (fun q => f q = K')).card : ℝ) * Ψ (f p) K' := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        exact sum_fiber_reindex S f I hI (fun K' => Ψ (f p) K')
    _ = ∑ K' ∈ I, ((S.filter (fun q => f q = K')).card : ℝ) * (∑ p ∈ S, Ψ (f p) K') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun K' _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ K' ∈ I, ((S.filter (fun q => f q = K')).card : ℝ) *
          (∑ K ∈ I, ((S.filter (fun p => f p = K)).card : ℝ) * Ψ K K') := by
        refine Finset.sum_congr rfl (fun K' _ => ?_)
        rw [sum_fiber_reindex S f I hI (fun K => Ψ K K')]
    _ = ∑ K' ∈ I, ∑ K ∈ I,
          ((S.filter (fun q => f q = K')).card : ℝ) *
            (((S.filter (fun p => f p = K)).card : ℝ) * Ψ K K') := by
        refine Finset.sum_congr rfl (fun K' _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ K ∈ I, ∑ K' ∈ I,
          ((S.filter (fun q => f q = K')).card : ℝ) *
            (((S.filter (fun p => f p = K)).card : ℝ) * Ψ K K') := Finset.sum_comm
    _ = ∑ K ∈ I, ∑ K' ∈ I,
          (((S.filter (fun p => f p = K)).card : ℝ) *
            ((S.filter (fun p => f p = K')).card : ℝ)) * Ψ K K' := by
        refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun K' _ => ?_))
        ring

theorem sumGroupByPairProd (M : ℕ) (Ψ : ℕ → ℕ → ℝ) :
    (∑ p ∈ pairBox M, ∑ q ∈ pairBox M, Ψ (pairProd p) (pairProd q))
      = ∑ K ∈ Finset.Icc 1 (M * M), ∑ K' ∈ Finset.Icc 1 (M * M),
          ((pairBox M).filter (fun p => pairProd p = K)).card *
            (((pairBox M).filter (fun p => pairProd p = K')).card : ℝ) * Ψ K K' := by
  exact sum_pair_reindex (pairBox M) pairProd (Finset.Icc 1 (M * M))
    (fun p hp => pairProd_mem_Icc M hp) Ψ

end Work.ZeroDensity.Ingham
