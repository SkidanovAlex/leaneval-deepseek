import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs

/-!
# Evaluation of a finitely supported family at `(w, z₁, …, z_d)`

For a finitely supported family `c` of multi-indices on `Fin (d+1)` with complex coefficients,
evaluating the associated polynomial at the point `consPt w z = (w, z₁, …, z_d)` may be done
"slice by slice": collecting the terms according to the exponent `t` of the first variable `w`,
one gets

`pevalF c (consPt w z) = ∑ t ∈ suppFst c, w ^ t * pevalF (sliceF c t) z`,

where `sliceF c t` is the family of coefficients of `w ^ t` (its coefficients are the `c m` with
`m 0 = t`, reindexed along the tail of `m`).

The proof is a reindexing of the sum over the support of `c` along the bijection
`m ↦ (m 0, tailIdx m)` between `c.support` and the sigma-type
`∐ t ∈ suppFst c, (sliceF c t).support`.
-/

namespace Work.Holonomy3

open scoped BigOperators

theorem pevalF_consPt {d : ℕ} (c : (Fin (d+1) →₀ ℕ) →₀ ℂ) (w : ℂ) (z : Fin d → ℂ) :
    pevalF c (consPt w z) = ∑ t ∈ suppFst c, w ^ t * pevalF (sliceF c t) z := by
  set F : (Fin (d+1) →₀ ℕ) → ℂ :=
    fun m => c m * (w ^ (m 0) * ∏ i : Fin d, z i ^ (tailIdx m i)) with hF
  set G : ℕ → (Fin d →₀ ℕ) → ℂ :=
    fun t m' => sliceF c t m' * (w ^ t * ∏ i : Fin d, z i ^ (m' i)) with hG
  -- Unfold `pevalF` at `(w, z)` and split off the first factor of the product.
  have h1 : pevalF c (consPt w z) = ∑ m ∈ c.support, F m := by
    rw [pevalF]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [hF, consPt, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, tailIdx_apply]
  -- Unfold `pevalF` on each slice and pull `w ^ t` inside.
  have h2 : (∑ t ∈ suppFst c, w ^ t * pevalF (sliceF c t) z)
      = ∑ t ∈ suppFst c, ∑ m' ∈ (sliceF c t).support, G t m' := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [pevalF, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    simp only [hG]
    ring
  -- Reindex `c.support` along the bijection `m ↦ (m 0, tailIdx m)`.
  have h3 : (∑ m ∈ c.support, F m)
      = ∑ p ∈ (suppFst c).sigma (fun t => (sliceF c t).support), G p.1 p.2 := by
    refine Finset.sum_bij (fun m _ => (⟨m 0, tailIdx m⟩ : Sigma fun _ : ℕ => Fin d →₀ ℕ)) ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_sigma]
      exact ⟨mem_suppFst.mpr ⟨m, hm, rfl⟩, by simpa [Finsupp.mem_support_iff] using hm⟩
    · intro a _ b _ hab
      have h0 : a 0 = b 0 := congrArg Sigma.fst hab
      have ht : tailIdx a = tailIdx b := congrArg Sigma.snd hab
      rw [← consIdx_tailIdx a, h0, ht, consIdx_tailIdx b]
    · rintro ⟨t, m'⟩ hp
      rw [Finset.mem_sigma] at hp
      obtain ⟨ht, hm'⟩ := hp
      refine ⟨consIdx t m', ?_, ?_⟩
      · simpa [Finsupp.mem_support_iff] using hm'
      · simp [consIdx_zero, tailIdx_consIdx]
    · intro a _
      simp only [hF, hG, sliceF_apply, consIdx_tailIdx]
  calc pevalF c (consPt w z)
      = ∑ m ∈ c.support, F m := h1
    _ = ∑ p ∈ (suppFst c).sigma (fun t => (sliceF c t).support), G p.1 p.2 := h3
    _ = ∑ t ∈ suppFst c, ∑ m' ∈ (sliceF c t).support, G t m' :=
        (Finset.sum_sigma' (suppFst c) (fun t => (sliceF c t).support) (fun t m' => G t m')).symm
    _ = ∑ t ∈ suppFst c, w ^ t * pevalF (sliceF c t) z := h2.symm

end Work.Holonomy3
