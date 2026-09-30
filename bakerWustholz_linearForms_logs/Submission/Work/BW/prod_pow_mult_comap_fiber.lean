import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

open scoped Classical

/-- **Infinite places.** The infinite places of `K` lying above a place `w` of `F` (`ℚ ⊆ F ⊆ K`),
weighted by their multiplicity, multiply up to the `[K : F]`-th power of `A ^ mult w`.

Suggested route: `∏ᶠ v ∈ {v | v.comap (algebraMap F K) = w}, A ^ v.mult` is `A ^ (∑ v, v.mult)`
by `finprod_mem_eq_prod_filter` + `Finset.prod_pow_eq_pow_sum` (use `open Classical`/`classical`),
the fibre is finite since `InfinitePlace K` is a `Fintype`, and the exponent identity
`∑_{v above w} v.mult = Module.finrank F K * w.mult` is Mathlib-adjacent: combine
`InfinitePlace.card_filter_mk_eq` (`#{φ | mk φ = v} = v.mult`) and `NumberField.Embeddings.card`
with `Fintype.card` of the restriction map, or use
`InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank` together with
`InfinitePlace.isUnramified_iff`/`not_isUnramified_iff` (`mult v = 1` iff `IsReal`).
NOTE: this statement deliberately has NO dependency on `Submission.Work.BW.logHeight_intermediate`
(do not import that module: its file imports this one's sibling). -/
theorem prod_pow_mult_comap_fiber {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) (w : InfinitePlace F) (A : ℝ) :
    ∏ᶠ v ∈ {v : InfinitePlace K | v.comap (algebraMap F K) = w}, A ^ v.mult =
      (A ^ w.mult) ^ Module.finrank F K := by
  classical
  -- The fibre of `comap` at `w` is exactly the set of places of `K` lying above `w`.
  have hS : {v : InfinitePlace K | v.comap (algebraMap F K) = w} =
      (↑(Finset.univ.filter (fun v : InfinitePlace K => v.comap (algebraMap F K) = w)) :
        Set (InfinitePlace K)) := by
    ext v; simp
  -- Rewrite the fibre as a finite sum over `Finset.univ` and use `∏ a ^ nᵢ = a ^ ∑ nᵢ`.
  have hfilter : (InfinitePlace.placesOver K w).toFinset =
      Finset.univ.filter (fun v : InfinitePlace K => v.comap (algebraMap F K) = w) := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv
      have hvLO : v.LiesOver w := hv
      exact InfinitePlace.LiesOver.comap_eq v w
    · intro h
      refine ⟨?_⟩
      have h2 : (v.comap (algebraMap F K)).val = w.val := congrArg Subtype.val h
      rw [← h2]; ext x; rfl
  -- The exponent identity: summing the multiplicities of the places above `w` gives
  -- `mult w · [K : F]`.
  have key : (∑ v ∈ (InfinitePlace.placesOver K w).toFinset, v.mult) =
      w.mult * Module.finrank F K := by
    rw [← InfinitePlace.sum_inertiaDeg_eq_finrank F K w, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hvLO : v.LiesOver w := (Set.mem_toFinset.mp hv : v ∈ InfinitePlace.placesOver K w)
    rw [InfinitePlace.inertiaDeg_eq_finrank, InfinitePlace.mult_mul_finrank]
  rw [hS, finprod_mem_coe_finset, Finset.prod_pow_eq_pow_sum, ← pow_mul, ← hfilter, key]

end Work.BW
