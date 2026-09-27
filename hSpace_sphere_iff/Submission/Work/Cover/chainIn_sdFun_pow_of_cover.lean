import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Cover
import Submission.Work.Subdivision.SdPiecesPow_diam_lt
import Submission.Work.Cohomology.sdFun_iterate_single

open CategoryTheory Simplicial Opposite

namespace Work.Cover

open Submission.Cohomology

noncomputable section

/-- **Lebesgue number for a two-set open cover.**  If `X = U ∪ V` with `U`, `V` open and
`σ : Δⁿ → X` is a singular simplex, then there is `δ > 0` such that any piece `q` of `Δⁿ` whose
image under `affineSimplex q` has diameter `< δ` is mapped by `σ` entirely into `U` or entirely
into `V`. -/
lemma exists_pos_forall_small (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x, x ∈ U ∨ x ∈ V) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    ∃ δ > 0, ∀ q : Piece n n,
      Metric.diam (Set.range fun t => affineSimplex q t) < δ →
      ((∀ t, (homOfSimplex σ) (affineSimplex q t) ∈ U) ∨
       (∀ t, (homOfSimplex σ) (affineSimplex q t) ∈ V)) := by
  -- The two open sets pulled back along `σ` cover the compact simplex `Δⁿ`.
  let c : Bool → Set (TSimplex n) := fun b => match b with
    | false => (homOfSimplex σ) ⁻¹' U
    | true => (homOfSimplex σ) ⁻¹' V
  have hcopen : ∀ b, IsOpen (c b) := by
    intro b
    cases b
    · show IsOpen ((homOfSimplex σ) ⁻¹' U)
      exact hU.preimage (TopCat.toSSetObjEquivT X (op ⦋n⦌) σ).continuous
    · show IsOpen ((homOfSimplex σ) ⁻¹' V)
      exact hV.preimage (TopCat.toSSetObjEquivT X (op ⦋n⦌) σ).continuous
  have hccover : (Set.univ : Set (TSimplex n)) ⊆ ⋃ b, c b := by
    intro x _
    rcases hUV ((homOfSimplex σ) x) with h | h
    · exact Set.mem_iUnion.2 ⟨false, h⟩
    · exact Set.mem_iUnion.2 ⟨true, h⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric (s := Set.univ) (c := c)
    isCompact_univ hcopen hccover
  refine ⟨δ, hδpos, fun q hq => ?_⟩
  obtain ⟨b, hb⟩ := hδ (affineSimplex q (vert 0)) trivial
  have hbounded : Bornology.IsBounded (Set.range (fun t => affineSimplex q t)) :=
    (isCompact_range (affineSimplex q).continuous).isBounded
  have hsub : ∀ t, affineSimplex q t ∈ c b := by
    intro t
    apply hb
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_le_of_lt
      (Metric.dist_le_diam_of_mem hbounded ⟨vert 0, rfl⟩ ⟨t, rfl⟩) hq
  cases b
  · left; intro t
    have := hsub t
    show (homOfSimplex σ) (affineSimplex q t) ∈ U
    simpa [c] using this
  · right; intro t
    have := hsub t
    show (homOfSimplex σ) (affineSimplex q t) ∈ V
    simpa [c] using this

/-- **Pushing the subdivided simplex into the submodule of chains in `U ∪ V`.**  If every piece in
the support of the chain of pieces `z` is mapped by `σ` into `U` or into `V`, then the singular
chain obtained by pushing `toSingChain z` forward along `σ` lies in the submodule
`chainIn X U n ⊔ chainIn X V n` of chains in `U` or in `V`. -/
lemma pushChain_toSingChain_mem_sup (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (z : Piece n n →₀ ℚ)
    (hz : ∀ q ∈ z.support,
      ((∀ t, (homOfSimplex σ) (affineSimplex q t) ∈ U) ∨
       (∀ t, (homOfSimplex σ) (affineSimplex q t) ∈ V))) :
    pushChain (homOfSimplex σ) n (toSingChain z) ∈ chainIn X U n ⊔ chainIn X V n := by
  have htc : toSingChain z
      = ∑ q ∈ z.support, z q • Finsupp.single (simplexOfPiece q) (1 : ℚ) := by
    rw [toSingChain, toSingChainLM, Finsupp.linearCombination_apply]
    rfl
  rw [htc, map_sum]
  refine Submodule.sum_mem _ (fun q hq => ?_)
  rw [map_smul, pushChain_single]
  rcases hz q hq with hUq | hVq
  · apply Submodule.smul_mem
    apply Submodule.mem_sup_left
    apply single_mem_chainIn
    intro t
    rw [pushSimplex_apply, ContinuousMap.comp_apply, toSSetObjEquivT_simplexOfPiece,
      homOfSimplex_apply]
    exact hUq t
  · apply Submodule.smul_mem
    apply Submodule.mem_sup_right
    apply single_mem_chainIn
    intro t
    rw [pushSimplex_apply, ContinuousMap.comp_apply, toSSetObjEquivT_simplexOfPiece,
      homOfSimplex_apply]
    exact hVq t

theorem chainIn_sdFun_pow_of_cover (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hUV : ∀ x, x ∈ U ∨ x ∈ V) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ∃ N : ℕ, Nat.iterate (Submission.Cohomology.sdFun X n) N (Finsupp.single σ 1)
      ∈ Submission.Cohomology.chainIn X U n ⊔ Submission.Cohomology.chainIn X V n := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_forall_small X U V hU hV hUV n σ
  obtain ⟨N, hN⟩ := Work.Subdivision.SdPiecesPow_diam_lt n δ hδpos
  refine ⟨N, ?_⟩
  rw [Work.Cohomology.sdFun_iterate_single]
  exact pushChain_toSingChain_mem_sup X U V n σ (SdPiecesPow N n)
    (fun q hq => hδ q (hN q hq))

end

end Work.Cover
