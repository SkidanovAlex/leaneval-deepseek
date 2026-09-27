import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Cover
import Submission.Work.Cohomology.sdFun_iterate_single

namespace Work.Cover

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

noncomputable section

/-! ## The subdivision preserves the chains lying in a subset

`chainIn X W n` is the submodule of singular `n`-chains of `X` spanned by the simplices whose
image lies in `W`.  The subdivision operator `sdFun X n` replaces a singular simplex `σ` by
`(homOfSimplex σ)♯ (Sd(Δⁿ))`, i.e. it pushes the barycentric subdivision of `Δⁿ` forward along
the map of `σ`.  Since the whole of `Δⁿ` is mapped into `W` by `homOfSimplex σ`, every simplex
occurring in that pushforward again lies in `W`, so the subdivision preserves `chainIn X W n`.

The proof splits into three routine steps:

* `linearCombination_mem_submodule` — a `Finsupp.linearCombination` of elements of a submodule
  lies in the submodule;
* `pushChain_map_le_chainIn` — pushing a chain in `f ⁻¹' W` forward along `f` lands in `chainIn Y W`
  (this is the functoriality of the condition "the image lies in `W`");
* `toSingChain_mem_chainIn` — the transport of a chain of pieces of `Δ^N` to singular chains lands
  in `chainIn` whenever every piece maps into the target set;
* finally `sdUniv n = toSingChain (SdPieces n)` and `sdFun_single` reduce the claim to the second
  and third steps. -/

/-- A `Finsupp.linearCombination` with values in a submodule lies in that submodule. -/
lemma linearCombination_mem_submodule {ι : Type*} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    {φ : ι → M} {S : Submodule ℚ M} (h : ∀ i, φ i ∈ S) (z : ι →₀ ℚ) :
    Finsupp.linearCombination ℚ φ z ∈ S := by
  rw [Finsupp.linearCombination_apply]
  exact Submodule.sum_mem S fun i _ => Submodule.smul_mem S _ (h i)

/-- **Pushforward of chains lying in a preimage**: if a chain of `X` is supported on simplices
whose image lies in `f ⁻¹' W`, then its pushforward along `f` is supported on simplices whose
image lies in `W`. -/
lemma pushChain_map_le_chainIn {X Y : TopCat.{0}} (f : X ⟶ Y) (W : Set Y) (n : ℕ) :
    (chainIn X (f ⁻¹' W) n).map (pushChain f n) ≤ chainIn Y W n := by
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro c ⟨σ, hσ, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, pushChain_single]
  refine single_mem_chainIn (pushSimplex f n σ) fun t => ?_
  rw [pushSimplex_apply]
  exact hσ t

/-- **Transport of a chain of pieces to a singular chain preserves the small chains**: if every
piece `q` occurring in `z` maps into `W'`, then `toSingChain z` lies in `chainIn W'`. -/
lemma toSingChain_mem_chainIn {N m : ℕ} {W' : Set (stdTopSimplex N)} (z : Piece N m →₀ ℚ)
    (hz : ∀ q : Piece N m, ∀ t : TSimplex m, (affineSimplex q) t ∈ W') :
    toSingChain z ∈ chainIn (stdTopSimplex N) W' m := by
  rw [toSingChain, toSingChainLM]
  refine linearCombination_mem_submodule (fun q => ?_) z
  exact single_mem_chainIn (simplexOfPiece q) fun t => by
    rw [toSSetObjEquivT_simplexOfPiece]
    exact hz q t

/-- **The subdivision operator preserves the chains lying in a subset.** -/
theorem sdFun_mem_chainIn (X : TopCat.{0}) (W : Set X) (n : ℕ) :
    (Submission.Cohomology.chainIn X W n).map (Submission.Cohomology.sdFun X n)
      ≤ Submission.Cohomology.chainIn X W n := by
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro c ⟨σ, hσ, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, sdFun_single, one_smul]
  have hmem : sdUniv n ∈ chainIn (stdTopSimplex n) (homOfSimplex σ ⁻¹' W) n := by
    rw [sdUniv]
    refine toSingChain_mem_chainIn (SdPieces n) (fun q t => ?_)
    simp only [Set.mem_preimage, homOfSimplex, TopCat.hom_ofHom]
    exact hσ ((affineSimplex q) t)
  exact pushChain_map_le_chainIn (homOfSimplex σ) W n (Submodule.mem_map_of_mem hmem)

end

end Work.Cover
