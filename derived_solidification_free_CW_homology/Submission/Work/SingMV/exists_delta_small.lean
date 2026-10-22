import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.bary_dist_le

/-!
# A Lebesgue number for a cover by two open sets

This file proves `Work.SingMV.exists_delta_small`: for open `U, V ⊆ X` with `U ∪ V = X` and any
singular `n`-simplex `σ : Δⁿ ⟶ X`, there is `d > 0` such that every affine `n`-simplex of `Δⁿ`
whose vertex tuple is `d`-close (in the sup metric on `ℝ^{n+1}`) is `(U,V)`-small after composing
with `σ`, i.e. its image lies in `U` or in `V`.

The proof is the classical Lebesgue-number argument. The continuous map `σ` pulls the open cover
`{U, V}` of `X` back to an open cover `{σ⁻¹U, σ⁻¹V}` of the compact simplex `Δⁿ`. Since `toE`
embeds `Δⁿ` into the pseudo-metric space `ℝ^{n+1}` with the sup metric
(`Convexity.StdSimplex.isEmbedding_toFun_comp_weights`), the two open sets can be written as the
preimages of open subsets `WA, WB` of `ℝ^{n+1}`; Lebesgue's number lemma applied to the compact
set `toE '' univ ⊆ ℝ^{n+1}` and the cover `{WA, WB}` produces `δ > 0` such that every
`δ`-ball around a point of `toE '' univ` is contained in `WA` or in `WB`. Halving `δ` and using
that a convex combination of `d`-close points is `d`-close to each of them (`bary_dist_le`), any
affine simplex with `d`-close vertices maps into `U` or into `V`.

## Main results

* `Work.SingMV.exists_pos_dist_le_or`: the Lebesgue number statement along a general embedding of
  a compact space into a pseudo-metric space.
* `Work.SingMV.isEmbedding_toE`: the standard simplex embeds in `ℝ^{n+1}` via `toE`.
* `Work.SingMV.exists_delta_small`: the requested statement.
-/

noncomputable section

namespace Work.SingMV

/-- **Lebesgue number for a pair of open sets, along an embedding.**

Let `f : α → β` be an embedding of a compact space `α` into a pseudo-metric space `β`, and let
`A, B ⊆ α` be open with `A ∪ B = α`. Then there is `δ > 0` such that for every centre `c : α`
the set of points of `α` whose `f`-image is within `δ` of `f c` is contained either in `A` or
in `B`.

This is the Lebesgue-number lemma for the two-element open cover obtained by pulling back an
open cover of the compact set `f '' univ`. -/
theorem exists_pos_dist_le_or {α β : Type*} [TopologicalSpace α] [CompactSpace α]
    [PseudoMetricSpace β] (f : α → β) (hf : Topology.IsEmbedding f)
    {A B : Set α} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = Set.univ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : α, (∀ x : α, dist (f x) (f c) ≤ δ → x ∈ A) ∨
      (∀ x : α, dist (f x) (f c) ≤ δ → x ∈ B) := by
  classical
  -- write `A` and `B` as preimages of open sets of the ambient space
  obtain ⟨WA, hWAo, hWA⟩ := hf.toIsInducing.isOpen_iff.mp hA
  obtain ⟨WB, hWBo, hWB⟩ := hf.toIsInducing.isOpen_iff.mp hB
  -- the range of `f` is compact and is covered by `WA ∪ WB`
  have hK : IsCompact (Set.range f) := by
    simpa [Set.image_univ] using isCompact_univ.image hf.continuous
  have hcov : Set.range f ⊆ WA ∪ WB := by
    rintro y ⟨x, rfl⟩
    rcases Set.mem_or_mem_of_mem_union (hAB ▸ Set.mem_univ x) with hx | hx
    · left; rw [← hWA] at hx; exact hx
    · right; rw [← hWB] at hx; exact hx
  -- Lebesgue number of the two-element cover of the compact set `range f`
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := lebesgue_number_lemma_of_metric (s := Set.range f) hK
    (c := fun b : Bool => match b with | true => WB | false => WA)
    (by intro b; cases b <;> assumption)
    (by
      intro y hy
      rcases hcov hy with h | h
      · exact Set.mem_iUnion.mpr ⟨false, h⟩
      · exact Set.mem_iUnion.mpr ⟨true, h⟩)
  refine ⟨δ₀ / 2, by linarith, fun c => ?_⟩
  obtain ⟨b, hb⟩ := hδ₀ (f c) (Set.mem_range_self c)
  -- a point within `δ₀ / 2` of `f c` lies in the ball of radius `δ₀` around `f c`
  have hstep : ∀ x : α, dist (f x) (f c) ≤ δ₀ / 2 → f x ∈ Metric.ball (f c) δ₀ := fun x hx =>
    Metric.mem_ball.mpr (lt_of_le_of_lt hx (by linarith))
  cases b with
  | false =>
      left
      intro x hx
      have hfx : f x ∈ WA := hb (hstep x hx)
      rw [← hWA]
      exact hfx
  | true =>
      right
      intro x hx
      have hfx : f x ∈ WB := hb (hstep x hx)
      rw [← hWB]
      exact hfx

/-- The map `toE` from the standard `m`-simplex to `ℝ^m` (with the sup metric) is an embedding:
this is `Convexity.StdSimplex.isEmbedding_toFun_comp_weights`, since `toE t` is the function
underlying the weight vector of `t`. -/
theorem isEmbedding_toE (m : ℕ) : Topology.IsEmbedding (@Work.SingMV.toE m) := by
  rw [show (@Work.SingMV.toE m) =
      (fun t : Convexity.StdSimplex ℝ (Fin m) => ⇑t.weights) from by funext t i; rfl]
  exact Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin m)

/-- **Existence of a Lebesgue number for the cover `{U, V}` of `X`.** For open `U, V ⊆ X` with
`U ∪ V = X`, any singular `n`-simplex `σ : Δⁿ ⟶ X` and `d > 0` small enough (depending on `σ`),
every affine `n`-simplex of `Δⁿ` whose vertex tuple is `d`-close has `σ`-image contained in `U`
or in `V`; its generator therefore lies in the submodule of `(U,V)`-small chains. -/
theorem exists_delta_small (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) (σ : Work.SingMV.singMap X n) :
    ∃ d : ℝ, 0 < d ∧ ∀ q : Fin (n+1) → Convexity.StdSimplex ℝ (Fin (n+1)),
      Work.SingMV.VClose q d →
        Work.SingMV.gen X n (σ.comp (Work.SingMV.affineSimplex q)) ∈
          Work.SingMV.smallChain X n U V := by
  -- the preimages of `U` and `V` under `σ` are open and cover `Δⁿ`
  have hU' : IsOpen (σ ⁻¹' U) := hU.preimage σ.continuous
  have hV' : IsOpen (σ ⁻¹' V) := hV.preimage σ.continuous
  have hcover : σ ⁻¹' U ∪ σ ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hUV, Set.preimage_univ]
  -- Lebesgue number for this cover of the compact simplex, measured along the embedding `toE`
  obtain ⟨δ, hδpos, hδ⟩ :=
    exists_pos_dist_le_or (@Work.SingMV.toE (n+1)) (isEmbedding_toE (n+1)) hU' hV' hcover
  refine ⟨δ, hδpos, fun q hq => ?_⟩
  rcases hδ (q 0) with h | h
  · -- the simplex lies in `U`
    have hmem : Work.SingMV.gen X n (σ.comp (Work.SingMV.affineSimplex q)) ∈
        Work.SingMV.smallSpan X n U := by
      apply Submodule.subset_span
      refine ⟨⟨σ.comp (Work.SingMV.affineSimplex q), ?_⟩, rfl⟩
      intro t
      -- every point of the affine simplex is within `δ` of the vertex `q 0`
      exact h ((Work.SingMV.affineSimplex q) t) (by
        show dist (Work.SingMV.toE ((Work.SingMV.affineSimplex q) t))
          (Work.SingMV.toE (q 0)) ≤ δ
        exact bary_dist_le t q δ 0 hq)
    rw [Work.SingMV.smallChain]
    exact Submodule.mem_sup_left hmem
  · -- the simplex lies in `V`
    have hmem : Work.SingMV.gen X n (σ.comp (Work.SingMV.affineSimplex q)) ∈
        Work.SingMV.smallSpan X n V := by
      apply Submodule.subset_span
      refine ⟨⟨σ.comp (Work.SingMV.affineSimplex q), ?_⟩, rfl⟩
      intro t
      exact h ((Work.SingMV.affineSimplex q) t) (by
        show dist (Work.SingMV.toE ((Work.SingMV.affineSimplex q) t))
          (Work.SingMV.toE (q 0)) ≤ δ
        exact bary_dist_le t q δ 0 hq)
    rw [Work.SingMV.smallChain]
    exact Submodule.mem_sup_right hmem

end Work.SingMV
