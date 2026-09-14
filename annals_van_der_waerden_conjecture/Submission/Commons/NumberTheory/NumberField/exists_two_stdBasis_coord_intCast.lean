import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Two `stdBasis` coordinates that read off an integer

For a number field `K` of unit rank `≠ 0` (equivalently: `K` has at least two infinite places),
there are two distinct indices `l₀ ≠ l₁` of the standard basis `NumberField.mixedEmbedding.stdBasis K`
of the mixed space `ℝ^{r₁} × ℂ^{r₂}` whose coordinates detect an integer `k : ℤ` embedded in `K`:
the `l₀`- and `l₁`-coordinates of `NumberField.mixedEmbedding K (k : K)` are both equal to `k`.

Concretely, the "real type" indices are those `inl w` with `w` a real infinite place together with
the first (`re`) coordinates `inr ⟨w, 0⟩` at a complex place; on them the coordinate of `k` is `k`,
while on the second (`im`) coordinates of a complex place it is `0`.  A choice of one real-type index
per infinite place gives an injection `InfinitePlace K → index K`, and `rank K ≠ 0` means that there
are at least two infinite places, whence two distinct such indices.
-/

open scoped Classical
open NumberField NumberField.mixedEmbedding

namespace Commons.NumberTheory.NumberField

noncomputable section

variable {K : Type*} [Field K]

/-- The index of the standard basis `stdBasis` of the mixed space associated with an infinite
place `w`, chosen to be of "real type": `inl w` if `w` is real, and the first coordinate
`inr ⟨w, 0⟩` (the real part of the complex embedding) if `w` is complex.  On such an index the
coordinate of an integer `k : ℤ` embedded in `K` is `k` itself. -/
def placeIndex (w : NumberField.InfinitePlace K) : NumberField.mixedEmbedding.index K :=
  if hw : w.IsReal then Sum.inl ⟨w, hw⟩
  else Sum.inr ⟨⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, 0⟩

/-- The infinite place underlying an index of the standard basis `stdBasis` of the mixed space. -/
def indexPlace (l : NumberField.mixedEmbedding.index K) : NumberField.InfinitePlace K :=
  match l with
  | Sum.inl w => w.1
  | Sum.inr wj => wj.1.1

@[simp]
theorem indexPlace_placeIndex (w : NumberField.InfinitePlace K) :
    indexPlace (placeIndex w) = w := by
  by_cases hw : w.IsReal
  · simp [placeIndex, indexPlace, dif_pos hw]
  · simp [placeIndex, indexPlace, dif_neg hw]

/-- The map sending an infinite place to its "real type" index of `stdBasis` is injective: in
particular, distinct infinite places give distinct indices. -/
theorem placeIndex_injective : Function.Injective (placeIndex (K := K)) := by
  intro a b hab
  have h := congrArg indexPlace hab
  simpa using h

variable [NumberField K]

/-- On a "real type" index, the coordinate of the image of an integer `k : ℤ` under the mixed
embedding is `k` itself. -/
theorem repr_placeIndex_intCast (w : NumberField.InfinitePlace K) (k : ℤ) :
    (NumberField.mixedEmbedding.stdBasis K).repr
      (NumberField.mixedEmbedding K ((k : K))) (placeIndex w) = (k : ℝ) := by
  by_cases hw : w.IsReal
  · simp only [placeIndex, dif_pos hw, NumberField.mixedEmbedding.stdBasis_apply_isReal,
      NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
    exact map_intCast _ k
  · simp only [placeIndex, dif_neg hw, NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
      NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
    rw [map_intCast]
    simp

/-- A number field of unit rank `≠ 0` has at least two infinite places. -/
theorem one_lt_card_infinitePlace_of_rank_ne_zero (h : NumberField.Units.rank K ≠ 0) :
    1 < Fintype.card (NumberField.InfinitePlace K) := by
  rw [NumberField.Units.rank] at h
  omega

theorem exists_two_stdBasis_coord_intCast {K : Type*} [Field K] [NumberField K]
    (h : NumberField.Units.rank K ≠ 0) :
    ∃ l₀ l₁ : NumberField.mixedEmbedding.index K, l₀ ≠ l₁ ∧
      (∀ k : ℤ, (NumberField.mixedEmbedding.stdBasis K).repr
        (NumberField.mixedEmbedding K ((k : K))) l₀ = (k : ℝ)) ∧
      (∀ k : ℤ, (NumberField.mixedEmbedding.stdBasis K).repr
        (NumberField.mixedEmbedding K ((k : K))) l₁ = (k : ℝ)) := by
  obtain ⟨w₀, w₁, hne⟩ :=
    Fintype.exists_pair_of_one_lt_card (one_lt_card_infinitePlace_of_rank_ne_zero (K := K) h)
  exact ⟨placeIndex w₀, placeIndex w₁,
    fun hh => hne (placeIndex_injective hh),
    fun k => repr_placeIndex_intCast w₀ k,
    fun k => repr_placeIndex_intCast w₁ k⟩

end

end Commons.NumberTheory.NumberField