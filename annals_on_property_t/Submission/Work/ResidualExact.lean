import Submission.Work.ResidualBalanced
import Submission.Commons.GroupTheory.FreeGroup.reduce_concat_length_cancel_middle
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_invRev_right

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# Residual (`NoEndCancel`) junction exactness

A **residual** state (`NielsenResidual.NoEndCancel`) admits no single
elementary right-composition strictly decreasing the total length `N` — the
four conjuncts say that no product `w_i·w_j^{±1}` / `w_j^{±1}·w_i` shortens
`w_i`.  This module reads off the *aggregate-level* consequences for the
Fall-II witnesses that a residual state carries (L1, `ResidualBalanced`):

1. **Junction products never shorten either factor.**  If `x = ±w_p` and
   `y = ±w_q` with `p ≠ q`, then `|x·y| ≥ |x|` and `|x·y| ≥ |y|` — for all
   four sign combinations (each conjunct of `NoEndCancel` covers one of the
   sign cases; the inverse-of-the-product identities cover the rest).  This
   is the non-strict form of `noEndCancel_no_left_strict` /
   `noEndCancel_no_right_strict`.

2. **Word-level bounds and exact seams.**  If `x` has word `X ++ invRev A`
   and `y` has word `A ++ B`, the middle `A⁻¹·A` cancels completely, so
   `|x·y| ≤ |X| + |B|` (and symmetrically `|x·y| ≤ |A| + |Z|` when `y` has
   word `invRev B ++ Z`).  Combined with the residual lower bound
   `|x| ≤ |x·y|` (`|x| = |X| + |A|`) this forces the **exact equality**
   `|x·y| = |X| + |B|`: the seam between the covering excess `X` and the
   second half `B` does *not* cancel at all in a residual state.  Symmetrically
   the right seam between `A` and the excess `Z` is exact (`|x·y| = |A|+|Z|`).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## 1. Junction products never shorten either factor (residual states) -/

/-- **A `NoEndCancel` state has no product at a left junction shorter than
its first factor.**  If `x = ±w_p`, `y = ±w_q` with `p ≠ q`, then
`|x| ≤ |x·y|` (non-strict form of `noEndCancel_no_left_strict`). -/
theorem junction_ge_left {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α) {p q : Fin n} (hpq : p ≠ q)
    {x y : FreeGroup (Fin n)}
    (hx : x = α (FreeGroup.of p) ∨ x = (α (FreeGroup.of p))⁻¹)
    (hy : y = α (FreeGroup.of q) ∨ y = (α (FreeGroup.of q))⁻¹) :
    FreeGroup.norm x ≤ FreeGroup.norm (x * y) := by
  by_contra h
  exact False.elim (noEndCancel_no_left_strict α hnec hpq hx hy (lt_of_not_ge h))

/-- **A `NoEndCancel` state has no product at a right junction shorter than
its second factor.**  If `x = ±w_p`, `y = ±w_q` with `p ≠ q`, then
`|y| ≤ |x·y|` (non-strict form of `noEndCancel_no_right_strict`). -/
theorem junction_ge_right {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α) {p q : Fin n} (hpq : p ≠ q)
    {x y : FreeGroup (Fin n)}
    (hx : x = α (FreeGroup.of p) ∨ x = (α (FreeGroup.of p))⁻¹)
    (hy : y = α (FreeGroup.of q) ∨ y = (α (FreeGroup.of q))⁻¹) :
    FreeGroup.norm y ≤ FreeGroup.norm (x * y) := by
  by_contra h
  exact False.elim (noEndCancel_no_right_strict α hnec hpq hx hy (lt_of_not_ge h))

/-! ## 2. Word-level seam bounds and exactness -/

/-- **Left junction word bound.**  If `x` has reduced word
`X ++ invRev A` and `y` has reduced word `A ++ B`, the cancelled middle
`A⁻¹·A` leaves at most `X ++ B`: `|x·y| ≤ |X| + |B|`. -/
theorem leftJunction_norm_le {α : Type*} [DecidableEq α]
    (A B X : List (α × Bool)) (x y : FreeGroup α)
    (hx : x.toWord = X ++ FreeGroup.invRev A)
    (hy : y.toWord = A ++ B) :
    FreeGroup.norm (x * y) ≤ X.length + B.length := by
  have hEq : x * y = FreeGroup.mk ((X ++ FreeGroup.invRev A) ++ (A ++ B)) := by
    calc
      x * y = FreeGroup.mk (X ++ FreeGroup.invRev A) * FreeGroup.mk (A ++ B) := by
              rw [← FreeGroup.mk_toWord (x := x), hx, ← FreeGroup.mk_toWord (x := y), hy]
      _ = FreeGroup.mk ((X ++ FreeGroup.invRev A) ++ (A ++ B)) := by rw [FreeGroup.mul_mk]
  have hAsso : (X ++ FreeGroup.invRev A) ++ (A ++ B) =
      X ++ (FreeGroup.invRev A ++ A) ++ B := by
    rw [List.append_assoc]
    rw [← List.append_assoc (FreeGroup.invRev A) A B]
    rw [← List.append_assoc X (FreeGroup.invRev A ++ A) B]
  have hC : FreeGroup.reduce (FreeGroup.invRev A ++ A) = [] :=
    FreeGroup.reduce_invRev_left_cancel (L := A)
  have hb : (FreeGroup.reduce ((X ++ FreeGroup.invRev A) ++ (A ++ B))).length ≤
      X.length + B.length := by
    rw [hAsso]
    exact Commons.GroupTheory.FreeGroup.reduce_concat_length_cancel_middle
      X (FreeGroup.invRev A ++ A) B hC
  calc
    FreeGroup.norm (x * y) = (x * y).toWord.length := rfl
    _ = (FreeGroup.reduce ((X ++ FreeGroup.invRev A) ++ (A ++ B))).length := by
          rw [hEq, FreeGroup.toWord_mk]
    _ ≤ X.length + B.length := hb

/-- **Right junction word bound.**  If `x` has reduced word `A ++ B` and `y`
has reduced word `invRev B ++ Z`, the cancelled middle `B·B⁻¹` leaves at most
`A ++ Z`: `|x·y| ≤ |A| + |Z|`. -/
theorem rightJunction_norm_le {α : Type*} [DecidableEq α]
    (A B Z : List (α × Bool)) (x y : FreeGroup α)
    (hx : x.toWord = A ++ B)
    (hy : y.toWord = FreeGroup.invRev B ++ Z) :
    FreeGroup.norm (x * y) ≤ A.length + Z.length := by
  have hEq : x * y = FreeGroup.mk ((A ++ B) ++ (FreeGroup.invRev B ++ Z)) := by
    calc
      x * y = FreeGroup.mk (A ++ B) * FreeGroup.mk (FreeGroup.invRev B ++ Z) := by
              rw [← FreeGroup.mk_toWord (x := x), hx, ← FreeGroup.mk_toWord (x := y), hy]
      _ = FreeGroup.mk ((A ++ B) ++ (FreeGroup.invRev B ++ Z)) := by rw [FreeGroup.mul_mk]
  have hAsso : (A ++ B) ++ (FreeGroup.invRev B ++ Z) =
      A ++ (B ++ FreeGroup.invRev B) ++ Z := by
    rw [List.append_assoc]
    rw [← List.append_assoc B (FreeGroup.invRev B) Z]
    rw [← List.append_assoc A (B ++ FreeGroup.invRev B) Z]
  have hC : FreeGroup.reduce (B ++ FreeGroup.invRev B) = [] := by
    simpa [FreeGroup.invRev_invRev] using
      (FreeGroup.reduce_invRev_left_cancel (L := FreeGroup.invRev B))
  have hb : (FreeGroup.reduce ((A ++ B) ++ (FreeGroup.invRev B ++ Z))).length ≤
      A.length + Z.length := by
    rw [hAsso]
    exact Commons.GroupTheory.FreeGroup.reduce_concat_length_cancel_middle
      A (B ++ FreeGroup.invRev B) Z hC
  calc
    FreeGroup.norm (x * y) = (x * y).toWord.length := rfl
    _ = (FreeGroup.reduce ((A ++ B) ++ (FreeGroup.invRev B ++ Z))).length := by
          rw [hEq, FreeGroup.toWord_mk]
    _ ≤ A.length + Z.length := hb

/-- **Exact left seam.**  If additionally the product does not shorten the
left factor (`|x| ≤ |x·y|` — automatic in a residual state) and
`|A| = |B|`, the seam is exact: `|x·y| = |X| + |B|`. -/
theorem exactLeftJunction {α : Type*} [DecidableEq α]
    (A B X : List (α × Bool)) (x y : FreeGroup α)
    (hx : x.toWord = X ++ FreeGroup.invRev A)
    (hy : y.toWord = A ++ B) (hAB : A.length = B.length)
    (hlo : FreeGroup.norm x ≤ FreeGroup.norm (x * y)) :
    FreeGroup.norm (x * y) = X.length + B.length := by
  have hxlen : FreeGroup.norm x = X.length + A.length := by
    rw [show FreeGroup.norm x = x.toWord.length by rfl, hx, List.length_append,
        FreeGroup.invRev_length]
  have hu := leftJunction_norm_le A B X x y hx hy
  omega

/-- **Exact right seam.**  If additionally the product does not shorten the
right factor (`|y| ≤ |x·y|` — automatic in a residual state) and
`|A| = |B|`, the seam is exact: `|x·y| = |A| + |Z|`. -/
theorem exactRightJunction {α : Type*} [DecidableEq α]
    (A B Z : List (α × Bool)) (x y : FreeGroup α)
    (hx : x.toWord = A ++ B)
    (hy : y.toWord = FreeGroup.invRev B ++ Z) (hAB : A.length = B.length)
    (hlo : FreeGroup.norm y ≤ FreeGroup.norm (x * y)) :
    FreeGroup.norm (x * y) = A.length + Z.length := by
  have hylen : FreeGroup.norm y = B.length + Z.length := by
    rw [show FreeGroup.norm y = y.toWord.length by rfl, hy, List.length_append,
        FreeGroup.invRev_length]
  have hu := rightJunction_norm_le A B Z x y hx hy
  omega



/-! ## 3. Aggregate Fall-Two exactness in residual states -/

/-- `A ++ invRev A` is never reduced for nonempty `A` (the first half fully
cancels against the inverse-reversal of itself). -/
private lemma not_reduced_append_invRev {α : Type*} [DecidableEq α]
    (A : List (α × Bool)) (hA : A ≠ []) :
    ¬ FreeGroup.IsReduced (A ++ FreeGroup.invRev A) := by
  intro hred
  have hrv : FreeGroup.reduce (A ++ FreeGroup.invRev A) = A ++ FreeGroup.invRev A :=
    FreeGroup.isReduced_iff_reduce_eq.mp hred
  have hc : FreeGroup.reduce (A ++ FreeGroup.invRev A) = [] :=
    Commons.GroupTheory.FreeGroup.reduce_append_invRev_right A
  have hne : A ++ FreeGroup.invRev A ≠ ([] : List (α × Bool)) := by
    intro hz
    have hpos : 0 < (A ++ FreeGroup.invRev A).length := by
      rw [List.length_append, FreeGroup.invRev_length]
      have hApos : 0 < A.length := by
        cases A with
        | nil => exact False.elim (hA rfl)
        | cons a t => simp
      omega
    have hzlen : (A ++ FreeGroup.invRev A).length = 0 := by
      rw [hz]
      rfl
    omega
  exact hne (hrv.symm.trans hc)

/-- A nontrivial aggregate factor with an even word `A ++ B` (`|A| = |B|`)
has a nonempty first half. -/
private lemma factor_word_half_ne_empty {n : ℕ} (es : List (FreeGroup (Fin n)))
    (hred : SystemReduced es) {j : ℕ} (hj : j < es.length)
    (A B : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hA : es[j].toWord = A ++ B) : A ≠ [] := by
  intro hA0
  have hB0 : B = [] := by
    have hlen : B.length = 0 := by rw [← hAB, hA0]; rfl
    exact List.eq_nil_iff_length_eq_zero.mpr hlen
  have hword : es[j].toWord = [] := by
    rw [hA, hA0, hB0]
    rfl
  have h1 : es[j] ≠ 1 := hred.1 (es[j]) (List.getElem_mem hj)
  apply h1
  exact FreeGroup.toWord_eq_nil_iff.mp hword

/-- **Left-neighbour coordinate distinctness.**  In a reduced system, the
coordinate `v` of the left neighbour `es[j-1] = ±w_v` of a balanced factor
`es[j]` (words `X ++ invRev A` and `A ++ B`, `|A| = |B|`) differs from the
coordinate `p` of `es[j]`: equal coordinates with equal signs would force the
word equality `X ++ invRev A = A ++ B`, hence `B = invRev A` and the reduced
word `A ++ B = A ++ invRev A` — impossible for a nonempty half; equal
coordinates with opposite signs make the two factors adjacent inverses,
which `SystemReduced` forbids. -/
private lemma left_coord_ne {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj0 : 0 < j) (hj : j < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hX : es[j - 1].toWord = X ++ FreeGroup.invRev A)
    (hA : es[j].toWord = A ++ B)
    {v p : Fin n}
    (hv : es[j - 1] = α (FreeGroup.of v) ∨ es[j - 1] = (α (FreeGroup.of v))⁻¹)
    (hp : es[j] = α (FreeGroup.of p) ∨ es[j] = (α (FreeGroup.of p))⁻¹) :
    v ≠ p := by
  intro hvp
  have hSameOrInv : es[j] = es[j - 1] ∨ es[j] = (es[j - 1])⁻¹ := by
    rcases hv with hv | hv
    · rcases hp with hp | hp
      · -- es[j-1] = +w_v, es[j] = +w_p, v = p: factors equal
        exact Or.inl (by rw [hv, hp, hvp])
      · -- es[j-1] = +w_v, es[j] = -w_p, v = p: es[j] = (es[j-1])⁻¹
        exact Or.inr (by rw [hv, hp, hvp])
    · rcases hp with hp | hp
      · -- es[j-1] = -w_v, es[j] = +w_p, v = p: es[j] = (es[j-1])⁻¹
        exact Or.inr (by rw [hv, hp, hvp]; simp)
      · -- both negative: factors equal
        exact Or.inl (by rw [hv, hp, hvp])
  rcases hSameOrInv with hSame | hInv
  · -- equal factors: their words are equal ⟹ B = invRev A ⟹ A ++ B non-reduced
    have heqw : X ++ FreeGroup.invRev A = A ++ B := by
      have hw : es[j - 1].toWord = es[j].toWord := by rw [hSame]
      rw [hX, hA] at hw
      exact hw
    have hlenX : X.length = A.length := by
      have hc := congrArg List.length heqw
      simp [List.length_append, FreeGroup.invRev_length] at hc
      omega
    have hB_eq : B = FreeGroup.invRev A := by
      have hd1 : (X ++ FreeGroup.invRev A).drop A.length = FreeGroup.invRev A := by
        rw [← hlenX]
        rw [List.drop_append_of_le_length (l₁ := X) (l₂ := FreeGroup.invRev A)
          (i := X.length) (by rfl)]
        simp
      have hd2 : (A ++ B).drop A.length = B := by
        rw [List.drop_append_of_le_length (l₁ := A) (l₂ := B) (i := A.length) (by rfl)]
        simp
      have hcon := congrArg (fun W : List (Fin n × Bool) => W.drop A.length) heqw
      rw [hd1, hd2] at hcon
      exact hcon.symm
    have hAn : A ≠ [] := factor_word_half_ne_empty es hred hj A B hAB hA
    have hred_word : FreeGroup.IsReduced (A ++ B) := by
      rw [← hA]
      exact FreeGroup.isReduced_toWord (x := es[j])
    have hnot : ¬ FreeGroup.IsReduced (A ++ FreeGroup.invRev A) :=
      not_reduced_append_invRev A hAn
    exact hnot (by simpa [hB_eq] using hred_word)
  · -- opposite signs: adjacent inverses, forbidden by SystemReduced
    have hne : es[j] ≠ (es[j - 1])⁻¹ := by
      have hji : (j - 1) + 1 = j := by omega
      have hsys := hred.2 (j - 1) (by omega)
      simpa [hji] using hsys
    exact hne hInv

/-- **Left junction exactness in a residual state (aggregate Fall-Two).**
  For a balanced witness factor `es[j]` of the image aggregate of `a_m`
  (word `A ++ B`, `|A| = |B|`, the left neighbour covering `invRev A` from
  the right: `es[j-1] = X ++ invRev A`), a residual (`NoEndCancel`) state
  makes the left junction exact: `|es[j-1]·es[j]| = |X| + |B|` — the seam
  between the covering excess `X` and the second half `B` does not cancel.
  (The lower bound is `junction_ge_left` with the distinct coordinates of
  `es[j-1]` and `es[j]`; the upper bound is `leftJunction_norm_le`.) -/
theorem residualLeftJunction_exact {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) (m : Fin n)
    {j : ℕ} (hj0 : 0 < j) (hj : j < (imageAggregate α m).length)
    (hmj : j - 1 < (imageAggregate α m).length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hX : ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A)
    (hA : ((imageAggregate α m)[j]).toWord = A ++ B) :
    FreeGroup.norm (((imageAggregate α m)[j - 1]) * ((imageAggregate α m)[j])) =
      X.length + B.length := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have hmj' : j - 1 < es.length := by
    dsimp [es]
    exact hmj
  have hj' : j < es.length := by
    dsimp [es]
    exact hj
  have hXe : es[j - 1].toWord = X ++ FreeGroup.invRev A := by
    simpa [es] using hX
  have hAe : es[j].toWord = A ++ B := by
    simpa [es] using hA
  rcases aggregate_factor_coordinate α es himg hmj' with ⟨v, hv⟩
  rcases aggregate_factor_coordinate α es himg hj' with ⟨p, hp⟩
  have hvp : v ≠ p := left_coord_ne α es hred hj0 hj' A B X hAB hXe hAe hv hp
  have hlo : FreeGroup.norm (es[j - 1]) ≤ FreeGroup.norm (es[j - 1] * es[j]) :=
    junction_ge_left α hres hvp hv hp
  have hE := exactLeftJunction A B X (es[j - 1]) (es[j]) hXe hAe hAB hlo
  simpa [es] using hE

/-- **Covering excess of the left neighbour is at least the half.**  In a
residual state the balanced witness is *both-excess-long* on the left: the
upper-bound-free equality `|es[j-1]·es[j]| = |X| + |B|`
(`residualLeftJunction_exact`) combined with the residual lower bound
`|es[j]| ≤ |es[j-1]·es[j]|` (`junction_ge_right`) gives `|X| ≥ |A|`. -/
theorem residualFallTwo_left_excess_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) (m : Fin n)
    {j : ℕ} (hj0 : 0 < j) (hj : j < (imageAggregate α m).length)
    (hmj : j - 1 < (imageAggregate α m).length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hX : ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A)
    (hA : ((imageAggregate α m)[j]).toWord = A ++ B) :
    A.length ≤ X.length := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have hmj' : j - 1 < es.length := by
    dsimp [es]
    exact hmj
  have hj' : j < es.length := by
    dsimp [es]
    exact hj
  have hXe : es[j - 1].toWord = X ++ FreeGroup.invRev A := by
    simpa [es] using hX
  have hAe : es[j].toWord = A ++ B := by
    simpa [es] using hA
  rcases aggregate_factor_coordinate α es himg hmj' with ⟨v, hv⟩
  rcases aggregate_factor_coordinate α es himg hj' with ⟨p, hp⟩
  have hvp : v ≠ p := left_coord_ne α es hred hj0 hj' A B X hAB hXe hAe hv hp
  have hge2 : FreeGroup.norm (es[j]) ≤ FreeGroup.norm (es[j - 1] * es[j]) :=
    junction_ge_right α hres hvp hv hp
  have hExact : FreeGroup.norm (es[j - 1] * es[j]) = X.length + B.length := by
    simpa [es] using (residualLeftJunction_exact α hres m (hj0 := hj0) (hj := hj)
      (hmj := hmj) A B X hAB hX hA)
  have hlen_mid : FreeGroup.norm (es[j]) = A.length + B.length := by
    rw [show FreeGroup.norm (es[j]) = es[j].toWord.length by rfl, hAe, List.length_append]
  omega

/-- **Right-neighbour coordinate distinctness.**  Mirror of
`left_coord_ne`: the coordinate `p` of the right neighbour `es[j+1] = ±w_p`
of a balanced factor `es[j]` (words `A ++ B` and `invRev B ++ Z`,
`|A| = |B|`) differs from the coordinate `v` of `es[j]` (equal coordinates
with equal signs force `A ++ B = invRev B ++ Z`, hence `A = invRev B`, so
the reduced word `A ++ B = A ++ invRev A` is impossible; opposite signs make
the two factors adjacent inverses, forbidden by `SystemReduced`). -/
private lemma right_coord_ne {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hA : es[j].toWord = A ++ B)
    (hZ : es[j + 1].toWord = FreeGroup.invRev B ++ Z)
    {v p : Fin n}
    (hv : es[j] = α (FreeGroup.of v) ∨ es[j] = (α (FreeGroup.of v))⁻¹)
    (hp : es[j + 1] = α (FreeGroup.of p) ∨ es[j + 1] = (α (FreeGroup.of p))⁻¹) :
    v ≠ p := by
  intro hvp
  have hSameOrInv : es[j + 1] = es[j] ∨ es[j + 1] = (es[j])⁻¹ := by
    rcases hv with hv | hv
    · rcases hp with hp | hp
      · exact Or.inl (by rw [hp, hv, hvp])
      · exact Or.inr (by rw [hp, hv, hvp])
    · rcases hp with hp | hp
      · exact Or.inr (by rw [hp, hv, hvp]; simp)
      · exact Or.inl (by rw [hp, hv, hvp])
  rcases hSameOrInv with hSame | hInv
  · -- equal factors: A ++ B = invRev B ++ Z ⟹ A = invRev B ⟹ A ++ B non-reduced
    have heqw : A ++ B = FreeGroup.invRev B ++ Z := by
      have hw : es[j].toWord = es[j + 1].toWord := by rw [hSame]
      rw [hA, hZ] at hw
      exact hw
    have hA_eq : A = FreeGroup.invRev B := by
      have hp1 : (A ++ B).take A.length = A := by
        rw [List.take_append_of_le_length (l₁ := A) (l₂ := B) (i := A.length) (by rfl)]
        simp
      have hp2 : (FreeGroup.invRev B ++ Z).take A.length = FreeGroup.invRev B := by
        rw [show A.length = (FreeGroup.invRev B).length by
          rw [FreeGroup.invRev_length, hAB]]
        rw [List.take_append_of_le_length (l₁ := FreeGroup.invRev B) (l₂ := Z)
          (i := (FreeGroup.invRev B).length) (by rfl)]
        simp
      have hcon := congrArg (fun W : List (Fin n × Bool) => W.take A.length) heqw
      rw [hp1, hp2] at hcon
      exact hcon
    have hB_eq : B = FreeGroup.invRev A := by
      rw [hA_eq, FreeGroup.invRev_invRev]
    have hAn : A ≠ [] := factor_word_half_ne_empty es hred hj A B hAB hA
    have hred_word : FreeGroup.IsReduced (A ++ B) := by
      rw [← hA]
      exact FreeGroup.isReduced_toWord (x := es[j])
    have hnot : ¬ FreeGroup.IsReduced (A ++ FreeGroup.invRev A) :=
      not_reduced_append_invRev A hAn
    exact hnot (by simpa [hB_eq] using hred_word)
  · -- opposite signs: adjacent inverses, forbidden by SystemReduced
    have hne : es[j + 1] ≠ (es[j])⁻¹ := by
      simpa using hred.2 j hjk
    exact hne hInv

/-- **Right junction exactness in a residual state (aggregate Fall-Two).**
  Mirror of `residualLeftJunction_exact`: for a balanced witness factor
  `es[j]` of the image aggregate of `a_m` (word `A ++ B`, `|A| = |B|`, the
  right neighbour covering `invRev B` from the left:
  `es[j+1] = invRev B ++ Z`), a residual (`NoEndCancel`) state makes the
  right junction exact: `|es[j]·es[j+1]| = |A| + |Z|`. -/
theorem residualRightJunction_exact {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) (m : Fin n)
    {j : ℕ} (hj : j < (imageAggregate α m).length)
    (hjk : j + 1 < (imageAggregate α m).length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hA : ((imageAggregate α m)[j]).toWord = A ++ B)
    (hZ : ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z) :
    FreeGroup.norm (((imageAggregate α m)[j]) * ((imageAggregate α m)[j + 1])) =
      A.length + Z.length := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have hj' : j < es.length := by
    dsimp [es]
    exact hj
  have hjk' : j + 1 < es.length := by
    dsimp [es]
    exact hjk
  have hAe : es[j].toWord = A ++ B := by
    simpa [es] using hA
  have hZe : es[j + 1].toWord = FreeGroup.invRev B ++ Z := by
    simpa [es] using hZ
  rcases aggregate_factor_coordinate α es himg hj' with ⟨v, hv⟩
  rcases aggregate_factor_coordinate α es himg hjk' with ⟨p, hp⟩
  have hvp : v ≠ p := right_coord_ne α es hred hj' hjk' A B Z hAB hAe hZe hv hp
  have hlo : FreeGroup.norm (es[j + 1]) ≤ FreeGroup.norm (es[j] * es[j + 1]) :=
    junction_ge_right α hres hvp hv hp
  have hE := exactRightJunction A B Z (es[j]) (es[j + 1]) hAe hZe hAB hlo
  simpa [es] using hE

/-- **Covering excess of the right neighbour is at least the half.**  Mirror
of `residualFallTwo_left_excess_ge`: the equality
`|es[j]·es[j+1]| = |A| + |Z|` (`residualRightJunction_exact`) combined with
the residual lower bound `|es[j]| ≤ |es[j]·es[j+1]|` (`junction_ge_left`)
gives `|Z| ≥ |B|`.  Together with `residualFallTwo_left_excess_ge` this is
the *both-excess-long* property of the balanced witness of a residual state. -/
theorem residualFallTwo_right_excess_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) (m : Fin n)
    {j : ℕ} (hj : j < (imageAggregate α m).length)
    (hjk : j + 1 < (imageAggregate α m).length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hA : ((imageAggregate α m)[j]).toWord = A ++ B)
    (hZ : ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z) :
    B.length ≤ Z.length := by
  classical
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  have hj' : j < es.length := by
    dsimp [es]
    exact hj
  have hjk' : j + 1 < es.length := by
    dsimp [es]
    exact hjk
  have hAe : es[j].toWord = A ++ B := by
    simpa [es] using hA
  have hZe : es[j + 1].toWord = FreeGroup.invRev B ++ Z := by
    simpa [es] using hZ
  rcases aggregate_factor_coordinate α es himg hj' with ⟨v, hv⟩
  rcases aggregate_factor_coordinate α es himg hjk' with ⟨p, hp⟩
  have hvp : v ≠ p := right_coord_ne α es hred hj' hjk' A B Z hAB hAe hZe hv hp
  have hge1 : FreeGroup.norm (es[j]) ≤ FreeGroup.norm (es[j] * es[j + 1]) :=
    junction_ge_left α hres hvp hv hp
  have hExact : FreeGroup.norm (es[j] * es[j + 1]) = A.length + Z.length := by
    simpa [es] using (residualRightJunction_exact α hres m (hj := hj) (hjk := hjk)
      A B Z hAB hA hZ)
  have hlen_mid : FreeGroup.norm (es[j]) = A.length + B.length := by
    rw [show FreeGroup.norm (es[j]) = es[j].toWord.length by rfl, hAe, List.length_append]
  omega

/-- **Exactness is junction balance at the seam (left).**  Under the
covering word identities and `|A| = |B|`, the left seam is exact
(`|x·y| = |X| + |B|`) if and only if the junction product does not shorten
the left factor: `|x·y| < |x|` is impossible exactly when the bound
`|x·y| ≤ |X| + |B| = |x|` is attained.  So in a residual state the witness's
seams are exact precisely because the witness junctions are balanced. -/
theorem exactLeftJunction_iff_junction_balanced {α : Type*} [DecidableEq α]
    (A B X : List (α × Bool)) (x y : FreeGroup α)
    (hx : x.toWord = X ++ FreeGroup.invRev A)
    (hy : y.toWord = A ++ B) (hAB : A.length = B.length) :
    FreeGroup.norm (x * y) = X.length + B.length ↔
      ¬ FreeGroup.norm (x * y) < FreeGroup.norm x := by
  constructor
  · intro h
    rw [h]
    rw [show FreeGroup.norm x = x.toWord.length by rfl, hx, List.length_append,
        FreeGroup.invRev_length]
    omega
  · intro hnot
    have hu := leftJunction_norm_le A B X x y hx hy
    have hxlen : FreeGroup.norm x = X.length + A.length := by
      rw [show FreeGroup.norm x = x.toWord.length by rfl, hx, List.length_append,
          FreeGroup.invRev_length]
    omega

/-- **Exactness is junction balance at the seam (right).**  Mirror: the
right seam is exact (`|x·y| = |A| + |Z|`) iff the junction product does not
shorten the right factor. -/
theorem exactRightJunction_iff_junction_balanced {α : Type*} [DecidableEq α]
    (A B Z : List (α × Bool)) (x y : FreeGroup α)
    (hx : x.toWord = A ++ B)
    (hy : y.toWord = FreeGroup.invRev B ++ Z) (hAB : A.length = B.length) :
    FreeGroup.norm (x * y) = A.length + Z.length ↔
      ¬ FreeGroup.norm (x * y) < FreeGroup.norm y := by
  constructor
  · intro h
    rw [h]
    rw [show FreeGroup.norm y = y.toWord.length by rfl, hy, List.length_append,
        FreeGroup.invRev_length]
    omega
  · intro hnot
    have hu := rightJunction_norm_le A B Z x y hx hy
    have hylen : FreeGroup.norm y = B.length + Z.length := by
      rw [show FreeGroup.norm y = y.toWord.length by rfl, hy, List.length_append,
          FreeGroup.invRev_length]
    omega

end Submission.Nielsen
