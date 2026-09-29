import Mathlib
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst.bounded_basis
import Submission.Work.ZeroEst.orbit_prefix

/-!
# `Work.ZeroEst.lam_cramer`

Uniform bounded-degree Cramer data for the `Λ`-orbit.

Let `q ≠ 0`, `A ∈ Mat_m(ℚ[X])`, `P ∈ ℚ[X]^m`, and let `Λ Q = q·Q' + Q·Aᵗ` so that
`orbit q A P k = ΛᵏP` (`Work.ZeroEst.one_var_defs`).  Suppose we are given `r`, selections
`V k0 : Fin r → Fin m` and rational functions `lam l j` such that

* the `r × r` matrix `M = (orbit q A P (k0 a) (V b))` has nonzero determinant, and
* for every `k < m` the vector `orbit q A P k` is a `ℚ(x)`-linear combination
  `orbit k j = Σ_l lam l j · orbit k (V l)` of the selected columns.

The lemma produces polynomial vectors `Q a : ℚ[X]^m` whose entries all have degree `≤ N`,
where `N = c(m,q,A)` is *independent of `P`*, such that `det (Q a (V b)) ≠ 0` and the
Cramer identity `det (Q a (V b)) · lam l j = det (Q a (if b = l then j else V b))` holds.
In other words: the Cramer coefficients `lam` of the orbit matrix can be recomputed from a
matrix of *bounded degree*.

## Proof

`N` is the constant `bounded_basis` (`Work.ZeroEst.bounded_basis`, the formalisation of
Lang VII §3 Lemma 2.4).  For a given `P`, let

* `t` and `v_0,…,v_{t-1}` be the prefix supplied by `orbit_prefix`: a `ℚ(x)`-basis of the
  span `U` of the first `m` orbit vectors which is `Λ`-stable, and
* `v_0',…,v_{t-1}'` the bounded-degree spanning family of `U` obtained from `bounded_basis`
  applied to that prefix (`deg v_i' ≤ c`).

Since `k0 a < m`, the row `orbit q A P (k0 a) ·` lies in `U`, so its projection
`b ↦ orbit q A P (k0 a) (V b)` lies in the span of `π v_i' = (v_i' (V ·))`.  The matrix
`(orbit (k0 a) (V b))` being invertible makes these rows `ℚ(x)`-independent, hence the
columns `π v_i'` span `ℚ(x)^r`, so the row space of the `r × t` matrix `Y a i = v_i'(V a)`
has rank `r`; `exists_det_submatrix_ne_zero` then yields an injection `J : Fin r → Fin t`
with `det (Y.submatrix id J) ≠ 0`.  Put `Q a j := v_{J a}' j`; then `deg Q a j ≤ c` and
`det (Q a (V b)) = det (Y.submatrix id J)ᵗ ≠ 0`.

Finally each row `Q a` lies in `U`, and by hypothesis every element of `U` satisfies the
`lam`-relation; multiplying the matrix identity `N = M·lam` by an elementary column
operation and applying `Matrix.det_updateCol_sum` produces the Cramer identity
(`lamCramer_cramer`).
-/

namespace Work.ZeroEst

open Polynomial Matrix

/-- **Cramer identity from the `lam`-relations.**  If the rows of a family `Q : Fin r → ℚ[X]^m`
all satisfy the relation `Q a j = Σ_l lam l j · Q a (V l)`, then replacing the `l`-th column of
the matrix `(Q a (V b))` by the `j`-th column `(Q a j)_a` multiplies its determinant by
`lam l j`.  This is `Matrix.det_updateCol_sum`: the replaced column is
`(Q a (V b)) *ᵥ (lam · j)`. -/
theorem lamCramer_cramer {r m : ℕ} (V : Fin r → Fin m) (lam : Fin r → Fin m → RatFunc ℚ)
    (Q : Fin r → Fin m → Polynomial ℚ)
    (hW : ∀ a j, ((Q a j : Polynomial ℚ) : RatFunc ℚ)
        = ∑ l, lam l j * ((Q a (V l) : Polynomial ℚ) : RatFunc ℚ)) :
    ∀ l j, (Matrix.of (fun a b : Fin r => ((Q a (V b) : Polynomial ℚ) : RatFunc ℚ))).det * lam l j
      = (Matrix.of (fun a b : Fin r => ((Q a (if b = l then j else V b) : Polynomial ℚ) : RatFunc ℚ))).det := by
  intro l j
  set A : Matrix (Fin r) (Fin r) (RatFunc ℚ) :=
    Matrix.of (fun a b : Fin r => ((Q a (V b) : Polynomial ℚ) : RatFunc ℚ)) with hA
  have key : ∀ a : Fin r, (A *ᵥ (fun i => lam i j)) a = ((Q a j : Polynomial ℚ) : RatFunc ℚ) := by
    intro a
    rw [hA]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [hW a j]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hmat : A.updateCol l (A *ᵥ (fun i => lam i j))
      = Matrix.of (fun a b : Fin r => ((Q a (if b = l then j else V b) : Polynomial ℚ) : RatFunc ℚ)) := by
    ext a b
    rw [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases h : b = l
    · rw [if_pos h, if_pos h]; exact key a
    · rw [if_neg h, if_neg h, hA, Matrix.of_apply]
  have hvec : (A *ᵥ (fun i => lam i j)) = fun k => ∑ i, (lam i j) • A k i := by
    funext k
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [← hmat, hvec, Matrix.det_updateCol_sum]
  simp [smul_eq_mul, mul_comm]

/-- **The projected orbit rows lie in the projected span.**  If every orbit vector
`orbit q A P k` (`k : Fin m`) lies in the `ℚ(x)`-span of the family `v : Fin t → ℚ[X]^m`, then
the projection `b ↦ orbit q A P (k0 a) (V b)` of the row `k0 a` lies in the span of the
projected family `b ↦ v i (V b)`.  (Apply the linear map `x ↦ x ∘ V` to a linear
combination.) -/
theorem lamCramer_rowMem {m r t : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) (V : Fin r → Fin m) (k0 : Fin r → Fin m)
    (v : Fin t → Fin m → Polynomial ℚ)
    (hvspan : ∀ k : Fin m,
      (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (k:ℕ) j)) ∈
        Submodule.span (RatFunc ℚ) (Set.range (fun i : Fin t => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j)))) :
    ∀ a : Fin r,
      (fun b : Fin r => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (k0 a) (V b))) ∈
        Submodule.span (RatFunc ℚ) (Set.range (fun i : Fin t => fun b : Fin r => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i (V b)))) := by
  intro a
  let π : (Fin m → RatFunc ℚ) →ₗ[RatFunc ℚ] (Fin r → RatFunc ℚ) :=
    { toFun := fun x b => x (V b)
      map_add' := by intro x y; funext b; rfl
      map_smul' := by intro c x; funext b; rfl }
  have hmem : (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (k0 a) j)) ∈
      Submodule.span (RatFunc ℚ) (Set.range (fun i : Fin t => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j))) :=
    hvspan (k0 a)
  change π (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (k0 a) j)) ∈
      Submodule.span (RatFunc ℚ) (Set.range (fun i : Fin t => fun b : Fin r => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i (V b))))
  refine Submodule.span_induction (p := fun x _ => π x ∈ Submodule.span (RatFunc ℚ)
      (Set.range (fun i : Fin t => fun b : Fin r => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i (V b))))) ?_ ?_ ?_ ?_ hmem
  · rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp
  · intro x y hx hy hx' hy'
    rw [map_add]
    exact Submodule.add_mem _ hx' hy'
  · intro c x hx hx'
    rw [map_smul]
    exact Submodule.smul_mem _ c hx'

/-- **Selecting bounded rows.**  Let `V : Fin r → Fin m`, `v : Fin t → ℚ[X]^m` and let
`W : Fin r → Fin r → K` be a family of independent rows each of which lies in the span of the
projected vectors `b ↦ v i (V b)`.  Then some injective `J : Fin r → Fin t` makes the
`r × r` matrix `(v (J a) (V b))` invertible.

The span hypothesis forces the projected vectors to span `K^r`; hence the `r × t` matrix
`Y a i = v i (V a)` has rank `r`, and `exists_det_submatrix_ne_zero` extracts `J`.  The
extracted submatrix is the transpose of `(v (J a) (V b))`. -/
theorem lamCramer_pick {K : Type*} [Field K] {m r t : ℕ} (V : Fin r → Fin m)
    (v : Fin t → Fin m → K) (W : Fin r → Fin r → K)
    (hW : ∀ a, (fun b : Fin r => W a b) ∈
      Submodule.span K (Set.range (fun i : Fin t => fun b : Fin r => v i (V b))))
    (hWli : LinearIndependent K (fun a => fun b => W a b)) :
    ∃ J : Fin r → Fin t, Function.Injective J ∧
      (Matrix.of (fun a b : Fin r => v (J a) (V b))).det ≠ 0 := by
  classical
  have hWtop : Submodule.span K (Set.range (fun a : Fin r => fun b : Fin r => W a b)) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank' hWli (by simp)
  have hle : Submodule.span K (Set.range (fun a : Fin r => fun b : Fin r => W a b)) ≤
      Submodule.span K (Set.range (fun i : Fin t => fun b : Fin r => v i (V b))) :=
    Submodule.span_le.mpr fun x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact hW a
  have htop : Submodule.span K (Set.range (fun i : Fin t => fun b : Fin r => v i (V b))) = ⊤ :=
    top_le_iff.mp (hWtop ▸ hle)
  set Y : Matrix (Fin r) (Fin t) K := Matrix.of (fun a i => v i (V a)) with hY
  have hYcol : Set.range Y.col = Set.range (fun i : Fin t => fun b : Fin r => v i (V b)) := by congr 1
  have hYrank : Y.rank = r := by
    rw [Matrix.rank_eq_finrank_span_cols, hYcol, htop]
    simp
  obtain ⟨J, hJinj, hJdet⟩ := exists_det_submatrix_ne_zero Y hYrank
  refine ⟨J, hJinj, ?_⟩
  have hm : (Matrix.of (fun a b : Fin r => v (J a) (V b))) = (Y.submatrix id J)ᵀ := by
    ext a b
    simp [hY, Matrix.submatrix_apply]
  rw [hm, Matrix.det_transpose]
  exact hJdet

theorem lam_cramer (m : ℕ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ) (hq : q ≠ 0) :
    ∃ N : ℕ, ∀ (P : Fin m → Polynomial ℚ) (r : ℕ) (V k0 : Fin r → Fin m)
      (lam : Fin r → Fin m → RatFunc ℚ),
      (Matrix.of (fun a b : Fin r => orbit q A P (k0 a) (V b))).det ≠ 0 →
      (∀ k, k < m → ∀ j, ((orbit q A P k j : Polynomial ℚ) : RatFunc ℚ)
          = ∑ l, lam l j * ((orbit q A P k (V l) : Polynomial ℚ) : RatFunc ℚ)) →
      ∃ Q : Fin r → Fin m → Polynomial ℚ,
        (∀ a j, (Q a j).natDegree ≤ N) ∧
        (Matrix.of (fun a b : Fin r => ((Q a (V b) : Polynomial ℚ) : RatFunc ℚ))).det ≠ 0 ∧
        (∀ l j, (Matrix.of (fun a b : Fin r => ((Q a (V b) : Polynomial ℚ) : RatFunc ℚ))).det * lam l j
          = (Matrix.of (fun a b : Fin r => ((Q a (if b = l then j else V b) : Polynomial ℚ) : RatFunc ℚ))).det) := by
  obtain ⟨c, hc⟩ := bounded_basis m q hq A
  refine ⟨c, ?_⟩
  intro P r V k0 lam hdet hrel
  -- the `Λ`-stable prefix of the orbit and a bounded-degree basis of its span
  obtain ⟨t, ht_le, hLI, hclos, hspan_eq⟩ := orbit_prefix m q A P
  obtain ⟨v, hvdeg, hvspan⟩ := hc t (fun a j => orbit q A P (a : ℕ) j) hLI hclos
  -- every orbit vector with index `< m` lies in the span of `v`
  have hv_all : ∀ k : Fin m,
      (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (k:ℕ) j)) ∈
        Submodule.span (RatFunc ℚ) (Set.range (fun i : Fin t => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j))) := by
    intro k
    rw [hvspan, hspan_eq]
    exact Submodule.subset_span ⟨k, rfl⟩
  -- the orbit rows lie in the span of the projected `v`
  have hrow := lamCramer_rowMem q A P V k0 v hv_all
  -- the orbit rows are independent, since the `(k0, V)`-minor is invertible
  have hWli : LinearIndependent (RatFunc ℚ)
      (fun a : Fin r => fun b : Fin r => ((orbit q A P (k0 a) (V b) : Polynomial ℚ) : RatFunc ℚ)) := by
    have hmapd : ((Matrix.of (fun a b : Fin r => orbit q A P (k0 a) (V b))).map
        (algebraMap (Polynomial ℚ) (RatFunc ℚ))).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      intro h
      exact hdet (RatFunc.algebraMap_injective ℚ (by simpa using h))
    exact Matrix.linearIndependent_rows_of_det_ne_zero hmapd
  -- select the rows
  obtain ⟨J, _hJinj, hJdet⟩ := lamCramer_pick V
    (fun i j => ((v i j : Polynomial ℚ) : RatFunc ℚ))
    (fun a b => ((orbit q A P (k0 a) (V b) : Polynomial ℚ) : RatFunc ℚ)) hrow hWli
  -- the `lam`-relation holds on the whole span of the first `m` orbit vectors
  have hWmem : ∀ w : Fin m → RatFunc ℚ,
      w ∈ Submodule.span (RatFunc ℚ) (Set.range (fun k : Fin m => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (k:ℕ) j))) →
      ∀ j, w j = ∑ l, lam l j * w (V l) := by
    intro w hw j
    refine Submodule.span_induction (p := fun x _ => x j = ∑ l, lam l j * x (V l)) ?_ ?_ ?_ ?_ hw
    · rintro x ⟨k, rfl⟩
      exact hrel (k:ℕ) k.isLt j
    · simp
    · intro x y hx hy hx' hy'
      rw [Pi.add_apply, hx', hy', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Pi.add_apply]; ring
    · intro a x hx hx'
      rw [Pi.smul_apply, hx', smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]; ring
  have hQW : ∀ a j, ((v (J a) j : Polynomial ℚ) : RatFunc ℚ)
      = ∑ l, lam l j * ((v (J a) (V l) : Polynomial ℚ) : RatFunc ℚ) := by
    intro a j
    have hmem : (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v (J a) j)) ∈
        Submodule.span (RatFunc ℚ) (Set.range (fun k : Fin m => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (k:ℕ) j))) := by
      rw [← hspan_eq, ← hvspan]
      exact Submodule.subset_span ⟨J a, rfl⟩
    exact hWmem _ hmem j
  refine ⟨fun a j => v (J a) j, fun a j => hvdeg (J a) j, ?_, ?_⟩
  · simpa using hJdet
  · intro l j
    exact lamCramer_cramer V lam (fun a j => v (J a) j) hQW l j

end Work.ZeroEst
