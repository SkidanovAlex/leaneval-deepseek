/-
  `opVal` is the fibrewise operator attached to a test `t = (i, m, l)` of a state `σ`:
  `opVal c σ t = yOpSt c σ.B t.m (testPoly σ t.i)`, the ordered iterate of the one-step
  determinants `detOpSt c σ.B l' = detOp c (hFun B) (pivFun B) (yDir p l')` with multiplicities
  `t.m l'`, applied to the `t.i`-th polynomial of the flatness family `σ.Φ`.

  A test is *valid* when its source index is in range and its multi-index vanishes in all the
  pivot directions `(σ.B.get a).2` of the state. This file proves that an invalid test has
  vanishing operator value — the easy half of the bookkeeping that makes the flat leaf of a
  state well behaved.

  The two mechanisms are exactly the two ways validity can fail:
  * out of range source: `testPoly σ t.i = (σ.Φ[t.i]?).getD 0 = 0`, and the iterated operator
    kills `0` because a determinant with a zero row is zero (`detOp_zero`);
  * a pivot direction `l = (σ.B.get a).2` carrying a nonzero multiplicity: then the iterate
    applies `detOpSt c σ.B l` at least once, and that operator is identically zero because
    the derivation in direction `l` occurs twice among the columns of the determinant
    (`detOp_eq_zero_of_mem_range`). Whatever the outer directions do, they all map `0` to `0`
    (again `detOp_zero`).
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Operators.detOp_eq_zero_of_mem_range
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-! ## §1. Iterated maps and the fold over `List.finRange` -/

/-- An element fixed by `g` is fixed by every iterate of `g`. -/
private lemma iterate_eq_self {α : Type*} (g : α → α) (x : α) (hg : g x = x) (n : ℕ) :
    (g^[n]) x = x := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hg]

/-- If every `g i` fixes `x`, then so does the right fold of the iterated maps with
multiplicities `m` applied to `x`. -/
private lemma foldr_iterate_const {ι α : Type*} (L : List ι) (g : ι → α → α) (m : ι → ℕ)
    (x : α) (hg : ∀ i, g i x = x) :
    L.foldr (fun i a => (g i)^[m i] a) x = x := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldr_cons, ih]
    exact iterate_eq_self (g a) x (hg a) (m a)

/-- If some index `l` of the list carries a nonzero multiplicity and its map `g l` is constant
equal to `x`, then the whole fold (with an arbitrary seed) has value `x`: the inner part of the
fold is killed by `g l`, and every outer map fixes `x`. -/
private lemma foldr_iterate_kill {ι α : Type*} (L : List ι) (g : ι → α → α) (m : ι → ℕ)
    (x seed : α) (hg : ∀ i, g i x = x) (l : ι) (hl : l ∈ L) (hm : m l ≠ 0)
    (hgl : ∀ y, g l y = x) :
    L.foldr (fun i a => (g i)^[m i] a) seed = x := by
  induction L with
  | nil => exact absurd hl (by simp)
  | cons a as ih =>
    rw [List.foldr_cons]
    show (g a)^[m a] (as.foldr (fun i a => (g i)^[m i] a) seed) = x
    rcases List.mem_cons.mp hl with hla | hl
    · have hma : m a ≠ 0 := hla ▸ hm
      have hga : ∀ y, g a y = x := hla ▸ hgl
      obtain ⟨n, hn⟩ : ∃ n, m a = n + 1 := ⟨m a - 1, by omega⟩
      rw [hn, Function.iterate_succ_apply']
      exact hga _
    · rw [ih hl]
      exact iterate_eq_self (g a) x (hg a) (m a)

/-! ## §2. The determinant operators -/

/-- The symbolic derivative kills the zero polynomial. -/
private lemma eaD_zero {k r : ℕ} (c : EAChain k r) (i : Fin k) :
    eaD c i (0 : EAPoly k r) = 0 := by simp [eaD]

/-- `detOp` of the zero polynomial vanishes: the last row of the determinant is zero. -/
private lemma detOp_zero {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) :
    detOp c h ι l (0 : EAPoly k r) = 0 := by
  unfold detOp
  refine Matrix.det_eq_zero_of_row_eq_zero (i := Fin.last j) ?_
  intro b
  simp [Fin.lastCases_last, eaD, MvPolynomial.pderiv]

/-- The one-step fibrewise operator vanishes when its direction is a pivot direction of the
state: the two columns with derivative `∂_l` coincide. -/
private lemma detOpSt_eq_zero_of_piv {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (l : Fin q)
    (hl : ∃ a : Fin B.length, (B.get a).2 = l) (ψ : EAPoly (p + q) r) :
    detOpSt c B l ψ = 0 := by
  obtain ⟨a, ha⟩ := hl
  refine Work.WilE5.Operators.detOp_eq_zero_of_mem_range c (hFun B) (pivFun B) (yDir p l)
    ⟨a, ?_⟩ ψ
  show yDir p (B.get a).2 = yDir p l
  rw [ha]

/-- The one-step fibrewise operator of a zero polynomial vanishes. -/
private lemma detOpSt_zero {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (l : Fin q) :
    detOpSt c B l (0 : EAPoly (p + q) r) = 0 :=
  detOp_zero c (hFun B) (pivFun B) (yDir p l)

/-! ## §3. The iterated fibrewise operator of a test -/

/-- `yOpSt` of the zero polynomial vanishes. -/
private lemma yOpSt_zero {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (m : Fin q → ℕ) :
    yOpSt c B m (0 : EAPoly (p + q) r) = 0 := by
  unfold yOpSt
  exact foldr_iterate_const (List.finRange q) (fun l => detOpSt c B l) m 0
    (fun l => detOpSt_zero c B l)

/-- `yOpSt` vanishes whenever the multi-index is nonzero in some pivot direction of the
state. -/
private lemma yOpSt_eq_zero_of_piv {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (m : Fin q → ℕ) (ψ : EAPoly (p + q) r)
    (h : ∃ a : Fin B.length, m (B.get a).2 ≠ 0) :
    yOpSt c B m ψ = 0 := by
  obtain ⟨a, ha⟩ := h
  unfold yOpSt
  exact foldr_iterate_kill (List.finRange q) (fun l => detOpSt c B l) m 0 ψ
    (fun l => detOpSt_zero c B l) (B.get a).2 (List.mem_finRange _) ha
    (fun y => detOpSt_eq_zero_of_piv c B (B.get a).2 ⟨a, rfl⟩ y)

/-! ## §4. The main statement -/

theorem opVal_eq_zero_of_not_valid {p q r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (σ : Work.WilE5.St p q r) (t : Work.WilE5.Test q) (h : ¬ Work.WilE5.valid σ t) :
    Work.WilE5.opVal c σ t = 0 := by
  by_cases hi : t.i < σ.Φ.length
  · -- the source is in range, so validity fails through a pivot direction
    have hpiv : ∃ a : Fin σ.B.length, t.m (σ.B.get a).2 ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h ⟨hi, hc⟩
    unfold opVal
    exact yOpSt_eq_zero_of_piv c σ.B t.m (testPoly σ t.i) hpiv
  · -- the source index is out of range, so the source polynomial is `0`
    have hpoly : testPoly σ t.i = 0 := by
      unfold testPoly
      rw [List.getElem?_eq_none (by omega)]
      rfl
    unfold opVal
    rw [hpoly]
    exact yOpSt_zero c σ.B t.m

end Work.WilE5.Strat
