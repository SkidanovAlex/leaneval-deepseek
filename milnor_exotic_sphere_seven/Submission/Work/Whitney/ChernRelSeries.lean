import Mathlib
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Whitney.cupChern_one_right

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Series bookkeeping for the Chern relation

This module collects the cast bookkeeping and the bridge lemmas between
`Work.LerayHirsch.convTerm` (the summand of the convolution of two even-degree series) and the
graded product `Work.Whitney.cupChern`, together with the congruence lemmas of the convolution.

It is the base of `Submission/Work/Whitney/convSeries_twoTerm_geo.lean`, whose target is the
telescoping identity

  `convSeries (twoTermSeries z) (convSeries u (geoSeriesOf z)) (k+1) = u (k+1)`.
-/

namespace Work.Whitney.ChernRel

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The two inverse laws of the degree cast -/

/-- The cast `cohTransport h` followed by `cohTransport h.symm` is the identity. -/
theorem cohTransport_symm_apply {n n' : ℕ} (h : n = n') (y : Coh ℤ n' B) :
    cohTransport h (cohTransport h.symm y) = y := by
  rw [Work.Whitney.cohTransport_trans]
  exact (Work.LerayHirsch.cohTransport_congr_proof _ rfl).trans (cohTransport_rfl y)

/-- The cast `cohTransport h.symm` followed by `cohTransport h` is the identity. -/
theorem cohTransport_apply_symm {n n' : ℕ} (h : n = n') (x : Coh ℤ n B) :
    cohTransport h.symm (cohTransport h x) = x := by
  rw [Work.Whitney.cohTransport_trans]
  exact (Work.LerayHirsch.cohTransport_congr_proof _ rfl).trans (cohTransport_rfl x)

/-- The cast of `Work.Thom.cohTransport` is additive. -/
theorem cohTransport_add {n n' : ℕ} (h : n = n') (x y : Coh ℤ n B) :
    cohTransport h (x + y) = cohTransport h x + cohTransport h y :=
  map_add (cohTransportLM h) x y

/-- The cast of `Work.Thom.cohTransport` is additive. -/
theorem cohTransport_neg {n n' : ℕ} (h : n = n') (x : Coh ℤ n B) :
    cohTransport h (-x) = -cohTransport h x :=
  map_neg (cohTransportLM h) x

/-- The cast of `Work.Thom.cohTransport` is additive. -/
theorem cohTransport_zero {n n' : ℕ} (h : n = n') :
    cohTransport (B := B) h (0 : Coh ℤ n B) = 0 :=
  map_zero (cohTransportLM h)

/-! ## The degree cast applied to a series

The series of this development are *dependent* families `(t : ℕ) → Coh ℤ (2 * t) B`, so replacing
the index `a` by an equal index `b` is not a `rw` (the two types `Coh ℤ (2*a) B` and `Coh ℤ (2*b) B`
are only propositionally equal): the cast has to be made explicit.  The lemmas below are the two
directions of that statement. -/

/-- **The degree cast of a series**: for a dependent family `v : (t : ℕ) → Coh ℤ (F t) B` and
`h : a = b`, the transport of `v a` along `F a = F b` is `v b`. -/
theorem cohTransport_series {F : ℕ → ℕ} (v : (t : ℕ) → Coh ℤ (F t) B) {a b : ℕ} (h : a = b) :
    cohTransport (congrArg F h) (v a) = v b := by
  cases h
  rw [cohTransport_rfl]

/-- **The degree cast of an even series**: `cohTransport (2*a = 2*b) (v a) = v b` for `h : a = b`. -/
theorem series_cast (v : (t : ℕ) → Coh ℤ (2 * t) B) {a b : ℕ} (h : a = b) :
    cohTransport (congrArg (fun t => 2 * t) h) (v a) = v b :=
  cohTransport_series v h

/-- **The inverse form of the degree cast of an even series**: `v a` is the transport of `v b`
back along `2*b = 2*a`. -/
theorem series_cast_symm (v : (t : ℕ) → Coh ℤ (2 * t) B) {a b : ℕ} (h : a = b) :
    v a = cohTransport (congrArg (fun t => 2 * t) h).symm (v b) := by
  have h1 := series_cast v h
  have h2 := congrArg
    (fun t => cohTransport (B := B) (congrArg (fun t => 2 * t) h).symm t) h1
  rwa [cohTransport_apply_symm] at h2

/-! ## The summand of the convolution is the graded product -/

/-- **The summand of the convolution is the graded product** `Work.Whitney.cupChern`: for `i ≤ k`,
`Work.LerayHirsch.convTerm x y k i` is `x i ⌣ y (k - i)`, the only difference being the degree
bookkeeping `2*i + 2*(k-i) = 2*k`. -/
theorem convTerm_eq_cupChern {x y : (i : ℕ) → Coh ℤ (2 * i) B} {k i : ℕ} (h : i ≤ k) :
    Work.LerayHirsch.convTerm x y k i
      = cohTransport (congrArg (fun t : ℕ => 2 * t) (Nat.add_sub_of_le h))
          (Work.Whitney.cupChern i (k - i) (x i) (y (k - i))) := by
  rw [Work.LerayHirsch.convTerm_pos h, Work.Whitney.cupChern_def, Work.Whitney.cohTransport_trans]

/-! ## Congruence of the convolution -/

/-- The convolution `convSeries x y k` only depends on the values `y j` for `j ≤ k`. -/
theorem convSeries_congr_right (x : (i : ℕ) → Coh ℤ (2 * i) B)
    {y y' : (i : ℕ) → Coh ℤ (2 * i) B} {k : ℕ}
    (h : ∀ j, j ≤ k → y j = y' j) :
    Work.LerayHirsch.convSeries x y k = Work.LerayHirsch.convSeries x y' k := by
  unfold Work.LerayHirsch.convSeries Work.LerayHirsch.convTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hik : i ≤ k
  · rw [dif_pos hik, dif_pos hik, h (k - i) (by omega)]
  · rw [dif_neg hik, dif_neg hik]

/-- The convolution `convSeries x y k` only depends on the values `x i` for `i ≤ k`. -/
theorem convSeries_congr_left {x x' : (i : ℕ) → Coh ℤ (2 * i) B}
    (y : (i : ℕ) → Coh ℤ (2 * i) B) {k : ℕ}
    (h : ∀ i, i ≤ k → x i = x' i) :
    Work.LerayHirsch.convSeries x y k = Work.LerayHirsch.convSeries x' y k := by
  unfold Work.LerayHirsch.convSeries Work.LerayHirsch.convTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hik : i ≤ k
  · rw [dif_pos hik, dif_pos hik, h i hik]
  · rw [dif_neg hik, dif_neg hik]

end

end Work.Whitney.ChernRel
