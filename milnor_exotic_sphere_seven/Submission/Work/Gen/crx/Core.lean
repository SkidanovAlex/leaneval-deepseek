import Mathlib
import Submission.Work.Gen.eSymClass
import Submission.Work.Whitney.ChernRelSeries
import Submission.Work.Whitney.convSeries_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Chern-root expansion: the algebraic core

`Work.Gen.eSymC n t k` is the `k`-th elementary symmetric class of a family of degree-`2` classes
`t : Fin n → H²(P;ℤ)`, and `Work.LerayHirsch.convSeries` is the convolution of the even series
`x, y : (i : ℕ) → H^{2i}(P;ℤ)`.  The target of the accompanying module is the identity

  `eSymC n (fun i => t i + x) n = convSeries (fun k => eSymC n t k) (zPow x) n`,

i.e. the expansion `∏_i (t_i + x) = Σ_k e_k(t) x^{n-k}` of the top elementary symmetric class.

This module contains the algebraic core of the proof:

* the `Work.Whitney.cupChern` cast calculus (`cupChern_cast_left/right`, `cupChern_assoc`,
  `cupChern_series_eq`) and the additivity of `cupChern` over a finite sum;
* `convTerm_zPow_succ`/`convTerm_zPow_top`: the summands of the convolution of a series with the
  powers `zPow x` of a degree-`2` class;
* `convSeries_zPow_succ`: **the recursion of the convolution with `zPow x`**,
  `convSeries E (zPow x) (n+1) = convSeries E (zPow x) n ⌣ x + E (n+1)`;
* `shiftSeries` and `convSeries_shiftSeries`: **the shift rule**,
  `convSeries (shiftSeries E a) (zPow x) (n+1)
      = convSeries E (zPow x) (n+1) + a ⌣ convSeries E (zPow x) n`.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The cast calculus of `cupChern` -/

/-- The degree cast in the left argument of the graded product. -/
theorem cupChern_cast_left {a a' b : ℕ} (h : 2 * a = 2 * a') (x : Coh ℤ (2 * a) B)
    (y : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a' b (cohTransport h x) y
      = cohTransport (by omega : 2 * (a + b) = 2 * (a' + b)) (Work.Whitney.cupChern a b x y) := by
  rw [Work.Whitney.cupChern_def, Work.Whitney.cupChern_def, Work.LerayHirsch.cupH'_cast_left]
  refine (Work.Whitney.cohTransport_trans _ _ _).trans
    ((Work.LerayHirsch.cohTransport_congr_proof _ _).trans
      (Work.Whitney.cohTransport_trans _ _ _).symm)

/-- The degree cast in the right argument of the graded product. -/
theorem cupChern_cast_right {a b b' : ℕ} (h : 2 * b' = 2 * b) (x : Coh ℤ (2 * a) B)
    (y : Coh ℤ (2 * b') B) :
    Work.Whitney.cupChern a b x (cohTransport h y)
      = cohTransport (by omega : 2 * (a + b') = 2 * (a + b)) (Work.Whitney.cupChern a b' x y) := by
  rw [Work.Whitney.cupChern_def, Work.Whitney.cupChern_def, Work.LerayHirsch.cupH'_cast_right]
  refine (Work.Whitney.cohTransport_trans _ _ _).trans
    ((Work.LerayHirsch.cohTransport_congr_proof _ _).trans
      (Work.Whitney.cohTransport_trans _ _ _).symm)

/-- **Associativity of the graded product.** -/
theorem cupChern_assoc (a b c : ℕ) (u : Coh ℤ (2 * a) B) (v : Coh ℤ (2 * b) B)
    (w : Coh ℤ (2 * c) B) :
    Work.Whitney.cupChern (a + b) c (Work.Whitney.cupChern a b u v) w
      = cohTransport (by omega : 2 * (a + (b + c)) = 2 * ((a + b) + c))
          (Work.Whitney.cupChern a (b + c) u (Work.Whitney.cupChern b c v w)) := by
  simp only [Work.Whitney.cupChern_def]
  rw [Work.LerayHirsch.cupH'_cast_left]
  rw [Work.LerayHirsch.cupH'_cast_right]
  rw [Work.LerayHirsch.cupH'_assoc_symm]
  rw [Work.LerayHirsch.eqRec_eq_cohTransport]
  simp only [Work.Whitney.cohTransport_trans]

/-- **The value of a series at a transported index.** -/
theorem cupChern_series_eq {E : (i : ℕ) → Coh ℤ (2 * i) B} {a b b' : ℕ} (h : b = b')
    (u : Coh ℤ (2 * a) B) :
    Work.Whitney.cupChern a b u (E b)
      = cohTransport (by omega : 2 * (a + b') = 2 * (a + b))
          (Work.Whitney.cupChern a b' u (E b')) := by
  have hb : E b = cohTransport (congrArg (fun t : ℕ => 2 * t) h).symm (E b') :=
    Work.Whitney.apply_cohTransport h E
  rw [hb, cupChern_cast_right]

/-- **The graded product is additive in a finite sum of its first arguments.** -/
theorem cupChern_sum_left {ι : Type} (a b : ℕ) (s : Finset ι) (f : ι → Coh ℤ (2 * a) B)
    (y : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b (∑ i ∈ s, f i) y
      = ∑ i ∈ s, Work.Whitney.cupChern a b (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Work.LerayHirsch.cupChern_zero_left]
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his, Work.Whitney.ChernRel.cupChern_add_left, ih]

/-! ## The summands of the convolution with the powers of `x` -/

/-- **The summands of the convolution with the powers of `x`.** -/
theorem convTerm_zPow_succ (E : (i : ℕ) → Coh ℤ (2 * i) B) (x : Coh ℤ 2 B) {n i : ℕ}
    (hi : i ≤ n) :
    Work.LerayHirsch.convTerm E (Work.Whitney.ChernRel.zPow x) (n + 1) i
      = Work.Whitney.cupChern n 1
          (Work.LerayHirsch.convTerm E (Work.Whitney.ChernRel.zPow x) n i) x := by
  have h1 : i ≤ n + 1 := by omega
  rw [Work.Whitney.ChernRel.convTerm_eq_cupChern (x := E)
        (y := Work.Whitney.ChernRel.zPow x) (k := n + 1) (i := i) h1,
    Work.Whitney.ChernRel.convTerm_eq_cupChern (x := E)
        (y := Work.Whitney.ChernRel.zPow x) (k := n) (i := i) hi]
  rw [cupChern_cast_left (a := i + (n - i)) (a' := n) (b := 1)
    (h := congrArg (fun t : ℕ => 2 * t) (Nat.add_sub_of_le hi))
    (x := Work.Whitney.cupChern i (n - i) (E i) (Work.Whitney.ChernRel.zPow x (n - i))) (y := x)]
  rw [cupChern_assoc]
  rw [← Work.Whitney.ChernRel.zPow_succ x (n - i)]
  rw [cupChern_series_eq (E := Work.Whitney.ChernRel.zPow x) (a := i) (b := n - i + 1)
    (b' := n + 1 - i) (by omega)]
  rw [Work.Whitney.cohTransport_trans]
  rw [Work.Whitney.cohTransport_trans]

/-- **The top summand of the convolution with the powers of `x`.** -/
theorem convTerm_zPow_top (E : (i : ℕ) → Coh ℤ (2 * i) B) (x : Coh ℤ 2 B) (n : ℕ) :
    Work.LerayHirsch.convTerm E (Work.Whitney.ChernRel.zPow x) (n + 1) (n + 1) = E (n + 1) := by
  have hsub : n + 1 - (n + 1) = 0 := Nat.sub_self _
  have hS : Work.Whitney.ChernRel.zPow x (n + 1 - (n + 1))
      = cohTransport (congrArg (fun t : ℕ => 2 * t) hsub).symm
          (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) := by
    rw [Work.Whitney.apply_cohTransport hsub (Work.Whitney.ChernRel.zPow x),
      Work.Whitney.ChernRel.zPow_zero]
  rw [Work.LerayHirsch.convTerm_pos (le_refl (n + 1)), hS,
    Work.LerayHirsch.cupH'_cast_right, Work.Cohomology.cupH'_one_right]
  simp only [Work.Whitney.cohTransport_trans]
  exact (Work.LerayHirsch.cohTransport_congr_proof _ rfl).trans (Work.Thom.cohTransport_rfl _)

/-! ## The recursion of the convolution with the powers of `x` -/

/-- **The recursion of the convolution with the powers of `x`**:
`convSeries E (zPow x) (n+1) = convSeries E (zPow x) n ⌣ x + E (n+1)`. -/
theorem convSeries_zPow_succ (E : (i : ℕ) → Coh ℤ (2 * i) B) (x : Coh ℤ 2 B) (n : ℕ) :
    Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow x) (n + 1)
      = Work.Whitney.cupChern n 1
          (Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow x) n) x + E (n + 1) := by
  unfold Work.LerayHirsch.convSeries
  rw [Finset.sum_range_succ]
  have htop : Work.LerayHirsch.convTerm E (Work.Whitney.ChernRel.zPow x) (n + 1) (n + 1)
      = E (n + 1) := convTerm_zPow_top E x n
  have hsum : (∑ i ∈ Finset.range (n + 1),
        Work.LerayHirsch.convTerm E (Work.Whitney.ChernRel.zPow x) (n + 1) i)
      = Work.Whitney.cupChern n 1
          (∑ i ∈ Finset.range (n + 1),
            Work.LerayHirsch.convTerm E (Work.Whitney.ChernRel.zPow x) n i) x := by
    rw [cupChern_sum_left]
    exact Finset.sum_congr rfl fun i hi =>
      (convTerm_zPow_succ (E := E) (x := x) (n := n) (i := i)
        (by have := Finset.mem_range.mp hi; omega))
  rw [htop, hsum]

end

end Work.Gen

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- **The convolution in degree `0`** is the degree-`0` coefficient of the first series. -/
theorem convSeries_zero (E S : (i : ℕ) → Coh ℤ (2 * i) B)
    (hS : S 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) :
    Work.LerayHirsch.convSeries E S 0 = E 0 := by
  unfold Work.LerayHirsch.convSeries
  rw [Finset.sum_range_one, Work.LerayHirsch.convTerm_pos (le_refl 0), hS,
    Work.Cohomology.cupH'_one_right]
  exact (Work.LerayHirsch.cohTransport_congr_proof _ rfl).trans (Work.Thom.cohTransport_rfl _)

/-- **The shift of a series by a degree-`2` class `a`**: the series `(1 + a t)·E`, i.e.
`shiftSeries E a 0 = E 0` and `shiftSeries E a (k+1) = E (k+1) + a ⌣ E k`. -/
noncomputable def shiftSeries (E : (i : ℕ) → Coh ℤ (2 * i) B) (a : Coh ℤ 2 B) :
    (i : ℕ) → Coh ℤ (2 * i) B
  | 0 => E 0
  | k + 1 => E (k + 1) + cohTransport (by omega : 2 * (1 + k) = 2 * (k + 1))
      (Work.Whitney.cupChern 1 k a (E k))

theorem shiftSeries_zero (E : (i : ℕ) → Coh ℤ (2 * i) B) (a : Coh ℤ 2 B) :
    shiftSeries E a 0 = E 0 := rfl

theorem shiftSeries_succ (E : (i : ℕ) → Coh ℤ (2 * i) B) (a : Coh ℤ 2 B) (k : ℕ) :
    shiftSeries E a (k + 1) = E (k + 1) + cohTransport (by omega : 2 * (1 + k) = 2 * (k + 1))
      (Work.Whitney.cupChern 1 k a (E k)) := rfl

/-- **Associativity of the graded product with a shifted summand**: combines the degree cast out
of the first argument with the reassociation `(u ⌣ v) ⌣ w = u ⌣ (v ⌣ w)`. -/
theorem cupChern_assoc_cast (b c : ℕ) (u : Coh ℤ 2 B) (v : Coh ℤ (2 * b) B)
    (w : Coh ℤ (2 * c) B) (h : 2 * (1 + b) = 2 * (b + 1)) :
    Work.Whitney.cupChern (b + 1) c (cohTransport h (Work.Whitney.cupChern 1 b u v)) w
      = cohTransport (by omega : 2 * (1 + (b + c)) = 2 * ((b + 1) + c))
          (Work.Whitney.cupChern 1 (b + c) u (Work.Whitney.cupChern b c v w)) := by
  rw [cupChern_cast_left, cupChern_assoc]
  simp only [Work.Whitney.cohTransport_trans]

/-- **The shift rule for the convolution with the powers of `x`.** -/
theorem convSeries_shiftSeries (E : (i : ℕ) → Coh ℤ (2 * i) B) (a x : Coh ℤ 2 B) (n : ℕ) :
    Work.LerayHirsch.convSeries (shiftSeries E a) (Work.Whitney.ChernRel.zPow x) (n + 1)
      = Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow x) (n + 1)
        + cohTransport (by omega : 2 * (1 + n) = 2 * (n + 1))
            (Work.Whitney.cupChern 1 n a
              (Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow x) n)) := by
  induction n with
  | zero =>
      rw [convSeries_zPow_succ (shiftSeries E a) x 0, convSeries_zPow_succ E x 0, shiftSeries_succ]
      rw [show Work.LerayHirsch.convSeries (shiftSeries E a) (Work.Whitney.ChernRel.zPow x) 0
            = Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow x) 0 from by
        rw [convSeries_zero (shiftSeries E a) (Work.Whitney.ChernRel.zPow x)
              (Work.Whitney.ChernRel.zPow_zero x),
            convSeries_zero E (Work.Whitney.ChernRel.zPow x)
              (Work.Whitney.ChernRel.zPow_zero x),
            shiftSeries_zero]]
      rw [convSeries_zero E (Work.Whitney.ChernRel.zPow x) (Work.Whitney.ChernRel.zPow_zero x)]
      simp only [Work.Whitney.ChernRel.cohTransport_self]
      abel
  | succ n ih =>
      rw [convSeries_zPow_succ (shiftSeries E a) x (n + 1), ih,
        Work.Whitney.ChernRel.cupChern_add_left, cupChern_assoc_cast, shiftSeries_succ,
        convSeries_zPow_succ E x (n + 1)]
      simp only [convSeries_zPow_succ (E := E) (x := x) (n := n),
        Work.Whitney.ChernRel.cupChern_add_left, Work.Whitney.ChernRel.cupChern_add_right,
        Work.Whitney.ChernRel.cohTransport_add, Work.Whitney.ChernRel.cohTransport_self]
      abel

/-! ## The recursion of `eSymC` in the top degree, normalised -/

/-- **The recursion of `eSymC` in the top degree**, with the degree cast normalised so that it
matches `Work.Gen.shiftSeries_succ`. -/
theorem eSymC_succ_top {P : Type} [TopologicalSpace P] {n : ℕ}
    (u : Fin (n + 1) → Coh ℤ 2 P) :
    Work.Gen.eSymC (P := P) (n + 1) u (n + 1)
      = Work.Gen.eSymC (P := P) n (fun i => u (Fin.castSucc i)) (n + 1)
        + cohTransport (by omega : 2 * (1 + n) = 2 * (n + 1))
            (Work.Whitney.cupChern 1 n (u (Fin.last n))
              (Work.Gen.eSymC (P := P) n (fun i => u (Fin.castSucc i)) n)) := by
  have h := Work.Gen.eSymC_succ (P := P) u (n + 1)
  rw [dif_pos (by omega : 1 ≤ n + 1)] at h
  rw [h]
  refine congrArg (fun z => Work.Gen.eSymC (P := P) n (fun i => u (Fin.castSucc i)) (n + 1) + z) ?_
  exact (Work.LerayHirsch.cohTransport_congr_proof _ _).trans rfl

/-- **The general recursion of `eSymC`**, normalised so that the degree cast matches
`Work.Gen.shiftSeries_succ`. -/
theorem eSymC_succ_shiftSeries {P : Type} [TopologicalSpace P] {n : ℕ}
    (u : Fin (n + 1) → Coh ℤ 2 P) (k : ℕ) :
    Work.Gen.eSymC (P := P) (n + 1) u (k + 1)
      = Work.Gen.eSymC (P := P) n (fun i => u (Fin.castSucc i)) (k + 1)
        + cohTransport (by omega : 2 * (1 + k) = 2 * (k + 1))
            (Work.Whitney.cupChern 1 k (u (Fin.last n))
              (Work.Gen.eSymC (P := P) n (fun i => u (Fin.castSucc i)) k)) := by
  have h := Work.Gen.eSymC_succ (P := P) u (k + 1)
  rw [dif_pos (by omega : 1 ≤ k + 1)] at h
  rw [h]
  refine congrArg (fun z =>
    Work.Gen.eSymC (P := P) n (fun i => u (Fin.castSucc i)) (k + 1) + z) ?_
  exact (Work.LerayHirsch.cohTransport_congr_proof _ _).trans rfl

/-- **The `eSymC` series of an extended family is the shift of the series.** -/
theorem eSymC_eq_shiftSeries {P : Type} [TopologicalSpace P] {n : ℕ}
    (u : Fin (n + 1) → Coh ℤ 2 P) :
    (fun k => Work.Gen.eSymC (P := P) (n + 1) u k)
      = Work.Gen.shiftSeries (fun k => Work.Gen.eSymC (P := P) n
            (fun i => u (Fin.castSucc i)) k) (u (Fin.last n)) := by
  funext k
  cases k with
  | zero =>
      rw [Work.Gen.shiftSeries_zero, Work.Gen.eSymC_zero_index, Work.Gen.eSymC_zero_index]
  | succ k => rw [eSymC_succ_shiftSeries, Work.Gen.shiftSeries_succ]

end

end Work.Gen
