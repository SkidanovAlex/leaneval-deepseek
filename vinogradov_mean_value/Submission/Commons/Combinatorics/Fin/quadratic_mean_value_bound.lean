import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.ExpLog.sum_Icc_one_div_le_log_add_one
import Submission.Commons.Data.Int.sum_gcd_div_max_bound
import Submission.Commons.Data.Int.card_signed_pair_le

open scoped BigOperators

set_option autoImplicit false

/-!
# The `k = 2` elementary mean-value bound

We prove: for every `s ≥ 3` there is a constant `C > 0` such that for all
`X ≥ 1`, the number of pairs `(x, y)` of `s`-tuples with entries in `[1, X]`
whose first and second power sums agree is at most
`C · X^(2s-3) · (1 + log(X+1))`.
-/

namespace Commons.Combinatorics.Fin

noncomputable section
open Classical

/-- An `n`-tuple with integer entries in `[1,X]`. -/
abbrev IntBox (n X : ℕ) := Fin n → Finset.Icc (1 : ℤ) (X : ℤ)
/-- An `n`-tuple with natural entries in `[1,X]`. -/
abbrev NatBox (n X : ℕ) := Fin n → Finset.Icc 1 X
/-- a single integer entry of the box `[1,X]` -/
abbrev BoxE (X : ℕ) := Finset.Icc (1 : ℤ) (X : ℤ)

/-- First moment (sum) over a tuple. -/
def s1 {n X : ℕ} (x : IntBox n X) : ℤ := ∑ i, (x i).1
/-- Second moment (sum of squares) over a tuple. -/
def s2 {n X : ℕ} (x : IntBox n X) : ℤ := ∑ i, ((x i).1) ^ 2

/-- Matching pairs of integer `s`-tuples (equal first and second moments). -/
def Sol (s X : ℕ) : Finset (IntBox s X × IntBox s X) :=
  (Finset.univ.filter (fun xy : IntBox s X × IntBox s X =>
    s1 xy.1 = s1 xy.2 ∧ s2 xy.1 = s2 xy.2))

/-- The count of matching pairs as a real number. -/
def J (s X : ℕ) : ℝ := ((Sol s X).card : ℝ)

/-- Fibre of the moment map over the value `(m,q)`. -/
def fib (s X : ℕ) (m q : ℤ) : ℕ :=
  ((Finset.univ.filter (fun x : IntBox s X => s1 x = m ∧ s2 x = q)).card)

/-- Range of the first moment of an `s`-tuple with entries in `[1,X]`. -/
def R1 (s X : ℕ) : Finset ℤ := Finset.Icc (s : ℤ) (s * (X : ℤ))
/-- Range of the second moment of an `s`-tuple with entries in `[1,X]`. -/
def R2 (s X : ℕ) : Finset ℤ := Finset.Icc (s : ℤ) (s * (X : ℤ) ^ 2)


/-- bounds of a boxed entry -/
lemma entry_bounds {X : ℕ} (z : BoxE X) : (1 : ℤ) ≤ z.1 ∧ z.1 ≤ (X : ℤ) := by
  have h := z.2
  rw [Finset.mem_Icc] at h
  exact h

/-- bounds of the first moment of an s-tuple with s ≥ 1 -/
lemma s1_bounds {s X : ℕ} (hs : 1 ≤ s) (x : IntBox s X) : (s : ℤ) ≤ s1 x ∧ s1 x ≤ s * (X : ℤ) := by
  have hge : ∀ i : Fin s, (1 : ℤ) ≤ (x i).1 := fun i => (entry_bounds (x i)).1
  have hle : ∀ i : Fin s, (x i).1 ≤ (X : ℤ) := fun i => (entry_bounds (x i)).2
  constructor
  · calc
      (s : ℤ) = ∑ _i : Fin s, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin s, (x i).1 := Finset.sum_le_sum (fun i _ => hge i)
  · calc
      ∑ i : Fin s, (x i).1 ≤ ∑ _i : Fin s, (X : ℤ) := Finset.sum_le_sum (fun i _ => hle i)
      _ = s * (X : ℤ) := by simp

/-- bounds of the second moment -/
lemma s2_bounds {s X : ℕ} (hs : 1 ≤ s) (x : IntBox s X) : (s : ℤ) ≤ s2 x ∧ s2 x ≤ s * (X : ℤ) ^ 2 := by
  have h1 : ∀ i : Fin s, (1 : ℤ) ≤ (x i).1 := fun i => (entry_bounds (x i)).1
  have hX : ∀ i : Fin s, (x i).1 ≤ (X : ℤ) := fun i => (entry_bounds (x i)).2
  have hsquares1 : ∀ i : Fin s, (1 : ℤ) ≤ (x i).1 ^ 2 := by
    intro i
    nlinarith [h1 i]
  have hsquares2 : ∀ i : Fin s, (x i).1 ^ 2 ≤ (X : ℤ) ^ 2 := by
    intro i
    have h0 : 0 ≤ (x i).1 := by linarith [h1 i]
    exact pow_le_pow_left₀ h0 (hX i) 2
  constructor
  · calc
      (s : ℤ) = ∑ _i : Fin s, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin s, ((x i).1) ^ 2 := Finset.sum_le_sum (fun i _ => hsquares1 i)
  · calc
      ∑ i : Fin s, ((x i).1) ^ 2 ≤ ∑ _i : Fin s, (X : ℤ) ^ 2 := Finset.sum_le_sum (fun i _ => hsquares2 i)
      _ = s * (X : ℤ) ^ 2 := by simp

lemma s1_mem_range {s X : ℕ} (hs : 1 ≤ s) (x : IntBox s X) : s1 x ∈ R1 s X := by
  exact (Finset.mem_Icc.mpr (s1_bounds hs x))
lemma s2_mem_range {s X : ℕ} (hs : 1 ≤ s) (x : IntBox s X) : s2 x ∈ R2 s X := by
  exact (Finset.mem_Icc.mpr (s2_bounds hs x))

/-- drop the last coordinate of an (s+1)-tuple -/
def initBox {s X : ℕ} (x : IntBox (s + 1) X) : IntBox s X :=
  fun i => x (Fin.castSucc i)

/-- append a last coordinate -/
def snocBox {s X : ℕ} (x : IntBox s X) (a : BoxE X) : IntBox (s + 1) X :=
  fun j => if hj : j.val < s then x ⟨j.val, hj⟩ else a

lemma snocBox_castSucc {s X : ℕ} (x : IntBox s X) (a : BoxE X) (i : Fin s) :
    snocBox x a (Fin.castSucc i) = x i := by
  simp [snocBox, i.isLt]

lemma snocBox_last {s X : ℕ} (x : IntBox s X) (a : BoxE X) :
    snocBox x a (Fin.last s) = a := by
  simp [snocBox]

lemma initBox_snocBox {s X : ℕ} (x : IntBox s X) (a : BoxE X) :
    initBox (snocBox x a) = x := by
  ext i
  simp [initBox, snocBox_castSucc]

lemma snocBox_initBox {s X : ℕ} (x : IntBox (s + 1) X) :
    snocBox (initBox x) (x (Fin.last s)) = x := by
  ext j
  induction j using Fin.lastCases with
  | last =>
      simp [snocBox, initBox]
  | cast i =>
      simp [snocBox, initBox, snocBox_castSucc]

lemma s1_snocBox {s X : ℕ} (x : IntBox s X) (a : BoxE X) :
    s1 (snocBox x a) = s1 x + a.1 := by
  unfold s1
  rw [Fin.sum_univ_castSucc]
  simp [snocBox_castSucc, snocBox_last]

lemma s2_snocBox {s X : ℕ} (x : IntBox s X) (a : BoxE X) :
    s2 (snocBox x a) = s2 x + a.1 ^ 2 := by
  unfold s2
  rw [Fin.sum_univ_castSucc]
  simp [snocBox_castSucc, snocBox_last]

lemma s1_initBox {s X : ℕ} (x : IntBox (s + 1) X) :
    s1 (initBox x) = s1 x - (x (Fin.last s)).1 := by
  have h := s1_snocBox (initBox x) (x (Fin.last s))
  rw [snocBox_initBox] at h
  linarith

lemma s2_initBox {s X : ℕ} (x : IntBox (s + 1) X) :
    s2 (initBox x) = s2 x - (x (Fin.last s)).1 ^ 2 := by
  have h := s2_snocBox (initBox x) (x (Fin.last s))
  rw [snocBox_initBox] at h
  linarith

/-- Card of a filtered product splits as a sum over the first coordinate of fibre cards. -/
lemma product_filter_card {α β : Type} (s : Finset α) (t : Finset β)
    (Q : α → β → Prop) :
    ((s.product t).filter (fun w : α × β => Q w.1 w.2)).card =
      ∑ a ∈ s, ((t.filter (fun b : β => Q a b)).card) := by
  calc
    ((s.product t).filter (fun w : α × β => Q w.1 w.2)).card
        = ∑ w ∈ (s.product t), if Q w.1 w.2 then (1 : ℕ) else 0 := by
          rw [Finset.card_filter]
    _ = ∑ a ∈ s, ∑ b ∈ t, if Q a b then (1 : ℕ) else 0 := by
          exact Finset.sum_product s t (fun w : α × β => if Q w.1 w.2 then (1 : ℕ) else 0)
    _ = ∑ a ∈ s, ((t.filter (fun b : β => Q a b)).card) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.card_filter]

lemma fib_succ_eq_sum (s X : ℕ) (m q : ℤ) :
    (fib (s + 1) X m q : ℕ) =
      ∑ a ∈ (Finset.univ : Finset (BoxE X)), fib s X (m - a.1) (q - a.1 ^ 2) := by
  classical
  let A : Finset (IntBox (s + 1) X) :=
    (Finset.univ.filter (fun x : IntBox (s + 1) X => s1 x = m ∧ s2 x = q))
  let B : Finset (BoxE X × IntBox s X) :=
    ((Finset.univ : Finset (BoxE X)).product (Finset.univ : Finset (IntBox s X))).filter
      (fun w : BoxE X × IntBox s X => s1 w.2 = m - w.1.1 ∧ s2 w.2 = q - w.1.1 ^ 2)
  have hcardA : (fib (s + 1) X m q : ℕ) = A.card := rfl
  have hbij : A.card = B.card := by
    apply Finset.card_bij (fun x _hx => (x (Fin.last s), initBox x))
    · intro x hx
      have hxP : s1 x = m ∧ s2 x = q := by simpa [A] using hx
      simp [B]
      constructor
      · rw [s1_initBox, hxP.1]
      · rw [s2_initBox, hxP.2]
    · intro x1 hx1 x2 hx2 h
      have hf : x1 (Fin.last s) = x2 (Fin.last s) := congrArg Prod.fst h
      have hs : initBox x1 = initBox x2 := congrArg Prod.snd h
      calc
        x1 = snocBox (initBox x1) (x1 (Fin.last s)) := by rw [snocBox_initBox]
        _ = snocBox (initBox x2) (x2 (Fin.last s)) := by rw [hs, hf]
        _ = x2 := by rw [snocBox_initBox]
    · intro w hw
      refine ⟨snocBox w.2 w.1, ?_, ?_⟩
      · have hw' : w ∈ B := hw
        have hs1 : s1 w.2 = m - w.1.1 := (Finset.mem_filter.mp hw').2.1
        have hs2 : s2 w.2 = q - w.1.1 ^ 2 := (Finset.mem_filter.mp hw').2.2
        have h1 : s1 (snocBox w.2 w.1) = m := by
          rw [s1_snocBox, hs1]
          ring
        have h2 : s2 (snocBox w.2 w.1) = q := by
          rw [s2_snocBox, hs2]
          ring
        simp [A, h1, h2]
      · apply Prod.ext
        · exact snocBox_last w.2 w.1
        · exact initBox_snocBox w.2 w.1
  have hB : B.card = ∑ a ∈ (Finset.univ : Finset (BoxE X)),
      fib s X (m - a.1) (q - a.1 ^ 2) := by
    dsimp [B]
    rw [Finset.card_filter]
    calc
      (∑ w ∈ ((Finset.univ : Finset (BoxE X)).product (Finset.univ : Finset (IntBox s X))),
          if s1 w.2 = m - w.1.1 ∧ s2 w.2 = q - w.1.1 ^ 2 then (1 : ℕ) else 0)
          = ∑ a ∈ (Finset.univ : Finset (BoxE X)), ∑ x' ∈ (Finset.univ : Finset (IntBox s X)),
              if s1 x' = m - a.1 ∧ s2 x' = q - a.1 ^ 2 then (1 : ℕ) else 0 := by
            exact Finset.sum_product (Finset.univ : Finset (BoxE X)) (Finset.univ : Finset (IntBox s X))
              (fun w : BoxE X × IntBox s X =>
                if s1 w.2 = m - w.1.1 ∧ s2 w.2 = q - w.1.1 ^ 2 then (1 : ℕ) else 0)
      _ = ∑ a ∈ (Finset.univ : Finset (BoxE X)), fib s X (m - a.1) (q - a.1 ^ 2) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [fib, Finset.card_filter]
  calc
    (fib (s + 1) X m q : ℕ) = A.card := hcardA
    _ = B.card := hbij
    _ = ∑ a ∈ (Finset.univ : Finset (BoxE X)), fib s X (m - a.1) (q - a.1 ^ 2) := hB

/-- A sum over a finite set of the indicator of `a = m` collapses to evaluation. -/
lemma sum_indicator_eq (r : Finset ℤ) (a : ℤ) (ha : a ∈ r) (F : ℤ → ℝ) :
    (∑ m ∈ r, if a = m then F m else 0) = F a := by
  classical
  calc
    (∑ m ∈ r, if a = m then F m else 0) = ∑ m ∈ (r.filter (fun m => a = m)), F m := by
      rw [← Finset.sum_filter]
    _ = F a := by
      have hf : r.filter (fun m => a = m) = {a} := by
        ext m
        constructor
        · intro hm
          have hma : a = m := (Finset.mem_filter.mp hm).2
          exact Finset.mem_singleton.mpr hma.symm
        · intro hm
          have hma : m = a := Finset.mem_singleton.mp hm
          rw [Finset.mem_filter]
          constructor
          · rw [hma]
            exact ha
          · rw [hma]
      rw [hf]
      simp

/-- the moment value of a boxed `s`-tuple lies in the product range -/
lemma mom_mem_range_prod {s X : ℕ} (hs : 1 ≤ s) (x : IntBox s X) :
    (s1 x, s2 x) ∈ (R1 s X).product (R2 s X) := by
  exact Finset.mem_product.mpr ⟨s1_mem_range hs x, s2_mem_range hs x⟩

/-- The moment fibre count equals the sum over the tuples of the indicator. -/
lemma fib_eq_sum_indicator (s X : ℕ) (m q : ℤ) :
    (fib s X m q : ℝ) =
      ∑ x ∈ (Finset.univ : Finset (IntBox s X)),
        if s1 x = m ∧ s2 x = q then (1 : ℝ) else 0 := by
  change (((Finset.univ.filter (fun x : IntBox s X => s1 x = m ∧ s2 x = q)).card : ℕ) : ℝ) = _
  rw [Finset.card_eq_sum_ones]
  simp

/-- The fibre count indexed by a moment pair. -/
lemma fib2_eq_sum_indicator (s X : ℕ) (w : ℤ × ℤ) :
    (fib s X w.1 w.2 : ℝ) =
      ∑ x ∈ (Finset.univ : Finset (IntBox s X)),
        if (s1 x, s2 x) = w then (1 : ℝ) else 0 := by
  classical
  rw [fib_eq_sum_indicator s X w.1 w.2]
  apply Finset.sum_congr rfl
  intro x hx
  have hpair : (s1 x, s2 x) = w ↔ s1 x = w.1 ∧ s2 x = w.2 := by
    constructor
    · intro hh
      exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
    · intro hh
      exact Prod.ext hh.1 hh.2
  by_cases h : (s1 x, s2 x) = w
  · have hc : s1 x = w.1 ∧ s2 x = w.2 := ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    simp [h, hc]
  · have hconj : ¬ (s1 x = w.1 ∧ s2 x = w.2) := by
      intro hc
      exact h (hpair.mpr hc)
    simp [h, hconj]

/-- The number of pairs of tuples whose moments agree equals the sum over the
moment range of the square of the fibre size. -/
lemma J_eq_sum_fib_sq (s X : ℕ) (hs : 1 ≤ s) :
    J s X = ∑ m ∈ R1 s X, ∑ q ∈ R2 s X, ((fib s X m q : ℕ) : ℝ) ^ 2 := by
  classical
  let U : Finset (IntBox s X) := Finset.univ
  let P : Finset (ℤ × ℤ) := (R1 s X).product (R2 s X)
  have hmom : ∀ x : IntBox s X, (s1 x, s2 x) ∈ P := fun x => by
    exact Finset.mem_product.mpr ⟨s1_mem_range hs x, s2_mem_range hs x⟩
  -- (1) J = Σ_x fib (mom x)
  have hJ : J s X = ∑ x ∈ U, (fib s X (s1 x) (s2 x) : ℝ) := by
    calc
      J s X = ((Finset.univ.filter (fun xy : IntBox s X × IntBox s X =>
            s1 xy.1 = s1 xy.2 ∧ s2 xy.1 = s2 xy.2)).card : ℝ) := rfl
      _ = ∑ xy ∈ (Finset.univ : Finset (IntBox s X × IntBox s X)),
            if s1 xy.1 = s1 xy.2 ∧ s2 xy.1 = s2 xy.2 then (1 : ℝ) else 0 := by
            rw [Finset.card_eq_sum_ones]
            simp
      _ = ∑ x ∈ (Finset.univ : Finset (IntBox s X)), ∑ y ∈ (Finset.univ : Finset (IntBox s X)),
            if s1 x = s1 y ∧ s2 x = s2 y then (1 : ℝ) else 0 := by
            rw [← Finset.univ_product_univ]
            exact Finset.sum_product (Finset.univ : Finset (IntBox s X)) (Finset.univ : Finset (IntBox s X))
              (fun xy : IntBox s X × IntBox s X =>
                if s1 xy.1 = s1 xy.2 ∧ s2 xy.1 = s2 xy.2 then (1 : ℝ) else 0)
      _ = ∑ x ∈ (Finset.univ : Finset (IntBox s X)), (fib s X (s1 x) (s2 x) : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [fib_eq_sum_indicator s X (s1 x) (s2 x)]
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hc : s1 x = s1 y ∧ s2 x = s2 y
            · have hn : s1 y = s1 x ∧ s2 y = s2 x := ⟨hc.1.symm, hc.2.symm⟩
              rw [if_pos hc, if_pos hn]
            · have hn : ¬ (s1 y = s1 x ∧ s2 y = s2 x) := by
                intro h
                exact hc ⟨h.1.symm, h.2.symm⟩
              rw [if_neg hc, if_neg hn]
  -- (2) Σ_x fib (mom x) = Σ_{w ∈ P} fib(w)²
  have h2p : (∑ w ∈ P, (fib s X w.1 w.2 : ℝ) ^ 2) =
      ∑ x ∈ U, (fib s X (s1 x) (s2 x) : ℝ) := by
    calc
      (∑ w ∈ P, (fib s X w.1 w.2 : ℝ) ^ 2)
          = ∑ w ∈ P, (fib s X w.1 w.2 : ℝ) *
              (∑ x ∈ U, if (s1 x, s2 x) = w then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [fib2_eq_sum_indicator s X w]
            ring
      _ = ∑ w ∈ P, ∑ x ∈ U, (fib s X w.1 w.2 : ℝ) *
              (if (s1 x, s2 x) = w then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact Finset.mul_sum U (fun x => if (s1 x, s2 x) = w then (1 : ℝ) else 0) (fib s X w.1 w.2 : ℝ)
      _ = ∑ x ∈ U, ∑ w ∈ P, (fib s X w.1 w.2 : ℝ) *
              (if (s1 x, s2 x) = w then (1 : ℝ) else 0) := by
            exact Finset.sum_comm
      _ = ∑ x ∈ U, (fib s X (s1 x) (s2 x) : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hstep : (∑ w ∈ P, (fib s X w.1 w.2 : ℝ) *
                  (if (s1 x, s2 x) = w then (1 : ℝ) else 0))
                = ∑ w ∈ P, if (s1 x, s2 x) = w then (fib s X w.1 w.2 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro w hw
              by_cases h : (s1 x, s2 x) = w <;> simp [h]
            have hcol : (∑ w ∈ P, if (s1 x, s2 x) = w then (fib s X w.1 w.2 : ℝ) else 0)
                = (fib s X (s1 x) (s2 x) : ℝ) := by
              calc
                (∑ w ∈ P, if (s1 x, s2 x) = w then (fib s X w.1 w.2 : ℝ) else 0)
                    = ∑ w ∈ P.filter (fun w => (s1 x, s2 x) = w), (fib s X w.1 w.2 : ℝ) := by
                      rw [← Finset.sum_filter]
                _ = (fib s X (s1 x) (s2 x) : ℝ) := by
                      have hf : P.filter (fun w => (s1 x, s2 x) = w) = {(s1 x, s2 x)} := by
                        ext w
                        constructor
                        · intro hw
                          exact Finset.mem_singleton.mpr ((Finset.mem_filter.mp hw).2).symm
                        · intro hw
                          rw [Finset.mem_filter]
                          constructor
                          · rw [Finset.mem_singleton.mp hw]
                            exact hmom x
                          · exact (Finset.mem_singleton.mp hw).symm
                      rw [hf]
                      simp
            rw [hstep]
            exact hcol
  -- (3) rewrite the product-sum as the double sum over m and q
  calc
    J s X = ∑ x ∈ U, (fib s X (s1 x) (s2 x) : ℝ) := hJ
    _ = ∑ w ∈ P, (fib s X w.1 w.2 : ℝ) ^ 2 := h2p.symm
    _ = ∑ m ∈ R1 s X, ∑ q ∈ R2 s X, ((fib s X m q : ℕ) : ℝ) ^ 2 := by
          exact Finset.sum_product (R1 s X) (R2 s X)
            (fun w : ℤ × ℤ => ((fib s X w.1 w.2 : ℕ) : ℝ) ^ 2)


/-- the box of last entries has X elements -/
lemma card_univ_box (X : ℕ) (hX : 1 ≤ X) : (Finset.univ : Finset (BoxE X)).card = X := by
  rw [BoxE]
  simp [Int.card_Icc, hX]

/-- first moment range shifts into the range of the longer system -/
lemma mem_R1_shift {s X : ℕ} {a : BoxE X} {w : ℤ} (hw : w ∈ R1 s X) :
    w + a.1 ∈ R1 (s + 1) X := by
  rw [R1] at hw
  change w + a.1 ∈ Finset.Icc (((s + 1 : ℕ) : ℤ)) (((s + 1 : ℕ) : ℤ) * (X : ℤ))
  rw [Finset.mem_Icc] at hw ⊢
  have h1 : (s : ℤ) ≤ w := hw.1
  have h2 : w ≤ s * (X : ℤ) := hw.2
  have ha1 : (1 : ℤ) ≤ a.1 := (entry_bounds a).1
  have haX : a.1 ≤ (X : ℤ) := (entry_bounds a).2
  have hcast1 : (((s + 1 : ℕ) : ℤ)) = (s : ℤ) + 1 := by norm_num [Nat.cast_add]
  constructor
  · rw [hcast1]
    linarith [h1, ha1]
  · have hcast2 : (((s + 1 : ℕ) : ℤ) * (X : ℤ)) = s * (X : ℤ) + (X : ℤ) := by
      rw [hcast1]
      ring
    rw [hcast2]
    nlinarith [h2, haX]
lemma mem_R2_shift {s X : ℕ} {a : BoxE X} {q : ℤ} (hq : q ∈ R2 s X) :
    q + a.1 ^ 2 ∈ R2 (s + 1) X := by
  rw [R2] at hq
  change q + a.1 ^ 2 ∈ Finset.Icc (((s + 1 : ℕ) : ℤ)) (((s + 1 : ℕ) : ℤ) * (X : ℤ) ^ 2)
  rw [Finset.mem_Icc] at hq ⊢
  have h1 : (s : ℤ) ≤ q := hq.1
  have h2 : q ≤ s * (X : ℤ) ^ 2 := hq.2
  have ha1 : (1 : ℤ) ≤ a.1 := (entry_bounds a).1
  have haX : a.1 ≤ (X : ℤ) := (entry_bounds a).2
  have ha1sq : (1 : ℤ) ≤ a.1 ^ 2 := by nlinarith [ha1]
  have hcast1 : (((s + 1 : ℕ) : ℤ)) = (s : ℤ) + 1 := by norm_num [Nat.cast_add]
  constructor
  · rw [hcast1]
    linarith [h1, ha1sq]
  · have hcast2 : (((s + 1 : ℕ) : ℤ) * (X : ℤ) ^ 2) = s * (X : ℤ) ^ 2 + (X : ℤ) ^ 2 := by
      rw [hcast1]
      ring
    rw [hcast2]
    nlinarith [h2, haX]
/-- summing a function supported on S over a shifted-in index set -/
lemma sum_shift_support {T S : Finset ℤ} (a : ℤ) (f : ℤ → ℝ)
    (hshift : ∀ w ∈ S, w + a ∈ T) (hsupp : ∀ m ∈ T, m - a ∉ S → f (m - a) = 0) :
    (∑ m ∈ T, f (m - a)) = ∑ w ∈ S, f w := by
  classical
  let F : Finset ℤ := T.filter (fun m => m - a ∈ S)
  have h1 : (∑ m ∈ T, f (m - a)) = ∑ m ∈ F, f (m - a) := by
    calc
      (∑ m ∈ T, f (m - a)) = ∑ m ∈ T, (if m - a ∈ S then f (m - a) else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        by_cases h : m - a ∈ S
        · simp [h]
        · simp [h, hsupp m hm h]
      _ = ∑ m ∈ F, f (m - a) := by
        rw [Finset.sum_filter]
  have himg : F.image (fun m => m - a) = S := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_image.mp hw with ⟨m, hmF, hmw⟩
      have hmS : m - a ∈ S := (Finset.mem_filter.mp hmF).2
      rwa [← hmw]
    · intro hw
      apply Finset.mem_image.mpr
      refine ⟨w + a, ?_, by ring⟩
      rw [Finset.mem_filter]
      exact ⟨hshift w hw, by simpa using hw⟩
  have hsi : (∑ w ∈ F.image (fun m => m - a), f w) = ∑ m ∈ F, f (m - a) := by
    exact Finset.sum_image (s := F) (g := fun m => m - a) (f := f)
      (by intro x hx y hy hxy; linarith)
  calc
    (∑ m ∈ T, f (m - a)) = ∑ m ∈ F, f (m - a) := h1
    _ = ∑ w ∈ F.image (fun m => m - a), f w := hsi.symm
    _ = ∑ w ∈ S, f w := by rw [himg]
/-- an s-tuple fibre is empty when the first moment is out of range -/
lemma fib_eq_zero_of_s1_nmem {s X : ℕ} (hs : 1 ≤ s) (m q : ℤ) (hm : m ∉ R1 s X) :
    fib s X m q = 0 := by
  classical
  have he : (Finset.univ.filter (fun x : IntBox s X => s1 x = m ∧ s2 x = q)) = ∅ := by
    ext x
    constructor
    · intro hx
      have hs1m : s1 x = m := (Finset.mem_filter.mp hx).2.1
      have hmem : m ∈ R1 s X := by
        simpa [hs1m] using s1_mem_range hs x
      exact (hm hmem).elim
    · intro hx
      simp at hx
  unfold fib
  rw [he]
  rfl

/-- an s-tuple fibre is empty when the second moment is out of range -/
lemma fib_eq_zero_of_s2_nmem {s X : ℕ} (hs : 1 ≤ s) (m q : ℤ) (hq : q ∉ R2 s X) :
    fib s X m q = 0 := by
  classical
  have he : (Finset.univ.filter (fun x : IntBox s X => s1 x = m ∧ s2 x = q)) = ∅ := by
    ext x
    constructor
    · intro hx
      have hs2q : s2 x = q := (Finset.mem_filter.mp hx).2.2
      have hmem : q ∈ R2 s X := by
        simpa [hs2q] using s2_mem_range hs x
      exact (hq hmem).elim
    · intro hx
      simp at hx
  unfold fib
  rw [he]
  rfl

/-- real-valued version of the moment-fibre convolution -/
lemma fib_succ_eq_sum_real (s X : ℕ) (m q : ℤ) :
    (fib (s + 1) X m q : ℝ) =
      ∑ a ∈ (Finset.univ : Finset (BoxE X)), (fib s X (m - a.1) (q - a.1 ^ 2) : ℝ) := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (fib_succ_eq_sum s X m q)
  rw [h]
  simp

/-- inner-shifted square sum over the bigger range equals J(s) -/
lemma sum_fib_sq_shifted_eq (s X : ℕ) (hs : 1 ≤ s) (a : BoxE X) :
    (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
        ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
      = J s X := by
  have hq : ∀ m : ℤ,
      (∑ q ∈ R2 (s + 1) X, ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
      = ∑ q' ∈ R2 s X, ((fib s X (m - a.1) q' : ℕ) : ℝ) ^ 2 := fun m =>
    sum_shift_support (a.1 ^ 2) (fun q' => ((fib s X (m - a.1) q' : ℕ) : ℝ) ^ 2)
      (fun q' hq' => mem_R2_shift hq')
      (fun q hq hn => by
        have hf0 : fib s X (m - a.1) (q - a.1 ^ 2) = 0 :=
          fib_eq_zero_of_s2_nmem hs (m - a.1) (q - a.1 ^ 2) hn
        simp [hf0])
  calc
    (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
        ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
        = ∑ m ∈ R1 (s + 1) X, ∑ q' ∈ R2 s X, ((fib s X (m - a.1) q' : ℕ) : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro m hm
          exact hq m
    _ = ∑ m' ∈ R1 s X, ∑ q' ∈ R2 s X, ((fib s X m' q' : ℕ) : ℝ) ^ 2 := by
          exact sum_shift_support a.1 (fun m' : ℤ => ∑ q' ∈ R2 s X, ((fib s X m' q' : ℕ) : ℝ) ^ 2)
            (fun m' hm' => mem_R1_shift hm')
            (fun m hm hn => by
              apply Finset.sum_eq_zero
              intro q' hq'
              have hf0 : fib s X (m - a.1) q' = 0 := fib_eq_zero_of_s1_nmem hs (m - a.1) q' hn
              simp [hf0])
    _ = J s X := (J_eq_sum_fib_sq s X hs).symm

/-- finite Fubini: moving the third of three nested sums to the front -/
lemma sum_three_comm {α β γ : Type} (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c)
      = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  classical
  calc
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c)
        = ∑ a ∈ s, ∑ p ∈ t.product u, f a p.1 p.2 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact (Finset.sum_product (s := t) (t := u) (f := fun p : β × γ => f a p.1 p.2)).symm
    _ = ∑ p ∈ t.product u, ∑ a ∈ s, f a p.1 p.2 := by
          exact Finset.sum_comm (s := s) (t := t.product u)
            (f := fun (a : α) (p : β × γ) => f a p.1 p.2)
    _ = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c := by
          exact (Finset.sum_product (s := t) (t := u)
            (f := fun p : β × γ => ∑ a ∈ s, f a p.1 p.2))
    _ = ∑ p ∈ u.product s, ∑ b ∈ t, f p.2 b p.1 := by
          calc
            (∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c) = ∑ b ∈ t, ∑ p ∈ u.product s, f p.2 b p.1 := by
              apply Finset.sum_congr rfl
              intro b hb
              exact (Finset.sum_product (s := u) (t := s) (f := fun p : γ × α => f p.2 b p.1)).symm
            _ = ∑ p ∈ u.product s, ∑ b ∈ t, f p.2 b p.1 := by
              exact Finset.sum_comm (s := t) (t := u.product s)
                (f := fun (b : β) (p : γ × α) => f p.2 b p.1)
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
          exact (Finset.sum_product (s := u) (t := s)
            (f := fun p : γ × α => ∑ b ∈ t, f p.2 b p.1))

/-- Adding one coordinate multiplies the number of solutions by at most `X²`. -/
lemma J_succ_le_X_sq_mul (s X : ℕ) (hs : 1 ≤ s) (hX : 1 ≤ X) :
    J (s + 1) X ≤ (X : ℝ) ^ 2 * J s X := by
  classical
  have hs1 : 1 ≤ s + 1 := by omega
  have hcard : (Finset.univ : Finset (BoxE X)).card = X := card_univ_box X hX
  have hJ1 := J_eq_sum_fib_sq (s + 1) X hs1
  have hineq : ∀ m q : ℤ,
      ((fib (s + 1) X m q : ℕ) : ℝ) ^ 2 ≤
        (X : ℝ) * ∑ a ∈ (Finset.univ : Finset (BoxE X)),
          ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2 := fun m q => by
    have hfib := fib_succ_eq_sum_real s X m q
    rw [hfib]
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (BoxE X)))
      (f := fun a => (fib s X (m - a.1) (q - a.1 ^ 2) : ℝ))
    rw [hcard] at hcs
    simpa using hcs
  calc
    J (s + 1) X = ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X, ((fib (s + 1) X m q : ℕ) : ℝ) ^ 2 := hJ1
    _ ≤ ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
          (X : ℝ) * ∑ a ∈ (Finset.univ : Finset (BoxE X)),
            ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro m hm
          apply Finset.sum_le_sum
          intro q hq
          exact hineq m q
    _ = (X : ℝ) * ∑ a ∈ (Finset.univ : Finset (BoxE X)),
          ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
            ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2 := by
          calc
            (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                (X : ℝ) * ∑ a ∈ (Finset.univ : Finset (BoxE X)),
                  ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
                = ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                    ∑ a ∈ (Finset.univ : Finset (BoxE X)),
                      (X : ℝ) * ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  apply Finset.sum_congr rfl
                  intro q hq
                  exact (Finset.mul_sum (s := (Finset.univ : Finset (BoxE X)))
                    (f := fun a : BoxE X => ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
                    (a := (X : ℝ)))
            _ = ∑ a ∈ (Finset.univ : Finset (BoxE X)),
                ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                  (X : ℝ) * ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2 := by
                  exact sum_three_comm (R1 (s + 1) X) (R2 (s + 1) X)
                    (Finset.univ : Finset (BoxE X))
                    (fun m q a =>
                      (X : ℝ) * ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
            _ = (X : ℝ) * ∑ a ∈ (Finset.univ : Finset (BoxE X)),
                ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                  ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2 := by
                  have hinner : ∀ a ∈ (Finset.univ : Finset (BoxE X)),
                      (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                        (X : ℝ) * ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
                      = (X : ℝ) * (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                          ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2) := by
                    intro a ha
                    calc
                      (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                          (X : ℝ) * ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
                          = ∑ m ∈ R1 (s + 1) X,
                              (X : ℝ) * (∑ q ∈ R2 (s + 1) X,
                                ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2) := by
                            apply Finset.sum_congr rfl
                            intro m hm
                            exact (Finset.mul_sum (s := R2 (s + 1) X)
                              (f := fun q : ℤ => ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
                              (a := (X : ℝ))).symm
                      _ = (X : ℝ) * (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                            ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2) := by
                            exact (Finset.mul_sum (s := R1 (s + 1) X)
                              (f := fun m : ℤ => (∑ q ∈ R2 (s + 1) X,
                                ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2))
                              (a := (X : ℝ))).symm
                  calc
                    (∑ a ∈ (Finset.univ : Finset (BoxE X)),
                        ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                          (X : ℝ) * ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2)
                        = ∑ a ∈ (Finset.univ : Finset (BoxE X)),
                            (X : ℝ) * (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                              ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2) := by
                          apply Finset.sum_congr rfl
                          intro a ha
                          exact hinner a ha
                    _ = (X : ℝ) * ∑ a ∈ (Finset.univ : Finset (BoxE X)),
                            ∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                              ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2 := by
                          exact (Finset.mul_sum (s := (Finset.univ : Finset (BoxE X)))
                            (f := fun a : BoxE X =>
                              (∑ m ∈ R1 (s + 1) X, ∑ q ∈ R2 (s + 1) X,
                                ((fib s X (m - a.1) (q - a.1 ^ 2) : ℕ) : ℝ) ^ 2))
                            (a := (X : ℝ))).symm
    _ = (X : ℝ) * ∑ a ∈ (Finset.univ : Finset (BoxE X)), J s X := by
          apply congrArg (fun z : ℝ => (X : ℝ) * z)
          apply Finset.sum_congr rfl
          intro a ha
          exact sum_fib_sq_shifted_eq s X hs a
    _ = (X : ℝ) ^ 2 * J s X := by
          rw [Finset.sum_const, hcard]
          ring

/-- Iterated dimension raising from `s = 3`. -/
lemma J_le_pow_two_mul (s X : ℕ) (hs : 3 ≤ s) (hX : 1 ≤ X) :
    J s X ≤ (X : ℝ) ^ (2 * (s - 3)) * J 3 X := by
  classical
  have hmain : ∀ k : ℕ, J (3 + k) X ≤ (X : ℝ) ^ (2 * k) * J 3 X := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hJsucc := J_succ_le_X_sq_mul (3 + k) X (by omega) hX
        calc
          J (3 + (k + 1)) X ≤ (X : ℝ) ^ 2 * J (3 + k) X := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hJsucc
          _ ≤ (X : ℝ) ^ 2 * ((X : ℝ) ^ (2 * k) * J 3 X) := by
            exact mul_le_mul_of_nonneg_left ih (by positivity)
          _ = ((X : ℝ) ^ 2 * (X : ℝ) ^ (2 * k)) * J 3 X := by
            ring
          _ = (X : ℝ) ^ (2 * (k + 1)) * J 3 X := by
            have hpow : (X : ℝ) ^ 2 * (X : ℝ) ^ (2 * k) = (X : ℝ) ^ (2 * (k + 1)) := by
              rw [← pow_add]
              congr 1
              omega
            rw [hpow]
  have hs' : s = 3 + (s - 3) := by omega
  have hleft : J s X = J (3 + (s - 3)) X := congrArg (fun t : ℕ => J t X) hs'
  rw [hleft]
  exact hmain (s - 3)


def V (X : ℕ) (xy : IntBox 3 X × IntBox 3 X) : Fin 3 → ℤ :=
  fun i => (xy.1 i).1 + (xy.2 i).1
def U (X : ℕ) (xy : IntBox 3 X × IntBox 3 X) : Fin 3 → ℤ :=
  fun i => (xy.1 i).1 - (xy.2 i).1
def c0 (X : ℕ) (xy : IntBox 3 X × IntBox 3 X) : ℤ := (V X xy 0) - (V X xy 2)
def c1 (X : ℕ) (xy : IntBox 3 X × IntBox 3 X) : ℤ := (V X xy 1) - (V X xy 2)

lemma u_val_le {X : ℕ} (hX : 1 ≤ X) (xy : IntBox 3 X × IntBox 3 X) (i : Fin 3) :
    (U X xy i).natAbs ≤ X - 1 := by
  have h1 : (1 : ℤ) ≤ (xy.1 i).1 := (entry_bounds (xy.1 i)).1
  have h2 : (xy.1 i).1 ≤ (X : ℤ) := (entry_bounds (xy.1 i)).2
  have h3 : (1 : ℤ) ≤ (xy.2 i).1 := (entry_bounds (xy.2 i)).1
  have h4 : (xy.2 i).1 ≤ (X : ℤ) := (entry_bounds (xy.2 i)).2
  dsimp [U]
  have habs : |(xy.1 i).1 - (xy.2 i).1| ≤ (X : ℤ) - 1 := by
    have hneg : -(((X : ℤ) - 1)) ≤ (xy.1 i).1 - (xy.2 i).1 := by linarith
    have hpos : (xy.1 i).1 - (xy.2 i).1 ≤ (X : ℤ) - 1 := by linarith
    exact abs_le.mpr ⟨hneg, hpos⟩
  have hcast : ((((xy.1 i).1 - (xy.2 i).1).natAbs : ℤ)) = |(xy.1 i).1 - (xy.2 i).1| := by
    rw [Int.abs_eq_natAbs]
  have hsub : ((X - 1 : ℕ) : ℤ) = (X : ℤ) - 1 := by
    rw [Nat.cast_sub hX]
    norm_num
  have hc : (((xy.1 i).1 - (xy.2 i).1).natAbs : ℤ) ≤ ((X - 1 : ℕ) : ℤ) := by
    rw [hcast, hsub]
    exact habs
  exact_mod_cast hc

lemma v_val_bounds {X : ℕ} (hX : 1 ≤ X) (xy : IntBox 3 X × IntBox 3 X) (i : Fin 3) :
    (2 : ℤ) ≤ (V X xy i) ∧ (V X xy i) ≤ 2 * (X : ℤ) := by
  have h1 : (1 : ℤ) ≤ (xy.1 i).1 := (entry_bounds (xy.1 i)).1
  have h2 : (xy.1 i).1 ≤ (X : ℤ) := (entry_bounds (xy.1 i)).2
  have h3 : (1 : ℤ) ≤ (xy.2 i).1 := (entry_bounds (xy.2 i)).1
  have h4 : (xy.2 i).1 ≤ (X : ℤ) := (entry_bounds (xy.2 i)).2
  dsimp [V]
  constructor <;> linarith

lemma sol_sumU_full (X : ℕ) {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Sol 3 X) :
    (∑ i : Fin 3, U X xy i) = 0 := by
  have hsum : s1 xy.1 = s1 xy.2 := (Finset.mem_filter.mp h).2.1
  calc
    (∑ i : Fin 3, U X xy i) = ∑ i : Fin 3, ((xy.1 i).1 - (xy.2 i).1) := rfl
    _ = (∑ i : Fin 3, (xy.1 i).1) - (∑ i : Fin 3, (xy.2 i).1) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
          dsimp [s1] at hsum
          rw [hsum]
          ring

lemma sol_sumU (X : ℕ) {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Sol 3 X) :
    (U X xy 0) + (U X xy 1) + (U X xy 2) = 0 := by
  have hfull := sol_sumU_full X h
  rw [Fin.sum_univ_three] at hfull
  simpa [add_assoc] using hfull

lemma sol_sumUV_full (X : ℕ) {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Sol 3 X) :
    (∑ i : Fin 3, (U X xy i) * (V X xy i)) = 0 := by
  have hsum : s2 xy.1 = s2 xy.2 := (Finset.mem_filter.mp h).2.2
  calc
    (∑ i : Fin 3, (U X xy i) * (V X xy i))
        = ∑ i : Fin 3, ((xy.1 i).1 ^ 2 - (xy.2 i).1 ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold U V
          ring
    _ = (∑ i : Fin 3, ((xy.1 i).1) ^ 2) - (∑ i : Fin 3, ((xy.2 i).1) ^ 2) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
          dsimp [s2] at hsum
          rw [hsum]
          ring

lemma sol_dot (X : ℕ) {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Sol 3 X) :
    (U X xy 0) * (V X xy 0) + (U X xy 1) * (V X xy 1) + (U X xy 2) * (V X xy 2) = 0 := by
  have hfull := sol_sumUV_full X h
  rw [Fin.sum_univ_three] at hfull
  simpa [add_assoc] using hfull

lemma sol_lin (X : ℕ) {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Sol 3 X) :
    (c0 X xy) * (U X xy 0) + (c1 X xy) * (U X xy 1) = 0 := by
  have hsum := sol_sumU X h
  have hdot := sol_dot X h
  unfold c0 c1
  calc
    ((V X xy 0) - (V X xy 2)) * (U X xy 0) + ((V X xy 1) - (V X xy 2)) * (U X xy 1)
        = ((U X xy 0) * (V X xy 0) + (U X xy 1) * (V X xy 1) + (U X xy 2) * (V X xy 2))
          - ((U X xy 0) + (U X xy 1) + (U X xy 2)) * (V X xy 2) := by ring
    _ = 0 := by rw [hdot, hsum]; ring

def Fib (X : ℕ) (a b : ℤ) : Finset (IntBox 3 X × IntBox 3 X) :=
  (Sol 3 X).filter (fun xy => c0 X xy = a ∧ c1 X xy = b)

lemma mem_pair_box (X : ℕ) (hX : 1 ≤ X) (xy : IntBox 3 X × IntBox 3 X) (h : xy ∈ Sol 3 X) :
    (c0 X xy, c1 X xy) ∈ (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ)).product
      (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ)) := by
  have hv0 := v_val_bounds hX xy 0
  have hv1 := v_val_bounds hX xy 1
  have hv2 := v_val_bounds hX xy 2
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · rw [Finset.mem_Icc]
    dsimp [c0]
    constructor <;> linarith
  · rw [Finset.mem_Icc]
    dsimp [c1]
    constructor <;> linarith

lemma flat_bound (X : ℕ) (hX : 1 ≤ X) :
    ((Fib X 0 0).card : ℝ) ≤ (X : ℝ) ^ 3 := by
  classical
  have hVflat : ∀ xy ∈ Fib X 0 0, ∀ i : Fin 3, (V X xy i) = (V X xy 2) := by
    intro xy hxy i
    have h0 : c0 X xy = 0 := (Finset.mem_filter.mp hxy).2.1
    have h1 : c1 X xy = 0 := (Finset.mem_filter.mp hxy).2.2
    have hV0 : V X xy 0 = V X xy 2 := by
      dsimp [c0] at h0
      linarith
    have hV1 : V X xy 1 = V X xy 2 := by
      dsimp [c1] at h1
      linarith
    fin_cases i <;> simp [hV0, hV1]
  have hV2eq : ∀ xy ∈ Fib X 0 0, (V X xy 2) * 3 = (s1 xy.1) * 2 := by
    intro xy hxy
    have hE : (∑ j : Fin 3, (xy.1 j).1) + (∑ j : Fin 3, (xy.2 j).1) = (V X xy 2) * 3 := by
      calc
        (∑ j : Fin 3, (xy.1 j).1) + (∑ j : Fin 3, (xy.2 j).1)
            = ∑ j : Fin 3, ((xy.1 j).1 + (xy.2 j).1) := by rw [← Finset.sum_add_distrib]
        _ = ∑ _j : Fin 3, (V X xy 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              change (V X xy j) = V X xy 2
              exact hVflat xy hxy j
        _ = (V X xy 2) * 3 := by simp [mul_comm]
    have hm : s1 xy.1 = s1 xy.2 :=
      (Finset.mem_filter.mp (show xy ∈ Sol 3 X from (Finset.mem_filter.mp hxy).1)).2.1
    have hE' : s1 xy.1 + s1 xy.2 = (V X xy 2) * 3 := by
      simpa [s1] using hE
    rw [hm] at hE'
    nlinarith
  have hinj : Set.InjOn (fun xy : IntBox 3 X × IntBox 3 X => xy.1) (Fib X 0 0) := by
    intro xy hxy xy' hxy' hx
    have hV2 : V X xy 2 = V X xy' 2 := by
      have h1 := hV2eq xy hxy
      have h2 := hV2eq xy' hxy'
      have hs : s1 xy.1 = s1 xy'.1 := by
        dsimp [s1]
        congr 1
        ext j
        exact congrArg (fun z : IntBox 3 X => (z j).1) hx
      have hmul : (V X xy 2) * 3 = (V X xy' 2) * 3 := by
        calc
          (V X xy 2) * 3 = (s1 xy.1) * 2 := h1
          _ = (s1 xy'.1) * 2 := by rw [hs]
          _ = (V X xy' 2) * 3 := h2.symm
      have h3ne : (3 : ℤ) ≠ 0 := by norm_num
      exact (mul_right_cancel₀ h3ne hmul)
    apply Prod.ext
    · exact hx
    · apply funext
      intro i
      have hvi : V X xy i = V X xy 2 := hVflat xy hxy i
      have hvi' : V X xy' i = V X xy' 2 := hVflat xy' hxy' i
      apply Subtype.ext
      have hsum_i : (xy.1 i).1 + (xy.2 i).1 = V X xy 2 := by
        rw [← hvi]
        rfl
      have hsum_i' : (xy'.1 i).1 + (xy'.2 i).1 = V X xy' 2 := by
        rw [← hvi']
        rfl
      have hxi : (xy.1 i).1 = (xy'.1 i).1 := congrArg (fun z : IntBox 3 X => (z i).1) hx
      linarith
  have himg : (Fib X 0 0).image (fun xy : IntBox 3 X × IntBox 3 X => xy.1)
      ⊆ (Finset.univ : Finset (IntBox 3 X)) := by
    intro x hx
    simp
  have hcard : (Fib X 0 0).card ≤ (Finset.univ : Finset (IntBox 3 X)).card := by
    calc
      (Fib X 0 0).card = ((Fib X 0 0).image (fun xy : IntBox 3 X × IntBox 3 X => xy.1)).card := by
        exact (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset (IntBox 3 X)).card := Finset.card_le_card himg
  have hcardu : (Finset.univ : Finset (IntBox 3 X)).card = X ^ 3 := by
    simp [Int.card_Icc, hX]
  calc
    ((Fib X 0 0).card : ℝ) ≤ ((Finset.univ : Finset (IntBox 3 X)).card : ℝ) := by exact_mod_cast hcard
    _ = (X : ℝ) ^ 3 := by
      rw [hcardu]
      norm_num

lemma card_multiples_nat_le (e L : ℕ) (he : e ≠ 0) :
    (((Finset.range (L + 1)).filter (fun n : ℕ => e ∣ n)).card : ℝ)
      ≤ (L : ℝ) / (e : ℝ) + 1 := by
  classical
  have hmap : (Finset.range ((L / e) + 1)).image (fun w : ℕ => e * w) =
      (Finset.range (L + 1)).filter (fun n : ℕ => e ∣ n) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨w, hw, hn0⟩
      rw [← hn0]
      have hmemw : e * w < L + 1 := by
        have hwle : w ≤ L / e := by
          have hlt : w < L / e + 1 := Finset.mem_range.mp hw
          omega
        have hmul : e * w ≤ e * (L / e) := Nat.mul_le_mul_left e hwle
        have hdiv : e * (L / e) ≤ L := Nat.mul_div_le L e
        exact Nat.lt_succ_of_le (hmul.trans hdiv)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hmemw, ⟨w, rfl⟩⟩
    · intro hn
      rcases (Finset.mem_filter.mp hn) with ⟨hmem, hdvd⟩
      rcases hdvd with ⟨w, hw⟩
      have hwle : w ≤ L / e := by
        have hlt : e * w < L + 1 := by rw [← hw]; exact Finset.mem_range.mp hmem
        have hlt' : w * e < L + 1 := by simpa [mul_comm] using hlt
        exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero he)).mpr (Nat.lt_succ_iff.mp hlt')
      apply Finset.mem_image.mpr
      exact ⟨w, Finset.mem_range.mpr (Nat.lt_succ_of_le hwle), hw.symm⟩
  calc
    (((Finset.range (L + 1)).filter (fun n : ℕ => e ∣ n)).card : ℝ)
        = ((Finset.range ((L / e) + 1)).image (fun w : ℕ => e * w)).card := by rw [← hmap]
    _ = ((Finset.range ((L / e) + 1)).card : ℝ) := by
        congr 1
        apply Finset.card_image_of_injOn
        intro a ha b hb h
        exact Nat.mul_left_cancel (Nat.pos_of_ne_zero he) h
    _ = ((L / e : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ (L : ℝ) / (e : ℝ) + 1 := by
        have hle : ((L / e : ℕ) : ℝ) ≤ (L : ℝ) / (e : ℝ) := Nat.cast_div_le
        linarith

lemma dvd_reduce_gcd {d e n : ℕ} (he : e ≠ 0) :
    (e ∣ d * n) → ((e / Nat.gcd d e) ∣ n) := by
  classical
  intro h
  let g := Nat.gcd d e
  let d' := d / g
  let e' := e / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right d (Nat.pos_of_ne_zero he)
  have hgD : g ∣ d := Nat.gcd_dvd_left d e
  have hgE : g ∣ e := Nat.gcd_dvd_right d e
  have hd : d = g * d' := by
    dsimp [d', g]
    exact (Nat.mul_div_cancel' hgD).symm
  have heq : e = g * e' := by
    dsimp [e', g]
    exact (Nat.mul_div_cancel' hgE).symm
  rcases h with ⟨k, hk⟩
  have hmain : e' ∣ d' * n := by
    have hkraw : d * n = e * k := hk
    rw [hd, heq] at hkraw
    have hg0 : g * (d' * n) = g * (e' * k) := by
      simpa [mul_assoc] using hkraw
    have hcancel : d' * n = e' * k := Nat.mul_left_cancel hgpos hg0
    exact ⟨k, hcancel⟩
  have hcop0 : Nat.Coprime d' e' := by
    dsimp [d', e', g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hcop' : Nat.Coprime e' d' := hcop0.symm
  have hres := (Nat.Coprime.dvd_mul_left hcop').mp hmain
  dsimp [e', g] at hres
  exact hres

def PairBox (X : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ)).product (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ))

lemma J_eq_sum_fib (X : ℕ) (hX : 1 ≤ X) :
    J 3 X = ∑ o ∈ PairBox X, (((Fib X o.1 o.2).card : ℕ) : ℝ) := by
  classical
  have hnat : (Sol 3 X).card = ∑ o ∈ PairBox X, (Fib X o.1 o.2).card := by
    calc
      (Sol 3 X).card = ∑ xy ∈ Sol 3 X, (1 : ℕ) := by simp
      _ = ∑ xy ∈ Sol 3 X, (∑ o ∈ PairBox X,
            if (c0 X xy = o.1 ∧ c1 X xy = o.2) then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro xy hxy
            have hint : (∑ o ∈ PairBox X,
                if (c0 X xy = o.1 ∧ c1 X xy = o.2) then (1 : ℕ) else 0) = 1 := by
              rw [← Finset.card_filter (s := PairBox X)
                (p := fun o : ℤ × ℤ => c0 X xy = o.1 ∧ c1 X xy = o.2)]
              have hf : (PairBox X).filter (fun o : ℤ × ℤ => c0 X xy = o.1 ∧ c1 X xy = o.2)
                  = {(c0 X xy, c1 X xy)} := by
                ext o
                constructor
                · intro ho
                  have hmem := (Finset.mem_filter.mp ho).2
                  apply Finset.mem_singleton.mpr
                  apply Prod.ext
                  · exact hmem.1.symm
                  · exact hmem.2.symm
                · intro ho
                  have hpair : o = (c0 X xy, c1 X xy) := Finset.mem_singleton.mp ho
                  rw [Finset.mem_filter]
                  constructor
                  · rw [hpair]
                    exact mem_pair_box X hX xy hxy
                  · rw [hpair]
                    exact ⟨rfl, rfl⟩
              rw [hf]
              simp
            exact hint.symm
      _ = ∑ o ∈ PairBox X, ∑ xy ∈ Sol 3 X,
            if (c0 X xy = o.1 ∧ c1 X xy = o.2) then (1 : ℕ) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ o ∈ PairBox X, (Fib X o.1 o.2).card := by
            apply Finset.sum_congr rfl
            intro o ho
            exact (Finset.card_filter (s := Sol 3 X)
              (p := fun xy : IntBox 3 X × IntBox 3 X => c0 X xy = o.1 ∧ c1 X xy = o.2)).symm
  calc
    J 3 X = ((Sol 3 X).card : ℝ) := rfl
    _ = ((∑ o ∈ PairBox X, (Fib X o.1 o.2).card) : ℝ) := by simpa [hnat]
    _ = ∑ o ∈ PairBox X, (((Fib X o.1 o.2).card : ℕ) : ℝ) := by simp

lemma pairbox_card_le (X : ℕ) (hX : 1 ≤ X) : (PairBox X).card ≤ 25 * X ^ 2 := by
  classical
  calc
    (PairBox X).card
        = ((Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ)).product
            (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ))).card := rfl
    _ = (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ)).card * (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ)).card := by
          exact (Finset.card_product _ _)
    _ = (4 * X + 1) * (4 * X + 1) := by
          have hc : (Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ)).card = 4 * X + 1 := by
            rw [Int.card_Icc]
            simp
            omega
          rw [hc]
    _ ≤ 25 * X ^ 2 := by
          have hle : 4 * X + 1 ≤ 5 * X := by omega
          have hle2 : (4 * X + 1) * (4 * X + 1) ≤ (5 * X) * (5 * X) := by
            exact Nat.mul_le_mul hle hle
          calc
            (4 * X + 1) * (4 * X + 1) ≤ (5 * X) * (5 * X) := hle2
            _ = 25 * X ^ 2 := by ring

lemma pairbox_erase_card_le (X : ℕ) (hX : 1 ≤ X) :
    ((PairBox X).erase (0, 0)).card ≤ 25 * X ^ 2 := by
  exact le_trans (Finset.card_le_card (Finset.erase_subset _ _)) (pairbox_card_le X hX)

lemma mem_u_range (X : ℕ) (hX : 1 ≤ X) {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Sol 3 X) :
    (U X xy 0) ∈ Finset.Icc (-((X - 1 : ℕ) : ℤ)) ((X - 1 : ℕ) : ℤ) := by
  have hle := u_val_le hX xy 0
  rw [Finset.mem_Icc]
  rw [← abs_le]
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle

lemma mem_u1_range (X : ℕ) (hX : 1 ≤ X) {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Sol 3 X) :
    (U X xy 1) ∈ Finset.Icc (-((X - 1 : ℕ) : ℤ)) ((X - 1 : ℕ) : ℤ) := by
  have hle := u_val_le hX xy 1
  rw [Finset.mem_Icc]
  rw [← abs_le]
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle

lemma inj_t_u0 {X : ℕ} (a b : ℤ) (hb : b ≠ 0) :
    Set.InjOn (fun xy : IntBox 3 X × IntBox 3 X => ((V X xy 2), (U X xy 0))) (Fib X a b) := by
  intro xy hxy xy' hxy' h
  have ht : V X xy 2 = V X xy' 2 := congrArg Prod.fst h
  have hu0 : U X xy 0 = U X xy' 0 := congrArg Prod.snd h
  have hca : c0 X xy = a := (Finset.mem_filter.mp hxy).2.1
  have hca' : c0 X xy' = a := (Finset.mem_filter.mp hxy').2.1
  have hcb : c1 X xy = b := (Finset.mem_filter.mp hxy).2.2
  have hcb' : c1 X xy' = b := (Finset.mem_filter.mp hxy').2.2
  have hV0 : V X xy 0 = V X xy' 0 := by
    have h0 : V X xy 0 - V X xy 2 = a := by dsimp [c0] at hca; linarith
    have h0' : V X xy' 0 - V X xy' 2 = a := by dsimp [c0] at hca'; linarith
    linarith
  have hV1 : V X xy 1 = V X xy' 1 := by
    have h1 : V X xy 1 - V X xy 2 = b := by dsimp [c1] at hcb; linarith
    have h1' : V X xy' 1 - V X xy' 2 = b := by dsimp [c1] at hcb'; linarith
    linarith
  have hs := sol_lin X (show xy ∈ Sol 3 X from (Finset.mem_filter.mp hxy).1)
  have hs' := sol_lin X (show xy' ∈ Sol 3 X from (Finset.mem_filter.mp hxy').1)
  have hu1 : U X xy 1 = U X xy' 1 := by
    have h1c : a * (U X xy 0) + b * (U X xy 1) = 0 := by
      rw [hca, hcb] at hs
      exact hs
    have h2c : a * (U X xy' 0) + b * (U X xy' 1) = 0 := by
      rw [hca', hcb'] at hs'
      exact hs'
    have hbeq : b * (U X xy 1) = b * (U X xy' 1) := by
      rw [hu0] at h1c
      linarith
    exact mul_left_cancel₀ hb hbeq
  have hU2 : U X xy 2 = U X xy' 2 := by
    have hsum := sol_sumU X (show xy ∈ Sol 3 X from (Finset.mem_filter.mp hxy).1)
    have hsum' := sol_sumU X (show xy' ∈ Sol 3 X from (Finset.mem_filter.mp hxy').1)
    linarith [hsum, hsum', hu0, hu1]
  have hUeq : U X xy = U X xy' := by
    ext i
    fin_cases i <;> simp [hu0, hu1, hU2]
  have hVeq : V X xy = V X xy' := by
    ext i
    fin_cases i <;> simp [hV0, hV1, ht]
  apply Prod.ext
  · apply funext
    intro i
    apply Subtype.ext
    have htwo : (2 : ℤ) ≠ 0 := by norm_num
    exact (mul_left_cancel₀ htwo (by
      have hvi : V X xy i + U X xy i = 2 * (xy.1 i).1 := by
        dsimp [V, U]
        ring
      have hvi' : V X xy' i + U X xy' i = 2 * (xy'.1 i).1 := by
        dsimp [V, U]
        ring
      calc
        2 * (xy.1 i).1 = V X xy i + U X xy i := hvi.symm
        _ = V X xy' i + U X xy' i := by rw [hVeq, hUeq]
        _ = 2 * (xy'.1 i).1 := hvi'))
  · apply funext
    intro i
    apply Subtype.ext
    have htwo : (2 : ℤ) ≠ 0 := by norm_num
    exact (mul_left_cancel₀ htwo (by
      have hvi : V X xy i - U X xy i = 2 * (xy.2 i).1 := by
        dsimp [V, U]
        ring
      have hvi' : V X xy' i - U X xy' i = 2 * (xy'.2 i).1 := by
        dsimp [V, U]
        ring
      calc
        2 * (xy.2 i).1 = V X xy i - U X xy i := hvi.symm
        _ = V X xy' i - U X xy' i := by rw [hVeq, hUeq]
        _ = 2 * (xy'.2 i).1 := hvi'))

lemma int_dvd_natAbs_iff (d : ℕ) (z : ℤ) : ((d : ℤ) ∣ z) ↔ d ∣ z.natAbs := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    rw [hk]
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  · intro h
    rcases h with ⟨w, hw⟩
    have habs : (z.natAbs : ℤ) = |z| := by
      rw [Int.abs_eq_natAbs]
    by_cases hz : 0 ≤ z
    · have haz : |z| = z := abs_of_nonneg hz
      exact ⟨(w : ℤ), by
        calc
          z = (z.natAbs : ℤ) := by
                have h1 : (z.natAbs : ℤ) = z := by
                  calc (z.natAbs : ℤ) = |z| := habs
                       _ = z := haz
                exact h1.symm
          _ = (d : ℤ) * (w : ℤ) := by rw [hw]; norm_num⟩
    · have haz : |z| = -z := abs_of_neg (by linarith)
      exact ⟨(-(w : ℤ)), by
        calc
          z = -((z.natAbs : ℤ)) := by
                have h1 : (z.natAbs : ℤ) = -z := by
                  calc (z.natAbs : ℤ) = |z| := habs
                       _ = -z := haz
                linarith
          _ = (d : ℤ) * (-(w : ℤ)) := by rw [hw]; norm_num⟩

lemma divZ_of_sol (X : ℕ) (a b : ℤ) (hb : b ≠ 0)
    {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Fib X a b) :
    (b.natAbs : ℤ) ∣ (a.natAbs : ℤ) * (U X xy 0) := by
  have hs := sol_lin X (show xy ∈ Sol 3 X from (Finset.mem_filter.mp h).1)
  have hcb : c1 X xy = b := (Finset.mem_filter.mp h).2.2
  have hca : c0 X xy = a := (Finset.mem_filter.mp h).2.1
  have hsol : a * (U X xy 0) + b * (U X xy 1) = 0 := by
    rw [hca, hcb] at hs
    exact hs
  have hdivZ : (b : ℤ) ∣ (a : ℤ) * (U X xy 0) := by
    refine ⟨- (U X xy 1), ?_⟩
    linarith
  have hnatdiv0 : b.natAbs ∣ ((a : ℤ) * (U X xy 0)).natAbs := by
    rcases hdivZ with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    calc
      ((a : ℤ) * (U X xy 0)).natAbs = ((b : ℤ) * k).natAbs := by rw [hk]
      _ = (b : ℤ).natAbs * k.natAbs := by rw [Int.natAbs_mul]
      _ = b.natAbs * k.natAbs := rfl
  have hz : ((a : ℤ) * (U X xy 0)).natAbs = a.natAbs * (U X xy 0).natAbs := by
    rw [Int.natAbs_mul]
  have hnatdiv : b.natAbs ∣ a.natAbs * (U X xy 0).natAbs := by
    rwa [hz] at hnatdiv0
  exact (int_dvd_natAbs_iff (b.natAbs) ((a.natAbs : ℤ) * (U X xy 0))).mpr (by
    have hz2 : (((a.natAbs : ℤ) * (U X xy 0)).natAbs) = a.natAbs * (U X xy 0).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [hz2]
    exact hnatdiv)

lemma u0_cond_of_sol (X : ℕ) (hX : 1 ≤ X) (a b : ℤ) (hb : b ≠ 0)
    {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Fib X a b) :
    (b.natAbs : ℤ) ∣ (a.natAbs : ℤ) * (U X xy 0) ∧
      (a.natAbs : ℤ) * (U X xy 0).natAbs ≤ ((X - 1 : ℕ) : ℤ) * (b.natAbs : ℤ) := by
  constructor
  · exact divZ_of_sol X a b hb h
  · have hs := sol_lin X (show xy ∈ Sol 3 X from (Finset.mem_filter.mp h).1)
    have hcb : c1 X xy = b := (Finset.mem_filter.mp h).2.2
    have hca : c0 X xy = a := (Finset.mem_filter.mp h).2.1
    have hsol : a * (U X xy 0) + b * (U X xy 1) = 0 := by
      rw [hca, hcb] at hs
      exact hs
    have hu1 := u_val_le hX xy 1
    have hnat0 : ((a : ℤ) * (U X xy 0)).natAbs = ((b : ℤ) * (U X xy 1)).natAbs := by
      have habs : ((a : ℤ) * (U X xy 0)) = - ((b : ℤ) * (U X xy 1)) := by linarith
      rw [habs]
      rw [Int.natAbs_neg]
    have hle0 : ((b : ℤ) * (U X xy 1)).natAbs ≤ b.natAbs * (X - 1) := by
      calc
        ((b : ℤ) * (U X xy 1)).natAbs = b.natAbs * (U X xy 1).natAbs := by
              rw [Int.natAbs_mul]
        _ ≤ b.natAbs * (X - 1) := by
              exact Nat.mul_le_mul_left b.natAbs hu1
    have hle1 : ((a : ℤ) * (U X xy 0)).natAbs ≤ b.natAbs * (X - 1) := by
      rwa [← hnat0] at hle0
    have hnat1 : ((a : ℤ) * (U X xy 0)).natAbs = a.natAbs * (U X xy 0).natAbs := by
      rw [Int.natAbs_mul]
    have hnatle : a.natAbs * (U X xy 0).natAbs ≤ (X - 1) * b.natAbs := by
      have hle1' : a.natAbs * (U X xy 0).natAbs ≤ b.natAbs * (X - 1) := by
        rwa [hnat1] at hle1
      rwa [Nat.mul_comm b.natAbs (X - 1)] at hle1'
    exact_mod_cast hnatle

def USet (X : ℕ) (a b : ℤ) : Finset ℤ :=
  (Finset.Icc (-((X - 1 : ℕ) : ℤ)) ((X - 1 : ℕ) : ℤ)).filter
    (fun u : ℤ => (b.natAbs : ℤ) ∣ (a.natAbs : ℤ) * u ∧
      (a.natAbs : ℤ) * u.natAbs ≤ ((X - 1 : ℕ) : ℤ) * (b.natAbs : ℤ))

def TRange (X : ℕ) : Finset ℤ := Finset.Icc (2 : ℤ) (2 * (X : ℤ))

lemma mem_TRange (X : ℕ) (hX : 1 ≤ X) (xy : IntBox 3 X × IntBox 3 X) :
    (V X xy 2) ∈ TRange X := by
  have hv := v_val_bounds hX xy 2
  change (V X xy 2) ∈ Finset.Icc (2 : ℤ) (2 * (X : ℤ))
  rw [Finset.mem_Icc]
  exact hv

lemma mem_USet (X : ℕ) (hX : 1 ≤ X) (a b : ℤ) (hb : b ≠ 0)
    {xy : IntBox 3 X × IntBox 3 X} (h : xy ∈ Fib X a b) :
    (U X xy 0) ∈ USet X a b := by
  have hu := mem_u_range X hX (show xy ∈ Sol 3 X from (Finset.mem_filter.mp h).1)
  have hcond := u0_cond_of_sol X hX a b hb h
  dsimp [USet]
  rw [Finset.mem_filter]
  exact ⟨hu, hcond⟩

lemma USet_card_le (X : ℕ) (hX : 1 ≤ X) (a b : ℤ) (hb : b ≠ 0) :
    ((USet X a b).card : ℝ) ≤
      2 * ((X - 1 : ℕ) : ℝ) * ((Nat.gcd a.natAbs b.natAbs : ℝ) / (max a.natAbs b.natAbs : ℝ)) + 3 := by
  have hmax : 0 < max a.natAbs b.natAbs := by
    have hb0 : 0 < b.natAbs := Int.natAbs_pos.mpr hb
    exact lt_of_lt_of_le hb0 (Nat.le_max_right a.natAbs b.natAbs)
  exact Commons.Data.Int.card_signed_pair_le (a.natAbs) (b.natAbs) (X - 1) hmax

lemma TRange_card_le (X : ℕ) (hX : 1 ≤ X) :
    ((TRange X).card : ℝ) ≤ (2 * (X : ℝ)) := by
  have hc : (Finset.Icc (2 : ℤ) (2 * (X : ℤ))).card = 2 * X - 1 := by
    rw [Int.card_Icc]
    rw [show (2 * (X : ℤ) + 1 - 2) = (2 * (X : ℤ)) - 1 by ring]
    have hpos : 0 ≤ (2 * (X : ℤ)) - 1 := by
      have hx : 1 ≤ (X : ℤ) := by exact_mod_cast hX
      linarith
    have hz := Int.toNat_of_nonneg hpos
    have hz2 : (2 * (X : ℤ)) - 1 = ((2 * X - 1 : ℕ) : ℤ) := by
      have hge : (1 : ℕ) ≤ 2 * X := by omega
      rw [Nat.cast_sub hge]
      simp [Nat.cast_mul]
    have hcast : (↑(((2 * (X : ℤ)) - 1).toNat) : ℤ) = ((2 * X - 1 : ℕ) : ℤ) := by
      rw [← hz2]
      exact hz
    exact_mod_cast hcast
  calc
    ((TRange X).card : ℝ) = (((2 * X - 1 : ℕ)) : ℝ) := by rw [TRange, hc]
    _ ≤ (2 * (X : ℝ)) := by
          rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ 2 * X)]
          norm_num

lemma fiber_bound_nonzero_b (X : ℕ) (hX : 1 ≤ X) (a b : ℤ) (hb : b ≠ 0) :
    ((Fib X a b).card : ℝ) ≤
      (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
        ((Nat.gcd a.natAbs b.natAbs : ℝ) / (max a.natAbs b.natAbs : ℝ)) + 3) := by
  classical
  let A := Fib X a b
  let B := (TRange X).product (USet X a b)
  let φ : IntBox 3 X × IntBox 3 X → ℤ × ℤ := fun xy => ((V X xy 2), (U X xy 0))
  have hinj : Set.InjOn φ (A : Set (IntBox 3 X × IntBox 3 X)) := by
    simpa [A, φ] using (inj_t_u0 (X := X) a b hb)
  have himg : A.image φ ⊆ B := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨xy, hxy, hp0⟩
    rw [← hp0]
    have hxyA : xy ∈ Fib X a b := by simpa [A] using hxy
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact mem_TRange X hX xy
    · exact mem_USet X hX a b hb hxyA
  have hcardnat : A.card ≤ B.card := by
    calc
      A.card = (A.image φ).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ B.card := Finset.card_le_card himg
  have htr := TRange_card_le X hX
  have hus := USet_card_le X hX a b hb
  have hB : (B.card : ℝ) ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
      ((Nat.gcd a.natAbs b.natAbs : ℝ) / (max a.natAbs b.natAbs : ℝ)) + 3) := by
    calc
      (B.card : ℝ) = ((((TRange X).card * (USet X a b).card) : ℕ) : ℝ) := by
            congr 1
            dsimp [B]
            exact (Finset.card_product (TRange X) (USet X a b))
      _ = ((TRange X).card : ℝ) * ((USet X a b).card : ℝ) := by norm_num
      _ ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
          ((Nat.gcd a.natAbs b.natAbs : ℝ) / (max a.natAbs b.natAbs : ℝ)) + 3) := by
            exact mul_le_mul htr hus (by positivity) (by positivity)
  calc
    ((Fib X a b).card : ℝ) = (A.card : ℝ) := rfl
    _ ≤ (B.card : ℝ) := by exact_mod_cast hcardnat
    _ ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
        ((Nat.gcd a.natAbs b.natAbs : ℝ) / (max a.natAbs b.natAbs : ℝ)) + 3) := hB


lemma inj_t_u1 {X : ℕ} (a : ℤ) (ha : a ≠ 0) :
    Set.InjOn (fun xy : IntBox 3 X × IntBox 3 X => ((V X xy 2), (U X xy 1))) (Fib X a 0) := by
  intro xy hxy xy' hxy' h
  have ht : V X xy 2 = V X xy' 2 := congrArg Prod.fst h
  have hu1 : U X xy 1 = U X xy' 1 := congrArg Prod.snd h
  have hca : c0 X xy = a := (Finset.mem_filter.mp hxy).2.1
  have hca' : c0 X xy' = a := (Finset.mem_filter.mp hxy').2.1
  have hcb : c1 X xy = 0 := (Finset.mem_filter.mp hxy).2.2
  have hcb' : c1 X xy' = 0 := (Finset.mem_filter.mp hxy').2.2
  have hs := sol_lin X (show xy ∈ Sol 3 X from (Finset.mem_filter.mp hxy).1)
  have hs' := sol_lin X (show xy' ∈ Sol 3 X from (Finset.mem_filter.mp hxy').1)
  have hu0 : U X xy 0 = 0 := by
    have h1 : a * (U X xy 0) + 0 * (U X xy 1) = 0 := by
      rw [hca, hcb] at hs
      exact hs
    have hmu : a * (U X xy 0) = 0 := by linarith
    rcases mul_eq_zero.mp hmu with ha0 | hz0
    · exact False.elim (ha ha0)
    · exact hz0
  have hu0' : U X xy' 0 = 0 := by
    have h1 : a * (U X xy' 0) + 0 * (U X xy' 1) = 0 := by
      rw [hca', hcb'] at hs'
      exact hs'
    have hmu : a * (U X xy' 0) = 0 := by linarith
    rcases mul_eq_zero.mp hmu with ha0 | hz0
    · exact False.elim (ha ha0)
    · exact hz0
  have hU2 : U X xy 2 = U X xy' 2 := by
    have hsum := sol_sumU X (show xy ∈ Sol 3 X from (Finset.mem_filter.mp hxy).1)
    have hsum' := sol_sumU X (show xy' ∈ Sol 3 X from (Finset.mem_filter.mp hxy').1)
    linarith [hsum, hsum', hu0, hu0', hu1]
  have hUeq : U X xy = U X xy' := by
    ext i
    fin_cases i <;> simp [hu0, hu0', hu1, hU2]
  have hV0 : V X xy 0 = V X xy' 0 := by
    have h0 : V X xy 0 - V X xy 2 = a := by dsimp [c0] at hca; linarith
    have h0' : V X xy' 0 - V X xy' 2 = a := by dsimp [c0] at hca'; linarith
    linarith
  have hV1 : V X xy 1 = V X xy' 1 := by
    have h1 : V X xy 1 - V X xy 2 = 0 := by dsimp [c1] at hcb; linarith
    have h1' : V X xy' 1 - V X xy' 2 = 0 := by dsimp [c1] at hcb'; linarith
    linarith
  have hVeq : V X xy = V X xy' := by
    ext i
    fin_cases i <;> simp [hV0, hV1, ht]
  apply Prod.ext
  · apply funext
    intro i
    apply Subtype.ext
    have htwo : (2 : ℤ) ≠ 0 := by norm_num
    exact (mul_left_cancel₀ htwo (by
      have hvi : V X xy i + U X xy i = 2 * (xy.1 i).1 := by
        dsimp [V, U]
        ring
      have hvi' : V X xy' i + U X xy' i = 2 * (xy'.1 i).1 := by
        dsimp [V, U]
        ring
      calc
        2 * (xy.1 i).1 = V X xy i + U X xy i := hvi.symm
        _ = V X xy' i + U X xy' i := by rw [hVeq, hUeq]
        _ = 2 * (xy'.1 i).1 := hvi'))
  · apply funext
    intro i
    apply Subtype.ext
    have htwo : (2 : ℤ) ≠ 0 := by norm_num
    exact (mul_left_cancel₀ htwo (by
      have hvi : V X xy i - U X xy i = 2 * (xy.2 i).1 := by
        dsimp [V, U]
        ring
      have hvi' : V X xy' i - U X xy' i = 2 * (xy'.2 i).1 := by
        dsimp [V, U]
        ring
      calc
        2 * (xy.2 i).1 = V X xy i - U X xy i := hvi.symm
        _ = V X xy' i - U X xy' i := by rw [hVeq, hUeq]
        _ = 2 * (xy'.2 i).1 := hvi'))

lemma Icc_card_le_two_L_add_three (L : ℕ) :
    ((Finset.Icc (-((L : ℕ) : ℤ)) ((L : ℕ) : ℤ)).card : ℝ) ≤ 2 * (L : ℝ) + 3 := by
  have hc : (Finset.Icc (-((L : ℕ) : ℤ)) ((L : ℕ) : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    have hZ0 : (((L : ℕ) : ℤ) + 1 - (-((L : ℕ) : ℤ))) = 2 * ((L : ℕ) : ℤ) + 1 := by ring
    rw [hZ0]
    have hcast : (2 * ((L : ℕ) : ℤ) + 1) = (((2 * L + 1 : ℕ) : ℤ)) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring
    rw [hcast]
    exact Int.toNat_natCast (2 * L + 1)
  calc
    ((Finset.Icc (-((L : ℕ) : ℤ)) ((L : ℕ) : ℤ)).card : ℝ) = (((2 * L + 1 : ℕ)) : ℝ) := by rw [hc]
    _ ≤ 2 * (L : ℝ) + 3 := by
          norm_num

lemma fiber_bound_b0 (X : ℕ) (hX : 1 ≤ X) (a : ℤ) (ha : a ≠ 0) :
    ((Fib X a 0).card : ℝ) ≤
      (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
        ((Nat.gcd a.natAbs 0 : ℝ) / (max a.natAbs 0 : ℝ)) + 3) := by
  classical
  let A := Fib X a 0
  let I := Finset.Icc (-((X - 1 : ℕ) : ℤ)) ((X - 1 : ℕ) : ℤ)
  let B := (TRange X).product I
  let φ : IntBox 3 X × IntBox 3 X → ℤ × ℤ := fun xy => ((V X xy 2), (U X xy 1))
  have hinj : Set.InjOn φ (A : Set (IntBox 3 X × IntBox 3 X)) := by
    simpa [A, φ] using (inj_t_u1 (X := X) a ha)
  have himg : A.image φ ⊆ B := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨xy, hxy, hp0⟩
    rw [← hp0]
    have hxyA : xy ∈ Fib X a 0 := by simpa [A] using hxy
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact mem_TRange X hX xy
    · exact mem_u1_range X hX (show xy ∈ Sol 3 X from (Finset.mem_filter.mp hxyA).1)
  have hcardnat : A.card ≤ B.card := by
    calc
      A.card = (A.image φ).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ B.card := Finset.card_le_card himg
  have htr := TRange_card_le X hX
  have hratio : (Nat.gcd a.natAbs 0 : ℝ) / (max a.natAbs 0 : ℝ) = 1 := by
    have hg : Nat.gcd a.natAbs 0 = a.natAbs := by simp
    have hmR : max (a.natAbs : ℝ) 0 = (a.natAbs : ℝ) := by
      exact max_eq_left (by positivity : 0 ≤ (a.natAbs : ℝ))
    rw [hg, hmR]
    have hnz : (a.natAbs : ℝ) ≠ 0 := by
      have hpos : 0 < (a.natAbs : ℝ) := by exact_mod_cast (Int.natAbs_pos.mpr ha)
      exact ne_of_gt hpos
    field_simp [hnz]
  have hu := Icc_card_le_two_L_add_three (X - 1)
  have hB : (B.card : ℝ) ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
      ((Nat.gcd a.natAbs 0 : ℝ) / (max a.natAbs 0 : ℝ)) + 3) := by
    calc
      (B.card : ℝ) = ((((TRange X).card * (I.card) : ℕ) : ℝ)) := by
            congr 1
            dsimp [B]
            exact (Finset.card_product (TRange X) I)
      _ = ((TRange X).card : ℝ) * ((I.card) : ℝ) := by norm_num
      _ ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) + 3) := by
            exact mul_le_mul htr hu (by positivity) (by positivity)
      _ = (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
          ((Nat.gcd a.natAbs 0 : ℝ) / (max a.natAbs 0 : ℝ)) + 3) := by
            rw [hratio]
            ring
  calc
    ((Fib X a 0).card : ℝ) = (A.card : ℝ) := rfl
    _ ≤ (B.card : ℝ) := by exact_mod_cast hcardnat
    _ ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
        ((Nat.gcd a.natAbs 0 : ℝ) / (max a.natAbs 0 : ℝ)) + 3) := hB

lemma fiber_bound (X : ℕ) (hX : 1 ≤ X) (a b : ℤ) (hp : (a, b) ≠ (0, 0)) :
    ((Fib X a b).card : ℝ) ≤
      (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
        ((Nat.gcd a.natAbs b.natAbs : ℝ) / (max a.natAbs b.natAbs : ℝ)) + 3) := by
  by_cases hb : b = 0
  · subst b
    have ha : a ≠ 0 := by
      intro ha0
      apply hp
      exact Prod.ext ha0 rfl
    simpa using fiber_bound_b0 X hX a ha
  · exact fiber_bound_nonzero_b X hX a b hb


/-- bound the gcd/max-sum over the erased pair box by the divisor-sum bound -/
lemma sum_ratio_erase_le (X : ℕ) (hX : 1 ≤ X) :
    (∑ o ∈ (PairBox X).erase (0, 0),
      ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
      ≤ 1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)) := by
  classical
  let G : Finset ℤ := Finset.Icc (-((2 * X : ℕ) : ℤ)) ((2 * X : ℕ) : ℤ)
  let rC : ℤ × ℤ → ℝ := fun o => (Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)
  let rI : ℤ × ℤ → ℝ := fun o => ((Int.gcd o.1.natAbs o.2.natAbs : ℕ) : ℝ) /
      (max o.1.natAbs o.2.natAbs : ℝ)
  have h00mem : (0, 0) ∈ PairBox X := by
    rw [PairBox]
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> linarith
    · rw [Finset.mem_Icc]
      constructor <;> linarith
  have hg00 : ∀ o : ℤ × ℤ, ((Int.gcd o.1.natAbs o.2.natAbs : ℕ) : ℝ) =
      (Nat.gcd o.1.natAbs o.2.natAbs : ℝ) := by
    intro o
    exact_mod_cast (Commons.Data.Int.int_gcd_natAbs o.1 o.2)
  have hsum_eq : (∑ o ∈ (PairBox X).erase (0, 0), rC o) = ∑ o ∈ PairBox X, rC o := by
    have h := Finset.sum_erase_add (s := PairBox X) (f := rC) (a := (0, 0)) h00mem
    have hC00 : rC (0, 0) = 0 := by simp [rC]
    rw [hC00] at h
    simpa using h
  have hsb := Commons.Data.Int.sum_gcd_div_max_bound (2 * X) (by omega : 1 ≤ 2 * X)
  calc
    (∑ o ∈ (PairBox X).erase (0, 0),
        ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
        ≤ 1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)) := by
      calc
        (∑ o ∈ (PairBox X).erase (0, 0),
            ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
            = ∑ o ∈ PairBox X, rC o := by
              change (∑ o ∈ (PairBox X).erase (0, 0), rC o) = ∑ o ∈ PairBox X, rC o
              exact hsum_eq
        _ = ∑ o ∈ PairBox X,
            (if o = (0, 0) then (0 : ℝ)
             else ((Int.gcd o.1.natAbs o.2.natAbs : ℕ) : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)) := by
              apply Finset.sum_congr rfl
              intro o ho
              by_cases h : o = (0, 0)
              · subst o
                simp [rC]
              · have hg := hg00 o
                dsimp [rC]
                rw [if_neg h, hg]
        _ = ∑ o ∈ PairBox X, (if o = (0, 0) then (0 : ℝ) else rI o) := by
              rfl
        _ = ∑ o ∈ G ×ˢ G, (if o = (0, 0) then (0 : ℝ) else rI o) := by
              have hI : Finset.Icc (-(2 * X : ℤ)) (2 * X : ℤ) =
                  Finset.Icc (-((2 * X : ℕ) : ℤ)) ((2 * X : ℕ) : ℤ) := by
                have hB : (2 * X : ℤ) = ((2 * X : ℕ) : ℤ) := by norm_num
                have hA : -(2 * X : ℤ) = -((2 * X : ℕ) : ℤ) := congrArg Neg.neg hB
                exact congrArg₂ Finset.Icc hA hB
              have hpair : PairBox X = G ×ˢ G := by
                unfold PairBox G
                rw [hI]
                rfl
              rw [hpair]
        _ = ∑ d ∈ G, ∑ g ∈ G, (if (d, g) = (0, 0) then (0 : ℝ) else rI (d, g)) := by
              exact Finset.sum_product (s := G) (t := G) (f := fun x : ℤ × ℤ =>
                if x = (0, 0) then (0 : ℝ) else rI x)
        _ ≤ 1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)) := by
              change (∑ d ∈ Finset.Icc (-((2 * X : ℕ) : ℤ)) ((2 * X : ℕ) : ℤ),
                ∑ g ∈ Finset.Icc (-((2 * X : ℕ) : ℤ)) ((2 * X : ℕ) : ℤ),
                  if (d, g) = (0, 0) then (0 : ℝ)
                  else ((Int.gcd d.natAbs g.natAbs : ℕ) : ℝ) / (max d.natAbs g.natAbs : ℝ))
                  ≤ 1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1))
              dsimp [G, rI]
              exact hsb

/-- `1 + log (2X + 1) ≤ 2 (1 + log (X + 1))` -/
lemma log_two_mul_plus_one_le (X : ℕ) (hX : 1 ≤ X) :
    1 + Real.log (((2 * X : ℕ) : ℝ) + 1) ≤ 2 * (1 + Real.log ((X : ℝ) + 1)) := by
  have hcast : (((2 * X : ℕ) : ℝ) + 1) = 2 * (X : ℝ) + 1 := by norm_num
  have hx : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hle : 2 * (X : ℝ) + 1 ≤ ((X : ℝ) + 1) ^ 2 := by nlinarith
  have hlog : Real.log (((2 * X : ℕ) : ℝ) + 1) ≤ 2 * Real.log ((X : ℝ) + 1) := by
    calc
      Real.log (((2 * X : ℕ) : ℝ) + 1) = Real.log (2 * (X : ℝ) + 1) := by rw [hcast]
      _ ≤ Real.log (((X : ℝ) + 1) ^ 2) := by
            apply Real.log_le_log (by nlinarith : 0 < 2 * (X : ℝ) + 1)
            exact hle
      _ = 2 * Real.log ((X : ℝ) + 1) := by
            rw [Real.log_pow]
            norm_num
  nlinarith

/-- the `4 X (X-1) · bound`-term ≤ `8000 X³ W'` -/
lemma A_le (z y c W' : ℝ) (hc : c = 2 * z) (hz0 : 0 ≤ z) (hW'0 : 0 ≤ W') (hyz : y ≤ z) :
    (2 * z) * (2 * y) * (1000 * c * W') ≤ 8000 * z ^ 3 * W' := by
  rw [hc]
  have h2 : 2 * y ≤ 2 * z := by nlinarith
  have hfac0 : 0 ≤ (2 * z) * 1000 * (2 * z) * W' := by
    positivity
  have hb : (2 * z) * (2 * y) * (1000 * (2 * z) * W')
      ≤ (2 * z) * (2 * z) * (1000 * (2 * z) * W') := by
    have h1 : (2 * z) * (2 * y) * (1000 * (2 * z) * W')
        = (2 * y) * ((2 * z) * 1000 * (2 * z) * W') := by ring
    have h3 : (2 * z) * (2 * z) * (1000 * (2 * z) * W')
        = (2 * z) * ((2 * z) * 1000 * (2 * z) * W') := by ring
    rw [h1, h3]
    exact mul_le_mul_of_nonneg_right h2 hfac0
  calc
    (2 * z) * (2 * y) * (1000 * (2 * z) * W') ≤ (2 * z) * (2 * z) * (1000 * (2 * z) * W') := hb
    _ = 8000 * z ^ 3 * W' := by ring

/-- the `6 X · #E`-term ≤ `150 X³` -/
lemma B_le (z : ℝ) (m : ℕ) (hz0 : 0 ≤ z) (hm : (m : ℝ) ≤ 25 * z ^ 2) :
    (2 * z) * 3 * (m : ℝ) ≤ 150 * z ^ 3 := by
  have hfac : 0 ≤ (2 * z) * 3 := by nlinarith
  have h1 : (2 * z) * 3 * (m : ℝ) ≤ (2 * z) * 3 * (25 * z ^ 2) :=
    mul_le_mul_of_nonneg_left hm hfac
  have h2 : (2 * z) * 3 * (25 * z ^ 2) = 150 * z ^ 3 := by ring
  rwa [h2] at h1

/-- final scalar assembly -/
lemma endgame (z W : ℝ) (hz0 : 0 ≤ z) (hW1 : 1 ≤ W) :
    z ^ 3 + 16000 * z ^ 3 * W + 150 * z ^ 3 ≤ 1000000 * z ^ 3 * W := by
  have h1 : z ^ 3 + 150 * z ^ 3 ≤ 151 * z ^ 3 * W := by
    have hz3 : 0 ≤ z ^ 3 := pow_nonneg hz0 3
    have h2 : z ^ 3 + 150 * z ^ 3 = 151 * z ^ 3 := by ring
    have h3 : 151 * z ^ 3 ≤ 151 * z ^ 3 * W := by
      have h3' : 151 * z ^ 3 * 1 ≤ 151 * z ^ 3 * W := by
        exact mul_le_mul_of_nonneg_left hW1 (mul_nonneg (by norm_num) hz3)
      simpa using h3'
    rwa [h2]
  have hz3W : 0 ≤ z ^ 3 * W := mul_nonneg (pow_nonneg hz0 3) (by linarith)
  have h4 : 151 * z ^ 3 * W + 16000 * z ^ 3 * W ≤ 1000000 * z ^ 3 * W := by
    have h5 : (151 + 16000 : ℝ) ≤ 1000000 := by norm_num
    calc
      151 * z ^ 3 * W + 16000 * z ^ 3 * W = (151 + 16000) * (z ^ 3 * W) := by ring
      _ ≤ 1000000 * (z ^ 3 * W) := mul_le_mul_of_nonneg_right h5 hz3W
      _ = 1000000 * z ^ 3 * W := by ring
  calc
    z ^ 3 + 16000 * z ^ 3 * W + 150 * z ^ 3 = (z ^ 3 + 150 * z ^ 3) + 16000 * z ^ 3 * W := by ring
    _ ≤ 151 * z ^ 3 * W + 16000 * z ^ 3 * W := add_le_add h1 le_rfl
    _ ≤ 1000000 * z ^ 3 * W := h4

/-- main bound: J₃ ≤ C X³ (1+log) -/
lemma core_three :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      J 3 X ≤ C * (X : ℝ) ^ 3 * (1 + Real.log ((X : ℝ) + 1)) := by
  classical
  refine ⟨1000000, by norm_num, ?_⟩
  intro X hX
  -- structural facts
  have hPB : J 3 X = ∑ o ∈ PairBox X, (((Fib X o.1 o.2).card : ℕ) : ℝ) := J_eq_sum_fib X hX
  have hmemb : (0, 0) ∈ PairBox X := by
    rw [PairBox]
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> linarith
    · rw [Finset.mem_Icc]
      constructor <;> linarith
  have hsplit : (∑ o ∈ PairBox X, (((Fib X o.1 o.2).card : ℕ) : ℝ)) =
      (((Fib X 0 0).card : ℕ) : ℝ) + ∑ o ∈ (PairBox X).erase (0, 0),
        (((Fib X o.1 o.2).card : ℕ) : ℝ) := by
    have h := Finset.sum_erase_add (s := PairBox X) (f := fun o : ℤ × ℤ => (((Fib X o.1 o.2).card : ℕ) : ℝ))
      (a := (0, 0)) hmemb
    -- h : (∑ x ∈ s.erase a, f x) + f a = ∑ x ∈ s, f x
    linarith
  -- bound the (0,0)-term
  have hflat : (((Fib X 0 0).card : ℕ) : ℝ) ≤ (X : ℝ) ^ 3 := flat_bound X hX
  -- bound the other terms
  have hothers : ∑ o ∈ (PairBox X).erase (0, 0), (((Fib X o.1 o.2).card : ℕ) : ℝ) ≤
      ∑ o ∈ (PairBox X).erase (0, 0),
        (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
          ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)) + 3) := by
    apply Finset.sum_le_sum
    intro o ho
    have hone : o ≠ (0, 0) := (Finset.mem_erase.mp ho).1
    exact fiber_bound X hX o.1 o.2 hone
  have hsplit2 : J 3 X ≤
      (X : ℝ) ^ 3 + ∑ o ∈ (PairBox X).erase (0, 0),
        (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
          ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)) + 3) := by
    calc
      J 3 X = ∑ o ∈ PairBox X, (((Fib X o.1 o.2).card : ℕ) : ℝ) := hPB
      _ = (((Fib X 0 0).card : ℕ) : ℝ) + ∑ o ∈ (PairBox X).erase (0, 0),
            (((Fib X o.1 o.2).card : ℕ) : ℝ) := hsplit
      _ ≤ (X : ℝ) ^ 3 + ∑ o ∈ (PairBox X).erase (0, 0),
            (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
              ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)) + 3) := by
            exact add_le_add hflat hothers
  -- bound the remaining sum
  have hsum1 : ∑ o ∈ (PairBox X).erase (0, 0),
      (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
        ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)) + 3)
      = (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
          (∑ o ∈ (PairBox X).erase (0, 0),
            ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
        + (2 * (X : ℝ)) * 3 * ((PairBox X).erase (0, 0)).card := by
    calc
      (∑ o ∈ (PairBox X).erase (0, 0),
          (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
            ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)) + 3))
          = ∑ o ∈ (PairBox X).erase (0, 0),
              ((2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
                ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
                + (2 * (X : ℝ)) * 3) := by
            apply Finset.sum_congr rfl
            intro o ho
            ring
      _ = (∑ o ∈ (PairBox X).erase (0, 0),
              ((2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
                ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))))
            + ∑ o ∈ (PairBox X).erase (0, 0), (2 * (X : ℝ)) * 3 := by
            rw [Finset.sum_add_distrib]
      _ = (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
            (∑ o ∈ (PairBox X).erase (0, 0),
              ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
          + (2 * (X : ℝ)) * 3 * ((PairBox X).erase (0, 0)).card := by
            congr 1
            · -- first sum: Σ c·r with c := (2X)·(2L)
              have hmul := Finset.mul_sum ((PairBox X).erase (0, 0))
                (fun o : ℤ × ℤ => ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
                ((2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)))
              -- c * Σ r = Σ (c * r): our summand is ((2X)·(2L))·r:
              simpa [mul_assoc] using hmul.symm
            · -- second: Σ over o of constant (2X)*3 = (2X)*3*card
              rw [Finset.sum_const]
              simp
              ring
  -- bound the gcd-sum over the erased box by the known divisor bound
  have hsb := Commons.Data.Int.sum_gcd_div_max_bound (2 * X) (by omega : 1 ≤ 2 * X)
  have hS : (∑ o ∈ (PairBox X).erase (0, 0),
      ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
      ≤ 1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)) :=
    sum_ratio_erase_le X hX
  -- final chain: J ≤ X³ + T, T = A + B, A ≤ 8000X³W', B ≤ 150X³, W' ≤ 2W
  have hz0 : 0 ≤ (X : ℝ) := by positivity
  have hy0 : 0 ≤ ((X - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (X - 1)
  have hyz : ((X - 1 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast Nat.sub_le X 1
  have hfac0 : 0 ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hz0) (mul_nonneg (by norm_num) hy0)
  have hA1 : (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
        (∑ o ∈ (PairBox X).erase (0, 0),
          ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
      ≤ (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
          (1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hS hfac0
  have hEr : (((PairBox X).erase (0, 0)).card : ℝ) ≤ 25 * (X : ℝ) ^ 2 := by
    have h1 : (((PairBox X).erase (0, 0)).card : ℕ) ≤ 25 * X ^ 2 := pairbox_erase_card_le X hX
    have h2 : ((((PairBox X).erase (0, 0)).card : ℕ) : ℝ) ≤ ((25 * X ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 : ((25 * X ^ 2 : ℕ) : ℝ) = 25 * (X : ℝ) ^ 2 := by norm_num
    rwa [h3] at h2
  have hB1 : (2 * (X : ℝ)) * 3 * (((PairBox X).erase (0, 0)).card : ℝ) ≤
      150 * (X : ℝ) ^ 3 :=
    B_le (X : ℝ) (((PairBox X).erase (0, 0)).card) hz0 hEr
  have hW'0 : 0 ≤ 1 + Real.log (((2 * X : ℕ) : ℝ) + 1) := by
    have h2 : (2 : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ 2 * X)
    have hlg : 0 ≤ Real.log (((2 * X : ℕ) : ℝ) + 1) := by
      apply Real.log_nonneg
      nlinarith
    linarith
  have hA2 : (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
      (1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)))
      ≤ 8000 * (X : ℝ) ^ 3 * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)) :=
    A_le (X : ℝ) ((X - 1 : ℕ) : ℝ) ((2 * X : ℕ) : ℝ)
      (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)) (by norm_num) hz0 hW'0 hyz
  have hW2 := log_two_mul_plus_one_le X hX
  have hW1 : 1 ≤ 1 + Real.log ((X : ℝ) + 1) := by
    have h : 0 ≤ Real.log ((X : ℝ) + 1) := by
      apply Real.log_nonneg
      nlinarith
    linarith
  calc
    J 3 X ≤ (X : ℝ) ^ 3 +
        (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
          (∑ o ∈ (PairBox X).erase (0, 0),
            ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
        + (2 * (X : ℝ)) * 3 * (((PairBox X).erase (0, 0)).card : ℝ) := by
          calc
            J 3 X ≤ (X : ℝ) ^ 3 + ∑ o ∈ (PairBox X).erase (0, 0),
                (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ) *
                  ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)) + 3) :=
                  hsplit2
            _ = (X : ℝ) ^ 3 +
                (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
                  (∑ o ∈ (PairBox X).erase (0, 0),
                    ((Nat.gcd o.1.natAbs o.2.natAbs : ℝ) / (max o.1.natAbs o.2.natAbs : ℝ)))
                + (2 * (X : ℝ)) * 3 * (((PairBox X).erase (0, 0)).card : ℝ) := by
                rw [hsum1]
                ring
    _ ≤ (X : ℝ) ^ 3 +
        (2 * (X : ℝ)) * (2 * ((X - 1 : ℕ) : ℝ)) *
          (1000 * ((2 * X : ℕ) : ℝ) * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1)))
        + (2 * (X : ℝ)) * 3 * (((PairBox X).erase (0, 0)).card : ℝ) := by
          exact add_le_add (add_le_add le_rfl hA1) le_rfl
    _ ≤ (X : ℝ) ^ 3 +
        8000 * (X : ℝ) ^ 3 * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1))
        + 150 * (X : ℝ) ^ 3 := by
          exact add_le_add (add_le_add le_rfl hA2) hB1
    _ ≤ (X : ℝ) ^ 3 +
        16000 * (X : ℝ) ^ 3 * (1 + Real.log ((X : ℝ) + 1))
        + 150 * (X : ℝ) ^ 3 := by
          have hz3 : 0 ≤ (X : ℝ) ^ 3 := pow_nonneg hz0 3
          have h16000 : 8000 * (X : ℝ) ^ 3 * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1))
              ≤ 16000 * (X : ℝ) ^ 3 * (1 + Real.log ((X : ℝ) + 1)) := by
            have hb : 8000 * (X : ℝ) ^ 3 * (1 + Real.log (((2 * X : ℕ) : ℝ) + 1))
                ≤ 8000 * (X : ℝ) ^ 3 * (2 * (1 + Real.log ((X : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left hW2 (mul_nonneg (by norm_num) hz3)
            have hc : 8000 * (X : ℝ) ^ 3 * (2 * (1 + Real.log ((X : ℝ) + 1)))
                = 16000 * (X : ℝ) ^ 3 * (1 + Real.log ((X : ℝ) + 1)) := by
              ring
            rwa [hc] at hb
          exact add_le_add (add_le_add le_rfl h16000) le_rfl
    _ ≤ 1000000 * (X : ℝ) ^ 3 * (1 + Real.log ((X : ℝ) + 1)) :=
          endgame (X : ℝ) (1 + Real.log ((X : ℝ) + 1)) hz0 hW1


/-! ## Part 3. Bridge between the natural and integer formulations -/

/-- natural moment sums -/
def s1N {n X : ℕ} (x : NatBox n X) : ℕ := ∑ i, (x i).1
def s2N {n X : ℕ} (x : NatBox n X) : ℕ := ∑ i, ((x i).1) ^ 2

/-- single coordinate: natural value to integer value -/
def coordNatInt {X : ℕ} (hX : 1 ≤ X) : (Finset.Icc 1 X : Type) → (Finset.Icc (1 : ℤ) (X : ℤ) : Type) :=
  fun n => ⟨(n.1 : ℤ), by
    have h1 : 1 ≤ n.1 := (Finset.mem_Icc.mp n.2).1
    have h2 : n.1 ≤ X := (Finset.mem_Icc.mp n.2).2
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2⟩

/-- single coordinate: integer value to natural value -/
def coordIntNat {X : ℕ} (hX : 1 ≤ X) : (Finset.Icc (1 : ℤ) (X : ℤ) : Type) → (Finset.Icc 1 X : Type) :=
  fun z => ⟨z.1.toNat, by
    have h1 : (1 : ℤ) ≤ z.1 := (Finset.mem_Icc.mp z.2).1
    have h2 : z.1 ≤ (X : ℤ) := (Finset.mem_Icc.mp z.2).2
    have hz : 0 ≤ z.1 := by linarith
    have hcast : (z.1.toNat : ℤ) = z.1 := Int.toNat_of_nonneg hz
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (z.1.toNat : ℤ) by rwa [hcast])
    · exact_mod_cast (show (z.1.toNat : ℤ) ≤ (X : ℤ) by rwa [hcast])⟩

lemma coordNatInt_val {X : ℕ} (hX : 1 ≤ X) (n : Finset.Icc 1 X) : (coordNatInt hX n).1 = (n.1 : ℤ) := rfl

lemma coord_left_inv {X : ℕ} (hX : 1 ≤ X) (n : Finset.Icc 1 X) :
    coordIntNat hX (coordNatInt hX n) = n := by
  apply Subtype.ext
  change (n.1 : ℤ).toNat = n.1
  exact Int.toNat_natCast n.1

lemma coord_right_inv {X : ℕ} (hX : 1 ≤ X) (z : Finset.Icc (1 : ℤ) (X : ℤ)) :
    coordNatInt hX (coordIntNat hX z) = z := by
  apply Subtype.ext
  change (z.1.toNat : ℤ) = z.1
  have h1 : (1 : ℤ) ≤ z.1 := (Finset.mem_Icc.mp z.2).1
  have hz : 0 ≤ z.1 := by linarith
  exact (Int.toNat_of_nonneg hz)

/-- natural box ≃ integer box (tuples) -/
def tupleNatInt {s X : ℕ} (hX : 1 ≤ X) : NatBox s X ≃ IntBox s X where
  toFun x := fun i => coordNatInt hX (x i)
  invFun z := fun i => coordIntNat hX (z i)
  left_inv x := by
    apply funext
    intro i
    exact coord_left_inv hX (x i)
  right_inv z := by
    apply funext
    intro i
    exact coord_right_inv hX (z i)

/-- pair equivalence -/
def pairNatInt {s X : ℕ} (hX : 1 ≤ X) :
    (NatBox s X × NatBox s X) ≃ (IntBox s X × IntBox s X) where
  toFun xy := (tupleNatInt hX xy.1, tupleNatInt hX xy.2)
  invFun xy := ((tupleNatInt hX).symm xy.1, (tupleNatInt hX).symm xy.2)
  left_inv xy := by
    apply Prod.ext
    · exact Equiv.symm_apply_apply (tupleNatInt hX) xy.1
    · exact Equiv.symm_apply_apply (tupleNatInt hX) xy.2
  right_inv xy := by
    apply Prod.ext
    · exact Equiv.apply_symm_apply (tupleNatInt hX) xy.1
    · exact Equiv.apply_symm_apply (tupleNatInt hX) xy.2

lemma s1_int_of_nat {s X : ℕ} (hX : 1 ≤ X) (x : NatBox s X) :
    s1 (tupleNatInt hX x) = (s1N x : ℤ) := by
  unfold s1 s1N tupleNatInt
  simp [coordNatInt_val]

lemma s2_int_of_nat {s X : ℕ} (hX : 1 ≤ X) (x : NatBox s X) :
    s2 (tupleNatInt hX x) = (s2N x : ℤ) := by
  unfold s2 s2N tupleNatInt
  simp [coordNatInt_val]

lemma match_nat_iff_int {s X : ℕ} (hX : 1 ≤ X) (p : NatBox s X × NatBox s X) :
    ((s1N p.1 = s1N p.2 ∧ s2N p.1 = s2N p.2)) ↔
      (s1 (pairNatInt hX p).1 = s1 (pairNatInt hX p).2 ∧
       s2 (pairNatInt hX p).1 = s2 (pairNatInt hX p).2) := by
  constructor
  · intro h
    have h1 := congrArg (fun t : ℕ => (t : ℤ)) h.1
    have h2 := congrArg (fun t : ℕ => (t : ℤ)) h.2
    rw [← s1_int_of_nat hX p.1, ← s1_int_of_nat hX p.2] at h1
    rw [← s2_int_of_nat hX p.1, ← s2_int_of_nat hX p.2] at h2
    exact ⟨h1, h2⟩
  · intro h
    have h1 : (s1N p.1 : ℤ) = (s1N p.2 : ℤ) := by
      rw [← s1_int_of_nat hX p.1, ← s1_int_of_nat hX p.2]
      exact h.1
    have h2 : (s2N p.1 : ℤ) = (s2N p.2 : ℤ) := by
      rw [← s2_int_of_nat hX p.1, ← s2_int_of_nat hX p.2]
      exact h.2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Natural-valued tuples and integer-valued tuples give the same count. -/
lemma card_filter_nat_eq_int (s X : ℕ) (hX : 1 ≤ X) :
    ((Finset.univ.filter (fun xy : (NatBox s X) × (NatBox s X) =>
      (∑ i, (xy.1 i).1) = (∑ i, (xy.2 i).1) ∧
      (∑ i, ((xy.1 i).1) ^ 2) = (∑ i, ((xy.2 i).1) ^ 2))).card : ℝ) = J s X := by
  classical
  change ((Finset.univ.filter (fun xy : (NatBox s X) × (NatBox s X) =>
      s1N xy.1 = s1N xy.2 ∧ s2N xy.1 = s2N xy.2)).card : ℝ) = J s X
  let A : Finset (NatBox s X × NatBox s X) :=
    (Finset.univ.filter (fun xy : NatBox s X × NatBox s X =>
      s1N xy.1 = s1N xy.2 ∧ s2N xy.1 = s2N xy.2))
  let E := pairNatInt (s := s) hX
  have hcard : A.card = (Sol s X).card := by
    dsimp [Sol]
    apply Finset.card_bij (fun (p : NatBox s X × NatBox s X) (_ : p ∈ A) => E p)
    · intro p hp
      have hp' : p ∈ A := hp
      have hm : s1N p.1 = s1N p.2 ∧ s2N p.1 = s2N p.2 := by simpa [A] using hp'
      have hm2 := (match_nat_iff_int hX p).mp hm
      rw [Finset.mem_filter]
      exact ⟨by simp, hm2⟩
    · intro p hp q hq hpq
      exact (Equiv.injective E) hpq
    · intro w hw
      refine ⟨E.symm w, ?_, ?_⟩
      · have hw' : w ∈ (Finset.univ.filter (fun xy : IntBox s X × IntBox s X =>
            s1 xy.1 = s1 xy.2 ∧ s2 xy.1 = s2 xy.2)) := hw
        have hmw : s1 w.1 = s1 w.2 ∧ s2 w.1 = s2 w.2 := (Finset.mem_filter.mp hw').2
        have hE : E (E.symm w) = w := Equiv.apply_symm_apply E w
        have hP : s1 (E (E.symm w)).1 = s1 (E (E.symm w)).2 ∧
            s2 (E (E.symm w)).1 = s2 (E (E.symm w)).2 := by
          rw [hE]
          exact hmw
        have hm2 := (match_nat_iff_int hX (E.symm w)).mpr hP
        rw [Finset.mem_filter]
        exact ⟨by simp, hm2⟩
      · exact Equiv.apply_symm_apply E w
  calc
    ((Finset.univ.filter (fun xy : (NatBox s X) × (NatBox s X) =>
      s1N xy.1 = s1N xy.2 ∧ s2N xy.1 = s2N xy.2)).card : ℝ) = (A.card : ℝ) := rfl
    _ = ((Sol s X).card : ℝ) := by rw [hcard]
    _ = J s X := rfl

/-! ## Assembly -/

/-- The main theorem. -/
theorem quadratic_mean_value_bound (s : ℕ) (hs : 3 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ((Finset.univ.filter (fun xy : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X) =>
        (∑ i, (xy.1 i).1) = (∑ i, (xy.2 i).1) ∧
        (∑ i, ((xy.1 i).1) ^ 2) = (∑ i, ((xy.2 i).1) ^ 2))).card : ℝ)
        ≤ C * (X : ℝ) ^ (2 * s - 3 : ℕ) * (1 + Real.log ((X : ℝ) + 1)) := by
  rcases core_three with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro X hX
  rw [card_filter_nat_eq_int s X hX]
  have hJ := J_le_pow_two_mul s X hs hX
  have h3 := hC X hX
  calc
    J s X ≤ (X : ℝ) ^ (2 * (s - 3)) * J 3 X := hJ
    _ ≤ (X : ℝ) ^ (2 * (s - 3)) * (C * (X : ℝ) ^ 3 * (1 + Real.log ((X : ℝ) + 1))) := by
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = C * ((X : ℝ) ^ (2 * (s - 3)) * (X : ℝ) ^ 3) * (1 + Real.log ((X : ℝ) + 1)) := by
      ring
    _ = C * (X : ℝ) ^ (2 * s - 3 : ℕ) * (1 + Real.log ((X : ℝ) + 1)) := by
      have hpow : (X : ℝ) ^ (2 * (s - 3)) * (X : ℝ) ^ 3 = (X : ℝ) ^ (2 * s - 3) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]

end
end Commons.Combinatorics.Fin
