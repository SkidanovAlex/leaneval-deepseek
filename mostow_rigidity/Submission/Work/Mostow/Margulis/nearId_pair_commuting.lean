import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.nearStabDefs
import Submission.Work.Mostow.isCompact_matBallToPO
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.boundedOrbitFixed
import Submission.Work.Mostow.Margulis.bdFix_size_of_no_fixed_point
import Submission.Work.Mostow.Margulis.bd_set_prop
import Submission.Work.Mostow.Margulis.same_pair_pair_commuting
import Submission.Work.Mostow.Margulis.same_point_pair_commuting

namespace Work.Mostow.Margulis

set_option maxHeartbeats 4000000

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## The contraction machinery -/

/-- `kappa n` is the constant in the commutator estimate: the defect of `[A,B]` is at most
`kappa n * a * b * (1 + a) * (1 + b)` when `A`, `B` have defects `a`, `b`. -/
def kappa (n : ℕ) : ℝ := 2 * (msz n) ^ 3

lemma kappa_nonneg (n : ℕ) : 0 ≤ kappa n := by
  have h : (0 : ℝ) ≤ msz n := msz_nonneg n
  simp only [kappa]; positivity

lemma kappa_pos (n : ℕ) : 0 < kappa n := by
  have h : (0 : ℝ) < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
  simp only [kappa]; positivity

/-- The small entrywise radius we work with. -/
def margQ (n : ℕ) : ℝ := min (1 / 1000) (1 / (8 * kappa n))

lemma margQ_pos (n : ℕ) : 0 < margQ n := by
  have h : 0 < 1 / (8 * kappa n) := by
    have := kappa_pos n; positivity
  simp only [margQ]; exact lt_min (by norm_num) h

lemma margQ_le (n : ℕ) : margQ n ≤ 1 / 1000 := min_le_left _ _

lemma margQ_le_one (n : ℕ) : margQ n ≤ 1 := by
  have := margQ_le n; norm_num at this ⊢; linarith

/-- The key smallness: `8 (n+1)^3 q ≤ 1/2` for `q = margQ n`. -/
lemma margQ_small (n : ℕ) : 8 * (msz n) ^ 3 * margQ n ≤ 1 / 2 := by
  have hk : kappa n = 2 * (msz n) ^ 3 := rfl
  have hpos : 0 < kappa n := kappa_pos n
  have hle : margQ n ≤ 1 / (8 * kappa n) := min_le_right _ _
  have h1 : margQ n * (8 * kappa n) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ 8 * kappa n)
    rw [one_div, inv_mul_cancel₀ (by positivity : (8 * kappa n) ≠ 0)] at this
    linarith [this]
  rw [hk] at h1
  nlinarith [h1]

/-- `Near1` is monotone in the radius. -/
lemma near1_mono {A : O1 n} {s t : ℝ} (h : Near1 A s) (hst : s ≤ t) : Near1 A t :=
  fun i j => le_trans (h i j) hst

/-- Entrywise bound for `AB - BA` in terms of the defects of `A` and `B`. -/
lemma abs_sub_comm_mul_le_gen {A B : O1 n} {a b : ℝ} (hA : Near1 A a) (hB : Near1 B b)
    (i j : Fin n ⊕ Fin 1) :
    |(mat A * mat B - mat B * mat A) i j| ≤ 2 * (msz n * a * b) := by
  have ha : 0 ≤ a := hA.nonneg
  have key : (mat A * mat B - mat B * mat A) i j =
      (∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
        (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)) := by
    have p1 := sub_mul_sub_apply (n := n) (A := mat A) (B := mat B) i j
    have p2 := sub_mul_sub_apply (n := n) (A := mat B) (B := mat A) i j
    rw [show (mat A * mat B - mat B * mat A) i j
        = (mat A * mat B) i j - (mat B * mat A) i j from rfl, p1, p2]
    abel
  have b1 : |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)| ≤ msz n * (a * b) := by
    calc |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
        ≤ ∑ k, |(mat A i k - dE n i k) * (mat B k j - dE n k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k, a * b := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
      _ = msz n * (a * b) := sum_const_sum n _
  have b2 : |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| ≤ msz n * (a * b) := by
    calc |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)|
        ≤ ∑ k, |(mat B i k - dE n i k) * (mat A k j - dE n k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k, a * b := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, mul_comm (|mat B i k - dE n i k|) (|mat A k j - dE n k j|)]
          exact mul_le_mul (hA k j) (hB i k) (abs_nonneg _) hA.nonneg
      _ = msz n * (a * b) := sum_const_sum n _
  have htri : |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
      (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))|
      ≤ |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
        + |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| := by
    calc |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
            (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))|
        = |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) +
            (-(∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)))| := by ring_nf
      _ ≤ |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
            + |-(∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))| := abs_add_le _ _
      _ = |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
            + |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| := by rw [abs_neg]
  rw [key]
  linarith [htri, b1, b2]

/-- Entrywise bound for the inverse product. -/
lemma abs_inv_mul_entry_le {A B : O1 n} {a b : ℝ} (hA : Near1 A a) (hB : Near1 B b)
    (k j : Fin n ⊕ Fin 1) :
    |((mat A)⁻¹ * (mat B)⁻¹) k j| ≤ msz n * (1 + a) * (1 + b) := by
  have ha : 0 ≤ a := hA.nonneg
  have hb : 0 ≤ b := hB.nonneg
  calc |((mat A)⁻¹ * (mat B)⁻¹) k j| ≤ ∑ l, |(mat A)⁻¹ k l * (mat B)⁻¹ l j| := by
        rw [Matrix.mul_apply]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l, (1 + a) * (1 + b) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_inv_matrix_entry_le' hA ha k l) (abs_inv_matrix_entry_le' hB hb l j)
          (abs_nonneg _) (by linarith)
    _ = msz n * ((1 + a) * (1 + b)) := sum_const_sum n _
    _ = msz n * (1 + a) * (1 + b) := by ring

/-- **The two-radius commutator estimate**. -/
lemma near1_commutator_gen {A B : O1 n} {a b : ℝ} (hA : Near1 A a) (hB : Near1 B b) :
    Near1 (A * B * A⁻¹ * B⁻¹) (2 * (msz n) ^ 3 * a * b * (1 + a) * (1 + b)) := by
  have hAA : mat A * (mat A)⁻¹ = 1 := by
    have h : mat A * mat A⁻¹ = 1 := by rw [← mat_mul_coe, mul_inv_cancel, mat_one_coe]
    rwa [mat_inv_coe] at h
  have hBB : mat B * (mat B)⁻¹ = 1 := by
    have h : mat B * mat B⁻¹ = 1 := by rw [← mat_mul_coe, mul_inv_cancel, mat_one_coe]
    rwa [mat_inv_coe] at h
  have hBA : (mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc (mat A), hAA, one_mul, hBB]
  have hmat : mat (A * B * A⁻¹ * B⁻¹) - 1 = (mat A * mat B - mat B * mat A) *
      ((mat A)⁻¹ * (mat B)⁻¹) := by
    have hL : mat (A * B * A⁻¹ * B⁻¹) = (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹) := by
      rw [mat_mul_coe, mat_mul_coe, mat_mul_coe, mat_inv_coe, mat_inv_coe, mul_assoc]
    rw [hL]
    have hexp : (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹) - 1
        = (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹)
          - (mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹) := by rw [hBA]
    rw [hexp, ← sub_mul]
  intro i j
  have hkey : mat (A * B * A⁻¹ * B⁻¹) i j - dE n i j =
      ((mat A * mat B - mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹)) i j := by
    have hD : (mat (A * B * A⁻¹ * B⁻¹) - 1) i j
        = mat (A * B * A⁻¹ * B⁻¹) i j - dE n i j :=
      sub_one_entry (A * B * A⁻¹ * B⁻¹) i j
    rw [← hD, hmat]
  rw [hkey, Matrix.mul_apply]
  calc |∑ k, (mat A * mat B - mat B * mat A) i k * ((mat A)⁻¹ * (mat B)⁻¹) k j|
      ≤ ∑ k, |(mat A * mat B - mat B * mat A) i k| * |((mat A)⁻¹ * (mat B)⁻¹) k j| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ _k, (2 * (msz n * a * b)) * (msz n * (1 + a) * (1 + b)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hnn : (0:ℝ) ≤ 2 * (msz n * a * b) := by
          have := msz_nonneg n; have := hA.nonneg; have := hB.nonneg
          positivity
        exact mul_le_mul (abs_sub_comm_mul_le_gen hA hB i k) (abs_inv_mul_entry_le hA hB k j)
          (abs_nonneg _) hnn
    _ = msz n * ((2 * (msz n * a * b)) * (msz n * (1 + a) * (1 + b))) := sum_const_sum n _
    _ = 2 * (msz n) ^ 3 * a * b * (1 + a) * (1 + b) := by ring

/-- The `j`-th iterated commutator of `B` with `A`: `c₀ = B`, `c_{j+1} = [A, c_j]`. -/
def commSeq (A B : O1 n) : ℕ → O1 n
  | 0 => B
  | (j + 1) => A * commSeq A B j * A⁻¹ * (commSeq A B j)⁻¹

@[simp] lemma commSeq_zero (A B : O1 n) : commSeq A B 0 = B := rfl

@[simp] lemma commSeq_succ (A B : O1 n) (j : ℕ) :
    commSeq A B (j + 1) = A * commSeq A B j * A⁻¹ * (commSeq A B j)⁻¹ := rfl

/-- The commutator defects shrink geometrically. -/
lemma near1_commSeq {A B : O1 n} {q : ℝ} (hA : Near1 A q) (hB : Near1 B q)
    (hq : 0 ≤ q) (hsmall : 8 * (msz n) ^ 3 * q ≤ 1 / 2) (hq1 : q ≤ 1) (j : ℕ) :
    Near1 (commSeq A B j) ((1 / 2 : ℝ) ^ j * q) := by
  induction j with
  | zero => simpa using hB
  | succ j ih =>
    have hs0 : 0 ≤ (1 / 2 : ℝ) ^ j * q := by positivity
    have hsle : (1 / 2 : ℝ) ^ j * q ≤ q := by
      have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [hq]
    have hstep := near1_commutator_gen hA ih
    refine fun i k => le_trans (hstep i k) ?_
    have h1 : (1 + q) * (1 + (1 / 2 : ℝ) ^ j * q) ≤ 4 := by nlinarith [hq, hsle, hq1, hs0]
    have hbase : (0:ℝ) ≤ 2 * (msz n) ^ 3 * q * ((1 / 2 : ℝ) ^ j * q) := by
      have := msz_nonneg n; positivity
    calc 2 * (msz n) ^ 3 * q * ((1 / 2 : ℝ) ^ j * q) * (1 + q) * (1 + (1 / 2 : ℝ) ^ j * q)
        = 2 * (msz n) ^ 3 * q * ((1 / 2 : ℝ) ^ j * q) * ((1 + q) * (1 + (1 / 2 : ℝ) ^ j * q)) := by
          ring
      _ ≤ 2 * (msz n) ^ 3 * q * ((1 / 2 : ℝ) ^ j * q) * 4 :=
          mul_le_mul_of_nonneg_left h1 hbase
      _ = (8 * (msz n) ^ 3 * q) * ((1 / 2 : ℝ) ^ j * q) := by ring
      _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ j * q) :=
          mul_le_mul_of_nonneg_right hsmall hs0
      _ = (1 / 2 : ℝ) ^ (j + 1) * q := by ring

/-- The same iterated commutator construction in an abstract group. -/
def commSeqG {G : Type*} [Group G] (a b : G) : ℕ → G
  | 0 => b
  | (j + 1) => a * commSeqG a b j * a⁻¹ * (commSeqG a b j)⁻¹

@[simp] lemma commSeqG_zero {G : Type*} [Group G] (a b : G) : commSeqG a b 0 = b := rfl

@[simp] lemma commSeqG_succ {G : Type*} [Group G] (a b : G) (j : ℕ) :
    commSeqG a b (j + 1) = a * commSeqG a b j * a⁻¹ * (commSeqG a b j)⁻¹ := rfl

/-- The image of `commSeq A B j` in `PO n 1` is the abstract iterated commutator. -/
lemma commSeq_coe {A B : O1 n} (j : ℕ) :
    ((commSeq A B j : O1 n) : PO n 1) = commSeqG (A : PO n 1) (B : PO n 1) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [commSeq_succ, commSeqG_succ]
    show (A : PO n 1) * ((commSeq A B j : O1 n) : PO n 1) * (A : PO n 1)⁻¹
        * (((commSeq A B j : O1 n) : PO n 1))⁻¹
      = (A : PO n 1) * commSeqG (A : PO n 1) (B : PO n 1) j * (A : PO n 1)⁻¹
        * (commSeqG (A : PO n 1) (B : PO n 1) j)⁻¹
    rw [ih]

/-- The iterated commutators lie in the image of `Γ`. -/
lemma commSeq_mem {A B : O1 n} {Γ : Subgroup (PO n 1)}
    (hA : (A : PO n 1) ∈ Γ) (hB : (B : PO n 1) ∈ Γ) (j : ℕ) :
    ((commSeq A B j : O1 n) : PO n 1) ∈ Γ := by
  induction j with
  | zero => exact hB
  | succ j ih =>
    rw [commSeq_succ]
    show (A : PO n 1) * ((commSeq A B j : O1 n) : PO n 1) * (A : PO n 1)⁻¹
        * (((commSeq A B j : O1 n) : PO n 1))⁻¹ ∈ Γ
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hA ih) (Γ.inv_mem hA)) (Γ.inv_mem ih)

/-- A sequence of natural numbers that is antitone is eventually constant. -/
lemma antitone_nat_eventually_const {c : ℕ → ℕ} (hc : Antitone c) :
    ∃ N : ℕ, ∀ n ≥ N, c n = c N := by
  have hbdd : (Set.range c).Nonempty := Set.range_nonempty c
  obtain ⟨N, hN⟩ := Nat.sInf_mem hbdd
  refine ⟨N, fun n hn => le_antisymm (hc hn) ?_⟩
  rw [hN]
  exact Nat.sInf_le (Set.mem_range_self n)

/-- Two matrices of defect `< 1` with the same image in `PO n 1` coincide. -/
lemma eq_of_near1_of_coe_eq {A B : O1 n} {s t : ℝ}
    (hcent : ∀ C : O1 n, C ∈ Subgroup.center (O1 n) ↔ C = 1 ∨ C = -1)
    (hs : s < 1) (ht : t < 1) (hA : Near1 A s) (hB : Near1 B t)
    (h : (A : PO n 1) = (B : PO n 1)) : A = B := by
  have hcenter : A⁻¹ * B ∈ Subgroup.center (O1 n) := by
    rw [← QuotientGroup.eq_one_iff]
    show ((A⁻¹ * B : O1 n) : PO n 1) = 1
    rw [show ((A⁻¹ * B : O1 n) : PO n 1) = (A : PO n 1)⁻¹ * (B : PO n 1) from rfl, h,
      inv_mul_cancel]
  have hBA : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
  rcases (hcent (A⁻¹ * B)).1 hcenter with h1 | h1
  · rw [h1, mul_one] at hBA
    exact hBA.symm
  · exfalso
    rw [h1, mul_neg, mul_one] at hBA
    have h2 := hB (Sum.inr 0) (Sum.inr 0)
    have h3 := hA (Sum.inr 0) (Sum.inr 0)
    rw [hBA] at h2
    have h4 : mat (-A) (Sum.inr 0) (Sum.inr 0) = - mat A (Sum.inr 0) (Sum.inr 0) := rfl
    rw [h4, dE_self] at h2
    rw [dE_self] at h3
    have hsum : (2:ℝ) ≤ |mat A (Sum.inr 0) (Sum.inr 0) - 1|
        + |- mat A (Sum.inr 0) (Sum.inr 0) - 1| := by
      have h5 : (2:ℝ) = |(mat A (Sum.inr 0) (Sum.inr 0) - 1)
          + (- mat A (Sum.inr 0) (Sum.inr 0) - 1)| := by
        rw [show (mat A (Sum.inr 0) (Sum.inr 0) - 1) + (- mat A (Sum.inr 0) (Sum.inr 0) - 1)
            = (-2 : ℝ) by ring, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
        norm_num
      calc (2:ℝ) = |(mat A (Sum.inr 0) (Sum.inr 0) - 1)
              + (- mat A (Sum.inr 0) (Sum.inr 0) - 1)| := h5
        _ ≤ |mat A (Sum.inr 0) (Sum.inr 0) - 1|
              + |(- mat A (Sum.inr 0) (Sum.inr 0) - 1)| := abs_add_le _ _
        _ = |mat A (Sum.inr 0) (Sum.inr 0) - 1|
              + |- mat A (Sum.inr 0) (Sum.inr 0) - 1| := rfl
    nlinarith [hsum, h2, h3]

/-- The set of elements of a discrete group having a near-identity representative of radius `r`
is finite. -/
lemma finite_nearId_set (n : ℕ) (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 < r) :
    {γ : Γ | ∃ A : O1 n, (A : PO n 1) = (γ : PO n 1) ∧ Near1 A r}.Finite := by
  have hsub : {γ : Γ | ∃ A : O1 n, (A : PO n 1) = (γ : PO n 1) ∧ Near1 A r} ⊆
      {γ : Γ | (γ : PO n 1) ∈ matBallToPO n (1 + r)} := by
    rintro γ ⟨A, hAeq, hAnear⟩
    have hentries : ∀ i j, |mat A i j| ≤ 1 + r := by
      intro i j
      refine le_trans (abs_entry_le hAnear i j) ?_
      have := abs_dE_le (n := n) i j
      linarith
    have hmem : mat A ∈ matBall n (1 + r) := ⟨hentries, O1_form_col A, O1_form_row A⟩
    have hEq : O1.ofMatrix (mat A) ⟨hmem.2.1, hmem.2.2⟩ = A :=
      Subtype.ext (mat_O1_ofMatrix (mat A) ⟨hmem.2.1, hmem.2.2⟩)
    change (γ : PO n 1) ∈ matBallToPO n (1 + r)
    rw [matBallToPO]
    refine ⟨⟨mat A, hmem⟩, Set.mem_univ _, ?_⟩
    show ((O1.ofMatrix (mat A) ⟨hmem.2.1, hmem.2.2⟩ : O1 n) : PO n 1) = (γ : PO n 1)
    rw [hEq]
    exact hAeq
  have htend : Filter.Tendsto ((↑) : Γ → PO n 1) Filter.cofinite (Filter.cocompact (PO n 1)) :=
    Subgroup.tendsto_coe_cofinite_of_isDiscrete Γ hdisc
  exact ((tendsto_cofinite_cocompact_iff.mp htend) _ (isCompact_matBallToPO (1 + r))).subset hsub

/-- **The discreteness gap**: there is an entrywise radius `r > 0` such that the only matrix in the
preimage of `Γ` within `r` of the identity is the identity. -/
theorem discrete_gap (n : ℕ) (hA : POActionProp n) (Γ : Subgroup (PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∀ A : O1 n, (A : PO n 1) ∈ Γ → Near1 A r → A = 1 := by
  have hcent := hA.1
  set S : ℝ → Set Γ := fun r => {γ : Γ | ∃ A : O1 n, (A : PO n 1) = (γ : PO n 1) ∧ Near1 A r}
    with hS
  have hfin : ∀ r : ℝ, 0 < r → (S r).Finite := fun r hr => finite_nearId_set n Γ hdisc hr
  have hmono : ∀ s t : ℝ, s ≤ t → S s ⊆ S t := by
    intro s t hst γ hγ
    obtain ⟨A, hAeq, hAnear⟩ := hγ
    exact ⟨A, hAeq, near1_mono hAnear hst⟩
  have hInter : ∀ γ : Γ, (∀ r : ℝ, 0 < r → γ ∈ S r) → γ = 1 := by
    intro γ hγ
    obtain ⟨A₀, hA₀eq, hA₀⟩ := hγ (1/2) (by norm_num)
    have hAall : ∀ r : ℝ, 0 < r → Near1 A₀ r := by
      intro r hr
      rcases le_or_gt r (1/2) with hr' | hr'
      · obtain ⟨B, hBeq, hB⟩ := hγ r hr
        have hBA : B = A₀ :=
          eq_of_near1_of_coe_eq hcent (by linarith) (by norm_num) hB hA₀
            (hBeq.trans hA₀eq.symm)
        rwa [hBA] at hB
      · exact near1_mono hA₀ (le_of_lt hr')
    have hmat : mat A₀ = 1 := by
      ext i j
      have h0 : |mat A₀ i j - dE n i j| = 0 := by
        refine le_antisymm ?_ (abs_nonneg _)
        by_contra hlt
        push_neg at hlt
        have hpos : (0:ℝ) < |mat A₀ i j - dE n i j| / 2 := by positivity
        have := hAall (|mat A₀ i j - dE n i j| / 2) hpos
        linarith [this i j]
      have h1 : mat A₀ i j = dE n i j := sub_eq_zero.mp (abs_eq_zero.mp h0)
      exact h1.trans (one_entry_eq_dE i j).symm
    have hA₀one : A₀ = 1 := Subtype.ext hmat
    have hcoe : (γ : PO n 1) = 1 := by
      rw [← hA₀eq]
      show ((A₀ : O1 n) : PO n 1) = 1
      rw [hA₀one]
      rfl
    exact Subtype.ext hcoe
  -- the decreasing family of finite sets stabilises
  have hstab : ∃ N : ℕ, ∀ m ≥ N, S ((1/2 : ℝ) ^ (m + 1)) = S ((1/2 : ℝ) ^ (N + 1)) := by
    have hanti : Antitone fun m : ℕ => (S ((1/2 : ℝ) ^ (m + 1))).ncard := by
      intro a b hab
      refine Set.ncard_le_ncard (hmono _ _ ?_) (hfin _ (by positivity))
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    obtain ⟨N, hN⟩ := antitone_nat_eventually_const hanti
    refine ⟨N, fun m hm => ?_⟩
    have h1 : S ((1/2 : ℝ) ^ (m + 1)) ⊆ S ((1/2 : ℝ) ^ (N + 1)) :=
      hmono _ _ (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
    have h2 : (S ((1/2 : ℝ) ^ (m + 1))).ncard = (S ((1/2 : ℝ) ^ (N + 1))).ncard := hN m hm
    exact Set.eq_of_subset_of_ncard_le h1 (le_of_eq h2.symm) (hfin _ (by positivity))
  obtain ⟨N, hN⟩ := hstab
  set r₀ : ℝ := (1/2 : ℝ) ^ (N + 1) with hr₀
  have hr₀pos : 0 < r₀ := by rw [hr₀]; positivity
  refine ⟨r₀, hr₀pos, ?_, ?_⟩
  · rw [hr₀]
    have h1 : (1/2 : ℝ) ^ (N + 1) ≤ (1/2 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at h1 ⊢
    linarith
  · have hset : S r₀ = {1} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · refine ⟨1, ?_, near1_mono near1_one (le_of_lt hr₀pos)⟩
        show ((1 : O1 n) : PO n 1) = ((1 : Γ) : PO n 1)
        rw [show ((1 : O1 n) : PO n 1) = 1 from rfl,
          show ((1 : Γ) : PO n 1) = 1 from rfl]
      · intro γ hγ
        refine hInter γ fun r hr => ?_
        rcases le_or_gt r₀ r with hle | hlt
        · obtain ⟨A, hAeq, hAnear⟩ := hγ
          exact ⟨A, hAeq, near1_mono hAnear hle⟩
        · obtain ⟨k, hk⟩ : ∃ k : ℕ, (1/2 : ℝ) ^ k < r :=
            exists_pow_lt_of_lt_one (show (0:ℝ) < r by positivity) (by norm_num)
          obtain ⟨m, hmN, hmn⟩ : ∃ m : ℕ, N ≤ m ∧ k ≤ m + 1 := ⟨max N k, le_max_left _ _, by omega⟩
          have hpow : (1/2 : ℝ) ^ (m + 1) ≤ (1/2 : ℝ) ^ k :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
          have hmem : γ ∈ S ((1/2 : ℝ) ^ (m + 1)) := by
            rw [hN m hmN]
            exact hγ
          obtain ⟨A, hAeq, hAnear⟩ := hmem
          exact ⟨A, hAeq, near1_mono hAnear (le_of_lt (lt_of_le_of_lt hpow hk))⟩
    intro A hAΓ hAnear
    have hmem : (⟨(A : PO n 1), hAΓ⟩ : Γ) ∈ S r₀ := ⟨A, rfl, hAnear⟩
    rw [hset] at hmem
    have hcoe : (A : PO n 1) = 1 := congrArg Subtype.val hmem
    rcases (hcent A).1 ((QuotientGroup.eq_one_iff (N := Subgroup.center (O1 n)) A).mp hcoe) with h1 | h1
    · exact h1
    · exfalso
      have h2 : mat (-1 : O1 n) (Sum.inr 0) (Sum.inr 0) = -1 := rfl
      have h3 := hAnear (Sum.inr 0) (Sum.inr 0)
      rw [h1, h2, dE_self] at h3
      have hr2 : r₀ ≤ 1 / 2 := by
        rw [hr₀]
        have h1' : (1/2 : ℝ) ^ (N + 1) ≤ (1/2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        norm_num at h1' ⊢
        linarith
      have := abs_le.mp h3
      linarith [this.1]
/-! ## The delegated geometric inputs

The parabolic endgame is proved in `Submission.Work.Mostow.Margulis.same_point_pair_commuting`
and the loxodromic one in `Submission.Work.Mostow.Margulis.same_pair_pair_commuting`; both are
imported above. -/

/-! ## Geometric helpers for the boundary fixed sets -/

/-- `bd g` is injective on the sphere. -/
lemma bd_inj_on_sph (hA : POActionProp n) (g : PO n 1) :
    ∀ x y : E n, x ∈ Sph n → y ∈ Sph n → bd g x = bd g y → x = y := by
  intro x y hx hy hxy
  have h := congrArg (bd g⁻¹) hxy
  rwa [bd_inv_apply (g := g) hA hx, bd_inv_apply (g := g) hA hy] at h

/-- If `g` has no fixed point in `ℍⁿ`, then neither does `g ^ 2`. -/
lemma noFixed_pow_two (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {g : PO n 1} (hg : ∀ u : E n, g • u ≠ u) : ∀ u : E n, (g ^ 2) • u ≠ u := by
  intro u hu
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hpar : ∀ m : ℕ, (g ^ m) • u = u ∨ (g ^ m) • u = g • u := by
    intro m
    induction m with
    | zero => exact Or.inl (by simpa using hone u)
    | succ m ih =>
      rw [pow_succ', hmul]
      rcases ih with h | h
      · rw [h]; exact Or.inr rfl
      · left
        rw [h, show g • (g • u) = (g ^ 2) • u from by rw [pow_two, hmul g g u]]
        exact hu
  have hbdd : ∃ R : ℝ, ∀ m : ℕ, hdist u ((g ^ m) • u) ≤ R := by
    refine ⟨hdist u (g • u), fun m => ?_⟩
    rcases hpar m with h | h
    · rw [h]
      exact le_trans (le_of_eq (show hdist u u = 0 from (hI.2.2.1 u u).mpr rfl)) (hI.1 u (g • u))
    · rw [h]
  obtain ⟨v, hv⟩ := boundedOrbitFixed n hn hA hI g u hbdd
  exact hg v hv

/-- `g` maps the fixed set of `g ^ 2` into itself. -/
lemma mapsTo_bdFix_pow_two (hA : POActionProp n) (g : PO n 1) :
    ∀ ζ ∈ bdFix (g ^ 2), bd g ζ ∈ bdFix (g ^ 2) := by
  intro ζ hζ
  have hSph : ∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  refine ⟨hSph g ζ hζ.1, ?_⟩
  have h1 : bd (g ^ 2) ζ = ζ := hζ.2
  rw [show bd (g ^ 2) (bd g ζ) = bd (g * g) (bd g ζ) from by rw [pow_two],
    hbdmul g g (bd g ζ) (hSph g ζ hζ.1)]
  congr 1
  rw [← hbdmul g g ζ hζ.1, ← pow_two]
  exact h1

/-- If `bd g` maps the two-element set `{ζ, θ}` into itself, then `g ^ 2` fixes both points. -/
lemma sq_fixes_pair (hA : POActionProp n) (g : PO n 1) {ζ θ : E n} (hne : ζ ≠ θ)
    (hζ : ζ ∈ Sph n) (hθ : θ ∈ Sph n)
    (hmap : ∀ y ∈ ({ζ, θ} : Set (E n)), bd g y ∈ ({ζ, θ} : Set (E n))) :
    bd (g ^ 2) ζ = ζ ∧ bd (g ^ 2) θ = θ := by
  have hinj := bd_inj_on_sph hA g
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  have hζ' : bd g ζ = ζ ∨ bd g ζ = θ :=
    Set.mem_insert_iff.mp (hmap ζ (Set.mem_insert_iff.mpr (Or.inl rfl)))
  have hθ' : bd g θ = ζ ∨ bd g θ = θ :=
    Set.mem_insert_iff.mp (hmap θ (Set.mem_insert_iff.mpr (Or.inr rfl)))
  have key : ∀ y ∈ ({ζ, θ} : Set (E n)), bd (g ^ 2) y = y := by
    intro y hy
    have hySph : y ∈ Sph n := by
      rcases Set.mem_insert_iff.mp hy with h | h
      · rw [h]; exact hζ
      · rw [Set.mem_singleton_iff.mp h]; exact hθ
    rw [pow_two, hbdmul g g y hySph]
    rcases Set.mem_insert_iff.mp hy with h | h
    · rw [h]
      rcases hζ' with h1 | h1
      · rw [h1]
        rcases hθ' with h2 | h2
        · exact absurd (hinj θ ζ hθ hζ (h2.trans h1.symm)) (fun hc => hne hc.symm)
        · exact h1
      · rw [h1]
        rcases hθ' with h2 | h2
        · exact h2
        · exact absurd (hinj ζ θ hζ hθ (h1.trans h2.symm)) hne
    · rw [Set.mem_singleton_iff.mp h]
      rcases hθ' with h2 | h2
      · rw [h2]
        rcases hζ' with h1 | h1
        · exact absurd (hinj ζ θ hζ hθ (h1.trans h2.symm)) hne
        · exact h1
      · rw [h2]
        exact h2
  exact ⟨key ζ (Set.mem_insert_iff.mpr (Or.inl rfl)),
    key θ (Set.mem_insert_iff.mpr (Or.inr rfl))⟩

/-- For `g` with no fixed point, `bdFix (g ^ 2) = bdFix g`. -/
lemma bdFix_pow_two (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {g : PO n 1} (hg : ∀ u : E n, g • u ≠ u) : bdFix (g ^ 2) = bdFix g := by
  have hno2 : ∀ u : E n, (g ^ 2) • u ≠ u := noFixed_pow_two hA hI hn hg
  have hsub : bdFix g ⊆ bdFix (g ^ 2) := by
    intro ζ hζ
    refine ⟨hζ.1, ?_⟩
    have h := hA.2.2.2.2.2.2.2.2.2.1 g g ζ hζ.1
    rw [hζ.2] at h
    rw [pow_two]
    exact h.trans hζ.2
  have hne : (bdFix g).Nonempty := by
    rcases bdFix_size_of_no_fixed_point n hA hI g hg with ⟨a, -, ha⟩ | ⟨a, -, b, -, -, ha⟩
    · exact ⟨a, by rw [ha]; exact Set.mem_singleton_iff.mpr rfl⟩
    · exact ⟨a, by rw [ha]; exact Set.mem_insert_iff.mpr (Or.inl rfl)⟩
  rcases bdFix_size_of_no_fixed_point n hA hI (g ^ 2) hno2 with ⟨ζ, -, hζ⟩ | ⟨ζ, -, θ, -, hζθ, hθ⟩
  · -- `bdFix (g ^ 2) = {ζ}`
    obtain ⟨x, hx⟩ := hne
    have hx2 : x ∈ bdFix (g ^ 2) := hsub hx
    have hxζ : x = ζ := by rw [hζ] at hx2; exact Set.mem_singleton_iff.mp hx2
    have h1 : bdFix g ⊆ ({ζ} : Set (E n)) := by
      intro y hy
      have hy2 : y ∈ bdFix (g ^ 2) := hsub hy
      rwa [hζ] at hy2
    have h2 : ({ζ} : Set (E n)) ⊆ bdFix g := by
      intro y hy
      have hyζ : y = ζ := Set.mem_singleton_iff.mp hy
      rw [hyζ, ← hxζ]
      exact hx
    rw [hζ]
    exact Set.Subset.antisymm h2 h1
  · -- `bdFix (g ^ 2) = {ζ, θ}`
    have hmemmap : ∀ y ∈ ({ζ, θ} : Set (E n)), bd g y ∈ ({ζ, θ} : Set (E n)) := by
      intro y hy
      have h1 : bd g y ∈ bdFix (g ^ 2) := mapsTo_bdFix_pow_two hA g y (by rw [hθ]; exact hy)
      rwa [hθ] at h1
    have hζSph : ζ ∈ Sph n := by
      have h : ζ ∈ bdFix (g ^ 2) := by rw [hθ]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
      exact h.1
    have hθSph : θ ∈ Sph n := by
      have h : θ ∈ bdFix (g ^ 2) := by
        rw [hθ]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
      exact h.1
    have hinj := bd_inj_on_sph hA g
    obtain ⟨x, hx⟩ := hne
    have hx2 : x ∈ bdFix (g ^ 2) := hsub hx
    have hxpair : x = ζ ∨ x = θ := by rw [hθ] at hx2; exact Set.mem_insert_iff.mp hx2
    have hgx : bd g x = x := hx.2
    have hgζ : bd g ζ = ζ := by
      rcases hxpair with hxz | hxθ
      · rw [hxz] at hgx; exact hgx
      · rw [hxθ] at hgx
        rcases Set.mem_insert_iff.mp (hmemmap ζ (Set.mem_insert_iff.mpr (Or.inl rfl))) with h | h
        · exact h
        · exact absurd (hinj ζ θ hζSph hθSph (h.trans hgx.symm)) hζθ
    have hgθ : bd g θ = θ := by
      rcases hxpair with hxz | hxθ
      · rw [hxz] at hgx
        rcases Set.mem_insert_iff.mp (hmemmap θ (Set.mem_insert_iff.mpr (Or.inr rfl))) with h | h
        · exact absurd (hinj θ ζ hθSph hζSph (h.trans hgx.symm)) (fun hc => hζθ hc.symm)
        · exact h
      · rw [hxθ] at hgx; exact hgx
    have h2 : ({ζ, θ} : Set (E n)) ⊆ bdFix g := by
      intro y hy
      rcases Set.mem_insert_iff.mp hy with h | h
      · rw [h]; exact ⟨hζSph, hgζ⟩
      · rw [Set.mem_singleton_iff.mp h]; exact ⟨hθSph, hgθ⟩
    have h1 : bdFix g ⊆ ({ζ, θ} : Set (E n)) := by
      intro y hy
      have hy2 : y ∈ bdFix (g ^ 2) := hsub hy
      rwa [hθ] at hy2
    rw [hθ]
    exact Set.Subset.antisymm h2 h1

/-- Two elements of `PO n 1` without fixed points, each preserving the other's boundary fixed set,
have the same boundary fixed set. -/
lemma bdFix_eq_of_perm (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {a b : PO n 1} (ha : ∀ u : E n, a • u ≠ u) (hb : ∀ u : E n, b • u ≠ u)
    (hba : ∀ ζ ∈ bdFix b, bd a ζ ∈ bdFix b)
    (hab : ∀ ζ ∈ bdFix a, bd b ζ ∈ bdFix a) :
    bdFix a = bdFix b := by
  have h2a : bdFix (a ^ 2) = bdFix a := bdFix_pow_two hA hI hn ha
  have h2b : bdFix (b ^ 2) = bdFix b := bdFix_pow_two hA hI hn hb
  have hinl : ∀ (g : PO n 1) (ξ η : E n), bdFix g = {ξ, η} → ξ ∈ Sph n :=
    fun g ξ η hF => (show ξ ∈ bdFix g from by rw [hF]; exact Set.mem_insert_iff.mpr (Or.inl rfl)).1
  have hinr : ∀ (g : PO n 1) (ξ η : E n), bdFix g = {ξ, η} → η ∈ Sph n :=
    fun g ξ η hF =>
      (show η ∈ bdFix g from by
        rw [hF]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))).1
  rcases bdFix_size_of_no_fixed_point n hA hI a ha with ⟨ξ, hξ, hF⟩ | ⟨ξ, hξ, η, hη, hne, hF⟩
  · -- `bdFix a = {ξ}`
    rcases bdFix_size_of_no_fixed_point n hA hI b hb with ⟨ξ', hξ', hF'⟩ | ⟨ξ', hξ', η', hη', hne', hF'⟩
    · -- both singletons
      have h1 : bd b ξ ∈ bdFix a := hab ξ (by rw [hF]; exact Set.mem_singleton_iff.mpr rfl)
      rw [hF] at h1
      have h2 : ξ ∈ bdFix b := ⟨hξ, Set.mem_singleton_iff.mp h1⟩
      rw [hF'] at h2
      rw [hF, hF', Set.mem_singleton_iff.mp h2]
    · -- `a` fixes one point and permutes a pair of fixed points: impossible
      exfalso
      have hξ'Sph : ξ' ∈ Sph n := hinl b ξ' η' hF'
      have hη'Sph : η' ∈ Sph n := hinr b ξ' η' hF'
      have hmap : ∀ y ∈ ({ξ', η'} : Set (E n)), bd a y ∈ ({ξ', η'} : Set (E n)) := by
        intro y hy
        have h := hba y (by rw [hF']; exact hy)
        rwa [hF'] at h
      have hsq := sq_fixes_pair hA a hne' hξ'Sph hη'Sph hmap
      have hm1 : ξ' ∈ bdFix a := by rw [← h2a]; exact ⟨hξ'Sph, hsq.1⟩
      have hm2 : η' ∈ bdFix a := by rw [← h2a]; exact ⟨hη'Sph, hsq.2⟩
      rw [hF] at hm1 hm2
      exact hne' ((Set.mem_singleton_iff.mp hm1).trans (Set.mem_singleton_iff.mp hm2).symm)
  · -- `bdFix a = {ξ, η}`
    rcases bdFix_size_of_no_fixed_point n hA hI b hb with ⟨ξ', hξ', hF'⟩ | ⟨ξ', hξ', η', hη', hne', hF'⟩
    · -- `b` fixes one point and permutes a pair of fixed points: impossible
      exfalso
      have hξSph : ξ ∈ Sph n := hinl a ξ η hF
      have hηSph : η ∈ Sph n := hinr a ξ η hF
      have hmap : ∀ y ∈ ({ξ, η} : Set (E n)), bd b y ∈ ({ξ, η} : Set (E n)) := by
        intro y hy
        have h := hab y (by rw [hF]; exact hy)
        rwa [hF] at h
      have hsq := sq_fixes_pair hA b hne hξSph hηSph hmap
      have hm1 : ξ ∈ bdFix b := by rw [← h2b]; exact ⟨hξSph, hsq.1⟩
      have hm2 : η ∈ bdFix b := by rw [← h2b]; exact ⟨hηSph, hsq.2⟩
      rw [hF'] at hm1 hm2
      exact hne ((Set.mem_singleton_iff.mp hm1).trans (Set.mem_singleton_iff.mp hm2).symm)
    · -- both pairs
      have hξSph : ξ ∈ Sph n := hinl a ξ η hF
      have hηSph : η ∈ Sph n := hinr a ξ η hF
      have hξ'Sph : ξ' ∈ Sph n := hinl b ξ' η' hF'
      have hη'Sph : η' ∈ Sph n := hinr b ξ' η' hF'
      have hmap : ∀ y ∈ ({ξ', η'} : Set (E n)), bd a y ∈ ({ξ', η'} : Set (E n)) := by
        intro y hy
        have h := hba y (by rw [hF']; exact hy)
        rwa [hF'] at h
      have hsq := sq_fixes_pair hA a hne' hξ'Sph hη'Sph hmap
      have hm1 : ξ' ∈ bdFix a := by rw [← h2a]; exact ⟨hξ'Sph, hsq.1⟩
      have hm2 : η' ∈ bdFix a := by rw [← h2a]; exact ⟨hη'Sph, hsq.2⟩
      have hsub : ({ξ', η'} : Set (E n)) ⊆ bdFix a := by
        intro y hy
        rcases Set.mem_insert_iff.mp hy with h | h
        · rw [h]; exact hm1
        · rw [Set.mem_singleton_iff.mp h]; exact hm2
      have hcard : (bdFix a).ncard = ({ξ', η'} : Set (E n)).ncard := by
        rw [hF, Set.ncard_pair hne, Set.ncard_pair hne']
      have hfinal : ({ξ', η'} : Set (E n)) = bdFix a :=
        Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard)
          (by rw [hF]; exact (Set.finite_singleton η).insert ξ)
      rw [hF', ← hfinal]

/-- Powers of an element fixing `u` under the chart action fix `u`. -/
lemma pow_smul_eq_self {g : PO n 1} {u : E n} (hA : POActionProp n) (h : g • u = u) (j : ℕ) :
    (g ^ j) • u = u := by
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  induction j with
  | zero => simpa using hone u
  | succ j ih => rw [pow_succ, hmul, h, ih]

/-- An element of a discrete subgroup with a fixed point in `ℍⁿ` has finite order. -/
lemma pow_eq_one_of_fixed_point (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) (γ : Γ)
    (hfix : ∃ u : E n, (γ : PO n 1) • u = u) :
    ∃ k : ℕ, 0 < k ∧ (γ : PO n 1) ^ k = 1 := by
  obtain ⟨u, hu⟩ := hfix
  have hdtri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z := hI.2.2.2.1
  have hisom : ∀ (g : PO n 1) (x y : E n), hdist (g • x) (g • y) = hdist x y :=
    hI.2.2.2.2.2.2.1
  have hdsym : ∀ x y : E n, hdist x y = hdist y x := hI.2.1
  have hsub : {g : Γ | (g : PO n 1) • u = u} ⊆
      {g : Γ | hdist 0 ((g : PO n 1) • (0 : E n)) ≤ 2 * hdist 0 u} := by
    intro g hg
    have h1 : hdist 0 ((g : PO n 1) • (0 : E n))
        ≤ hdist 0 ((g : PO n 1) • u) + hdist ((g : PO n 1) • u) ((g : PO n 1) • (0 : E n)) :=
      hdtri 0 ((g : PO n 1) • u) ((g : PO n 1) • (0 : E n))
    rw [hisom g u 0, hdsym u 0, hg] at h1
    rw [two_mul]
    exact h1
  have hfin := (finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc
    (2 * hdist 0 u)).subset hsub
  have hmaps : Set.MapsTo (fun j : ℕ => (γ ^ j : Γ)) Set.univ
      {g : Γ | (g : PO n 1) • u = u} := by
    intro j _
    exact pow_smul_eq_self hA hu j
  obtain ⟨a, -, b, -, hab, heq⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (Set.infinite_univ (α := ℕ)) hmaps hfin
  have h2 : (γ : PO n 1) ^ a = (γ : PO n 1) ^ b := congrArg (fun g : Γ => (g : PO n 1)) heq
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨b - a, by omega, ?_⟩
    have h3 : (γ : PO n 1) ^ b = (γ : PO n 1) ^ a * (γ : PO n 1) ^ (b - a) := by
      rw [← pow_add]; congr 1; omega
    rw [h3] at h2
    exact mul_left_cancel (a := (γ : PO n 1) ^ a) (by rw [mul_one]; exact h2.symm)
  · refine ⟨a - b, by omega, ?_⟩
    have h3 : (γ : PO n 1) ^ a = (γ : PO n 1) ^ b * (γ : PO n 1) ^ (a - b) := by
      rw [← pow_add]; congr 1; omega
    rw [h3] at h2
    exact mul_left_cancel (a := (γ : PO n 1) ^ b) (by rw [mul_one]; exact h2)

/-- If `A`, `B` are near the identity and their images lie in a discrete group, then some iterated
commutator `commSeq A B j` is the identity. -/
theorem commSeq_eq_one {Γ : Subgroup (PO n 1)} (hA : POActionProp n)
    (hdisc : IsDiscrete (SetLike.coe Γ)) {A B : O1 n} {q : ℝ} (hq : 0 < q)
    (hsmall : 8 * (msz n) ^ 3 * q ≤ 1 / 2) (hq1 : q ≤ 1)
    (hA' : Near1 A q) (hB' : Near1 B q) (hAmem : (A : PO n 1) ∈ Γ)
    (hBmem : (B : PO n 1) ∈ Γ) :
    ∃ j : ℕ, commSeq A B j = 1 := by
  obtain ⟨r, hrpos, -, hgap⟩ := discrete_gap n hA Γ hdisc
  have hqr : (0:ℝ) < r / q := div_pos hrpos hq
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 / 2 : ℝ) ^ j < r / q :=
    exists_pow_lt_of_lt_one hqr (by norm_num)
  have hjq : (1 / 2 : ℝ) ^ j * q < r := by
    have h := mul_lt_mul_of_pos_right hj hq
    rwa [div_mul_cancel₀ r (ne_of_gt hq)] at h
  have hmem : ((commSeq A B j : O1 n) : PO n 1) ∈ Γ := commSeq_mem hAmem hBmem j
  have hnear : Near1 (commSeq A B j) r :=
    near1_mono (near1_commSeq hA' hB' (le_of_lt hq) hsmall hq1 j) (le_of_lt hjq)
  exact ⟨j, hgap (commSeq A B j) hmem hnear⟩

/-! ## The main theorem -/

theorem nearId_pair_commuting (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 1000 ∧
      ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
        ∀ γ δ : Γ, NearId q (γ : PO n 1) → NearId q (δ : PO n 1) →
          ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
            (γ : PO n 1) ^ m * (δ : PO n 1) ^ k = (δ : PO n 1) ^ k * (γ : PO n 1) ^ m := by
  refine ⟨margQ n, margQ_pos n, margQ_le n, ?_⟩
  intro Γ hdisc γ δ hγ hδ
  have hγ' : NearId (margQ n) (γ : PO n 1) := hγ
  have hδ' : NearId (margQ n) (δ : PO n 1) := hδ
  obtain ⟨A, hAeq, hAnear⟩ := hγ
  obtain ⟨B, hBeq, hBnear⟩ := hδ
  -- the finite order cases
  by_cases hfγ : ∃ u : E n, (γ : PO n 1) • u = u
  · obtain ⟨k, hk, hk1⟩ := pow_eq_one_of_fixed_point n hA hI Γ hdisc γ hfγ
    exact ⟨k, 1, hk, Nat.one_pos, by rw [hk1, one_mul, mul_one]⟩
  by_cases hfδ : ∃ u : E n, (δ : PO n 1) • u = u
  · obtain ⟨k, hk, hk1⟩ := pow_eq_one_of_fixed_point n hA hI Γ hdisc δ hfδ
    exact ⟨1, k, Nat.one_pos, hk, by rw [hk1, one_mul, mul_one]⟩
  have hnfγ : ∀ u : E n, (γ : PO n 1) • u ≠ u := fun u hu => hfγ ⟨u, hu⟩
  have hnfδ : ∀ u : E n, (δ : PO n 1) • u ≠ u := fun u hu => hfδ ⟨u, hu⟩
  have hn1 : 1 ≤ n := by omega
  -- the commutator sequences terminate
  obtain ⟨j, hj⟩ := commSeq_eq_one (Γ := Γ) hA hdisc (margQ_pos n) (margQ_small n)
    (margQ_le_one n) hAnear hBnear (hAeq ▸ γ.2) (hBeq ▸ δ.2)
  obtain ⟨j', hj'⟩ := commSeq_eq_one (Γ := Γ) hA hdisc (margQ_pos n) (margQ_small n)
    (margQ_le_one n) hBnear hAnear (hBeq ▸ δ.2) (hAeq ▸ γ.2)
  -- the propagation
  have hpropγ : ∀ ζ ∈ bdFix (γ : PO n 1), bd (δ : PO n 1) ζ ∈ bdFix (γ : PO n 1) := by
    have h1 : commSeqG (γ : PO n 1) (δ : PO n 1) j = 1 := by
      have h2 : ((commSeq A B j : O1 n) : PO n 1) = commSeqG (γ : PO n 1) (δ : PO n 1) j := by
        rw [commSeq_coe, hAeq, hBeq]
      rw [hj] at h2
      exact h2.symm
    have key : ∀ i : ℕ, ∀ m : ℕ, m + i = j →
        ∀ ζ ∈ bdFix (γ : PO n 1),
          bd (commSeqG (γ : PO n 1) (δ : PO n 1) m) ζ ∈ bdFix (γ : PO n 1) := by
      intro i
      induction i with
      | zero =>
        intro m hm ζ hζ
        have hmj : m = j := by omega
        subst hmj
        rw [h1]
        have hbd1 : ∀ ζ : E n, ζ ∈ Sph n → bd (1 : PO n 1) ζ = ζ := hA.2.2.2.2.2.2.2.2.1
        rw [hbd1 ζ hζ.1]
        exact hζ
      | succ i ih =>
        intro m hm ζ hζ
        have hmP : ∀ y ∈ bdFix (γ : PO n 1),
            bd (commSeqG (γ : PO n 1) (δ : PO n 1) (m + 1)) y ∈ bdFix (γ : PO n 1) :=
          ih (m + 1) (by omega)
        refine bd_set_prop n hA hI hn1 hnfγ ?_ ζ hζ
        intro y hy
        rw [← commSeqG_succ]
        exact hmP y hy
    exact key j 0 (by omega)
  have hpropδ : ∀ ζ ∈ bdFix (δ : PO n 1), bd (γ : PO n 1) ζ ∈ bdFix (δ : PO n 1) := by
    have h1 : commSeqG (δ : PO n 1) (γ : PO n 1) j' = 1 := by
      have h2 : ((commSeq B A j' : O1 n) : PO n 1) = commSeqG (δ : PO n 1) (γ : PO n 1) j' := by
        rw [commSeq_coe, hBeq, hAeq]
      rw [hj'] at h2
      exact h2.symm
    have key : ∀ i : ℕ, ∀ m : ℕ, m + i = j' →
        ∀ ζ ∈ bdFix (δ : PO n 1),
          bd (commSeqG (δ : PO n 1) (γ : PO n 1) m) ζ ∈ bdFix (δ : PO n 1) := by
      intro i
      induction i with
      | zero =>
        intro m hm ζ hζ
        have hmj : m = j' := by omega
        subst hmj
        rw [h1]
        have hbd1 : ∀ ζ : E n, ζ ∈ Sph n → bd (1 : PO n 1) ζ = ζ := hA.2.2.2.2.2.2.2.2.1
        rw [hbd1 ζ hζ.1]
        exact hζ
      | succ i ih =>
        intro m hm ζ hζ
        have hmP : ∀ y ∈ bdFix (δ : PO n 1),
            bd (commSeqG (δ : PO n 1) (γ : PO n 1) (m + 1)) y ∈ bdFix (δ : PO n 1) :=
          ih (m + 1) (by omega)
        refine bd_set_prop n hA hI hn1 hnfδ ?_ ζ hζ
        intro y hy
        rw [← commSeqG_succ]
        exact hmP y hy
    exact key j' 0 (by omega)
  -- case analysis on the boundary fixed sets
  have hFixEq : bdFix (γ : PO n 1) = bdFix (δ : PO n 1) :=
    bdFix_eq_of_perm hA hI hn1 hnfγ hnfδ hpropδ hpropγ
  rcases bdFix_size_of_no_fixed_point n hA hI (γ : PO n 1) hnfγ with
    ⟨ξ, hξ, hFγ⟩ | ⟨ξ, hξ, η, hη, hne, hFγ⟩
  · exact same_point_pair_commuting n hn hA hI Γ hdisc γ δ (margQ n) (margQ_pos n)
      (margQ_small n) hγ' hδ' hnfγ hnfδ ξ hξ hFγ (by rw [← hFixEq]; exact hFγ)
  · exact same_pair_pair_commuting n hn hA hI Γ hdisc γ δ (margQ n) (margQ_pos n)
      (margQ_small n) hγ' hδ' hnfγ hnfδ ξ η hξ hη hne hFγ (by rw [← hFixEq]; exact hFγ)

end

end Work.Mostow.Margulis
