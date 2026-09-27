import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.nearStabDefs
import Submission.Work.Mostow.isCompact_matBallToPO
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.boundedOrbitFixed

/-!
# Snapshot of the commutator/discreteness machinery (support module)

`Work.Mostow.margulisCuspV2` (and the Zassenhaus argument it contains) needs the
iterated-commutator sequence `commSeq`/`commSeqG`, the two-radius commutator estimate
`near1_commutator_gen` and the discreteness gap `discrete_gap`.  These live in
`Submission/Work/Mostow/Margulis/nearId_pair_commuting.lean`, which is being extended by
another agent and does not currently compile; this file is a verbatim snapshot of the
(compiling) prefix of that file so that `margulisCuspV2` does not depend on their
in-flight edits.  Its declarations live in the separate namespace
`Work.Mostow.Margulis.Snap` so that importing this module together with the original (or with
`toO_ci_shrink`, which imports it) cannot produce duplicate declarations.
-/
namespace Work.Mostow.Margulis.Snap

set_option maxHeartbeats 1000000

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

end

end Work.Mostow.Margulis.Snap
