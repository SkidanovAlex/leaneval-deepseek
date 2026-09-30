import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.bprod_real_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- `bwW η n = ∏_{i=1}^{n} (i - η)`. -/
noncomputable def bwW (η : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 n, ((i : ℝ) - η)

lemma bwW_zero (η : ℝ) : bwW η 0 = 1 := by simp [bwW]

lemma bwW_succ (η : ℝ) (n : ℕ) :
    bwW η (n + 1) = bwW η n * ((n : ℝ) + 1 - η) := by
  unfold bwW
  rw [Finset.prod_Icc_succ_top (show (1:ℕ) ≤ n + 1 by omega) (fun i => ((i:ℝ) - η))]
  push_cast
  ring

lemma bwW_lower_succ (η : ℝ) (h1 : η < 1) (n : ℕ) :
    (1 - η) * ((n.factorial : ℕ) : ℝ) ≤ bwW η (n + 1) := by
  have h1n : (0:ℝ) ≤ 1 - η := by linarith
  induction n with
  | zero =>
    rw [bwW_succ, bwW_zero, Nat.factorial_zero, Nat.cast_one]
    apply le_of_eq; ring
  | succ m ih =>
    rw [bwW_succ, Nat.factorial_succ]
    push_cast
    have hW : (0:ℝ) ≤ bwW η (m + 1) :=
      le_trans (mul_nonneg h1n (Nat.cast_nonneg _)) ih
    have hstep : ((m:ℝ) + 1) ≤ (m:ℝ) + 1 + 1 - η := by linarith
    have hmain := mul_le_mul ih hstep (by positivity) hW
    calc (1 - η) * ((↑m + 1) * ↑(m.factorial))
        = ((1 - η) * ↑(m.factorial)) * (↑m + 1) := by ring
      _ ≤ bwW η (m + 1) * (↑m + 1 + 1 - η) := hmain

lemma bwW_lower (η : ℝ) (h0 : 0 ≤ η) (h1 : η < 1) (n : ℕ) :
    (1 - η) * (((n - 1).factorial : ℕ) : ℝ) ≤ bwW η n := by
  cases n with
  | zero =>
    rw [bwW_zero]
    simp only [Nat.zero_sub, Nat.factorial_zero, Nat.cast_one, mul_one]
    linarith
  | succ k =>
    rw [show (k + 1) - 1 = k by omega]
    exact bwW_lower_succ η h1 k

/-- `bprod` splits into the `k = 0` factor and the pairs `±k`. -/
lemma bprod_split_aux (R : ℝ) (z : ℂ) (X : ℕ) :
    bprod R X z
      = bfac R 0 z * ∏ k ∈ Finset.Icc 1 X, (bfac R (k : ℤ) z * bfac R (-(k : ℤ)) z) := by
  induction X with
  | zero => simp [bprod]
  | succ n ih =>
    rw [bprod_peel, ih, Finset.prod_Icc_succ_top (show (1:ℕ) ≤ n + 1 by omega)
      (fun k => (bfac R (k : ℤ) z * bfac R (-(k : ℤ)) z))]
    push_cast
    ring

/-- `‖β(z;0)‖ = ‖z‖/R` for `R > 0`. -/
lemma bfac_zero_complex (R : ℝ) (hR : 0 < R) (z : ℂ) :
    ‖bfac R 0 z‖ = ‖z‖ / R := by
  have hRne : (R : ℂ) ≠ 0 := by
    intro hcon
    have h0 : R = 0 := by exact_mod_cast hcon
    linarith
  have h : bfac R 0 z = z / (R : ℂ) := by
    unfold bfac
    push_cast
    field_simp
    ring
  rw [h, norm_div, Complex.norm_of_nonneg (le_of_lt hR)]

/-- Shifting the index set: `∏_{k=1}^{X}(k + r - η) = ∏_{j=r+1}^{r+X}(j - η)`. -/
lemma prod_shift_Icc (η : ℝ) (X r : ℕ) :
    (∏ k ∈ Finset.Icc 1 X, (((k:ℝ) + (r:ℝ)) - η))
      = ∏ j ∈ Finset.Icc (r + 1) (r + X), ((j:ℝ) - η) := by
  have h1 : (∏ k ∈ Finset.Icc 1 X, (((k:ℝ) + (r:ℝ)) - η))
      = ∏ k ∈ Finset.Ico 1 (X + 1), (((k:ℝ) + (r:ℝ)) - η) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  have h2 : (∏ j ∈ Finset.Icc (r + 1) (r + X), ((j:ℝ) - η))
      = ∏ j ∈ Finset.Ico (r + 1) ((r + X) + 1), ((j:ℝ) - η) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  rw [h1, h2]
  have h3 : (∏ k ∈ Finset.Ico 1 (X + 1), (((k:ℝ) + (r:ℝ)) - η))
      = ∏ k ∈ Finset.Ico 1 (X + 1), ((fun j : ℕ => ((j:ℝ) - η)) (r + k)) := by
    apply Finset.prod_congr rfl
    intro k _
    push_cast
    ring
  rw [h3, Finset.prod_Ico_add (fun j : ℕ => ((j:ℝ) - η)) 1 (X + 1) r]
  rw [show Finset.Ico (1 + r) ((X + 1) + r) = Finset.Ico (r + 1) ((r + X) + 1) by
    congr 1 <;> omega]

/-- Splitting `bwW η (X+r)` off its first `r` factors. -/
lemma bwW_consecutive (η : ℝ) (X r : ℕ) :
    bwW η (X + r) = bwW η r * ∏ j ∈ Finset.Icc (r + 1) (r + X), ((j:ℝ) - η) := by
  have e1 : bwW η r = ∏ j ∈ Finset.Ico 1 (r + 1), ((j:ℝ) - η) := by
    rw [bwW, Finset.Ico_add_one_right_eq_Icc]
  have e2 : bwW η (X + r) = ∏ j ∈ Finset.Ico 1 (X + r + 1), ((j:ℝ) - η) := by
    rw [bwW, Finset.Ico_add_one_right_eq_Icc]
  have e3 : (∏ j ∈ Finset.Icc (r + 1) (r + X), ((j:ℝ) - η))
      = ∏ j ∈ Finset.Ico (r + 1) (X + r + 1), ((j:ℝ) - η) := by
    rw [Finset.Ico_add_one_right_eq_Icc, show r + X = X + r by omega]
  have hcon := Finset.prod_Ico_consecutive (fun j : ℕ => ((j:ℝ) - η))
      (show (1:ℕ) ≤ r + 1 by omega) (show r + 1 ≤ X + r + 1 by omega)
  rw [e1, e2, e3, hcon]

/-- Peeling the last factor of `bwW`. -/
lemma bwW_peel (η : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    bwW η r = bwW η (r - 1) * ((r:ℝ) - η) := by
  conv_lhs => rw [← Nat.sub_add_cancel hr]
  rw [bwW_succ]
  have hc : (((r - 1 : ℕ)):ℝ) + 1 = (r:ℝ) := by
    rw [Nat.cast_sub hr]; ring
  rw [hc]

set_option maxHeartbeats 1000000 in
/-- The product of `| |k − r| − η |` over `1 ≤ k ≤ X`. -/
lemma bwW_abs_split (η : ℝ) (h0 : 0 ≤ η) (h1 : η < 1) (X r : ℕ) (hr : 1 ≤ r) (hrX : r ≤ X) :
    (∏ k ∈ Finset.Icc 1 X, |(|(k:ℝ) - (r:ℝ)|) - η|)
      = η * bwW η (r - 1) * bwW η (X - r) := by
  refine Nat.le_induction (m := r) ?base ?step X hrX
  · rw [Nat.sub_self, bwW_zero, mul_one]
    have hgr : |(|(r:ℝ) - (r:ℝ)|) - η| = η := by
      rw [sub_self, abs_zero, zero_sub, abs_neg, abs_of_nonneg h0]
    have hp : (∏ k ∈ Finset.Icc 1 r, |(|(k:ℝ) - (r:ℝ)|) - η|)
        = (∏ k ∈ Finset.Ico 1 r, |(|(k:ℝ) - (r:ℝ)|) - η|) * η := by
      rw [← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := r)]
      rw [Finset.prod_Ico_succ_top (show (1:ℕ) ≤ r by omega)
        (fun k => |(|(k:ℝ) - (r:ℝ)|) - η|)]
      rw [hgr]
    rw [hp]
    have hp2 : (∏ k ∈ Finset.Ico 1 r, |(|(k:ℝ) - (r:ℝ)|) - η|) = bwW η (r - 1) := by
      have h1' : (∏ k ∈ Finset.Ico 1 r, |(|(k:ℝ) - (r:ℝ)|) - η|)
          = ∏ k ∈ Finset.Ico 1 r, ((((r - k : ℕ)):ℝ) - η) := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [Finset.mem_Ico] at hk
        have hkr : k ≤ r := by omega
        have hle : (k:ℝ) ≤ (r:ℝ) := by exact_mod_cast hkr
        rw [abs_of_nonpos (by linarith : (k:ℝ) - (r:ℝ) ≤ 0), neg_sub]
        rw [← Nat.cast_sub hkr]
        have h3 : (0:ℝ) ≤ (((r - k : ℕ)):ℝ) - η := by
          have hk1 : (1:ℝ) ≤ ((r - k : ℕ):ℝ) := by
            have : 1 ≤ r - k := by omega
            exact_mod_cast this
          linarith
        rw [abs_of_nonneg h3]
      rw [h1']
      rw [Finset.prod_Ico_reflect (fun j : ℕ => ((j:ℝ) - η)) 1 (m := r) (n := r) (by omega)]
      rw [show r + 1 - r = 1 by omega, show r + 1 - 1 = r by omega]
      unfold bwW
      rfl
    rw [hp2]
    ring
  · intro n hn ih
    rw [Finset.prod_Icc_succ_top (show (1:ℕ) ≤ n + 1 by omega)
      (fun k => |(|(k:ℝ) - (r:ℝ)|) - η|), ih]
    have hg : |(|((n+1:ℕ):ℝ) - (r:ℝ)|) - η| = (((n+1-r:ℕ)):ℝ) - η := by
      rw [abs_of_nonneg (by
        have : (r:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast (show r ≤ n + 1 by omega)
        linarith : (0:ℝ) ≤ ((n+1:ℕ):ℝ) - (r:ℝ))]
      rw [← Nat.cast_sub (show r ≤ n + 1 by omega)]
      have h3 : (0:ℝ) ≤ (((n+1-r:ℕ)):ℝ) - η := by
        have hk1 : (1:ℝ) ≤ (((n+1-r:ℕ)):ℝ) := by
          have : 1 ≤ n + 1 - r := by omega
          exact_mod_cast this
        linarith
      rw [abs_of_nonneg h3]
    rw [hg]
    have hcast : (((n+1-r:ℕ)):ℝ) = (((n-r:ℕ)):ℝ) + 1 := by
      rw [show n + 1 - r = n - r + 1 by omega, Nat.cast_add, Nat.cast_one]
    rw [hcast, show (n + 1) - r = (n - r) + 1 by omega, bwW_succ]
    ring

set_option maxHeartbeats 1000000 in
/-- `(X-1)!² ≤ (X+r-1)! (X-r-1)!` for `r ≤ X`. -/
lemma fact_paired_le (X r : ℕ) (hX : 1 ≤ X) (hr : r ≤ X) :
    ((((X - 1).factorial : ℕ)) : ℝ) ^ 2 ≤
      ((((X + r - 1).factorial : ℕ)) : ℝ) * ((((X - r - 1).factorial : ℕ)) : ℝ) := by
  by_cases hcase : r ≤ X - 1
  · have h1 : X + r - 1 - r = X - 1 := by omega
    have h2 : X - 1 - r = X - r - 1 := by omega
    have hd1 : (X + r - 1).choose r * r.factorial * (X - 1).factorial = (X + r - 1).factorial := by
      have hh := Nat.choose_mul_factorial_mul_factorial (show r ≤ X + r - 1 by omega)
      rw [h1] at hh
      exact hh
    have hd2 : (X - 1).choose r * r.factorial * (X - r - 1).factorial = (X - 1).factorial := by
      have hh := Nat.choose_mul_factorial_mul_factorial (show r ≤ X - 1 by omega)
      rw [h2] at hh
      exact hh
    have hchoose : (X - 1).choose r ≤ (X + r - 1).choose r :=
      Nat.choose_le_choose r (show X - 1 ≤ X + r - 1 by omega)
    have hcast : (((X - 1).choose r : ℕ) : ℝ) ≤ (((X + r - 1).choose r : ℕ) : ℝ) := by
      exact_mod_cast hchoose
    have e1 : (((X - 1).choose r : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ) *
        (((X - r - 1).factorial : ℕ) : ℝ) = (((X - 1).factorial : ℕ) : ℝ) := by
      have hh := congrArg (fun n : ℕ => (n:ℝ)) hd2
      push_cast at hh
      exact hh
    have e2 : (((X + r - 1).choose r : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ) *
        (((X - 1).factorial : ℕ) : ℝ) = (((X + r - 1).factorial : ℕ) : ℝ) := by
      have hh := congrArg (fun n : ℕ => (n:ℝ)) hd1
      push_cast at hh
      exact hh
    have hpos : (0:ℝ) < ((r.factorial : ℕ) : ℝ) * (((X - 1).factorial : ℕ) : ℝ) *
        (((X - r - 1).factorial : ℕ) : ℝ) := by
      have h1p : (0:ℝ) < ((r.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos r
      have h2p : (0:ℝ) < (((X - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos (X-1)
      have h3p : (0:ℝ) < (((X - r - 1).factorial : ℕ) : ℝ) :=
        by exact_mod_cast Nat.factorial_pos (X-r-1)
      exact mul_pos (mul_pos h1p h2p) h3p
    have hmul := mul_le_mul_of_nonneg_right hcast (le_of_lt hpos)
    have hA : (((X - 1).choose r : ℕ) : ℝ) * (((r.factorial : ℕ) : ℝ) *
        (((X - 1).factorial : ℕ) : ℝ) * (((X - r - 1).factorial : ℕ) : ℝ))
        = (((X - 1).factorial : ℕ) : ℝ) * (((X - 1).factorial : ℕ) : ℝ) := by
      rw [show (((X - 1).choose r : ℕ) : ℝ) * (((r.factorial : ℕ) : ℝ) *
          (((X - 1).factorial : ℕ) : ℝ) * (((X - r - 1).factorial : ℕ) : ℝ))
          = ((((X - 1).choose r : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ) *
              (((X - r - 1).factorial : ℕ) : ℝ)) * (((X - 1).factorial : ℕ) : ℝ) by ring]
      rw [e1]
    have hB : (((X + r - 1).choose r : ℕ) : ℝ) * (((r.factorial : ℕ) : ℝ) *
        (((X - 1).factorial : ℕ) : ℝ) * (((X - r - 1).factorial : ℕ) : ℝ))
        = (((X + r - 1).factorial : ℕ) : ℝ) * (((X - r - 1).factorial : ℕ) : ℝ) := by
      rw [show (((X + r - 1).choose r : ℕ) : ℝ) * (((r.factorial : ℕ) : ℝ) *
          (((X - 1).factorial : ℕ) : ℝ) * (((X - r - 1).factorial : ℕ) : ℝ))
          = ((((X + r - 1).choose r : ℕ) : ℝ) * ((r.factorial : ℕ) : ℝ) *
              (((X - 1).factorial : ℕ) : ℝ)) * (((X - r - 1).factorial : ℕ) : ℝ) by ring]
      rw [e2]
    rw [hA, hB] at hmul
    simpa [pow_two] using hmul
  · have hrX' : r = X := by omega
    rw [hrX']
    have hXr : X - X - 1 = 0 := by omega
    have hXX : X + X - 1 = 2 * X - 1 := by omega
    rw [hXr, hXX, Nat.factorial_zero, Nat.cast_one, mul_one]
    have had : (2 * X - 1).choose (X - 1) * (X - 1).factorial * X.factorial
        = (2 * X - 1).factorial := by
      have hh := Nat.choose_mul_factorial_mul_factorial (show X - 1 ≤ 2 * X - 1 by omega)
      rw [show 2 * X - 1 - (X - 1) = X by omega] at hh
      exact hh
    have eC : (((2 * X - 1).choose (X - 1) : ℕ) : ℝ) * (((X - 1).factorial : ℕ) : ℝ) *
        ((X.factorial : ℕ) : ℝ) = (((2 * X - 1).factorial : ℕ) : ℝ) := by
      have hh := congrArg (fun n : ℕ => (n:ℝ)) had
      push_cast at hh
      exact hh
    have hXf : (((X - 1).factorial : ℕ) : ℝ) ≤ ((X.factorial : ℕ) : ℝ) := by
      have hfac : X.factorial = X * (X - 1).factorial := by
        conv_lhs => rw [show X = (X - 1) + 1 by omega]
        rw [Nat.factorial_succ, show (X - 1) + 1 = X by omega]
      rw [hfac]
      push_cast
      have h1X : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
      have := mul_le_mul_of_nonneg_right h1X (Nat.cast_nonneg ((X - 1).factorial))
      simpa using this
    have hC1 : (1:ℝ) ≤ (((2 * X - 1).choose (X - 1) : ℕ) : ℝ) := by
      have : (1:ℕ) ≤ (2 * X - 1).choose (X - 1) :=
        Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.choose_pos (show X - 1 ≤ 2 * X - 1 by omega)))
      exact_mod_cast this
    rw [pow_two]
    calc (((X - 1).factorial : ℕ) : ℝ) * (((X - 1).factorial : ℕ) : ℝ)
        ≤ (((X - 1).factorial : ℕ) : ℝ) * ((X.factorial : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hXf (Nat.cast_nonneg _)
      _ ≤ (((2 * X - 1).choose (X - 1) : ℕ) : ℝ) * (((X - 1).factorial : ℕ) : ℝ) *
            ((X.factorial : ℕ) : ℝ) := by
          have hnn : (0:ℝ) ≤ (((X-1).factorial:ℕ):ℝ) * ((X.factorial:ℕ):ℝ) :=
            mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          have hthis := mul_le_mul_of_nonneg_right hC1 hnn
          calc (((X - 1).factorial : ℕ) : ℝ) * ((X.factorial : ℕ) : ℝ)
              = (1:ℝ) * ((((X-1).factorial:ℕ):ℝ) * ((X.factorial:ℕ):ℝ)) := by ring
            _ ≤ (((2*X-1).choose (X-1) : ℕ) : ℝ) *
                  ((((X-1).factorial:ℕ):ℝ) * ((X.factorial:ℕ):ℝ)) := hthis
            _ = (((2 * X - 1).choose (X - 1) : ℕ) : ℝ) * (((X - 1).factorial : ℕ) : ℝ) *
                  ((X.factorial : ℕ) : ℝ) := by ring
      _ = (((2 * X - 1).factorial : ℕ) : ℝ) := eC

/-- **BW p. 51, assembly of the lower bound for `B(z;X)` on `C_l`.** Given the per-pair bounds `hpair` (the conclusion of `bprod_pair_lower`), deduce
`η·(1−η)²·((X−1)!)²/R^{2X+1} ≤ ‖B(z;X)‖`, where `B(z;X) = ∏_{|k|≤X} β(z;k)`.
Proof: peel the two extreme factors with `bprod_peel` (`B(·;n+1) = β(·;n+1)β(·;−(n+1))B(·;n)`) and induct, or use `bprod(·;X) = β(·;0)·∏_{k=1}^{X} β(·;k)β(·;−k)`. Also `‖β(z;0)‖ = ‖z‖/R ≥ |‖l‖−η|/R`. Then `∏_{k=1}^{X}(|l|+k−η) ≥ (X+|l|−1)!/(|l|−1)!`, `∏_{k=1}^{X} |‖l|−k|−η| ≥ η(|l|−2)!(X−|l|−1)!` (empty products = 1, so `|l| ≤ 1` and `|l| = X` are fine), and `(X+r−1)!(X−r−1)! ≥ ((X−1)!)²` for `0 ≤ r ≤ X`. -/
theorem bprod_lower_assemb (R η : ℝ) (hη : 0 < η) (hη' : η < 1 / 2) (X : ℕ) (hX : 1 ≤ X)
    (hXR : (X : ℝ) + η ≤ R) (l : ℤ) (hl : |l| ≤ (X : ℤ)) (z : ℂ) (hz : ‖z - (l : ℂ)‖ = η)
    (hpair : ∀ k : ℤ, 1 ≤ k → k ≤ (X : ℤ) →
      |(|(|l| : ℝ) - (k : ℝ)|) - η| * ((|l| : ℝ) + (k : ℝ) - η) / R ^ 2 ≤
        ‖bfac R k z * bfac R (-k) z‖) :
    η * (1 - η) ^ 2 * ((((X - 1).factorial : ℕ)) : ℝ) ^ 2 / R ^ (2 * X + 1) ≤ ‖bprod R X z‖ := by
  have hR : 0 < R := by
    have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
    have : (0:ℝ) < (X:ℝ) + η := by linarith
    linarith
  have hη0 : (0:ℝ) ≤ η := le_of_lt hη
  have hη1 : η < 1 := by linarith
  have h1η : (0:ℝ) < 1 - η := by linarith
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, (r:ℤ) = |l| := ⟨l.natAbs, Int.natCast_natAbs l⟩
  have hrR : (r:ℝ) = |(l:ℝ)| := by
    have h : ((r:ℤ):ℝ) = ((|l|:ℤ):ℝ) := by rw [hrdef]
    rw [Int.cast_abs] at h
    simpa using h
  have hrX : r ≤ X := by
    have h : (r:ℤ) ≤ (X:ℤ) := by rw [hrdef]; exact hl
    exact_mod_cast h
  have hL : ‖bprod R X z‖
      = ‖bfac R 0 z‖ * ∏ k ∈ Finset.Icc 1 X, ‖bfac R (k:ℤ) z * bfac R (-(k:ℤ)) z‖ := by
    rw [bprod_split_aux, norm_mul, norm_prod]
  rcases r.eq_zero_or_pos with hr0 | hrpos
  · -- r = 0
    have hl0 : l = 0 := by
      have h2 : |(l:ℝ)| = 0 := by rw [← hrR, hr0]; simp
      have h3 : (l:ℝ) = 0 := abs_eq_zero.mp h2
      exact_mod_cast h3
    have hz0 : ‖z‖ = η := by rw [← hz, hl0]; simp
    have hlem0 : |(l:ℝ)| = 0 := by rw [← hrR, hr0]; simp
    have hbf0 : ‖bfac R 0 z‖ = η / R := by rw [bfac_zero_complex R hR z, hz0]
    have hprod0 : (∏ k ∈ Finset.Icc 1 X, (((k:ℝ) - η)^2 / R^2))
        = (bwW η X)^2 / R^(2*X) := by
      have hnum : (∏ k ∈ Finset.Icc 1 X, (((k:ℝ) - η)^2)) = (bwW η X)^2 := by
        rw [Finset.prod_pow]
        simp only [bwW]
      have hden : (∏ k ∈ Finset.Icc 1 X, (R^2)) = R^(2*X) := by
        rw [Finset.prod_const (R^2), show (Finset.Icc 1 X).card = X by simp, pow_mul R 2 X]
      rw [Finset.prod_div_distrib, hnum, hden]
    have hpairs0 : (∏ k ∈ Finset.Icc 1 X, (((k:ℝ) - η)^2 / R^2))
        ≤ ∏ k ∈ Finset.Icc 1 X, ‖bfac R (k:ℤ) z * bfac R (-(k:ℤ)) z‖ := by
      apply Finset.prod_le_prod₀
      · intro k _
        exact div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hR) 2)
      · intro k hk
        rw [Finset.mem_Icc] at hk
        have hk1 : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk.1
        have hk2 : (k:ℤ) ≤ (X:ℤ) := by exact_mod_cast hk.2
        have h := hpair (k:ℤ) hk1 hk2
        rw [hlem0] at h
        have hk1' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        push_cast at h
        have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        have hkη : (0:ℝ) ≤ (k:ℝ) - η := by linarith
        have e1 : |(0:ℝ) - (k:ℝ)| = (k:ℝ) := by rw [zero_sub, abs_neg, abs_of_nonneg hk0]
        have e2 : |(k:ℝ) - η| = (k:ℝ) - η := abs_of_nonneg hkη
        have hsimp : |(|(0:ℝ) - (k:ℝ)|) - η| * (0 + (k:ℝ) - η) / R^2
            = ((k:ℝ) - η)^2 / R^2 := by
          rw [e1, e2, zero_add]
          ring_nf
        rwa [hsimp] at h
    have hbig0 : η * (bwW η X)^2 / R^(2*X+1) ≤ ‖bprod R X z‖ := by
      rw [hL, hbf0]
      have h1 : (η/R) * ((bwW η X)^2 / R^(2*X))
          ≤ (η/R) * (∏ k ∈ Finset.Icc 1 X, ‖bfac R (k:ℤ) z * bfac R (-(k:ℤ)) z‖) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hη0 (le_of_lt hR))
        rw [← hprod0]
        exact hpairs0
      have h2 : η * (bwW η X)^2 / R^(2*X+1) = (η/R) * ((bwW η X)^2 / R^(2*X)) := by
        rw [div_mul_div_comm, ← pow_succ']
      rw [h2]
      exact h1
    have hbwX : (1 - η) * ((((X - 1).factorial : ℕ)) : ℝ) ≤ bwW η X := bwW_lower η hη0 hη1 X
    have hsq0 : (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2 ≤ (bwW η X)^2 := by
      have h1 : ((1-η) * ((((X-1).factorial:ℕ)):ℝ))^2 ≤ (bwW η X)^2 :=
        pow_le_pow_left₀ (mul_nonneg (le_of_lt h1η) (Nat.cast_nonneg _)) hbwX 2
      have h2 : ((1-η) * ((((X-1).factorial:ℕ)):ℝ))^2
          = (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2 := by ring
      rwa [h2] at h1
    have hfin0 : η * (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2 / R^(2*X+1)
        ≤ η * (bwW η X)^2 / R^(2*X+1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (le_of_lt hR) _)
      have h3 : η * ((1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2) ≤ η * (bwW η X)^2 :=
        mul_le_mul_of_nonneg_left hsq0 hη0
      calc η * (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2
          = η * ((1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2) := by ring
        _ ≤ η * (bwW η X)^2 := h3
    exact le_trans hfin0 hbig0
  · -- 1 ≤ r
    have hr1 : 1 ≤ r := hrpos
    have hnl : ‖(l:ℂ)‖ = |(l:ℝ)| := Complex.norm_intCast l
    have hz_ge : |(l:ℝ)| ≤ ‖z‖ + η := by
      have h := norm_add_le ((l:ℂ) - z) z
      rw [show (l:ℂ) - z + z = (l:ℂ) by ring] at h
      have h2 : ‖(l:ℂ) - z‖ = η := by
        rw [show (l:ℂ) - z = -(z - (l:ℂ)) by ring, norm_neg, hz]
      rw [h2, hnl] at h
      linarith
    have hbf0 : (r - η)/R ≤ ‖bfac R 0 z‖ := by
      rw [bfac_zero_complex R hR z, div_le_div_iff_of_pos_right hR]
      have hre : (r - η) = |(l:ℝ)| - η := by rw [hrR]
      rw [hre]
      linarith
    have hpairs : (∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η) / R^2))
        ≤ ∏ k ∈ Finset.Icc 1 X, ‖bfac R (k:ℤ) z * bfac R (-(k:ℤ)) z‖ := by
      apply Finset.prod_le_prod₀
      · intro k hk
        rw [Finset.mem_Icc] at hk
        have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
        exact div_nonneg (mul_nonneg (abs_nonneg _) (by linarith)) (pow_nonneg (le_of_lt hR) 2)
      · intro k hk
        rw [Finset.mem_Icc] at hk
        have hk1 : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk.1
        have hk2 : (k:ℤ) ≤ (X:ℤ) := by exact_mod_cast hk.2
        have h := hpair (k:ℤ) hk1 hk2
        rwa [← hrR] at h
    have hprodabs : (∏ k ∈ Finset.Icc 1 X, |(|(r:ℝ) - (k:ℝ)|) - η|)
        = η * bwW η (r - 1) * bwW η (X - r) := by
      rw [show (∏ k ∈ Finset.Icc 1 X, |(|(r:ℝ) - (k:ℝ)|) - η|)
            = ∏ k ∈ Finset.Icc 1 X, |(|(k:ℝ) - (r:ℝ)|) - η| from by
            apply Finset.prod_congr rfl
            intro k _
            rw [abs_sub_comm (r:ℝ) (k:ℝ)]]
      exact bwW_abs_split η hη0 hη1 X r hr1 hrX
    have hprodlin : (∏ k ∈ Finset.Icc 1 X, ((r:ℝ) + (k:ℝ) - η))
        = ∏ j ∈ Finset.Icc (r + 1) (r + X), ((j:ℝ) - η) := by
      rw [show (∏ k ∈ Finset.Icc 1 X, ((r:ℝ) + (k:ℝ) - η))
            = ∏ k ∈ Finset.Icc 1 X, (((k:ℝ) + (r:ℝ)) - η) from by
            apply Finset.prod_congr rfl
            intro k _
            ring]
      exact prod_shift_Icc η X r
    have hkey : (r - η) * (∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η)))
        = η * bwW η (X + r) * bwW η (X - r) := by
      rw [Finset.prod_mul_distrib, hprodabs, hprodlin, bwW_consecutive η X r, bwW_peel η r hr1]
      ring
    have hproddiv : (∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η) / R^2))
        = (∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η))) / R^(2*X) := by
      rw [Finset.prod_div_distrib, Finset.prod_const (R^2),
        show (Finset.Icc 1 X).card = X by simp, pow_mul R 2 X]
    have hbig : (r - η) * (∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η))) / R^(2*X+1)
        ≤ ‖bprod R X z‖ := by
      rw [hL]
      have h1 : (r-η)/R * ((∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η))) / R^(2*X))
          ≤ ‖bfac R 0 z‖ * (∏ k ∈ Finset.Icc 1 X, ‖bfac R (k:ℤ) z * bfac R (-(k:ℤ)) z‖) := by
        refine mul_le_mul hbf0 ?_ ?_ (norm_nonneg _)
        · rw [← hproddiv]; exact hpairs
        · exact div_nonneg (Finset.prod_nonneg (fun k hk => by
            rw [Finset.mem_Icc] at hk
            have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
            have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
            exact mul_nonneg (abs_nonneg _) (by linarith))) (pow_nonneg (le_of_lt hR) _)
      have h2 : (r-η) * (∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η))) / R^(2*X+1)
          = (r-η)/R * ((∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η))) / R^(2*X)) := by
        rw [div_mul_div_comm, ← pow_succ']
      rw [h2]
      exact h1
    have hbw1 : (1 - η) * ((((X + r - 1).factorial : ℕ)) : ℝ) ≤ bwW η (X + r) :=
      bwW_lower η hη0 hη1 (X + r)
    have hbw2 : (1 - η) * ((((X - r - 1).factorial : ℕ)) : ℝ) ≤ bwW η (X - r) :=
      bwW_lower η hη0 hη1 (X - r)
    have hfact := fact_paired_le X r hX hrX
    have hbwpos : (0:ℝ) ≤ bwW η (X + r) :=
      le_trans (mul_nonneg (le_of_lt h1η) (Nat.cast_nonneg _)) hbw1
    have hkey2 : η * (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2 ≤ η * bwW η (X + r) * bwW η (X - r) := by
      have h1 : ((1-η) * ((((X+r-1).factorial:ℕ)):ℝ)) * ((1-η) * ((((X-r-1).factorial:ℕ)):ℝ))
          ≤ bwW η (X + r) * bwW η (X - r) :=
        mul_le_mul hbw1 hbw2 (mul_nonneg (le_of_lt h1η) (Nat.cast_nonneg _)) hbwpos
      have h2 : (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2
          ≤ ((1-η) * ((((X+r-1).factorial:ℕ)):ℝ)) * ((1-η) * ((((X-r-1).factorial:ℕ)):ℝ)) := by
        have h2a : (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2
            ≤ (1-η)^2 * (((((X+r-1).factorial:ℕ)):ℝ) * ((((X-r-1).factorial:ℕ)):ℝ)) :=
          mul_le_mul_of_nonneg_left hfact (sq_nonneg _)
        convert h2a using 1
        ring
      have h3 : η * (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2 ≤ η * (bwW η (X + r) * bwW η (X - r)) := by
        calc η * (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2
            = η * ((1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2) := by ring
          _ ≤ η * (bwW η (X + r) * bwW η (X - r)) :=
              mul_le_mul_of_nonneg_left (le_trans h2 h1) hη0
      calc η * (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2
          ≤ η * (bwW η (X + r) * bwW η (X - r)) := h3
        _ = η * bwW η (X + r) * bwW η (X - r) := by ring
    have hfin : η * (1-η)^2 * ((((X-1).factorial:ℕ)):ℝ)^2 / R^(2*X+1)
        ≤ (r - η) * (∏ k ∈ Finset.Icc 1 X, (|(|(r:ℝ) - (k:ℝ)|) - η| * ((r:ℝ) + (k:ℝ) - η))) / R^(2*X+1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (le_of_lt hR) _)
      rw [hkey]
      exact hkey2
    exact le_trans hfin hbig

end Work.BW
