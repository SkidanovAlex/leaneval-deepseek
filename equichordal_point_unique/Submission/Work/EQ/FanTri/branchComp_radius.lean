import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanTri.BranchCompDefs
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.FanTri.wtAux_uniform_bound
import Submission.Work.EQ.FanTri.radius_constants_v3
import Submission.Work.EQ.FanTri.invBranch_axis_second_order_sharp
import Submission.Work.EQ.FanTri.absorb_coord1
import Submission.Work.EQ.FanTri.absorb_coord2

namespace Work.EQ.FanTri

open Work.EQ

set_option maxHeartbeats 4000000

noncomputable section

/-- The point `A₁ = (-1/2, 0)`. -/
abbrev A1 : ℂ × ℂ := (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))

/-! ## Bookkeeping

`branchComp a w` reads the word from the head (the head letter is applied last), so the walk on
the real axis that governs the composition reads `w.reverse`. -/

/-- The walk state of the word `w`: the state reached by reading `w.reverse` from state `0`. -/
def wSt (w : List Bool) : ℕ := stAux w.reverse 0

/-- The walk weight of the word `w`: the product of the step weights along the walk of
`w.reverse`; it equals `∏_j stW a c_j (state_j)`. -/
def wWt (a : ℝ) (w : List Bool) : ℝ := wtAux a w.reverse 0

@[simp] lemma wSt_nil : wSt ([] : List Bool) = 0 := rfl

lemma wSt_cons (c : Bool) (w : List Bool) : wSt (c :: w) = stp c (wSt w) := by
  simp only [wSt, List.reverse_cons, stAux_append, stAux_nil]
  rfl

@[simp] lemma wWt_nil (a : ℝ) : wWt a ([] : List Bool) = 1 := rfl

lemma wWt_cons (a : ℝ) (c : Bool) (w : List Bool) :
    wWt a (c :: w) = stW a c (wSt w) * wWt a w := by
  simp only [wWt, List.reverse_cons, wtAux_append, wtAux_nil, wtAux_cons, wSt]
  ring

/-- **The centre of a finite composition of inverse branches is a walk centre.** -/
lemma branchComp_centre {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (w : List Bool) :
    branchComp a w A1 = (((stCtr (wSt w) : ℝ) : ℂ), (0 : ℂ)) := by
  obtain ⟨hstp, -, hne, -⟩ := walk_bounds (a := a) ha0 ha1
  induction w with
  | nil => simp [wSt, stCtr_zero]
  | cons c w ih =>
      rw [branchComp_cons, ih, wSt_cons]
      rw [FanSep.invBranch_axis (a := a) c (hne (wSt w))]
      rw [hstp]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst]
        congr 1
        rw [axStep]
        have h1 : sgnB c = (if c = true then (1 : ℝ) else -1) := by cases c <;> rfl
        have h2 : sgnR (stCtr (wSt w) + a / 2)
            = (stCtr (wSt w) + a / 2) / |stCtr (wSt w) + a / 2| :=
          (div_abs_self (hne (wSt w))).symm
        rw [h1, h2, ← mul_div_assoc]
      · simp

/-- The step weight is `λ` times the modulus of the one-step factor `-1 + sgnB c / q`. -/
lemma stW_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : Bool) (n : ℕ) :
    stW a c n = eqLam a * |(-1 + sgnB c / stQ a n)| := by
  have hq : 0 < stQ a n := wb_stQ_pos ha0 ha1 n
  have hlam : 0 < eqLam a := eqLam_pos' ha0 ha1
  cases c with
  | true =>
      have h1 : stW a true n = |dnW a n| := by simp [stW]
      rw [h1, dnW, abs_mul, abs_of_pos hlam, sgnB_true]
      congr 1
      rw [show (-1 + 1 / stQ a n) = -(1 - 1 / stQ a n) by ring, abs_neg]
  | false =>
      have h1 : stW a false n = upW a n := by simp [stW]
      rw [h1, upW, sgnB_false]
      congr 1
      rw [show (-1 + -1 / stQ a n) = -(1 + 1 / stQ a n) by ring, abs_neg,
        abs_of_pos (by positivity)]

/-- The axis points of the walk are far from `-a/2`. -/
lemma stQ_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) : (1 - a) / 2 ≤ stQ a n := by
  obtain ⟨-, hmem, -⟩ := walk_bounds (a := a) ha0 ha1
  obtain ⟨k, hk⟩ := hmem n
  rw [stQ, hk]
  rcases le_or_gt k 0 with h | h
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1 : (1 : ℤ) ≤ k := by omega
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Every `stQ` value is either the minimal one `(1-a)/2` (the centre `A₁`) or at least `3/2`. -/
lemma stQ_eq_min_or_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    stQ a n = (1 - a) / 2 ∨ 3 / 2 ≤ stQ a n := by
  have hctr : stCtr n = -1 / 2 + 2 * (stIdx n : ℝ) := rfl
  have hbeta : 0 < (1 - a) / 2 := by linarith
  have hbeta' : (1 - a) / 2 ≤ 1 / 2 := by linarith
  have hkey : stCtr n + a / 2 = 2 * (stIdx n : ℝ) - (1 - a) / 2 := by
    rw [hctr]; ring
  rcases lt_trichotomy (stIdx n) 0 with hlt | heq | hgt
  · right
    have hkR : ((stIdx n : ℤ) : ℝ) ≤ -1 := by
      have : stIdx n ≤ -1 := by omega
      exact_mod_cast this
    rw [stQ, hkey, abs_of_neg (by linarith)]
    linarith
  · left
    have hkR : ((stIdx n : ℤ) : ℝ) = 0 := by exact_mod_cast heq
    rw [stQ, hkey, hkR]
    rw [show 2 * (0 : ℝ) - (1 - a) / 2 = -((1 - a) / 2) by ring, abs_neg,
      abs_of_pos hbeta]
  · right
    have hkR : (1 : ℝ) ≤ ((stIdx n : ℤ) : ℝ) := by
      have : (1 : ℤ) ≤ stIdx n := by omega
      exact_mod_cast this
    rw [stQ, hkey, abs_of_pos (by linarith)]
    linarith

/-- The one-step factor at an axis point has modulus at least `1/3`. -/
lemma abs_one_step_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : Bool) (n : ℕ) :
    1 / 3 ≤ |(-1 + sgnB c / stQ a n)| := by
  have hq0 : 0 < stQ a n := wb_stQ_pos ha0 ha1 n
  have hlam : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hupper3 : (1 : ℝ) / 3 ≤ 1 := by norm_num
  rcases stQ_eq_min_or_ge ha0 ha1 n with hq | hq
  · cases c with
    | true =>
        rw [sgnB_true, hq]
        have hb : 0 < (1 - a) / 2 := by linarith
        have h : (-1 + 1 / ((1 - a) / 2)) = 1 / eqLam a := by
          rw [eqLam]
          have h1a : (1 : ℝ) - a ≠ 0 := by linarith
          have h1b : (1 : ℝ) + a ≠ 0 := by linarith
          field_simp
          ring
        rw [h, abs_of_pos (by positivity : (0:ℝ) < 1 / eqLam a)]
        have hinv : (1 : ℝ) ≤ 1 / eqLam a := by
          rw [le_div_iff₀ hlam, one_mul]
          exact le_of_lt hlam1
        exact le_trans hupper3 hinv
    | false =>
        rw [sgnB_false, hq]
        have h : (-1 + -1 / ((1 - a) / 2)) = -(1 + 2 / (1 - a)) := by
          field_simp
          ring
        rw [h, abs_neg, abs_of_nonneg (by positivity)]
        have : 0 < 2 / (1 - a) := by positivity
        linarith
  · cases c with
    | true =>
        rw [sgnB_true]
        have hq1 : 1 ≤ stQ a n := by linarith
        have h2 : 1 / stQ a n ≤ 1 := by
          rw [div_le_one hq0]; exact hq1
        rw [show (-1 + 1 / stQ a n) = -(1 - 1 / stQ a n) by ring, abs_neg,
          abs_of_nonneg (by linarith)]
        have h3 : 1 / stQ a n ≤ 2 / 3 := by
          rw [div_le_iff₀ hq0]; linarith
        linarith
    | false =>
        rw [sgnB_false]
        rw [show (-1 + -1 / stQ a n) = -(1 + 1 / stQ a n) by ring, abs_neg,
          abs_of_nonneg (by positivity)]
        have : 0 < 1 / stQ a n := by positivity
        linarith


/-! ## The word weight `wLam` -/

/-- The product of the one-step factors `|-1 + sgnB c / stQ a (state)|` along the word `w`,
read from the head (`wLam a (c :: w) = wLam a w * |σ|`, with `σ` evaluated at the state
`wSt w` reached by the tail).  It equals `λ^{-|w|} · wWt a w`, the reciprocal density factor of
the composition `branchComp a w` at `A₁`. -/
def wLam (a : ℝ) : List Bool → ℝ
  | [] => 1
  | c :: w => wLam a w * |(-1 + sgnB c / stQ a (wSt w))|

@[simp] lemma wLam_nil (a : ℝ) : wLam a ([] : List Bool) = 1 := rfl

lemma wLam_cons (a : ℝ) (c : Bool) (w : List Bool) :
    wLam a (c :: w) = wLam a w * |(-1 + sgnB c / stQ a (wSt w))| := rfl

lemma wLam_nonneg (a : ℝ) (w : List Bool) : 0 ≤ wLam a w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [wLam_cons]; exact mul_nonneg ih (abs_nonneg _)

lemma wLam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (w : List Bool) : 0 < wLam a w := by
  induction w with
  | nil => simp
  | cons c w ih =>
      rw [wLam_cons]
      exact mul_pos ih (lt_of_lt_of_le (by norm_num) (abs_one_step_ge ha0 ha1 c (wSt w)))

/-- **The walk-weight identity** `Λ_w · λ^{|w|} = wWt a w`. -/
lemma wLam_mul_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (w : List Bool) :
    wLam a w * (eqLam a) ^ w.length = wWt a w := by
  induction w with
  | nil => simp [wWt]
  | cons c w ih =>
      rw [wLam_cons, wWt_cons, List.length_cons, pow_succ]
      rw [← ih, stW_eq ha0 ha1 c (wSt w)]
      ring

/-! ## Power bookkeeping -/

private lemma invpow_eq_zpow {x : ℝ} (k : ℕ) : x⁻¹ ^ k = x ^ (-(k : ℤ)) := by
  rw [inv_pow, ← zpow_natCast, ← zpow_neg]

private lemma pow_eq_zpow (x : ℝ) (k : ℕ) : x ^ k = x ^ (k : ℤ) := (zpow_natCast x k).symm

/-- `u^{2m}·λ^{m+1} = λ²·u^{m+1}` for `u = λ⁻¹`. -/
private lemma idA {lam : ℝ} (h : lam ≠ 0) (m : ℕ) :
    lam⁻¹ ^ (2 * m) * lam ^ (m + 1) = lam ^ 2 * lam⁻¹ ^ (m + 1) := by
  rw [invpow_eq_zpow, pow_eq_zpow, invpow_eq_zpow, pow_eq_zpow]
  push_cast
  rw [← zpow_add₀ h, ← zpow_add₀ h]
  ring_nf

/-- `u^m·λ^{m+1} = λ` for `u = λ⁻¹`. -/
private lemma idB {lam : ℝ} (h : lam ≠ 0) (m : ℕ) : lam⁻¹ ^ m * lam ^ (m + 1) = lam := by
  rw [invpow_eq_zpow, pow_eq_zpow]
  push_cast
  rw [← zpow_add₀ h]
  ring_nf
  simp

/-- `λ²·u^{2(m+1)} = u^{2m}` for `u = λ⁻¹`. -/
private lemma idC {lam : ℝ} (h : lam ≠ 0) (m : ℕ) :
    lam ^ 2 * lam⁻¹ ^ (2 * (m + 1)) = lam⁻¹ ^ (2 * m) := by
  rw [pow_eq_zpow, invpow_eq_zpow, invpow_eq_zpow]
  push_cast
  rw [← zpow_add₀ h]
  ring_nf

/-- `λ·u^{m+1} = u^m` for `u = λ⁻¹`. -/
private lemma idD {lam : ℝ} (h : lam ≠ 0) (m : ℕ) : lam * lam⁻¹ ^ (m + 1) = lam⁻¹ ^ m := by
  rw [invpow_eq_zpow, invpow_eq_zpow]
  nth_rewrite 1 [show lam = lam ^ (1 : ℤ) by rw [zpow_one]]
  rw [← zpow_add₀ h]
  push_cast
  rw [show (1 : ℤ) + -(↑m + 1) = -(↑m) by ring]

/-- `λ^k·u^k = 1` for `u = λ⁻¹`. -/
private lemma idE {lam : ℝ} (h : lam ≠ 0) (k : ℕ) : lam ^ k * lam⁻¹ ^ k = 1 := by
  rw [pow_eq_zpow, invpow_eq_zpow, ← zpow_add₀ h]
  simp

/-- `u^k·λ^k = 1` for `u = λ⁻¹`. -/
private lemma idE' {lam : ℝ} (h : lam ≠ 0) (k : ℕ) : lam⁻¹ ^ k * lam ^ k = 1 := by
  rw [mul_comm]; exact idE h k

/-! ## The invariant induction -/

/-- **The invariant induction behind `branchComp_radius`.**
For a word `w` of length `n` and `‖z - A₁‖ ≤ ρλ^n`,
`‖(F_w z - c_w).1‖ ≤ 𝔸‖z-A₁‖ + 𝒞·u^{2n}·(‖z-A₁‖²/ρ)` and
`‖(F_w z - c_w).2‖ ≤ 𝔹Λ_w‖z-A₁‖ + 𝒟·(Λ_w·(u^n·(‖z-A₁‖²/ρ)))`, where `u = λ⁻¹` and
`Λ_w = wLam a w`; `hstep` is the sharp one-step linearisation at an axis point, `hR1`, `hR2`,
`hR3a-c` the numerical side conditions and `habs1`, `habs2` the two absorption lemmas
(`Work.EQ.FanTri.absorb_coord1`, `absorb_coord2`). -/
theorem branchComp_radius_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {ρ 𝔸 𝒞 𝔹 𝒟 K C : ℝ} (hρ : 0 < ρ) (h𝔸 : 1 ≤ 𝔸) (h𝔹 : 1 ≤ 𝔹) (h𝒞 : 0 ≤ 𝒞)
    (h𝒟 : 0 ≤ 𝒟) (hKpos : 0 < K) (hK : ∀ w : List Bool, wWt a w ≤ K) (hCpos : 0 < C)
    (hstep : ∀ (x : ℝ), (∃ k : ℤ, x = -1 / 2 + 2 * (k : ℝ)) → ∀ (s : Bool) {p : ℂ × ℂ},
      ‖p‖ ≤ (1 - a) / 8 →
      ‖(invBranch a s (((x : ℂ), (0 : ℂ)) + p) - invBranch a s (((x : ℂ), (0 : ℂ)))).1 + p.1‖
        ≤ C * ‖p.2‖ ^ 2 / |x + a / 2| ^ 2 ∧
      ‖(invBranch a s (((x : ℂ), (0 : ℂ)) + p) - invBranch a s (((x : ℂ), (0 : ℂ)))).2
        - (-1 + sgnB s / |x + a / 2|) * p.2‖ ≤ C * ‖p.2‖ * ‖p‖ / |x + a / 2| ^ 2)
    (hR1 : ρ * (𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K) ≤ (1 - a) / 8)
    (hR2 : C * (𝔹 + 𝒟 * eqLam a) ^ 2 * K ^ 2 * (eqLam a) ^ 2 * ρ
      ≤ 𝒞 * (1 - (eqLam a) ^ 2) * ((1 - a) / 2) ^ 2)
    (hR3a : 9 * C * (𝔹 + 𝒟 * eqLam a) * 𝔸 * ρ ≤ 𝒟 * (1 - eqLam a) * ((1 - a) / 2) ^ 2)
    (hR3b : 9 * C * (𝔹 + 𝒟 * eqLam a) * 𝒞 * ρ * (eqLam a) ^ 2
      ≤ 𝒟 * (1 - eqLam a) * ((1 - a) / 2) ^ 2)
    (hR3c : 9 * C * (𝔹 + 𝒟 * eqLam a) ^ 2 * K * eqLam a * ρ
      ≤ 𝒟 * (1 - eqLam a) * ((1 - a) / 2) ^ 2)
    (habs1 : ∀ (m : ℕ) (Lm Q q : ℝ), 0 < q → (1 - a) / 2 ≤ q → 0 ≤ Q → 0 ≤ Lm →
      Lm * (eqLam a) ^ (m + 1) ≤ K * eqLam a →
      C * ((𝔹 + 𝒟 * eqLam a) * Lm * Q) ^ 2 / q ^ 2
        ≤ (1 - (eqLam a) ^ 2) * 𝒞 * ((eqLam a)⁻¹ ^ (2 * (m + 1)) * (Q ^ 2 / ρ)))
    (habs2 : ∀ (m : ℕ) (Lm Ln Q q sig : ℝ), 0 < q → (1 - a) / 2 ≤ q → 0 ≤ Q → 0 < Lm →
      1 / 3 ≤ |sig| → Ln = |sig| * Lm → Lm * (eqLam a) ^ (m + 1) ≤ K * eqLam a →
      (C * ((𝔹 + 𝒟 * eqLam a) * Lm * Q))
          * ((𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (m + 1) + (𝔹 + 𝒟 * eqLam a) * Lm) * Q)
            / q ^ 2
        ≤ (1 - eqLam a) * 𝒟 * (Ln * ((eqLam a)⁻¹ ^ (m + 1) * (Q ^ 2 / ρ)))) :
    ∀ (w : List Bool) (z : ℂ × ℂ), ‖z - A1‖ ≤ ρ * (eqLam a) ^ w.length →
      (eqLam a) ^ w.length * ‖branchComp a w z - branchComp a w A1‖
        ≤ (𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K) * ‖z - A1‖ := by
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlam1' : eqLam a ≤ 1 := le_of_lt hlam1
  have hlamne : eqLam a ≠ 0 := ne_of_gt hlam0
  have hbeta : 0 < (1 - a) / 2 := by linarith
  have hu0 : 0 < (eqLam a)⁻¹ := inv_pos.mpr hlam0
  have hu1 : 0 ≤ (eqLam a)⁻¹ := hu0.le
  have hDK : 0 < 𝔹 * K + 𝒟 * K := by nlinarith [h𝔹, h𝒟, hKpos]
  have hAK : 0 < 𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K := by nlinarith [h𝔸, h𝒞, h𝔹, h𝒟, hKpos]
  have hLpos : 0 ≤ 𝔹 + 𝒟 * eqLam a := by nlinarith [h𝔹, h𝒟, hlam0]
  have hpow_le_one : (eqLam a) ^ 2 ≤ 1 := pow_le_one₀ hlam0.le hlam1'
  have hsplitP : ∀ p : ℂ × ℂ, ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
    intro p
    rw [Prod.norm_def]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  have INV : ∀ w : List Bool, ∀ z : ℂ × ℂ, ‖z - A1‖ ≤ ρ * (eqLam a) ^ w.length →
      (‖(branchComp a w z - branchComp a w A1).1‖
          ≤ 𝔸 * ‖z - A1‖ + 𝒞 * ((eqLam a)⁻¹ ^ (2 * w.length) * (‖z - A1‖ ^ 2 / ρ))) ∧
      (‖(branchComp a w z - branchComp a w A1).2‖
          ≤ 𝔹 * wLam a w * ‖z - A1‖
            + 𝒟 * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (‖z - A1‖ ^ 2 / ρ)))) := by
    intro w
    induction w with
    | nil =>
        intro z _
        simp only [List.length_nil, Nat.mul_zero, pow_zero, one_mul, mul_one,
          branchComp_apply_nil, wLam_nil]
        refine ⟨?_, ?_⟩
        · calc ‖(z - A1).1‖ ≤ ‖z - A1‖ := norm_fst_le (z - A1)
            _ ≤ 𝔸 * ‖z - A1‖ := by
                simpa using mul_le_mul_of_nonneg_right h𝔸 (norm_nonneg (z - A1))
            _ ≤ 𝔸 * ‖z - A1‖ + 𝒞 * (‖z - A1‖ ^ 2 / ρ) := by
                have h2 : 0 ≤ 𝒞 * (‖z - A1‖ ^ 2 / ρ) := by positivity
                linarith
        · calc ‖(z - A1).2‖ ≤ ‖z - A1‖ := norm_snd_le (z - A1)
            _ ≤ 𝔹 * ‖z - A1‖ := by
                simpa using mul_le_mul_of_nonneg_right h𝔹 (norm_nonneg (z - A1))
            _ ≤ 𝔹 * ‖z - A1‖ + 𝒟 * (‖z - A1‖ ^ 2 / ρ) := by
                have h2 : 0 ≤ 𝒟 * (‖z - A1‖ ^ 2 / ρ) := by positivity
                linarith
    | cons b w' ih =>
        intro z hz
        rw [List.length_cons] at hz
        set P : ℝ := ‖z - A1‖ with hPdef
        have hP0 : 0 ≤ P := by rw [hPdef]; exact norm_nonneg _
        have hzP : P ≤ ρ * (eqLam a) ^ (w'.length + 1) := hz
        have hlam_pow : (eqLam a) ^ (w'.length + 1) ≤ (eqLam a) ^ w'.length :=
          pow_le_pow_of_le_one hlam0.le hlam1' (Nat.le_succ _)
        have hz' : P ≤ ρ * (eqLam a) ^ w'.length :=
          le_trans hzP (mul_le_mul_of_nonneg_left hlam_pow hρ.le)
        obtain ⟨hI1, hI2⟩ := ih z (hPdef ▸ hz')
        rw [← hPdef] at hI1 hI2
        set p : ℂ × ℂ := branchComp a w' z - branchComp a w' A1 with hpdef
        have hΛ0 : 0 ≤ wLam a w' := wLam_nonneg a w'
        have hΛpos : 0 < wLam a w' := wLam_pos ha0 ha1 w'
        have hΛK : wLam a w' * (eqLam a) ^ (w'.length + 1) ≤ K * eqLam a := by
          have h := hK w'
          rw [← wLam_mul_pow ha0 ha1 w'] at h
          calc wLam a w' * (eqLam a) ^ (w'.length + 1)
              = wLam a w' * (eqLam a) ^ w'.length * eqLam a := by rw [pow_succ]; ring
            _ ≤ K * eqLam a := mul_le_mul_of_nonneg_right h hlam0.le
        have hqpos : 0 < stQ a (wSt w') := wb_stQ_pos ha0 ha1 (wSt w')
        have hqge : (1 - a) / 2 ≤ stQ a (wSt w') := stQ_ge ha0 ha1 (wSt w')
        have hsplit : ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := hsplitP p
        have hPPsm : P ^ 2 / ρ ≤ P * (eqLam a) ^ (w'.length + 1) := by
          rw [div_le_iff₀ hρ, pow_two]
          calc P * P ≤ P * (ρ * (eqLam a) ^ (w'.length + 1)) :=
                mul_le_mul_of_nonneg_left hzP hP0
            _ = P * (eqLam a) ^ (w'.length + 1) * ρ := by ring
        -- deviation bound for the first coordinate
        have hb1 : ‖p.1‖
            ≤ (𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)) * P := by
          have key : (eqLam a)⁻¹ ^ (2 * w'.length) * (P ^ 2 / ρ)
              ≤ (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1) * P := by
            calc (eqLam a)⁻¹ ^ (2 * w'.length) * (P ^ 2 / ρ)
                ≤ (eqLam a)⁻¹ ^ (2 * w'.length) * (P * (eqLam a) ^ (w'.length + 1)) :=
                  mul_le_mul_of_nonneg_left hPPsm (pow_nonneg hu1 _)
              _ = (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1) * P := by
                  rw [show (eqLam a)⁻¹ ^ (2 * w'.length) * (P * (eqLam a) ^ (w'.length + 1))
                      = ((eqLam a)⁻¹ ^ (2 * w'.length) * (eqLam a) ^ (w'.length + 1)) * P
                      by ring,
                    idA hlamne w'.length]
          calc ‖p.1‖ ≤ 𝔸 * P + 𝒞 * ((eqLam a)⁻¹ ^ (2 * w'.length) * (P ^ 2 / ρ)) := hI1
            _ ≤ 𝔸 * P + 𝒞 * ((eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1) * P) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left key h𝒞)
            _ = (𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)) * P := by ring
        -- deviation bound for the second coordinate
        have hb2 : ‖p.2‖ ≤ (𝔹 + 𝒟 * eqLam a) * wLam a w' * P := by
          have key : (eqLam a)⁻¹ ^ w'.length * (P ^ 2 / ρ) ≤ eqLam a * P := by
            calc (eqLam a)⁻¹ ^ w'.length * (P ^ 2 / ρ)
                ≤ (eqLam a)⁻¹ ^ w'.length * (P * (eqLam a) ^ (w'.length + 1)) :=
                  mul_le_mul_of_nonneg_left hPPsm (pow_nonneg hu1 _)
              _ = eqLam a * P := by
                  rw [show (eqLam a)⁻¹ ^ w'.length * (P * (eqLam a) ^ (w'.length + 1))
                      = ((eqLam a)⁻¹ ^ w'.length * (eqLam a) ^ (w'.length + 1)) * P by ring,
                    idB hlamne w'.length]
          calc ‖p.2‖ ≤ 𝔹 * wLam a w' * P
                + 𝒟 * (wLam a w' * ((eqLam a)⁻¹ ^ w'.length * (P ^ 2 / ρ))) := hI2
            _ ≤ 𝔹 * wLam a w' * P + 𝒟 * (wLam a w' * (eqLam a * P)) :=
                add_le_add le_rfl
                  (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hΛ0) h𝒟)
            _ = (𝔹 + 𝒟 * eqLam a) * wLam a w' * P := by ring
        -- the total deviation is small enough for the sharp one-step estimate
        have hp1 : 𝔸 * P ≤ ρ * 𝔸 := by
          have h1 : P ≤ ρ := le_trans hzP (by
            calc ρ * (eqLam a) ^ (w'.length + 1) ≤ ρ * 1 :=
                  mul_le_mul_of_nonneg_left (pow_le_one₀ hlam0.le hlam1') hρ.le
              _ = ρ := mul_one ρ)
          calc 𝔸 * P ≤ 𝔸 * ρ := mul_le_mul_of_nonneg_left h1 (by linarith)
            _ = ρ * 𝔸 := by ring
        have hp2 : 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1) * P ≤ ρ * 𝒞 := by
          calc 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1) * P
              ≤ 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)
                  * (ρ * (eqLam a) ^ (w'.length + 1)) :=
                mul_le_mul_of_nonneg_left hzP (by positivity)
            _ = ρ * 𝒞 * ((eqLam a) ^ 2 * ((eqLam a)⁻¹ ^ (w'.length + 1)
                  * (eqLam a) ^ (w'.length + 1))) := by ring
            _ = ρ * 𝒞 * ((eqLam a) ^ 2 * 1) := by rw [idE' hlamne (w'.length + 1)]
            _ ≤ ρ * 𝒞 := by
                rw [mul_one]
                exact mul_le_of_le_one_right (by positivity) hpow_le_one
        have hp3 : (𝔹 + 𝒟 * eqLam a) * wLam a w' * P ≤ ρ * (𝔹 * K + 𝒟 * K) := by
          calc (𝔹 + 𝒟 * eqLam a) * wLam a w' * P
              ≤ (𝔹 + 𝒟 * eqLam a) * wLam a w' * (ρ * (eqLam a) ^ (w'.length + 1)) :=
                mul_le_mul_of_nonneg_left hzP (by positivity)
            _ = ρ * ((𝔹 + 𝒟 * eqLam a) * (wLam a w' * (eqLam a) ^ (w'.length + 1))) := by ring
            _ ≤ ρ * ((𝔹 + 𝒟 * eqLam a) * (K * eqLam a)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hΛK (by linarith)) hρ.le
            _ ≤ ρ * (𝔹 * K + 𝒟 * K) := by
                apply mul_le_mul_of_nonneg_left _ hρ.le
                have hBK : 0 ≤ 𝔹 * K := by nlinarith
                have hDK : 0 ≤ 𝒟 * K := by nlinarith
                have hl2 : (eqLam a) ^ 2 ≤ 1 := hpow_le_one
                have h1' : 𝔹 * K * eqLam a ≤ 𝔹 * K := by
                  calc 𝔹 * K * eqLam a ≤ 𝔹 * K * 1 :=
                        mul_le_mul_of_nonneg_left hlam1' hBK
                    _ = 𝔹 * K := by ring
                have h2' : 𝒟 * K * (eqLam a) ^ 2 ≤ 𝒟 * K := by
                  calc 𝒟 * K * (eqLam a) ^ 2 ≤ 𝒟 * K * 1 :=
                        mul_le_mul_of_nonneg_left hl2 hDK
                    _ = 𝒟 * K := by ring
                nlinarith [h1', h2']
        have hdev : ‖p‖ ≤ (1 - a) / 8 := by
          have hfirst : (𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)) * P
              ≤ ρ * (𝔸 + 𝒞) := by
            rw [add_mul]
            calc 𝔸 * P + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1) * P
                ≤ ρ * 𝔸 + ρ * 𝒞 := add_le_add hp1 hp2
              _ = ρ * (𝔸 + 𝒞) := by ring
          calc ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := hsplit
            _ ≤ (𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)) * P
                  + (𝔹 + 𝒟 * eqLam a) * wLam a w' * P := add_le_add hb1 hb2
            _ ≤ ρ * (𝔸 + 𝒞) + ρ * (𝔹 * K + 𝒟 * K) := add_le_add hfirst hp3
            _ = ρ * (𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K) := by ring
            _ ≤ (1 - a) / 8 := hR1
        -- the sharp one-step estimate at the axis point `stCtr (wSt w')`
        set xa : ℝ := stCtr (wSt w') with hxadef
        have hxa_mem : ∃ k : ℤ, xa = -1 / 2 + 2 * (k : ℝ) := by
          rw [hxadef]; exact wb_stCtr_mem (wSt w')
        have hqdef : stQ a (wSt w') = |xa + a / 2| := by rw [hxadef]; rfl
        set X : ℂ × ℂ := invBranch a b (((xa : ℂ), (0 : ℂ)) + p)
            - invBranch a b (((xa : ℂ), (0 : ℂ))) with hXdef
        have hbr : branchComp a w' z = (((xa : ℝ) : ℂ), (0 : ℂ)) + p := by
          rw [hpdef, hxadef, branchComp_centre ha0 ha1 w']
          ext <;> simp
        have hbrc : branchComp a (b :: w') z - branchComp a (b :: w') A1 = X := by
          rw [branchComp_cons, branchComp_cons, hbr, hxadef, branchComp_centre ha0 ha1 w', hXdef]
        obtain ⟨hstep1, hstep2⟩ := hstep xa hxa_mem b (p := p) hdev
        have hstep1' : ‖X.1 + p.1‖ ≤ C * ‖p.2‖ ^ 2 / (stQ a (wSt w')) ^ 2 := by
          rw [hqdef]; exact hstep1
        have hstep2' : ‖X.2 - (-1 + sgnB b / stQ a (wSt w')) * p.2‖
            ≤ C * ‖p.2‖ * ‖p‖ / (stQ a (wSt w')) ^ 2 := by
          rw [hqdef]; exact hstep2
        have hsige : 1 / 3 ≤ |(-1 + sgnB b / stQ a (wSt w'))| :=
          abs_one_step_ge ha0 ha1 b (wSt w')
        have hLn : wLam a (b :: w') = |(-1 + sgnB b / stQ a (wSt w'))| * wLam a w' := by
          rw [wLam_cons, mul_comm]
        have hple : ‖p‖ ≤ (𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)
            + (𝔹 + 𝒟 * eqLam a) * wLam a w') * P := by
          calc ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := hsplit
            _ ≤ (𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)) * P
                  + (𝔹 + 𝒟 * eqLam a) * wLam a w' * P := add_le_add hb1 hb2
            _ = (𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)
                  + (𝔹 + 𝒟 * eqLam a) * wLam a w') * P := by ring
        refine ⟨?_, ?_⟩
        · -- coordinate 1
          have habs1' := habs1 w'.length (wLam a w') P (stQ a (wSt w')) hqpos hqge hP0 hΛ0 hΛK
          have hsq : ‖p.2‖ ^ 2 ≤ ((𝔹 + 𝒟 * eqLam a) * wLam a w' * P) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb2 2
          have hcorr1 : C * ‖p.2‖ ^ 2 / (stQ a (wSt w')) ^ 2
              ≤ (1 - (eqLam a) ^ 2) * 𝒞
                  * ((eqLam a)⁻¹ ^ (2 * (w'.length + 1)) * (P ^ 2 / ρ)) := by
            calc C * ‖p.2‖ ^ 2 / (stQ a (wSt w')) ^ 2
                ≤ C * (((𝔹 + 𝒟 * eqLam a) * wLam a w' * P) ^ 2) / (stQ a (wSt w')) ^ 2 :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCpos.le) (by positivity)
              _ ≤ (1 - (eqLam a) ^ 2) * 𝒞
                    * ((eqLam a)⁻¹ ^ (2 * (w'.length + 1)) * (P ^ 2 / ρ)) := habs1'
          have hcomb1 : 𝒞 * ((eqLam a)⁻¹ ^ (2 * w'.length) * (P ^ 2 / ρ))
                + C * ‖p.2‖ ^ 2 / (stQ a (wSt w')) ^ 2
              ≤ 𝒞 * ((eqLam a)⁻¹ ^ (2 * (w'.length + 1)) * (P ^ 2 / ρ)) := by
            have hidC' : 𝒞 * ((eqLam a)⁻¹ ^ (2 * w'.length) * (P ^ 2 / ρ))
                = (eqLam a) ^ 2 * (𝒞 * ((eqLam a)⁻¹ ^ (2 * (w'.length + 1))
                    * (P ^ 2 / ρ))) := by
              rw [← idC hlamne w'.length]; ring
            nlinarith [hidC', hcorr1]
          have he : X.1 = -p.1 + (X.1 + p.1) := by ring
          calc ‖(branchComp a (b :: w') z - branchComp a (b :: w') A1).1‖ = ‖X.1‖ := by rw [hbrc]
            _ = ‖-p.1 + (X.1 + p.1)‖ := congrArg (fun t => ‖t‖) he
            _ ≤ ‖-p.1‖ + ‖X.1 + p.1‖ := norm_add_le _ _
            _ = ‖p.1‖ + ‖X.1 + p.1‖ := by rw [norm_neg]
            _ ≤ (𝔸 * P + 𝒞 * ((eqLam a)⁻¹ ^ (2 * w'.length) * (P ^ 2 / ρ)))
                  + C * ‖p.2‖ ^ 2 / (stQ a (wSt w')) ^ 2 := add_le_add hI1 hstep1'
            _ = 𝔸 * P + (𝒞 * ((eqLam a)⁻¹ ^ (2 * w'.length) * (P ^ 2 / ρ))
                  + C * ‖p.2‖ ^ 2 / (stQ a (wSt w')) ^ 2) := by ring
            _ ≤ 𝔸 * P + 𝒞 * ((eqLam a)⁻¹ ^ (2 * (w'.length + 1)) * (P ^ 2 / ρ)) := by
                linarith [hcomb1]
            _ = 𝔸 * ‖z - A1‖ + 𝒞 * ((eqLam a)⁻¹ ^ (2 * (b :: w').length)
                  * (‖z - A1‖ ^ 2 / ρ)) := by
                rw [hPdef, List.length_cons]
        · -- coordinate 2
          have habs2' := habs2 w'.length (wLam a w') (wLam a (b :: w')) P (stQ a (wSt w'))
            (-1 + sgnB b / stQ a (wSt w')) hqpos hqge hP0 hΛpos hsige hLn hΛK
          have hcorr2 : C * ‖p.2‖ * ‖p‖ / (stQ a (wSt w')) ^ 2
              ≤ (1 - eqLam a) * 𝒟 * (wLam a (b :: w')
                  * ((eqLam a)⁻¹ ^ (w'.length + 1) * (P ^ 2 / ρ))) := by
            have h2 : C * ‖p.2‖ ≤ C * ((𝔹 + 𝒟 * eqLam a) * wLam a w' * P) :=
              mul_le_mul_of_nonneg_left hb2 hCpos.le
            have h3 : (C * ‖p.2‖) * ‖p‖ ≤ (C * ((𝔹 + 𝒟 * eqLam a) * wLam a w' * P))
                * ((𝔸 + 𝒞 * (eqLam a) ^ 2 * (eqLam a)⁻¹ ^ (w'.length + 1)
                    + (𝔹 + 𝒟 * eqLam a) * wLam a w') * P) :=
              mul_le_mul h2 hple (norm_nonneg _) (by positivity)
            exact le_trans (div_le_div_of_nonneg_right h3 (by positivity)) habs2'
          have hprop : |(-1 + sgnB b / stQ a (wSt w'))| * ‖p.2‖
              ≤ 𝔹 * wLam a (b :: w') * P
                + 𝒟 * (wLam a (b :: w') * ((eqLam a)⁻¹ ^ w'.length * (P ^ 2 / ρ))) := by
            have h := mul_le_mul_of_nonneg_left hI2 (abs_nonneg (-1 + sgnB b / stQ a (wSt w')))
            calc |(-1 + sgnB b / stQ a (wSt w'))| * ‖p.2‖
                ≤ |(-1 + sgnB b / stQ a (wSt w'))|
                    * (𝔹 * wLam a w' * P
                        + 𝒟 * (wLam a w' * ((eqLam a)⁻¹ ^ w'.length * (P ^ 2 / ρ)))) := h
              _ = 𝔹 * wLam a (b :: w') * P
                    + 𝒟 * (wLam a (b :: w')
                        * ((eqLam a)⁻¹ ^ w'.length * (P ^ 2 / ρ))) := by
                  rw [hLn]; ring
          have hcomb2 : |(-1 + sgnB b / stQ a (wSt w'))| * ‖p.2‖
                + C * ‖p.2‖ * ‖p‖ / (stQ a (wSt w')) ^ 2
              ≤ 𝔹 * wLam a (b :: w') * P
                + 𝒟 * (wLam a (b :: w')
                    * ((eqLam a)⁻¹ ^ (w'.length + 1) * (P ^ 2 / ρ))) := by
            have hidD' : 𝒟 * (wLam a (b :: w') * ((eqLam a)⁻¹ ^ w'.length * (P ^ 2 / ρ)))
                = eqLam a * (𝒟 * (wLam a (b :: w')
                    * ((eqLam a)⁻¹ ^ (w'.length + 1) * (P ^ 2 / ρ)))) := by
              rw [← idD hlamne w'.length]; ring
            have hcorr2' : C * ‖p.2‖ * ‖p‖ / (stQ a (wSt w')) ^ 2
                ≤ (1 - eqLam a) * (𝒟 * (wLam a (b :: w')
                    * ((eqLam a)⁻¹ ^ (w'.length + 1) * (P ^ 2 / ρ)))) := by
              have he : (1 - eqLam a) * 𝒟 * (wLam a (b :: w')
                    * ((eqLam a)⁻¹ ^ (w'.length + 1) * (P ^ 2 / ρ)))
                  = (1 - eqLam a) * (𝒟 * (wLam a (b :: w')
                      * ((eqLam a)⁻¹ ^ (w'.length + 1) * (P ^ 2 / ρ)))) := by ring
              rw [he] at hcorr2
              exact hcorr2
            linarith [hprop, hidD', hcorr2']
          have he2 : X.2 = (-1 + sgnB b / stQ a (wSt w')) * p.2
              + (X.2 - (-1 + sgnB b / stQ a (wSt w')) * p.2) := by ring
          calc ‖(branchComp a (b :: w') z - branchComp a (b :: w') A1).2‖ = ‖X.2‖ := by rw [hbrc]
            _ = ‖(-1 + sgnB b / stQ a (wSt w')) * p.2
                  + (X.2 - (-1 + sgnB b / stQ a (wSt w')) * p.2)‖ :=
                congrArg (fun t => ‖t‖) he2
            _ ≤ ‖(-1 + sgnB b / stQ a (wSt w')) * p.2‖
                  + ‖X.2 - (-1 + sgnB b / stQ a (wSt w')) * p.2‖ := norm_add_le _ _
            _ = |(-1 + sgnB b / stQ a (wSt w'))| * ‖p.2‖
                  + ‖X.2 - (-1 + sgnB b / stQ a (wSt w')) * p.2‖ := by
                rw [norm_mul]
                rw [show (-1 : ℂ) + ((sgnB b : ℝ) : ℂ) / ((stQ a (wSt w') : ℝ) : ℂ)
                    = (((-1 + sgnB b / stQ a (wSt w') : ℝ)) : ℂ) by push_cast; ring]
                have hnorm : ‖(((-1 + sgnB b / stQ a (wSt w') : ℝ)) : ℂ)‖
                    = |(-1 + sgnB b / stQ a (wSt w'))| := RCLike.norm_ofReal (K := ℂ) _
                rw [hnorm]
            _ ≤ |(-1 + sgnB b / stQ a (wSt w'))| * ‖p.2‖
                  + C * ‖p.2‖ * ‖p‖ / (stQ a (wSt w')) ^ 2 := add_le_add le_rfl hstep2'
            _ ≤ 𝔹 * wLam a (b :: w') * P
                  + 𝒟 * (wLam a (b :: w')
                      * ((eqLam a)⁻¹ ^ (w'.length + 1) * (P ^ 2 / ρ))) := hcomb2
            _ = 𝔹 * wLam a (b :: w') * ‖z - A1‖
                  + 𝒟 * (wLam a (b :: w') * ((eqLam a)⁻¹ ^ (b :: w').length
                      * (‖z - A1‖ ^ 2 / ρ))) := by
                rw [hPdef, List.length_cons]
  intro w z hz
  set P : ℝ := ‖z - A1‖ with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; exact norm_nonneg _
  have hzP : P ≤ ρ * (eqLam a) ^ w.length := hz
  obtain ⟨h1, h2⟩ := INV w z (hPdef ▸ hzP)
  rw [← hPdef] at h1 h2
  have hΛ0 : 0 ≤ wLam a w := wLam_nonneg a w
  have hΛK : wLam a w * (eqLam a) ^ w.length ≤ K := by
    rw [wLam_mul_pow ha0 ha1 w]; exact hK w
  have hsplit : ‖branchComp a w z - branchComp a w A1‖
      ≤ ‖(branchComp a w z - branchComp a w A1).1‖
        + ‖(branchComp a w z - branchComp a w A1).2‖ := hsplitP _
  have hun : (eqLam a) ^ w.length * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))
      = P ^ 2 / ρ := by
    rw [show (eqLam a) ^ w.length * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))
        = ((eqLam a) ^ w.length * (eqLam a)⁻¹ ^ w.length) * (P ^ 2 / ρ) by ring,
      idE hlamne w.length, one_mul]
  have hu2n : (eqLam a) ^ w.length * ((eqLam a)⁻¹ ^ (2 * w.length) * (P ^ 2 / ρ))
      = (eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ) := by
    rw [show ((eqLam a)⁻¹) ^ (2 * w.length)
        = (eqLam a)⁻¹ ^ w.length * (eqLam a)⁻¹ ^ w.length by rw [two_mul, pow_add]]
    rw [show (eqLam a) ^ w.length * (((eqLam a)⁻¹ ^ w.length * (eqLam a)⁻¹ ^ w.length)
        * (P ^ 2 / ρ))
        = ((eqLam a) ^ w.length * (eqLam a)⁻¹ ^ w.length)
          * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)) by ring,
      idE hlamne w.length, one_mul]
  have t1 : (eqLam a) ^ w.length * (𝔸 * P + 𝒞 * ((eqLam a)⁻¹ ^ (2 * w.length)
        * (P ^ 2 / ρ))) ≤ (𝔸 + 𝒞) * P := by
    have e : (eqLam a) ^ w.length * (𝔸 * P + 𝒞 * ((eqLam a)⁻¹ ^ (2 * w.length)
          * (P ^ 2 / ρ)))
        = 𝔸 * ((eqLam a) ^ w.length * P)
          + 𝒞 * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)) := by
      have h1 : (eqLam a) ^ w.length * (𝒞 * ((eqLam a)⁻¹ ^ (2 * w.length) * (P ^ 2 / ρ)))
          = 𝒞 * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)) := by
        rw [show (eqLam a) ^ w.length * (𝒞 * ((eqLam a)⁻¹ ^ (2 * w.length) * (P ^ 2 / ρ)))
            = 𝒞 * ((eqLam a) ^ w.length * ((eqLam a)⁻¹ ^ (2 * w.length) * (P ^ 2 / ρ)))
            by ring, hu2n]
      rw [mul_add, h1]; ring
    rw [e]
    have hAP : 𝔸 * ((eqLam a) ^ w.length * P) ≤ 𝔸 * P := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      calc (eqLam a) ^ w.length * P ≤ 1 * P :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlam1') hP0
        _ = P := one_mul P
    have huP : (eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ) ≤ P := by
      have hPP : P ^ 2 / ρ ≤ P * (eqLam a) ^ w.length := by
        rw [div_le_iff₀ hρ, pow_two]
        calc P * P ≤ P * (ρ * (eqLam a) ^ w.length) :=
              mul_le_mul_of_nonneg_left hzP hP0
          _ = P * (eqLam a) ^ w.length * ρ := by ring
      calc (eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)
          ≤ (eqLam a)⁻¹ ^ w.length * (P * (eqLam a) ^ w.length) :=
            mul_le_mul_of_nonneg_left hPP (pow_nonneg hu1 _)
        _ = P := by
            rw [show (eqLam a)⁻¹ ^ w.length * (P * (eqLam a) ^ w.length)
                = ((eqLam a)⁻¹ ^ w.length * (eqLam a) ^ w.length) * P by ring,
              idE' hlamne w.length, one_mul]
    calc 𝔸 * ((eqLam a) ^ w.length * P) + 𝒞 * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))
        ≤ 𝔸 * P + 𝒞 * P := add_le_add hAP (mul_le_mul_of_nonneg_left huP h𝒞)
      _ = (𝔸 + 𝒞) * P := by ring
  have t2 : (eqLam a) ^ w.length * (𝔹 * wLam a w * P
        + 𝒟 * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))))
      ≤ (𝔹 * K + 𝒟 * K) * P := by
    have e : (eqLam a) ^ w.length * (𝔹 * wLam a w * P
          + 𝒟 * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))))
        = 𝔹 * (wLam a w * ((eqLam a) ^ w.length * P)) + 𝒟 * (wLam a w * (P ^ 2 / ρ)) := by
      have h1 : (eqLam a) ^ w.length * (𝒟 * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))))
          = 𝒟 * (wLam a w * (P ^ 2 / ρ)) := by
        rw [show (eqLam a) ^ w.length
              * (𝒟 * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))))
            = 𝒟 * ((eqLam a) ^ w.length * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ))))
            by ring,
          show (eqLam a) ^ w.length * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)))
            = wLam a w * (P ^ 2 / ρ) by
              rw [show (eqLam a) ^ w.length
                    * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)))
                  = wLam a w * ((eqLam a) ^ w.length * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)))
                  by ring, hun]]
      rw [mul_add, h1]; ring
    rw [e]
    have hb : 𝔹 * (wLam a w * ((eqLam a) ^ w.length * P)) ≤ 𝔹 * (K * P) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      calc wLam a w * ((eqLam a) ^ w.length * P)
          = wLam a w * (eqLam a) ^ w.length * P := by ring
        _ ≤ K * P := mul_le_mul_of_nonneg_right hΛK hP0
    have hd : 𝒟 * (wLam a w * (P ^ 2 / ρ)) ≤ 𝒟 * (K * P) := by
      apply mul_le_mul_of_nonneg_left _ h𝒟
      have hPP : P ^ 2 / ρ ≤ P * (eqLam a) ^ w.length := by
        rw [div_le_iff₀ hρ, pow_two]
        calc P * P ≤ P * (ρ * (eqLam a) ^ w.length) :=
              mul_le_mul_of_nonneg_left hzP hP0
          _ = P * (eqLam a) ^ w.length * ρ := by ring
      calc wLam a w * (P ^ 2 / ρ) ≤ wLam a w * (P * (eqLam a) ^ w.length) :=
            mul_le_mul_of_nonneg_left hPP hΛ0
        _ = wLam a w * (eqLam a) ^ w.length * P := by ring
        _ ≤ K * P := mul_le_mul_of_nonneg_right hΛK hP0
    calc 𝔹 * (wLam a w * ((eqLam a) ^ w.length * P)) + 𝒟 * (wLam a w * (P ^ 2 / ρ))
        ≤ 𝔹 * (K * P) + 𝒟 * (K * P) := add_le_add hb hd
      _ = (𝔹 * K + 𝒟 * K) * P := by ring
  have hmul := mul_le_mul_of_nonneg_left hsplit (pow_nonneg hlam0.le w.length)
  have hres : (eqLam a) ^ w.length * ‖branchComp a w z - branchComp a w A1‖
      ≤ (𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K) * P := by
    calc (eqLam a) ^ w.length * ‖branchComp a w z - branchComp a w A1‖
        ≤ (eqLam a) ^ w.length * (‖(branchComp a w z - branchComp a w A1).1‖
            + ‖(branchComp a w z - branchComp a w A1).2‖) := hmul
      _ = (eqLam a) ^ w.length * ‖(branchComp a w z - branchComp a w A1).1‖
            + (eqLam a) ^ w.length * ‖(branchComp a w z - branchComp a w A1).2‖ := by ring
      _ ≤ (eqLam a) ^ w.length * (𝔸 * P + 𝒞 * ((eqLam a)⁻¹ ^ (2 * w.length)
              * (P ^ 2 / ρ)))
            + (eqLam a) ^ w.length * (𝔹 * wLam a w * P
              + 𝒟 * (wLam a w * ((eqLam a)⁻¹ ^ w.length * (P ^ 2 / ρ)))) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (pow_nonneg hlam0.le w.length))
            (mul_le_mul_of_nonneg_left h2 (pow_nonneg hlam0.le w.length))
      _ ≤ (𝔸 + 𝒞) * P + (𝔹 * K + 𝒟 * K) * P := add_le_add t1 t2
      _ = (𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K) * P := by ring
  rw [hPdef] at hres
  exact hres


/-- **Uniform analytic radius and Lipschitz bound for a finite composition of inverse branches
at `A₁`.**  There are `ρ D > 0` such that for every word `w` the composition
`branchComp a w` is analytic on the ball of radius `ρ * λ ^ |w|` about `A₁ = (-1/2,0)` and
satisfies the scaled Lipschitz bound `λ ^ |w| * ‖F z - F A₁‖ ≤ D * ‖z - A₁‖` there.

Route: `branchComp_radius_aux` (the invariant induction, in this file) with the constants of
`Work.EQ.FanTri.radius_constants_v3`, the sharp one-step linearisation
`Work.EQ.FanTri.invBranch_axis_second_order_sharp`, the two numerical absorption lemmas
`Work.EQ.FanTri.absorb_coord1`, `absorb_coord2`, and the bound `K` on the walk weights
`Work.EQ.FanTri.wtAux_uniform_bound`. -/
theorem branchComp_radius {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ ρ D : ℝ, 0 < ρ ∧ 0 < D ∧ ∀ (w : List Bool) (z : ℂ × ℂ),
      ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ * (Work.EQ.eqLam a) ^ w.length →
      (Work.EQ.eqLam a) ^ w.length *
        ‖Work.EQ.FanTri.branchComp a w z
          - Work.EQ.FanTri.branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
        ≤ D * ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ := by
  obtain ⟨K, hKpos, hKw⟩ := wtAux_uniform_bound ha0 ha1
  obtain ⟨C, hCpos, hstep0⟩ := invBranch_axis_second_order_sharp ha0 ha1
  obtain ⟨ρ, 𝔸, 𝒞, 𝔹, 𝒟, hρ, h𝔸, h𝔹, h𝒞, h𝒟, hρ1, hR1, hR2, hR3a, hR3b, hR3c⟩ :=
    radius_constants_v3 ha0 ha1 rfl hKpos hCpos
  have hDpos : 0 < 𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K := by nlinarith [h𝔸, h𝒞, h𝔹, h𝒟, hKpos]
  refine ⟨ρ, 𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K, hρ, hDpos, ?_⟩
  intro w z hz
  refine branchComp_radius_aux (a := a) (ρ := ρ) (𝔸 := 𝔸) (𝒞 := 𝒞) (𝔹 := 𝔹) (𝒟 := 𝒟)
    (K := K) (C := C) ha0 ha1 hρ h𝔸 h𝔹 h𝒞 h𝒟 hKpos (fun w => hKw w.reverse) hCpos ?_ hR1 hR2 hR3a hR3b hR3c ?_ ?_ w z hz
  · intro x hx s p hp
    exact hstep0 x hx s hp
  · intro m Lm Q q hq hbq hQ hLm hKL
    have h := absorb_coord1 (lam := eqLam a) (rho := ρ) (q := q) (beta := (1 - a) / 2)
      (Cc := 𝒞) (C := C) (Bb := 𝔹) (Dd := 𝒟) (Lm := Lm) (K := K) (P := Q) m
      (eqLam_pos' ha0 ha1) (eqLam_lt_one' ha0 ha1) hρ hq (by linarith) hbq h𝒞 hCpos hLm
      hKpos hQ hR2 hKL
    rw [show C * ((𝔹 + 𝒟 * eqLam a) * Lm * Q) ^ 2 / q ^ 2
        = C * (𝔹 + 𝒟 * eqLam a) ^ 2 * Lm ^ 2 * Q ^ 2 / q ^ 2 by ring,
      show (1 - (eqLam a) ^ 2) * 𝒞 * ((eqLam a)⁻¹ ^ (2 * (m + 1)) * (Q ^ 2 / ρ))
        = (1 - (eqLam a) ^ 2) * 𝒞 * (eqLam a)⁻¹ ^ (2 * (m + 1)) * Q ^ 2 / ρ by ring]
    exact h
  · intro m Lm Ln Q q sig hq hbq hQ hLm hsig hLn hKL
    have h := absorb_coord2 (lam := eqLam a) (rho := ρ) (q := q) (beta := (1 - a) / 2)
      (A := 𝔸) (Cc := 𝒞) (Bb := 𝔹) (Dd := 𝒟) (Lm := Lm) (Ln := Ln) (C := C) (K := K)
      (P := Q) (sig := sig) m
      (eqLam_pos' ha0 ha1) (eqLam_lt_one' ha0 ha1) hρ hq (by linarith) hbq (by linarith)
      h𝒞 h𝒟 hCpos hLm hKpos hQ (by linarith) hsig hLn hR3a hR3b hR3c hKL
    rw [show (1 - eqLam a) * 𝒟 * (Ln * ((eqLam a)⁻¹ ^ (m + 1) * (Q ^ 2 / ρ)))
        = (1 - eqLam a) * 𝒟 * Ln * (eqLam a)⁻¹ ^ (m + 1) * Q ^ 2 / ρ by ring]
    exact h

end

end Work.EQ.FanTri
