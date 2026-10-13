import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.pb_poly_bound
import Submission.Work.WilC4.DeepRatioDefs
import Submission.Work.WilC4.oneSided_ratio_deep
import Submission.Work.WilC4.deepThetaG_definableB

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr ratioY valY valY_mem eq_valY InD)

/-! ## 0. A small arithmetic helper -/

theorem abs_div_eq_div_of_mul_pos {a b : ℝ} (h : 0 < a * b) : |a| / |b| = a / b := by
  rcases mul_pos_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_pos ha, abs_of_pos hb]
  · rw [abs_of_neg ha, abs_of_neg hb, neg_div_neg_eq]

variable {k : ℕ}

/-! ## 1. Two arithmetic telescoping lemmas

These convert a chain of multiplicative relations `g (j+1) = r j * g j` with `r j ≥ β ≥ 0` into
the super-polynomial lower bound `β^M ≤ g M / g 0`. -/

theorem pow_le_prod_ge {r : ℕ → ℝ} {M : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (hr : ∀ j, j < M → β ≤ r j) :
    β ^ M ≤ ∏ j ∈ Finset.range M, r j := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ]
    have h1 : β ^ n ≤ ∏ j ∈ Finset.range n, r j :=
      ih (fun j hj => hr j (Nat.lt_succ_of_lt hj))
    have h2 : β ≤ r n := hr n (Nat.lt_succ_self n)
    have hP : 0 ≤ ∏ j ∈ Finset.range n, r j :=
      Finset.prod_nonneg fun j hj => le_trans hβ (hr j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))
    exact mul_le_mul h1 h2 hβ hP

theorem pow_le_div_of_chain {g r : ℕ → ℝ} {M : ℕ} {β : ℝ} (hβ : 0 ≤ β) (hg0 : g 0 ≠ 0)
    (hrel : ∀ j, j < M → g (j + 1) = r j * g j) (hr : ∀ j, j < M → β ≤ r j) :
    β ^ M ≤ g M / g 0 := by
  have hprod : ∀ M : ℕ, (∀ j, j < M → g (j + 1) = r j * g j) →
      g M = g 0 * ∏ j ∈ Finset.range M, r j := by
    intro M
    induction M with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      have h1 : g n = g 0 * ∏ j ∈ Finset.range n, r j :=
        ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
      rw [h n (Nat.lt_succ_self n), h1, Finset.prod_range_succ]
      ring
  rw [hprod M hrel]
  have hle : β ^ M ≤ ∏ j ∈ Finset.range M, r j := pow_le_prod_ge hβ hr
  rw [mul_div_cancel_left₀ _ hg0]
  exact hle

theorem pow_mul_le_of_chain_bwd {h r : ℕ → ℝ} {M : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (hpos : ∀ j, j ≤ M → 0 ≤ h j)
    (hrel : ∀ j, j < M → h j = r j * h (j + 1)) (hr : ∀ j, j < M → β ≤ r j) :
    β ^ M * h M ≤ h 0 := by
  have key : ∀ M : ℕ, (∀ j, j < M → h j = r j * h (j + 1)) →
      (∀ j, j < M → β ≤ r j) → (∀ j, j ≤ M → 0 ≤ h j) → β ^ M * h M ≤ h 0 := by
    intro M
    induction M with
    | zero => intro _ _ _; simp
    | succ n ih =>
      intro hh hrr hps
      have h1 : β ^ n * h n ≤ h 0 :=
        ih (fun j hj => hh j (Nat.lt_succ_of_lt hj)) (fun j hj => hrr j (Nat.lt_succ_of_lt hj))
          (fun j hj => hps j (le_trans hj (Nat.le_succ n)))
      have h2 : β ≤ r n := hrr n (Nat.lt_succ_self n)
      have hβn : 0 ≤ β ^ n := pow_nonneg hβ n
      have hhn : 0 ≤ h (n + 1) := hps (n + 1) le_rfl
      have hstep : β ^ n * β * h (n + 1) ≤ β ^ n * r n * h (n + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hβn) hhn
      have heq : β ^ n * r n * h (n + 1) = β ^ n * h n := by
        rw [mul_assoc, ← hh n (Nat.lt_succ_self n)]
      have : β ^ (n + 1) * h (n + 1) ≤ h 0 := by
        rw [pow_succ]
        calc β ^ n * β * h (n + 1) ≤ β ^ n * r n * h (n + 1) := hstep
          _ = β ^ n * h n := heq
          _ ≤ h 0 := h1
      exact this
  exact key M hrel hr hpos

/-! ## 2. Elementary facts about the deep window -/

/-- Two fibre values taken at points of the deep window have positive product (the fibre is
nonvanishing and continuous there). -/
theorem deep_mul_pos {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀) {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 ≤ β) (hx : 0 < x)
    (hdeep : IsDeepR B₀ c β x) {s t : ℝ}
    (hs : s ∈ Set.Ioo (x / (2 * β)) (2 * β * x))
    (ht : t ∈ Set.Ioo (x / (2 * β)) (2 * β * x)) :
    0 < valY Y c s * valY Y c t := by
  obtain ⟨hu, -, -⟩ := deep_nice hst.1 hβ hx hdeep
  exact deep_sign hst.1 hβ hx hdeep hs ht
    (valY_mem Y c s (hu s hs).exists)
    (valY_mem Y c t (hu t ht).exists)

/-- The value of the fibre at a point of the deep window is nonzero. -/
theorem deep_val_ne {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀) {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 ≤ β) (hx : 0 < x)
    (hdeep : IsDeepR B₀ c β x) {z : ℝ} (hz : z ∈ Set.Ioo (x / (2 * β)) (2 * β * x)) :
    valY Y c z ≠ 0 :=
  (deep_val hst.1 hβ hx hdeep hz).2

/-- The ratio at a point of the deep window (whose double is again in the window) is positive. -/
theorem deep_ratio_pos {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀) {c : Fin k → ℝ} {β x t : ℝ} (hβ : 1 ≤ β) (hx : 0 < x)
    (hdeep : IsDeepR B₀ c β x) (ht : t ∈ Set.Ioo (x / (2 * β)) (2 * β * x))
    (h2t : 2 * t ∈ Set.Ioo (x / (2 * β)) (2 * β * x)) :
    0 < ratioY Y c t := by
  have h := deep_mul_pos hst hβ hx hdeep h2t ht
  rw [ratioY, div_pos_iff]
  rcases mul_pos_iff.mp h with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'

/-! ## 3. The forward telescoping at a deep point -/

theorem deep_forward_le {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {c : Fin k → ℝ} {β x w y y₂ v : ℝ} {M : ℕ}
    (hβM : β = (2 : ℝ) ^ M) (hM : 1 ≤ M) (hx : 0 < x) (hdeep : IsDeepR B₀ c β x)
    (hy : Gr Y c x y) (hy0 : y ≠ 0) (hy₂ : Gr Y c (2 * x) y₂) (hwy : w * y = y₂)
    (hv : Gr Y c (β * x) v) (hw : β ≤ w)
    (hmono : ∀ t : ℝ, x < t → t < β * x → ratioY Y c x ≤ ratioY Y c t) :
    β ^ M ≤ |v| / |y| := by
  have hβ2 : (2 : ℝ) ≤ β := by
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ M :=
      pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hM
    simpa [hβM] using h2
  have hβ1 : (1 : ℝ) ≤ β := by linarith
  have hβ1lt : (1 : ℝ) < β := by linarith
  have hβpos : (0 : ℝ) < β := by linarith
  -- every chain point `2^j x`, `j ≤ M`, lies in the deep window
  have hmem : ∀ j : ℕ, j ≤ M → (2 : ℝ) ^ j * x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    intro j hj
    have hpj : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
    have hpMj : (2 : ℝ) ^ j ≤ β := by
      rw [hβM]; exact pow_le_pow_right₀ (by norm_num) hj
    constructor
    · have h1 : x / (2 * β) < x := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hβ1lt, hx]
      have h2 : x ≤ (2 : ℝ) ^ j * x := by
        have h3 : (1 : ℝ) * x ≤ (2 : ℝ) ^ j * x := mul_le_mul_of_nonneg_right hpj (le_of_lt hx)
        simpa using h3
      linarith
    · have h3 : (2 : ℝ) ^ j < 2 * β := by linarith
      calc (2 : ℝ) ^ j * x < (2 * β) * x := mul_lt_mul_of_pos_right h3 hx
        _ = 2 * β * x := by ring
  have hratx : ratioY Y c x = w := by
    rw [ratioY, (eq_valY hfun hy).symm, (eq_valY hfun hy₂).symm, div_eq_iff hy0]
    exact hwy.symm
  have hg0 : (fun j => |valY Y c ((2 : ℝ) ^ j * x)|) 0 ≠ 0 := by
    show |valY Y c ((2 : ℝ) ^ 0 * x)| ≠ 0
    rw [pow_zero, one_mul, (eq_valY hfun hy).symm]
    simpa using hy0
  have hgM : (fun j => |valY Y c ((2 : ℝ) ^ j * x)|) M = |v| := by
    show |valY Y c ((2 : ℝ) ^ M * x)| = |v|
    rw [← hβM, (eq_valY hfun hv).symm]
  have hrel : ∀ j, j < M → (fun j => |valY Y c ((2 : ℝ) ^ j * x)|) (j + 1)
      = ratioY Y c ((2 : ℝ) ^ j * x) * (fun j => |valY Y c ((2 : ℝ) ^ j * x)|) j := by
    intro j hj
    show |valY Y c ((2 : ℝ) ^ (j + 1) * x)|
        = ratioY Y c ((2 : ℝ) ^ j * x) * |valY Y c ((2 : ℝ) ^ j * x)|
    have h1 : (2 : ℝ) ^ j * x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := hmem j (le_of_lt hj)
    have h2 : (2 : ℝ) ^ (j + 1) * x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := hmem (j + 1) hj
    have h2eq : (2 : ℝ) ^ (j + 1) * x = 2 * ((2 : ℝ) ^ j * x) := by
      rw [pow_succ]; ring
    have hne : valY Y c ((2 : ℝ) ^ j * x) ≠ 0 := deep_val_ne hst hβ1 hx hdeep h1
    have hpos : 0 < ratioY Y c ((2 : ℝ) ^ j * x) :=
      deep_ratio_pos hst hβ1 hx hdeep h1 (by rw [← h2eq]; exact h2)
    rw [h2eq]
    calc |valY Y c (2 * ((2 : ℝ) ^ j * x))|
        = |valY Y c (2 * ((2 : ℝ) ^ j * x))| / |valY Y c ((2 : ℝ) ^ j * x)| *
            |valY Y c ((2 : ℝ) ^ j * x)| :=
          (div_mul_cancel₀ _ (abs_ne_zero.mpr hne)).symm
      _ = |valY Y c (2 * ((2 : ℝ) ^ j * x)) / valY Y c ((2 : ℝ) ^ j * x)| *
            |valY Y c ((2 : ℝ) ^ j * x)| := by rw [abs_div]
      _ = |ratioY Y c ((2 : ℝ) ^ j * x)| * |valY Y c ((2 : ℝ) ^ j * x)| := rfl
      _ = ratioY Y c ((2 : ℝ) ^ j * x) * |valY Y c ((2 : ℝ) ^ j * x)| := by
          rw [abs_of_pos hpos]
  have hrr : ∀ j, j < M → β ≤ ratioY Y c ((2 : ℝ) ^ j * x) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [pow_zero, one_mul, hratx]
      exact hw
    · have hlt1 : x < (2 : ℝ) ^ j * x := by
        have : (1 : ℝ) < (2 : ℝ) ^ j := one_lt_pow₀ (show (1 : ℝ) < 2 by norm_num) (by omega)
        nlinarith
      have hlt2 : (2 : ℝ) ^ j * x < β * x := by
        have : (2 : ℝ) ^ j < β := by
          rw [hβM]; exact pow_lt_pow_right₀ (by norm_num) hj
        nlinarith
      have hmon := hmono _ hlt1 hlt2
      rw [hratx] at hmon
      linarith
  have hmain := pow_le_div_of_chain (β := β) (M := M) (le_of_lt hβpos)
    (g := fun j => |valY Y c ((2 : ℝ) ^ j * x)|) (r := fun j => ratioY Y c ((2 : ℝ) ^ j * x))
    hg0 hrel hrr
  have h10 : |valY Y c ((2 : ℝ) ^ 0 * x)| = |y| := by
    rw [pow_zero, one_mul, (eq_valY hfun hy).symm]
  have h1M : |valY Y c ((2 : ℝ) ^ M * x)| = |v| := by
    rw [← hβM, (eq_valY hfun hv).symm]
  rw [h1M, h10] at hmain
  exact hmain

/-! ## 4. The backward telescoping at a deep point -/

theorem deep_backward_le {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {c : Fin k → ℝ} {β x w y y₂ y₀ : ℝ} {M : ℕ}
    (hβM : β = (2 : ℝ) ^ M) (hM : 1 ≤ M) (hx : 0 < x) (hdeep : IsDeepR B₀ c β x)
    (hy : Gr Y c x y) (hy0 : y ≠ 0) (hy₂ : Gr Y c (2 * x) y₂) (hwy : w * y = y₂)
    (hy₀ : Gr Y c (x / β) y₀) (hw : β ≤ w)
    (hmono : ∀ t : ℝ, x / (2 * β) < t → t < x → ratioY Y c x ≤ ratioY Y c t) :
    β ^ M ≤ |y| / |y₀| := by
  have hβ1 : (1 : ℝ) ≤ β := by
    rw [hβM]
    exact one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
  have hβ1lt : (1 : ℝ) < β := by
    have h2 : (2 : ℝ) ≤ β := by
      rw [hβM]
      have h3 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ M :=
        pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hM
      simpa using h3
    linarith
  have hβpos : (0 : ℝ) < β := by linarith
  have hratx : ratioY Y c x = w := by
    rw [ratioY, (eq_valY hfun hy).symm, (eq_valY hfun hy₂).symm, div_eq_iff hy0]
    exact hwy.symm
  -- every chain point `x/2^j`, `j ≤ M`, lies in the deep window
  have hmem : ∀ j : ℕ, j ≤ M → x / (2 : ℝ) ^ j ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    intro j hj
    have hpj : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
    have hpMj : (2 : ℝ) ^ j ≤ β := by
      rw [hβM]; exact pow_le_pow_right₀ (by norm_num) hj
    constructor
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · have h1 : x / (2 : ℝ) ^ j ≤ x := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have h2 : x < 2 * β * x := by nlinarith
      linarith
  have hpos : ∀ j : ℕ, j ≤ M → 0 ≤ |valY Y c (x / (2 : ℝ) ^ j)| := fun j _ => abs_nonneg _
  have hM0 : |valY Y c (x / (2 : ℝ) ^ M)| = |y₀| := by
    rw [← hβM, (eq_valY hfun hy₀).symm]
  have h00 : |valY Y c (x / (2 : ℝ) ^ 0)| = |y| := by
    rw [pow_zero, div_one, (eq_valY hfun hy).symm]
  have hrel : ∀ j, j < M → |valY Y c (x / (2 : ℝ) ^ j)|
      = ratioY Y c (x / (2 : ℝ) ^ (j + 1)) * |valY Y c (x / (2 : ℝ) ^ (j + 1))| := by
    intro j hj
    have h1 : x / (2 : ℝ) ^ (j + 1) ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := hmem (j + 1) hj
    have h2 : x / (2 : ℝ) ^ j ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := hmem j (le_of_lt hj)
    have h2eq : x / (2 : ℝ) ^ j = 2 * (x / (2 : ℝ) ^ (j + 1)) := by
      rw [pow_succ]
      field_simp
    have hne : valY Y c (x / (2 : ℝ) ^ (j + 1)) ≠ 0 := deep_val_ne hst hβ1 hx hdeep h1
    have hrat : 0 < ratioY Y c (x / (2 : ℝ) ^ (j + 1)) :=
      deep_ratio_pos hst hβ1 hx hdeep h1 (by rw [← h2eq]; exact h2)
    rw [h2eq]
    calc |valY Y c (2 * (x / (2 : ℝ) ^ (j + 1)))|
        = |valY Y c (2 * (x / (2 : ℝ) ^ (j + 1)))| /
            |valY Y c (x / (2 : ℝ) ^ (j + 1))| * |valY Y c (x / (2 : ℝ) ^ (j + 1))| :=
          (div_mul_cancel₀ _ (abs_ne_zero.mpr hne)).symm
      _ = |valY Y c (2 * (x / (2 : ℝ) ^ (j + 1))) / valY Y c (x / (2 : ℝ) ^ (j + 1))| *
            |valY Y c (x / (2 : ℝ) ^ (j + 1))| := by rw [abs_div]
      _ = |ratioY Y c (x / (2 : ℝ) ^ (j + 1))| * |valY Y c (x / (2 : ℝ) ^ (j + 1))| := rfl
      _ = ratioY Y c (x / (2 : ℝ) ^ (j + 1)) * |valY Y c (x / (2 : ℝ) ^ (j + 1))| := by
          rw [abs_of_pos hrat]
  have hrr : ∀ j, j < M → β ≤ ratioY Y c (x / (2 : ℝ) ^ (j + 1)) := by
    intro j hj
    have h1 : x / (2 * β) < x / (2 : ℝ) ^ (j + 1) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have h2 : (2 : ℝ) ^ (j + 1) ≤ β := by
        rw [hβM]
        exact pow_le_pow_right₀ (by norm_num) hj
      nlinarith [h2, hβpos, hx]
    have h2 : x / (2 : ℝ) ^ (j + 1) < x := by
      rw [div_lt_iff₀ (by positivity)]
      have h3 : (1 : ℝ) < (2 : ℝ) ^ (j + 1) :=
        one_lt_pow₀ (show (1 : ℝ) < 2 by norm_num) (Nat.succ_ne_zero j)
      nlinarith
    have hmon := hmono _ h1 h2
    rw [hratx] at hmon
    linarith
  have hmain := pow_mul_le_of_chain_bwd (β := β) (M := M) (le_of_lt hβpos)
    (h := fun j => |valY Y c (x / (2 : ℝ) ^ j)|)
    (r := fun j => ratioY Y c (x / (2 : ℝ) ^ (j + 1))) hpos hrel hrr
  rw [hM0, h00] at hmain
  have hxβI : x / β ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    constructor
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [div_lt_iff₀ (by positivity)]
      have hβsq : (1 : ℝ) < β * β := by nlinarith [hβ1lt]
      have h1 : x < β * β * x := by
        have := mul_lt_mul_of_pos_right hβsq hx
        simpa using this
      nlinarith [h1]
  have hxI : x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    constructor
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
    · nlinarith
  have hyy₀ : 0 < y * y₀ := deep_sign hst.1 hβ1 hx hdeep hxI hxβI hy hy₀
  have hy₀ne : y₀ ≠ 0 := by rintro rfl; linarith
  rw [le_div_iff₀ (abs_pos.mpr hy₀ne)]
  exact hmain

/-! ## 5. The lower bound for the elements of `DeepRatSet` -/

/-- Every element of `DeepRatSet Y B₀ β` at a *dyadic* scale `β = 2^M` with `M ≥ 1` is at least
`β^M`.  Each element comes from a bad point; the doubling ratio is monotone on one side of it
(`oneSided_ratio_deep`), so either the forward or the backward telescoping applies. -/
theorem deepRatSet_lower {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ t ∈ DeepRatSet Y B₀ ((2 : ℝ) ^ M), ((2 : ℝ) ^ M) ^ M ≤ t := by
  intro t ht
  obtain ⟨c, x, w, y, y₂, v, y₀, A, B, hx, hdeep, hy, hy0, hy₂, hwy, hwabs, hv, hy₀, hA, hB,
    htmax⟩ := ht
  have hβ2 : (2 : ℝ) ≤ (2 : ℝ) ^ M := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hM
    simpa using h
  have hβ1 : (1 : ℝ) ≤ (2 : ℝ) ^ M := by linarith
  have hβ1lt : (1 : ℝ) < (2 : ℝ) ^ M := by linarith
  have hβpos : (0 : ℝ) < (2 : ℝ) ^ M := by linarith
  -- the relevant points all lie in the deep window
  have hxI : x ∈ Set.Ioo (x / (2 * (2 : ℝ) ^ M)) (2 * (2 : ℝ) ^ M * x) := by
    constructor
    · rw [div_lt_iff₀ (by positivity)]; nlinarith [hx, hβ1lt]
    · nlinarith [hx, hβ1lt]
  have h2xI : 2 * x ∈ Set.Ioo (x / (2 * (2 : ℝ) ^ M)) (2 * (2 : ℝ) ^ M * x) := by
    constructor
    · rw [div_lt_iff₀ (by positivity)]; nlinarith [hx, hβ1lt]
    · nlinarith [hx, hβ1lt]
  have hβxI : (2 : ℝ) ^ M * x ∈ Set.Ioo (x / (2 * (2 : ℝ) ^ M)) (2 * (2 : ℝ) ^ M * x) := by
    constructor
    · rw [div_lt_iff₀ (by positivity)]
      have hsq : (1 : ℝ) < (2 : ℝ) ^ M * (2 : ℝ) ^ M := by nlinarith [hβ1lt]
      nlinarith [hsq, hx]
    · nlinarith [hx, hβpos]
  have hxβI : x / (2 : ℝ) ^ M ∈ Set.Ioo (x / (2 * (2 : ℝ) ^ M)) (2 * (2 : ℝ) ^ M * x) := by
    constructor
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [hx]
    · rw [div_lt_iff₀ (by positivity)]
      have hsq : (1 : ℝ) < (2 : ℝ) ^ M * (2 : ℝ) ^ M := by nlinarith [hβ1lt]
      nlinarith [hsq, hx]
  -- signs
  have hsgn2 : 0 < y * y₂ := deep_sign hst.1 hβ1 hx hdeep hxI h2xI hy hy₂
  have hwpos : 0 < w := by
    have hw' : w = y₂ / y := ((div_eq_iff hy0).mpr hwy.symm).symm
    rw [hw']
    rcases mul_pos_iff.mp hsgn2 with h | h
    · exact div_pos h.2 h.1
    · exact div_pos_of_neg_of_neg h.2 h.1
  have hwge : (2 : ℝ) ^ M ≤ w := by
    rcases hwabs with h | h
    · exact h
    · exfalso; linarith
  have hratx : ratioY Y c x = w := by
    rw [ratioY, (eq_valY hfun hy).symm, (eq_valY hfun hy₂).symm, div_eq_iff hy0]
    exact hwy.symm
  have hvy : 0 < v * y := deep_sign hst.1 hβ1 hx hdeep hβxI hxI hv hy
  have hyy₀ : 0 < y * y₀ := deep_sign hst.1 hβ1 hx hdeep hxI hxβI hy hy₀
  have hgoal : ((2 : ℝ) ^ M) ^ M ≤ max A B := by
    rcases oneSided_ratio_deep Y B₀ hfun hst c ((2 : ℝ) ^ M) x hβ1lt hx hdeep with hmono | hmono
    · have hf := deep_forward_le hst hfun (β := (2 : ℝ) ^ M) (M := M) rfl hM hx hdeep
        hy hy0 hy₂ hwy hv hwge hmono
      rw [abs_div_eq_div_of_mul_pos hvy] at hf
      have hAeq : A = v / y := ((isDivR_iff v y A).mp hA).symm
      rw [hAeq]
      exact le_trans hf (le_max_left _ _)
    · have hb := deep_backward_le hst hfun (β := (2 : ℝ) ^ M) (M := M) rfl hM hx hdeep
        hy hy0 hy₂ hwy hy₀ hwge hmono
      rw [abs_div_eq_div_of_mul_pos hyy₀] at hb
      have hBeq : B = y / y₀ := ((isDivR_iff y y₀ B).mp hB).symm
      rw [hBeq]
      exact le_trans hb (le_max_right _ _)
  rw [htmax]
  exact hgoal

/-! ## 6. The glb of `DeepRatSet` at a bad scale -/

/-- At a dyadic scale `β = 2^M` at which a bad point exists, the glb of `DeepRatSet` exists, is
the value of the definable function `DeepThetaG`, and is at least `β^M`. -/
theorem deepThetaG_glb_lower {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {M : ℕ} (hM : 1 ≤ M)
    (hbad : ∃ (c : Fin k → ℝ) (x w : ℝ), 0 < x ∧ IsDeepR B₀ c ((2 : ℝ) ^ M) x ∧
      RatW Y c x w ∧ (2 : ℝ) ^ M ≤ |w|) :
    ∃ y : ℝ, ![((2 : ℝ) ^ M), y] ∈ DeepThetaG Y B₀ ∧ ((2 : ℝ) ^ M) ^ M ≤ y := by
  obtain ⟨c, x, w, hx, hdeep, hrat, hbw⟩ := hbad
  obtain ⟨y, y₂, hy, hy₂, hy0, hwy⟩ := hrat
  have hβ1 : (1 : ℝ) ≤ (2 : ℝ) ^ M := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (Nat.zero_le M)
    simpa using h
  have hβ1lt : (1 : ℝ) < (2 : ℝ) ^ M := by
    have hβ2 : (2 : ℝ) ≤ (2 : ℝ) ^ M := by
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hM
      simpa using h
    linarith
  have hβxI : (2 : ℝ) ^ M * x ∈ Set.Ioo (x / (2 * (2 : ℝ) ^ M)) (2 * (2 : ℝ) ^ M * x) := by
    constructor
    · rw [div_lt_iff₀ (by positivity)]
      have hsq : (1 : ℝ) < (2 : ℝ) ^ M * (2 : ℝ) ^ M := by nlinarith [hβ1lt]
      nlinarith [hsq, hx]
    · nlinarith [hx, hβ1lt]
  have hxβI : x / (2 : ℝ) ^ M ∈ Set.Ioo (x / (2 * (2 : ℝ) ^ M)) (2 * (2 : ℝ) ^ M * x) := by
    constructor
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [hx]
    · rw [div_lt_iff₀ (by positivity)]
      have hsq : (1 : ℝ) < (2 : ℝ) ^ M * (2 : ℝ) ^ M := by nlinarith [hβ1lt]
      nlinarith [hsq, hx]
  obtain ⟨hu, -, -⟩ := deep_nice hst.1 hβ1 hx hdeep
  have hv : Gr Y c ((2 : ℝ) ^ M * x) (valY Y c ((2 : ℝ) ^ M * x)) :=
    valY_mem Y c _ (hu _ hβxI).exists
  have hy₀ : Gr Y c (x / (2 : ℝ) ^ M) (valY Y c (x / (2 : ℝ) ^ M)) :=
    valY_mem Y c _ (hu _ hxβI).exists
  have hwabs : (2 : ℝ) ^ M ≤ w ∨ w ≤ -(2 : ℝ) ^ M := by
    rcases le_abs.mp hbw with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hA : IsDivR (valY Y c ((2 : ℝ) ^ M * x)) y (valY Y c ((2 : ℝ) ^ M * x) / y) :=
    (isDivR_iff _ _ _).mpr rfl
  have hB : IsDivR y (valY Y c (x / (2 : ℝ) ^ M)) (y / valY Y c (x / (2 : ℝ) ^ M)) :=
    (isDivR_iff _ _ _).mpr rfl
  have hne : (DeepRatSet Y B₀ ((2 : ℝ) ^ M)).Nonempty :=
    ⟨max _ _, c, x, w, y, y₂, valY Y c ((2 : ℝ) ^ M * x), valY Y c (x / (2 : ℝ) ^ M),
      _, _, hx, hdeep, hy, hy0, hy₂, hwy, hwabs, hv, hy₀, hA, hB, rfl⟩
  have hbdd : BddBelow (DeepRatSet Y B₀ ((2 : ℝ) ^ M)) :=
    ⟨_, fun t ht => deepRatSet_lower hst hfun hM t ht⟩
  obtain ⟨y', hy'⟩ := Real.exists_isGLB hne hbdd
  refine ⟨y', ?_, ?_⟩
  · rw [mem_deepThetaG_vec]
    exact ⟨hβ1, hy'⟩
  · exact hy'.2 (fun t ht => deepRatSet_lower hst hfun hM t ht)

/-! ## 7. Badness at every scale -/

/-- If for every `Γ` there is a bad point at some scale `β ≥ Γ`, then there is a bad point at
*every* scale `B ≥ 1`: a bad point at scale `β` is also bad at every smaller scale. -/
theorem bad_at_all_scales {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfail : ∀ Γ : ℝ, ∃ β : ℝ, Γ ≤ β ∧ ∃ (c : Fin k → ℝ) (x w : ℝ),
      0 < x ∧ IsDeepR B₀ c β x ∧ RatW Y c x w ∧ β ≤ |w|)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ (c : Fin k → ℝ) (x w : ℝ), 0 < x ∧ IsDeepR B₀ c B x ∧ RatW Y c x w ∧ B ≤ |w| := by
  obtain ⟨β, hβ, c, x, w, hx, hdeep, hrat, hbw⟩ := hfail B
  exact ⟨c, x, w, hx, hdeep.mono (by linarith) hβ hx, hrat, le_trans hβ hbw⟩

theorem deep_ratio_scale_bdd {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hst : Work.WilC4.ULPMStruct Y B₀) :
    ∃ Γ : ℝ, 1 ≤ Γ ∧ ∀ (β : ℝ), Γ ≤ β → ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      Work.WilC4.IsDeepR B₀ c β x → Work.WilC4.RatW Y c x w → |w| < β := by
  by_contra hcon
  -- failure of the statement gives bad points at every scale
  have hfail : ∀ Γ : ℝ, ∃ β : ℝ, Γ ≤ β ∧ ∃ (c : Fin k → ℝ) (x w : ℝ),
      0 < x ∧ IsDeepR B₀ c β x ∧ RatW Y c x w ∧ β ≤ |w| := by
    intro Γ
    by_contra h
    push_neg at h
    exact hcon ⟨max 1 Γ, le_max_left 1 Γ, fun β hβ =>
      h β (le_trans (le_max_right 1 Γ) hβ)⟩
  -- the polynomial bound for the definable glb function
  obtain ⟨n, R, hbound⟩ := pb_poly_bound hR hPB (deepThetaG_definable_b hY hB₀)
    (deepThetaG_functional Y B₀)
  -- a dyadic scale past both `R` and the polynomial exponent
  obtain ⟨M₁, hM₁⟩ := pow_unbounded_of_one_lt (max R 1) (show (1 : ℝ) < 2 by norm_num)
  let M : ℕ := max M₁ (n + 1)
  have hM1 : 1 ≤ M := by
    have : n + 1 ≤ M := le_max_right _ _
    omega
  have hMn : n + 1 ≤ M := le_max_right _ _
  have hRle : R ≤ (2 : ℝ) ^ M := by
    have h1 : max R 1 ≤ (2 : ℝ) ^ M₁ := le_of_lt hM₁
    have h2 : (2 : ℝ) ^ M₁ ≤ (2 : ℝ) ^ M :=
      pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (le_max_left _ _)
    linarith [le_max_left R 1, h1, h2]
  -- a bad point at the dyadic scale, and the glb it produces
  obtain ⟨c, x, w, hx, hdeep, hrat, hbw⟩ :=
    bad_at_all_scales hfail (B := (2 : ℝ) ^ M)
      (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) : (1 : ℝ) ≤ (2 : ℝ) ^ M)
  obtain ⟨y, hy, hyle⟩ := deepThetaG_glb_lower hst hfun hM1 ⟨c, x, w, hx, hdeep, hrat, hbw⟩
  have hyn : |y| ≤ ((2 : ℝ) ^ M) ^ n := hbound ((2 : ℝ) ^ M) y hRle hy
  -- the glb is at least `β^M`, which dominates the polynomial bound
  have hβ1 : (1 : ℝ) < (2 : ℝ) ^ M := by
    have h := pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num) hM1
    simpa using h
  have hlt : ((2 : ℝ) ^ M) ^ n < ((2 : ℝ) ^ M) ^ (n + 1) := by
    have h := pow_lt_pow_right₀ hβ1 (Nat.lt_succ_self n)
    simpa using h
  have hle : ((2 : ℝ) ^ M) ^ (n + 1) ≤ ((2 : ℝ) ^ M) ^ M :=
    pow_le_pow_right₀ (le_of_lt hβ1) hMn
  have hgt : ((2 : ℝ) ^ M) ^ n < y := lt_of_lt_of_le hlt (le_trans hle hyle)
  linarith [le_abs_self y]

end Work.WilC4
