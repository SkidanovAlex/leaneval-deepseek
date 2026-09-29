import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Trig.coprime_of_sep
import Submission.Work.TMC16Core.Trig.grid_sep
import Submission.Work.TMC16Core.Trig.rat_prod_erase_le
import Submission.Work.TMC16Core.Trig.rat_prod_min_removed_v2
import Submission.Work.TMC16Core.Trig.grid_nn_sum

/-!
# The shifted block product with the minimal factor removed (AJ §9, `shift1`)

This proves `Work.TMC16Core.Trig.shift_block`: the block product with the minimal `|sin|`-factor
removed, for *shifted* sites `k + c k`, is `2^{-(q-1)}` up to a factor `q^{32}`, uniformly in `x`.

The argument is the shifted form of the (proved) unshifted estimate `Trig/irrat_block`: after
replacing `k α` by `(k + c k) α` the shifted block is compared term by term with the rational
block `k ↦ k p/q`; the rational block bounds (`rat_prod_erase_le`, `rat_prod_min_removed_v2`),
the grid separation (`grid_sep`) and the grid reciprocal sum (`grid_nn_sum`) are used unchanged.
The only genuinely new ingredient is that coprimality of `p` and `q` now has to be extracted from
the *shifted* approximation and separation hypotheses.
-/

namespace Work.TMC16Core.Trig

open Finset

/-! ### Elementary estimates for `nn` (distance to ℤ) and `S w = |sin (π w)|` -/

/-- `nn (a - b) ≤ nn a + nn b`. -/
private lemma nn_sub_le' (a b : ℝ) : Basic.nn (a - b) ≤ Basic.nn a + Basic.nn b := by
  have h := round_le (a - b) (round a - round b)
  have h2 : |(a - b) - ↑(round a - round b)| = |(a - ↑(round a)) - (b - ↑(round b))| := by
    push_cast
    ring_nf
  have h3 : |(a - ↑(round a)) - (b - ↑(round b))| ≤
      |a - ↑(round a)| + |b - ↑(round b)| := by
    have h4 := abs_add_le (a - ↑(round a)) (-(b - ↑(round b)))
    rw [abs_neg] at h4
    calc |(a - ↑(round a)) - (b - ↑(round b))|
        = |(a - ↑(round a)) + -(b - ↑(round b))| := by rw [sub_eq_add_neg]
      _ ≤ |a - ↑(round a)| + |b - ↑(round b)| := h4
  calc Basic.nn (a - b) = |(a - b) - ↑(round (a - b))| := rfl
    _ ≤ |(a - b) - ↑(round a - round b)| := h
    _ = |(a - ↑(round a)) - (b - ↑(round b))| := h2
    _ ≤ |a - ↑(round a)| + |b - ↑(round b)| := h3
    _ = Basic.nn a + Basic.nn b := rfl

/-- `2 * nn w ≤ S w`. -/
private lemma two_mul_nn_le_S (t : ℝ) : 2 * Basic.nn t ≤ Basic.S t := by
  have h := Basic.two_div_pi_mul_le_S t
  have hpi : (2 : ℝ) / Real.pi * (Real.pi * Basic.nn t) = 2 * Basic.nn t := by
    field_simp
  rwa [hpi] at h

/-- `S` is `π`-Lipschitz. -/
private lemma abs_S_sub_S_le (a b : ℝ) : |Basic.S a - Basic.S b| ≤ Real.pi * |a - b| := by
  have h1 : |Basic.S a - Basic.S b| ≤ |Real.sin (Real.pi * a) - Real.sin (Real.pi * b)| := by
    rw [Basic.S, Basic.S]
    exact abs_abs_sub_abs_le_abs_sub _ _
  have h2 : |Real.sin (Real.pi * a) - Real.sin (Real.pi * b)| ≤ |Real.pi * a - Real.pi * b| :=
    Real.abs_sin_sub_sin_le _ _
  have h3 : |Real.pi * a - Real.pi * b| = Real.pi * |a - b| := by
    rw [show Real.pi * a - Real.pi * b = Real.pi * (a - b) by ring, abs_mul,
      abs_of_pos Real.pi_pos]
  linarith

/-- `S a ≤ S b` is the same as `nn a ≤ nn b`. -/
private lemma S_le_iff_nn_le (a b : ℝ) : Basic.S a ≤ Basic.S b ↔ Basic.nn a ≤ Basic.nn b := by
  rw [Basic.S_eq_sin_nn, Basic.S_eq_sin_nn]
  have ha : Real.pi * Basic.nn a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    constructor <;> nlinarith [Real.pi_pos, Basic.nn_nonneg a, Basic.nn_le_half a]
  have hb : Real.pi * Basic.nn b ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    constructor <;> nlinarith [Real.pi_pos, Basic.nn_nonneg b, Basic.nn_le_half b]
  rw [Real.strictMonoOn_sin.le_iff_le ha hb]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- The `k`-th factor of the *shifted* block, as `S` of the doubled argument. -/
private lemma block_term_shift (α : ℝ) (c : ℕ → ℤ) (x : ℝ) (k : ℕ) :
    |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| =
      Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
  rw [Basic.S]
  congr 1
  ring

/-- The `k`-th factor of the *rational* block, as `S` of the doubled argument. -/
private lemma block_term_rat (p : ℤ) (q : ℕ) (x : ℝ) (k : ℕ) :
    |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| =
      Basic.S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
  rw [Basic.S]
  congr 1
  ring_nf

/-- `fracDist` is the distance to the nearest integer `nn`. -/
private lemma fracDist_eq_nn' (t : ℝ) : Work.TMC16Core.fracDist t = Basic.nn t := rfl

/-! ### A self-contained logarithm-of-ratio estimate -/

/-- `|log (1 + u)| ≤ 2 |u|` for `|u| ≤ 1/2`. -/
private lemma abs_log_one_add_le (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u)| ≤ 2 * |u| := by
  have hu' := abs_le.mp hu
  by_cases h : 0 ≤ u
  · have h1 : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith [hu'.1])
      linarith
    have h2 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg h2, abs_of_nonneg h]
    linarith
  · push_neg at h
    have hw : (0 : ℝ) < 1 + u := by linarith [hu'.1]
    have h1 : Real.log (1 + u) = -Real.log (1 / (1 + u)) := by
      rw [one_div, Real.log_inv, neg_neg]
    have h2 : Real.log (1 / (1 + u)) ≤ 1 / (1 + u) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : 1 / (1 + u) - 1 = -u / (1 + u) := by field_simp; ring
    have h4 : -u / (1 + u) ≤ -2 * u := by
      rw [div_le_iff₀ hw]; nlinarith [hu'.1]
    have h5 : 2 * u ≤ Real.log (1 + u) := by linarith
    rw [abs_of_neg (Real.log_neg hw (by linarith)), abs_of_neg h]
    linarith

/-- Sum of logarithmic ratios: if `B` is positive on `s` with `1/B ≤ q` there and
`|A - B| ≤ c` with `q c ≤ 1/2`, then `|∑ (log A - log B)| ≤ 2 c ∑ 1/B`. -/
private lemma log_ratio_sum_bound {s : Finset ℕ} {A B : ℕ → ℝ} {c S : ℝ} {q : ℕ}
    (hc : 0 ≤ c) (hq : 0 < q) (hB : ∀ k ∈ s, 0 < B k)
    (hBq : ∀ k ∈ s, 1 / (q : ℝ) ≤ B k) (hAB : ∀ k ∈ s, |A k - B k| ≤ c)
    (hcq : (q : ℝ) * c ≤ 1 / 2) (hS : ∑ k ∈ s, (B k)⁻¹ ≤ S) :
    |∑ k ∈ s, (Real.log (A k) - Real.log (B k))| ≤ 2 * c * S := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have key : ∀ k ∈ s, |Real.log (A k) - Real.log (B k)| ≤ 2 * c * (B k)⁻¹ := by
    intro k hk
    have hBk : 0 < B k := hB k hk
    have hAb : |A k - B k| ≤ c := hAB k hk
    have hc' : c ≤ 1 / (2 * (q : ℝ)) := by
      refine (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))).mpr ?_
      nlinarith [hcq]
    have hqB : (1 : ℝ) / (2 * (q : ℝ)) ≤ (1 / 2) * B k := by
      have h4 : (1 : ℝ) / (2 * (q : ℝ)) = (1 / 2) * (1 / (q : ℝ)) := by
        rw [one_div_mul_one_div]
      rw [h4]
      exact mul_le_mul_of_nonneg_left (hBq k hk) (by norm_num)
    have hcB : c ≤ (1 / 2) * B k := le_trans hc' hqB
    have hApos : 0 < A k := by
      have := (abs_le.mp hAb).1
      linarith
    have hu : |(A k - B k) / B k| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hBk, div_le_iff₀ hBk]
      linarith
    calc |Real.log (A k) - Real.log (B k)|
        = |Real.log (1 + (A k - B k) / B k)| := by
          have h := Real.log_div (ne_of_gt hApos) (ne_of_gt hBk)
          have h2 : A k / B k = 1 + (A k - B k) / B k := by field_simp; ring
          rw [← h, h2]
      _ ≤ 2 * |(A k - B k) / B k| := abs_log_one_add_le _ hu
      _ = 2 * (|A k - B k| / B k) := by rw [abs_div, abs_of_pos hBk]
      _ ≤ 2 * (c / B k) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact div_le_div_of_nonneg_right hAb (le_of_lt hBk)
      _ = 2 * c * (B k)⁻¹ := by rw [div_eq_mul_inv]; ring
  have h1 : |∑ k ∈ s, (Real.log (A k) - Real.log (B k))| ≤ ∑ k ∈ s, 2 * c * (B k)⁻¹ := by
    refine le_trans (Finset.abs_sum_le_sum_abs (s := s)
      (f := fun k => Real.log (A k) - Real.log (B k))) ?_
    exact Finset.sum_le_sum (fun k hk => key k hk)
  have h2 : ∑ k ∈ s, 2 * c * (B k)⁻¹ ≤ 2 * c * S := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS (by linarith)
  linarith

/-! ### Numeric and logarithmic helpers for the final assembly -/

private lemma aux_log_ge (q : ℕ) (hq : 1 ≤ q) : 0 ≤ Real.log q :=
  Real.log_nonneg (by exact_mod_cast hq)

private lemma aux_log_pos (q : ℕ) (hq : 2 ≤ q) : (1 : ℝ) / 2 ≤ Real.log q := by
  have h : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq : (2 : ℝ) ≤ q)
  linarith [Real.log_two_gt_d9]

private lemma aux_log2le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]

private lemma aux_log2pi : -(1 : ℝ) ≤ Real.log (2 / Real.pi) := by
  have h1 : Real.log (2 / Real.pi) = -Real.log (Real.pi / 2) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  have h2 : Real.log (Real.pi / 2) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Real.pi / 2)
    linarith [Real.pi_le_four]
  linarith

private lemma aux_log4 : Real.log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  push_cast
  linarith [aux_log2le]

private lemma num_lower (L : ℝ) (hL : (1 : ℝ) / 2 ≤ L) :
    -32 * L ≤ -(Real.pi * (1 + L)) - 1 := by
  have h1 : Real.pi * (1 + L) ≤ 4 * (1 + L) := by
    apply mul_le_mul_of_nonneg_right Real.pi_le_four
    linarith
  have h2 : (5 : ℝ) + 4 * L ≤ 32 * L := by linarith
  calc -32 * L ≤ -(5 + 4 * L) := by linarith [h2]
    _ = -4 * (1 + L) - 1 := by ring
    _ ≤ -(Real.pi * (1 + L)) - 1 := by linarith [h1]

private lemma num_lower2 (L : ℝ) (hL : (1 : ℝ) / 2 ≤ L) :
    -32 * L ≤ -(Real.pi * (1 + L)) - 2 := by
  have h1 : Real.pi * (1 + L) ≤ 4 * (1 + L) := by
    apply mul_le_mul_of_nonneg_right Real.pi_le_four
    linarith
  have h2 : (6 : ℝ) + 4 * L ≤ 32 * L := by linarith
  calc -32 * L ≤ -(6 + 4 * L) := by linarith [h2]
    _ = -4 * (1 + L) - 2 := by ring
    _ ≤ -(Real.pi * (1 + L)) - 2 := by linarith [h1]

private lemma num_upper1 (L : ℝ) (hL : (1 : ℝ) / 2 ≤ L) :
    Real.pi * (1 + L) + 2 + 2 * L ≤ 32 * L := by
  have h1 : Real.pi * (1 + L) ≤ 4 * (1 + L) := by
    apply mul_le_mul_of_nonneg_right Real.pi_le_four
    linarith
  have h2 : (6 : ℝ) + 6 * L ≤ 32 * L := by linarith
  calc Real.pi * (1 + L) + 2 + 2 * L ≤ 4 * (1 + L) + 2 + 2 * L := by linarith [h1]
    _ = 6 + 6 * L := by ring
    _ ≤ 32 * L := h2

private lemma num_upper2 (L : ℝ) (hL : (1 : ℝ) / 2 ≤ L) :
    Real.pi * (1 + L) + 2 + 3 * L ≤ 32 * L := by
  have h1 : Real.pi * (1 + L) ≤ 4 * (1 + L) := by
    apply mul_le_mul_of_nonneg_right Real.pi_le_four
    linarith
  have h2 : (6 : ℝ) + 7 * L ≤ 32 * L := by linarith
  calc Real.pi * (1 + L) + 2 + 3 * L ≤ 4 * (1 + L) + 2 + 3 * L := by linarith [h1]
    _ = 6 + 7 * L := by ring
    _ ≤ 32 * L := h2

private lemma assemble_A_lo (q : ℕ) (hq : 2 ≤ q) {R LB : ℝ}
    (hR : -(Real.pi * (1 + Real.log q)) ≤ R)
    (hLB : Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2 ≤ LB) :
    -(32 * Real.log q) ≤ R + LB + ((q : ℝ) - 1) * Real.log 2 := by
  have h5 := num_lower (Real.log q) (aux_log_pos q hq)
  have h6 : -(Real.pi * (1 + Real.log q)) - 1 ≤ -(Real.pi * (1 + Real.log q))
      + (Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2)
      + ((q : ℝ) - 1) * Real.log 2 := by
    linarith [aux_log2pi, aux_log_ge q (by omega : 1 ≤ q)]
  calc -(32 * Real.log q) = -32 * Real.log q := by ring
    _ ≤ -(Real.pi * (1 + Real.log q)) - 1 := h5
    _ ≤ -(Real.pi * (1 + Real.log q))
        + (Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2)
        + ((q : ℝ) - 1) * Real.log 2 := h6
    _ ≤ R + LB + ((q : ℝ) - 1) * Real.log 2 := by linarith [hR, hLB]

private lemma assemble_A_hi (q : ℕ) (hq : 2 ≤ q) {R LB : ℝ}
    (hR : R ≤ Real.pi * (1 + Real.log q))
    (hUB : LB ≤ Real.log 4 + 2 * Real.log q - ((q : ℝ) - 1) * Real.log 2) :
    R + LB + ((q : ℝ) - 1) * Real.log 2 ≤ 32 * Real.log q := by
  have h6 : Real.pi * (1 + Real.log q)
      + (Real.log 4 + 2 * Real.log q - ((q : ℝ) - 1) * Real.log 2)
      + ((q : ℝ) - 1) * Real.log 2 ≤ 32 * Real.log q := by
    have h := num_upper1 (Real.log q) (aux_log_pos q hq)
    linarith [h, aux_log4]
  linarith [hR, hUB, h6]

private lemma assemble_B_lo (q : ℕ) (hq : 2 ≤ q) {R LB AB Ak : ℝ}
    (hR : -(Real.pi * (1 + Real.log q)) ≤ R)
    (hLB : Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2 ≤ LB)
    (hAB : 0 ≤ -AB) (hAk : -(Real.log 2 + Real.log q) ≤ Ak) :
    -(32 * Real.log q) ≤ R + (LB - AB) + Ak + ((q : ℝ) - 1) * Real.log 2 := by
  have h5 := num_lower2 (Real.log q) (aux_log_pos q hq)
  have h6 : -(Real.pi * (1 + Real.log q)) - 2 ≤ -(Real.pi * (1 + Real.log q))
      + (Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2)
      - AB + Ak + ((q : ℝ) - 1) * Real.log 2 := by
    linarith [aux_log2pi, aux_log_ge q (by omega : 1 ≤ q), hAB, hAk, aux_log2le]
  calc -(32 * Real.log q) = -32 * Real.log q := by ring
    _ ≤ -(Real.pi * (1 + Real.log q)) - 2 := h5
    _ ≤ -(Real.pi * (1 + Real.log q))
        + (Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2)
        - AB + Ak + ((q : ℝ) - 1) * Real.log 2 := h6
    _ ≤ R + (LB - AB) + Ak + ((q : ℝ) - 1) * Real.log 2 := by linarith [hR, hLB]

private lemma assemble_B_hi (q : ℕ) (hq : 2 ≤ q) {R LB AB Ak : ℝ}
    (hR : R ≤ Real.pi * (1 + Real.log q))
    (hUB : LB ≤ Real.log 4 + 2 * Real.log q - ((q : ℝ) - 1) * Real.log 2)
    (hAB : -AB ≤ Real.log q) (hAk : Ak ≤ 0) :
    R + (LB - AB) + Ak + ((q : ℝ) - 1) * Real.log 2 ≤ 32 * Real.log q := by
  have h6 : Real.pi * (1 + Real.log q)
      + (Real.log 4 + 2 * Real.log q - ((q : ℝ) - 1) * Real.log 2)
      + Real.log q + 0 + ((q : ℝ) - 1) * Real.log 2 ≤ 32 * Real.log q := by
    have h := num_upper2 (Real.log q) (aux_log_pos q hq)
    have h4 := aux_log4
    linarith [h, h4]
  calc R + (LB - AB) + Ak + ((q : ℝ) - 1) * Real.log 2
      ≤ Real.pi * (1 + Real.log q)
        + (Real.log 4 + 2 * Real.log q - ((q : ℝ) - 1) * Real.log 2)
        + Real.log q + 0 + ((q : ℝ) - 1) * Real.log 2 := by linarith [hR, hUB, hAB, hAk]
    _ ≤ 32 * Real.log q := h6

/-! ### Coprimality from the shifted hypotheses -/

/-- **Coprimality of the convergent numerator with the scale, shifted version.**
If for all `k ∈ {1,…,q}` the shifted multiple `(k + c k) α` tracks `k p/q` to within `η`,
if the shifted sites are pairwise separated from `ℤ` by `1/(2q)`, and `q η ≤ 1/8`, then
`p` is coprime to `q`. -/
theorem coprime_of_sep_shift {α : ℝ} {q : ℕ} (hq : 0 < q) {c : ℕ → ℤ} {η : ℝ} (hη : 0 ≤ η)
    {p : ℤ}
    (happ : ∀ k ∈ Finset.Icc 1 q,
        |((k : ℝ) + (c k : ℝ)) * α - (k : ℝ) * ((p : ℝ) / q)| ≤ η)
    (hsep : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q → k ≠ l →
        1 / (2 * (q : ℝ)) ≤ Work.TMC16Core.fracDist
          ((((k : ℤ) + c k - ((l : ℤ) + c l) : ℤ) : ℝ) * α))
    (hsmall : (q : ℝ) * η ≤ 1 / 8) :
    Nat.Coprime p.natAbs q := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with hq1 | hq2
  · rw [← hq1]; exact Nat.coprime_one_right _
  by_contra hcop
  rw [Nat.coprime_iff_gcd_eq_one] at hcop
  set d : ℕ := Nat.gcd p.natAbs q with hddef
  have hdvdq : d ∣ q := by rw [hddef]; exact Nat.gcd_dvd_right _ _
  have hdvdp : d ∣ p.natAbs := by rw [hddef]; exact Nat.gcd_dvd_left _ _
  have hdne1 : d ≠ 1 := by rw [hddef]; exact hcop
  have hd2 : 2 ≤ d := by
    have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvdq hq
    omega
  set q' : ℕ := q / d with hq'def
  have hq'mul : d * q' = q := by rw [hq'def]; exact Nat.mul_div_cancel' hdvdq
  have hq'le : q' + 1 ≤ q := by
    have h1 : 2 * q' ≤ d * q' := Nat.mul_le_mul_right q' hd2
    rw [hq'mul] at h1
    omega
  have hq'pos : 0 < q' := by
    by_contra h
    have h0 : q' = 0 := Nat.eq_zero_of_not_pos h
    rw [h0, Nat.mul_zero] at hq'mul
    omega
  have hdvdZ : (d : ℤ) ∣ p := by
    rw [← Int.dvd_natAbs]; exact_mod_cast hdvdp
  obtain ⟨p', hp'⟩ := hdvdZ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- `q' * (p/q) = p'`
  have hp'q : ((q' : ℝ) * ((p : ℝ) / q)) = (p' : ℝ) := by
    have hqeq : (q : ℝ) = (d : ℝ) * (q' : ℝ) := by rw [← hq'mul]; push_cast; ring
    have hpeq : (p : ℝ) = (d : ℝ) * (p' : ℝ) := by rw [hp']; push_cast; ring
    have hq'ne : (q' : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq'pos)
    have hdne : (d : ℝ) ≠ 0 := by
      have : 0 < d := by omega
      exact_mod_cast (ne_of_gt this)
    rw [hqeq, hpeq]
    field_simp
  -- the two shifted approximation bounds
  have hk_mem : q' + 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr ⟨by omega, hq'le⟩
  have hl_mem : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩
  set Ak : ℝ := ((q' + 1 : ℕ) : ℝ) + (c (q' + 1) : ℝ) with hAkdef
  set Al : ℝ := (((1 : ℕ) : ℝ) + (c 1 : ℝ)) with hAldef
  have hAkh : Ak = ((q' + 1 : ℕ) : ℝ) + (c (q' + 1) : ℝ) := rfl
  have hAlh : Al = (((1 : ℕ) : ℝ) + (c 1 : ℝ)) := rfl
  have hbnd_k : |Ak * α - ((q' + 1 : ℕ) : ℝ) * ((p : ℝ) / q)| ≤ η := happ (q' + 1) hk_mem
  have hbnd_l : |Al * α - (((1 : ℕ) : ℝ)) * ((p : ℝ) / q)| ≤ η := happ 1 hl_mem
  -- the integer `z = ((q'+1) + c (q'+1)) - (1 + c 1)` and the real identity
  have hzid : ((((q' + 1 : ℕ) : ℤ) + c (q' + 1) - (((1 : ℕ) : ℤ) + c 1) : ℤ) : ℝ) * α - (p' : ℝ)
      = (Ak * α - ((q' + 1 : ℕ) : ℝ) * ((p : ℝ) / q))
        - (Al * α - (((1 : ℕ) : ℝ)) * ((p : ℝ) / q)) := by
    rw [hAkh, hAlh]
    rw [show ((((q' + 1 : ℕ) : ℤ) + c (q' + 1) - (((1 : ℕ) : ℤ) + c 1) : ℤ) : ℝ)
          = ((q' : ℝ) + (c (q' + 1) : ℝ) - (c 1 : ℝ)) by push_cast; ring]
    rw [show (((q' + 1 : ℕ) : ℝ) + (c (q' + 1) : ℝ)) * α
            - ((q' + 1 : ℕ) : ℝ) * ((p : ℝ) / q)
            - ((((1 : ℕ) : ℝ) + (c 1 : ℝ)) * α - (((1 : ℕ) : ℝ)) * ((p : ℝ) / q))
          = ((q' : ℝ) + (c (q' + 1) : ℝ) - (c 1 : ℝ)) * α
            - (q' : ℝ) * ((p : ℝ) / q) by push_cast; ring]
    rw [hp'q]
  -- hence `fracDist (z α) ≤ 2 η`
  have hzle : Work.TMC16Core.fracDist
      (((((q' + 1 : ℕ) : ℤ) + c (q' + 1) - (((1 : ℕ) : ℤ) + c 1) : ℤ) : ℝ) * α) ≤ 2 * η := by
    calc Work.TMC16Core.fracDist (((((q' + 1 : ℕ) : ℤ) + c (q' + 1)
            - (((1 : ℕ) : ℤ) + c 1) : ℤ) : ℝ) * α)
        = Basic.nn (((((q' + 1 : ℕ) : ℤ) + c (q' + 1) - (((1 : ℕ) : ℤ) + c 1) : ℤ) : ℝ) * α) :=
          rfl
      _ ≤ |(((((q' + 1 : ℕ) : ℤ) + c (q' + 1) - (((1 : ℕ) : ℤ) + c 1) : ℤ) : ℝ) * α)
            - (p' : ℝ)| := by
          simpa [Basic.nn] using
            (round_le (((((q' + 1 : ℕ) : ℤ) + c (q' + 1)
              - (((1 : ℕ) : ℤ) + c 1) : ℤ) : ℝ) * α) p')
      _ = |(Ak * α - ((q' + 1 : ℕ) : ℝ) * ((p : ℝ) / q))
            - (Al * α - (((1 : ℕ) : ℝ)) * ((p : ℝ) / q))| := by rw [hzid]
      _ ≤ |Ak * α - ((q' + 1 : ℕ) : ℝ) * ((p : ℝ) / q)|
            + |Al * α - (((1 : ℕ) : ℝ)) * ((p : ℝ) / q)| := by
          have htri := abs_add_le (Ak * α - ((q' + 1 : ℕ) : ℝ) * ((p : ℝ) / q))
            (-(Al * α - (((1 : ℕ) : ℝ)) * ((p : ℝ) / q)))
          rw [abs_neg] at htri
          simpa only [sub_eq_add_neg] using htri
      _ ≤ η + η := add_le_add hbnd_k hbnd_l
      _ = 2 * η := by ring
  -- the separation hypothesis at `k = q'+1`, `l = 1`
  have hres := hsep (q' + 1) 1 (by omega) hq'le (by omega) (by omega) (by omega)
  -- `2η ≤ 1/(4q) < 1/(2q) ≤ fracDist`, contradiction
  have hquarter : 2 * η ≤ 1 / (4 * (q : ℝ)) := by
    have h1 : η ≤ 1 / (8 * (q : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (q : ℝ))]
      nlinarith [hsmall]
    calc 2 * η ≤ 2 * (1 / (8 * (q : ℝ))) := by linarith
      _ = 1 / (4 * (q : ℝ)) := by ring
  have hlt : (1 : ℝ) / (4 * (q : ℝ)) < 1 / (2 * (q : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith [hqR])
  have hle : (1 : ℝ) / (2 * (q : ℝ)) ≤ 1 / (4 * (q : ℝ)) :=
    le_trans hres (le_trans hzle hquarter)
  exact absurd hle (not_le.mpr hlt)

/-! ### The shifted block estimate -/

/-- **AJ §9, `shift1`**: the shifted block product with the minimal factor removed is
`2^{-(q-1)}` up to a factor `q^{32}`. -/
theorem shift_block {α : ℝ} {q : ℕ} (hq : 0 < q) {c : ℕ → ℤ} {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∃ p : ℤ, ∀ k ∈ Finset.Icc 1 q,
        |((k : ℝ) + (c k : ℝ)) * α - (k : ℝ) * ((p : ℝ) / q)| ≤ η)
    (hsep : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q → k ≠ l →
        1 / (2 * (q : ℝ)) ≤ Work.TMC16Core.fracDist ((((k : ℤ) + c k - ((l : ℤ) + c l) : ℤ) : ℝ) * α))
    (hsmall : (q : ℝ) * η ≤ 1 / 8)
    (x : ℝ) {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
        |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| ≥
        |Real.sin (2 * Real.pi * (x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α / 2))|) :
    |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀,
        |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))|) + ((q : ℝ) - 1) * Real.log 2|
      ≤ 32 * Real.log q := by
  obtain ⟨p, hp⟩ := happrox
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1' : 1 ≤ q := by omega
  have hlogq_ge : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1')
  rcases eq_or_lt_of_le hq1' with hq1 | hq2
  · -- ## `q = 1`: the product is empty
    have hq1'' : q = 1 := hq1.symm
    subst hq1''
    have hk : k₀ = 1 := by
      have h := hk₀
      simp only [Finset.mem_Icc] at h
      omega
    subst hk
    simp
  -- ## `q ≥ 2`
  have hcop : Nat.Coprime p.natAbs q := coprime_of_sep_shift hq hη hp hsep hsmall
  set B : ℕ → ℝ := fun k =>
    |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| with hBdef
  obtain ⟨k₁, hk₁, hminB⟩ := Finset.exists_min_image (Finset.Icc 1 q) B ⟨k₀, hk₀⟩
  have hAdef : ∀ k : ℕ,
      |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| =
      Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := fun k => block_term_shift α c x k
  have hB_unfold : ∀ k : ℕ, B k =
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| := by
    intro k; rw [hBdef]
  have hB_S : ∀ k : ℕ, B k = Basic.S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
    intro k
    rw [hB_unfold k]
    exact block_term_rat p q x k
  -- ## rewriting the goal in terms of `S`
  rw [Finset.prod_congr rfl (fun k _ => hAdef k)]
  -- ## minimisation hypotheses in `nn` form
  have hminA_nn : ∀ k ∈ Finset.Icc 1 q,
      Basic.nn (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α) ≤
        Basic.nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
    intro k hk
    have h1 : Basic.S (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α) ≤
        Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
      rw [← hAdef k₀, ← hAdef k]
      exact hmin k hk
    exact (S_le_iff_nn_le _ _).mp h1
  have hminB_nn : ∀ k ∈ Finset.Icc 1 q,
      Basic.nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤
        Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
    intro k hk
    have h1 : Basic.S (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤
        Basic.S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
      rw [← hB_S k₁, ← hB_S k]
      exact hminB k hk
    exact (S_le_iff_nn_le _ _).mp h1
  -- ## grid facts for the rational block
  have hgrid := grid_sep hq hcop x hk₁ hminB_nn
  have hgrid_sep : ∀ k ∈ Finset.Icc 1 q, k ≠ k₁ →
      1 / (2 * (q : ℝ)) ≤ Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := hgrid.1
  have hSum_nn := grid_nn_sum hq hcop x hk₁ hminB_nn
  have hSum : ∑ k ∈ (Finset.Icc 1 q).erase k₁, (B k)⁻¹ ≤
      4 * (q : ℝ) * (1 + Real.log q) := by
    refine le_trans ?_ hSum_nn
    apply Finset.sum_le_sum
    intro k hk
    have hkI : k ∈ Finset.Icc 1 q := Finset.mem_of_mem_erase hk
    have hkne : k ≠ k₁ := Finset.ne_of_mem_erase hk
    have h1 : 0 < Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
      have h2 := hgrid_sep k hkI hkne
      have h3 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    have h2 : 0 < B k := by
      rw [hB_S k]
      have h3 := two_mul_nn_le_S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
      linarith
    rw [inv_le_inv₀ h2 h1]
    rw [hB_S k]
    have h3 := two_mul_nn_le_S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
    linarith
  have hB_lb : ∀ k ∈ Finset.Icc 1 q, k ≠ k₁ → 1 / (q : ℝ) ≤ B k := by
    intro k hk hkne
    rw [hB_S k]
    have h2 := hgrid_sep k hk hkne
    have h3 := two_mul_nn_le_S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
    have h4 : 2 * (1 / (2 * (q : ℝ))) = 1 / (q : ℝ) := by
      rw [mul_one_div]
      ring_nf
    linarith [h2, h3, h4.le, h4.ge]
  have hBpos_e1 : ∀ k ∈ (Finset.Icc 1 q).erase k₁, 0 < B k := by
    intro k hk
    have h1 : 1 / (q : ℝ) ≤ B k :=
      hB_lb k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
    have h2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
    linarith
  -- ## the shifted side: separation away from the minimum
  have hsep_w : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ →
      1 / (2 * (q : ℝ)) ≤
        Basic.nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α - (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α)) := by
    intro k hk hkne
    have h1 := hsep k k₀ (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
      (Finset.mem_Icc.mp hk₀).1 (Finset.mem_Icc.mp hk₀).2 hkne
    have h2 : ((((k : ℤ) + c k - ((k₀ : ℤ) + c k₀) : ℤ) : ℝ) * α) =
        2 * x + ((k : ℝ) + (c k : ℝ)) * α - (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α) := by
      push_cast
      ring
    rw [fracDist_eq_nn', h2] at h1
    exact h1
  have hnn_w : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ →
      1 / (4 * (q : ℝ)) ≤ Basic.nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
    intro k hk hkne
    have h1 := hsep_w k hk hkne
    have h2 := nn_sub_le' (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
      (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α)
    have h3 := hminA_nn k hk
    have h4 : (1 : ℝ) / (4 * (q : ℝ)) = (1 / 2) * (1 / (2 * (q : ℝ))) := by
      rw [one_div_mul_one_div]
      ring_nf
    have h5 : (1 / 2 : ℝ) * (1 / (2 * (q : ℝ))) ≤ (1 / 2 : ℝ) *
        (Basic.nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
          + Basic.nn (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α)) :=
      mul_le_mul_of_nonneg_left (le_trans h1 h2) (by norm_num)
    have h6 : (1 / 2 : ℝ) *
        (Basic.nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
          + Basic.nn (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α))
        ≤ Basic.nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by linarith
    rw [h4]
    linarith [h5, h6]
  have hA_lb : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ →
      1 / (2 * (q : ℝ)) ≤ Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
    intro k hk hkne
    have h1 := hnn_w k hk hkne
    have h2 := two_mul_nn_le_S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
    have h3 : 2 * (1 / (4 * (q : ℝ))) = 1 / (2 * (q : ℝ)) := by
      rw [mul_one_div]
      ring_nf
    linarith [h1, h2, h3.le, h3.ge]
  -- ## comparison of the two blocks
  have hAB : ∀ k ∈ Finset.Icc 1 q,
      |Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) - B k| ≤ Real.pi * η := by
    intro k hk
    rw [hB_S k]
    have h1 := abs_S_sub_S_le (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
      (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
    have h2 : |(2 * x + ((k : ℝ) + (c k : ℝ)) * α)
        - (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))| ≤ η := by
      have h3 : (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
          - (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
          = ((k : ℝ) + (c k : ℝ)) * α - (k : ℝ) * ((p : ℝ) / q) := by ring
      rw [h3]
      exact hp k hk
    have h6 : Real.pi * |(2 * x + ((k : ℝ) + (c k : ℝ)) * α)
        - (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))| ≤ Real.pi * η :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt Real.pi_pos)
    linarith [h1, h6]
  have hcq : (q : ℝ) * (Real.pi * η) ≤ 1 / 2 := by
    have h1 : (q : ℝ) * (Real.pi * η) = Real.pi * ((q : ℝ) * η) := by ring
    rw [h1]
    have hqd : 0 ≤ (q : ℝ) * η := mul_nonneg hqR.le hη
    nlinarith [Real.pi_le_four, Real.pi_pos, hsmall, hqd]
  have hcS : 2 * (Real.pi * η) * (4 * (q : ℝ) * (1 + Real.log q)) ≤
      Real.pi * (1 + Real.log q) := by
    have h2 : 0 ≤ 1 + Real.log q := by linarith
    have heq : 2 * (Real.pi * η) * (4 * (q : ℝ) * (1 + Real.log q))
        = 8 * Real.pi * ((q : ℝ) * η) * (1 + Real.log q) := by ring
    rw [heq]
    calc 8 * Real.pi * ((q : ℝ) * η) * (1 + Real.log q)
        ≤ 8 * Real.pi * (1 / 8) * (1 + Real.log q) := by
          apply mul_le_mul_of_nonneg_right _ h2
          apply mul_le_mul_of_nonneg_left hsmall
          positivity
      _ = Real.pi * (1 + Real.log q) := by ring
  -- ## the rational block with the minimal factor removed
  have hRatLB : (q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1) ≤
      ∏ k ∈ (Finset.Icc 1 q).erase k₁, B k := by
    have h := rat_prod_min_removed_v2 (q := q) (p := p) hq hcop x hk₁
      (fun k hk => by
        have h1 := hminB k hk
        rwa [hB_unfold k, hB_unfold k₁] at h1)
    rwa [Finset.prod_congr rfl (fun k _ => (hB_unfold k).symm)] at h
  have hRatUB : ∏ k ∈ (Finset.Icc 1 q).erase k₁, B k ≤
      4 * (q : ℝ) ^ 2 / 2 ^ (q - 1) := by
    have h := rat_prod_erase_le hq hcop x hk₁ (fun k hk => by
      have h1 := hminB k hk
      rwa [hB_unfold k, hB_unfold k₁] at h1)
    rwa [Finset.prod_congr rfl (fun k _ => (hB_unfold k).symm)] at h
  have hcast1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq1']
    norm_num
  have hId1 : Real.log ((q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1))
      = Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (ne_of_gt hqR) (by positivity), Real.log_pow, hcast1]
  have hId2 : Real.log (4 * (q : ℝ) ^ 2 / 2 ^ (q - 1))
      = Real.log 4 + 2 * Real.log q - ((q : ℝ) - 1) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, hcast1]
    push_cast
    ring
  -- ## case split on whether the two minimisers coincide
  by_cases hkk : k₁ = k₀
  · -- ### Case A: `k₁ = k₀`
    rw [← hkk]
    have hApos : ∀ k ∈ (Finset.Icc 1 q).erase k₁,
        0 < Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
      intro k hk
      have hkI : k ∈ Finset.Icc 1 q := Finset.mem_of_mem_erase hk
      have hkne : k ≠ k₁ := Finset.ne_of_mem_erase hk
      have hkne' : k ≠ k₀ := fun h => hkne (h.trans hkk.symm)
      have h1 := hA_lb k hkI hkne'
      have h2 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    have hlogA : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
        = ∑ k ∈ (Finset.Icc 1 q).erase k₁,
            Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) :=
      Real.log_prod (fun k hk => ne_of_gt (hApos k hk))
    have hlogB : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k)
        = ∑ k ∈ (Finset.Icc 1 q).erase k₁, Real.log (B k) :=
      Real.log_prod (fun k hk => ne_of_gt (hBpos_e1 k hk))
    have hratio := log_ratio_sum_bound (s := (Finset.Icc 1 q).erase k₁)
      (A := fun k => Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) (B := B)
      (c := Real.pi * η) (S := 4 * (q : ℝ) * (1 + Real.log q)) (q := q) (by positivity) hq
      (fun k hk => hBpos_e1 k hk)
      (fun k hk => hB_lb k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
      (fun k hk => hAB k (Finset.mem_of_mem_erase hk)) hcq hSum
    have hT : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
        = (∑ k ∈ (Finset.Icc 1 q).erase k₁,
            (Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) - Real.log (B k)))
          + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k) := by
      rw [hlogA, hlogB, Finset.sum_sub_distrib]
      ring
    have hlogLB : Real.log ((q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1))
        ≤ Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k) :=
      Real.log_le_log (by positivity) hRatLB
    have hlogUB : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k)
        ≤ Real.log (4 * (q : ℝ) ^ 2 / 2 ^ (q - 1)) :=
      Real.log_le_log (Finset.prod_pos (fun k hk => hBpos_e1 k hk)) hRatUB
    rw [hT]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : -(Real.pi * (1 + Real.log q)) ≤
          ∑ k ∈ (Finset.Icc 1 q).erase k₁,
            (Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) - Real.log (B k)) := by
        have h := (abs_le.mp hratio).1
        linarith [hcS]
      rw [hId1] at hlogLB
      exact assemble_A_lo q hq2 h1 hlogLB
    · have h1 : ∑ k ∈ (Finset.Icc 1 q).erase k₁,
            (Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) - Real.log (B k))
          ≤ Real.pi * (1 + Real.log q) := by
        have h := (abs_le.mp hratio).2
        linarith [hcS]
      rw [hId2] at hlogUB
      exact assemble_A_hi q hq2 h1 hlogUB
  · -- ### Case B: `k₁ ≠ k₀`
    have hk₁ne : k₁ ≠ k₀ := hkk
    have hk₀ne : k₀ ≠ k₁ := fun h => hkk h.symm
    have hAk₁ : 1 / (2 * (q : ℝ)) ≤ Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α) :=
      hA_lb k₁ hk₁ hk₁ne
    have hpos2q : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
    have hAk₁pos : 0 < Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α) := by linarith
    have hBk₀pos : 0 < B k₀ := by
      have h1 := hB_lb k₀ hk₀ hk₀ne
      have h2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
      linarith
    have hBk₀le : B k₀ ≤ 1 := by
      rw [hB_unfold k₀]
      exact Real.abs_sin_le_one _
    have hAk₁le : Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α) ≤ 1 := by
      rw [Basic.S]
      exact Real.abs_sin_le_one _
    set s : Finset ℕ := ((Finset.Icc 1 q).erase k₁).erase k₀ with hsdef
    have hs_sub : s ⊆ (Finset.Icc 1 q).erase k₁ := by
      intro k hk
      rw [hsdef] at hk
      exact Finset.mem_of_mem_erase hk
    have herase : ((Finset.Icc 1 q).erase k₀).erase k₁ = s := by
      rw [hsdef]
      ext t
      simp only [Finset.mem_erase]
      tauto
    have hBpos_s : ∀ k ∈ s, 0 < B k := fun k hk => hBpos_e1 k (hs_sub hk)
    have hBq_s : ∀ k ∈ s, 1 / (q : ℝ) ≤ B k := fun k hk =>
      hB_lb k (Finset.mem_of_mem_erase (hs_sub hk)) (Finset.ne_of_mem_erase (hs_sub hk))
    have hApos_s : ∀ k ∈ s, 0 < Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
      intro k hk
      have hkI : k ∈ Finset.Icc 1 q := Finset.mem_of_mem_erase (hs_sub hk)
      have hkne : k ≠ k₀ := Finset.ne_of_mem_erase hk
      have h1 := hA_lb k hkI hkne
      have h2 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    have hSum_s : ∑ k ∈ s, (B k)⁻¹ ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
      refine le_trans ?_ hSum
      apply Finset.sum_le_sum_of_subset_of_nonneg hs_sub
      intro k _ _
      positivity
    have hratio := log_ratio_sum_bound (s := s)
      (A := fun k => Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) (B := B)
      (c := Real.pi * η) (S := 4 * (q : ℝ) * (1 + Real.log q)) (q := q) (by positivity) hq
      hBpos_s hBq_s (fun k hk => hAB k (Finset.mem_of_mem_erase (hs_sub hk))) hcq hSum_s
    have hprodA : ∏ k ∈ (Finset.Icc 1 q).erase k₀,
        Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
        = (∏ k ∈ s, Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
          * Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α) := by
      rw [← herase]
      exact (Finset.prod_erase_mul ((Finset.Icc 1 q).erase k₀)
        (fun k => Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
        (Finset.mem_erase.mpr ⟨hk₁ne, hk₁⟩)).symm
    have hprodB : ∏ k ∈ (Finset.Icc 1 q).erase k₁, B k = (∏ k ∈ s, B k) * B k₀ := by
      have h := Finset.prod_erase_mul ((Finset.Icc 1 q).erase k₁) (fun k => B k)
        (Finset.mem_erase.mpr ⟨hk₀ne, hk₀⟩)
      rw [hsdef]
      exact h.symm
    have hlogA : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀,
        Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
        = Real.log (∏ k ∈ s, Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
          + Real.log (Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α)) := by
      rw [hprodA, Real.log_mul (ne_of_gt (Finset.prod_pos (fun k hk => hApos_s k hk)))
        (ne_of_gt hAk₁pos)]
    have hlogB : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k)
        = Real.log (∏ k ∈ s, B k) + Real.log (B k₀) := by
      rw [hprodB, Real.log_mul (ne_of_gt (Finset.prod_pos (fun k hk => hBpos_s k hk)))
        (ne_of_gt hBk₀pos)]
    have hlogA_s : Real.log (∏ k ∈ s, Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
        = ∑ k ∈ s, Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) :=
      Real.log_prod (fun k hk => ne_of_gt (hApos_s k hk))
    have hlogB_s : Real.log (∏ k ∈ s, B k) = ∑ k ∈ s, Real.log (B k) :=
      Real.log_prod (fun k hk => ne_of_gt (hBpos_s k hk))
    have hT : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀,
        Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
        = (∑ k ∈ s, (Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) - Real.log (B k)))
          + (Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k) - Real.log (B k₀))
          + Real.log (Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α)) := by
      rw [hlogA, hlogA_s, hlogB, hlogB_s, Finset.sum_sub_distrib]
      ring
    rw [hT]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : -(Real.pi * (1 + Real.log q)) ≤
          ∑ k ∈ s, (Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α)) - Real.log (B k)) := by
        have h := (abs_le.mp hratio).1
        linarith [hcS]
      have h2 : Real.log q + Real.log (2 / Real.pi) - ((q : ℝ) - 1) * Real.log 2
          ≤ Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k) := by
        rw [← hId1]
        exact Real.log_le_log (by positivity) hRatLB
      have h3 : 0 ≤ -Real.log (B k₀) := by
        have h := Real.log_nonpos (le_of_lt hBk₀pos) hBk₀le
        linarith
      have h4 : -(Real.log 2 + Real.log q)
          ≤ Real.log (Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α)) := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (2 * (q : ℝ))) hAk₁
        have he : Real.log (1 / (2 * (q : ℝ))) = -(Real.log 2 + Real.log q) := by
          rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (ne_of_gt hqR)]
        rwa [he] at h
      exact assemble_B_lo q hq2 h1 h2 h3 h4
    · have h1 : ∑ k ∈ s, (Real.log (Basic.S (2 * x + ((k : ℝ) + (c k : ℝ)) * α))
          - Real.log (B k)) ≤ Real.pi * (1 + Real.log q) := by
        have h := (abs_le.mp hratio).2
        linarith [hcS]
      have h2 : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, B k)
          ≤ Real.log 4 + 2 * Real.log q - ((q : ℝ) - 1) * Real.log 2 := by
        rw [← hId2]
        exact Real.log_le_log (Finset.prod_pos (fun k hk => hBpos_e1 k hk)) hRatUB
      have h3 : -Real.log (B k₀) ≤ Real.log q := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (q : ℝ))
          (hB_lb k₀ hk₀ hk₀ne)
        have he : Real.log (1 / (q : ℝ)) = -Real.log q := by
          rw [one_div, Real.log_inv]
        rw [he] at h
        linarith
      have h4 : Real.log (Basic.S (2 * x + ((k₁ : ℝ) + (c k₁ : ℝ)) * α)) ≤ 0 :=
        Real.log_nonpos (le_of_lt hAk₁pos) hAk₁le
      exact assemble_B_hi q hq2 h1 h2 h3 h4

end Work.TMC16Core.Trig
