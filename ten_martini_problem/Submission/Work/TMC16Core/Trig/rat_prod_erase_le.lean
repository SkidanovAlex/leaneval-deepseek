/-
# The rational block product with the minimal factor removed: upper bound

Avila–Jitomirskaya, *The Ten Martini Problem*, §9, use the trigonometric product estimate
(their (9.25)/(9.26))

  `∏_{k ≠ k₁} |sin (2π (x + k p/(2q)))| ≍ 2^{-(q-1)} q^{O(1)}`

for `k₁ ∈ {1,…,q}` a minimiser of `k ↦ |sin (2π (x + k p/(2q)))|` (`p, q` coprime, `q ≥ 1`).

This file proves the **upper half** of that estimate, and in fact a slightly stronger
statement: the product of the remaining factors is at most `q / 2^{q-1}` (for *any* removed
index `k₁`, not only a minimiser), which is `≤ 4 q² / 2^{q-1}`.

The proof does not even need minimality.  Writing `S w = |sin (π w)|`, we have
`|sin (2π (x + k p/(2q)))| = S (2x + k p/q)`, and `Basic/rational_block_prod` gives the exact
identity

  `∏_{k=1}^{q} S (2x + k p/q) = |sin (2π q x)| · 2 / 2^q`.

Removing the `k₁`-th factor and using the elementary Dirichlet bound `|sin (n t)| ≤ n |sin t|`
(applied with `n = q`, `t = π (2x + k₁ p/q)`, so that `|sin (2π q x)| = S (q · (2x + k₁ p/q))`)
yields

  `(∏_{k ≠ k₁} S (2x + k p/q)) · S (2x + k₁ p/q) ≤ S (2x + k₁ p/q) · q / 2^{q-1}`,

hence the bound whenever the removed factor is nonzero.  The degenerate case
`S (2x + k₁ p/q) = 0` is handled by continuity: the left side is continuous in `x`, and one can
always move `x` by an arbitrarily small amount so that the factor at `k₁` becomes nonzero
(`exists_nn_pos_shift`, via the density of the irrationals), after which the non-degenerate
bound applies.
-/
import Mathlib
import Submission.Work.TMC16Core.Basic.rational_block_prod
import Submission.Work.TMC16Core.Basic.nnDist

set_option linter.unusedVariables false

namespace Work.TMC16Core.Trig

open Finset
open Work.TMC16Core.Basic

/-- **Dirichlet's elementary sine bound**: `|sin (n t)| ≤ n |sin t|` for every `n : ℕ`. -/
lemma abs_sin_nat_mul_le (n : ℕ) (t : ℝ) :
    |Real.sin ((n : ℝ) * t)| ≤ (n : ℝ) * |Real.sin t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((n+1 : ℕ) : ℝ) * t = (n : ℝ) * t + t := by push_cast; ring
    rw [h1, Real.sin_add]
    calc |Real.sin ((n:ℝ)*t) * Real.cos t + Real.cos ((n:ℝ)*t) * Real.sin t|
        ≤ |Real.sin ((n:ℝ)*t) * Real.cos t| + |Real.cos ((n:ℝ)*t) * Real.sin t| := abs_add_le _ _
      _ = |Real.sin ((n:ℝ)*t)| * |Real.cos t| + |Real.cos ((n:ℝ)*t)| * |Real.sin t| := by
            rw [abs_mul, abs_mul]
      _ ≤ (n:ℝ)*|Real.sin t| * 1 + 1 * |Real.sin t| := by
          apply add_le_add
          · exact mul_le_mul ih (Real.abs_cos_le_one t) (abs_nonneg _) (by positivity)
          · exact mul_le_mul (Real.abs_cos_le_one _) (le_refl _) (abs_nonneg _) (by positivity)
      _ = (Nat.succ n : ℝ) * |Real.sin t| := by push_cast; ring

/-- For any real `c`, centre `x` and radius `r > 0`, there is `y` with `|y - x| < r` and
`2 y + c` not an integer (indeed `2 y + c` can be taken irrational).  Used to move off the
degenerate locus `S (2x + k₁ p/q) = 0`. -/
lemma exists_nn_pos_shift (c x r : ℝ) (hr : 0 < r) :
    ∃ y, |y - x| < r ∧ ¬ ∃ m : ℤ, 2*y + c = (m:ℝ) := by
  have hlt : 2*x + c - 2*r < 2*x + c + 2*r := by linarith
  obtain ⟨w, hwirr, hw1, hw2⟩ := exists_irrational_btwn hlt
  refine ⟨(w - c)/2, ?_, ?_⟩
  · have hw : |w - (2*x + c)| < 2*r := by
      rw [abs_lt]; constructor <;> linarith
    rw [show (w - c)/2 - x = (w - (2*x + c))/2 by ring,
        abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  · rintro ⟨m, hm⟩
    apply hwirr
    refine ⟨(m:ℚ), ?_⟩
    have hwm : w = (m:ℝ) := by linarith [hm]
    rw [hwm]; push_cast; ring

/-- `S w > 0` whenever `w` is not an integer. -/
lemma S_pos_of_not_int (w : ℝ) (hw : ¬ ∃ m : ℤ, w = (m:ℝ)) : 0 < S w := by
  rw [S_eq_sin_nn]
  have h0 : nn w ≠ 0 := by
    intro h; exact hw ((nn_eq_zero_iff w).mp h)
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · exact mul_pos Real.pi_pos (lt_of_le_of_ne (nn_nonneg w) (Ne.symm h0))
  · nlinarith [Real.pi_pos, nn_le_half w]

/-- **The non-degenerate block bound**: if the removed factor is nonzero, the product of the
remaining `q - 1` absolute sine factors is at most `q / 2^{q-1}`. -/
lemma erase_prod_le_of_pos {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    (x : ℝ) {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hpos : 0 < S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))) :
    ∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| ≤
      (q:ℝ) / (2:ℝ)^(q-1) := by
  have hA : ∀ k : ℕ,
      |Real.sin (2 * Real.pi * (x + (k:ℝ)*((p:ℝ)/(2*(q:ℝ)))))| =
        S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))) := by
    intro k
    unfold S
    congr 1
    field_simp
  have hP : ∏ k ∈ Finset.Icc 1 q, S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))) =
      |Real.sin (2 * Real.pi * ((q:ℝ) * x))| * (2 / (2:ℝ)^q) := by
    rw [← rational_block_prod p q hq hcop x]
    exact Finset.prod_congr rfl (fun k _ => (hA k).symm)
  have hSqv : S ((q:ℝ) * (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))) =
      |Real.sin (2 * Real.pi * ((q:ℝ) * x))| := by
    unfold S
    have h1 : Real.pi * ((q:ℝ) * (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))))
        = 2 * Real.pi * ((q:ℝ)*x) + ((k₁:ℤ)*p : ℤ) * Real.pi := by
      push_cast
      field_simp
    rw [h1, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have hdir : S ((q:ℝ) * (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))) ≤
      (q:ℝ) * S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))) := by
    unfold S
    rw [show Real.pi * ((q:ℝ)*(2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))))
        = (q:ℝ)*(Real.pi*(2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))) by ring]
    exact abs_sin_nat_mul_le q (Real.pi*(2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))))
  have hsplit : (∏ k ∈ (Finset.Icc 1 q).erase k₁, S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))))
      * S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))
      = ∏ k ∈ Finset.Icc 1 q, S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))) :=
    Finset.prod_erase_mul (Finset.Icc 1 q) (fun k => S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ)))) hk₁
  have hkey : (∏ k ∈ (Finset.Icc 1 q).erase k₁, S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))))
      * S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))
      ≤ S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))) * ((q:ℝ)/(2:ℝ)^(q-1)) := by
    rw [hsplit, hP]
    calc |Real.sin (2 * Real.pi * ((q:ℝ) * x))| * (2 / (2:ℝ)^q)
        = S ((q:ℝ)*(2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))) * (2/(2:ℝ)^q) := by rw [hSqv]
      _ ≤ ((q:ℝ) * S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))) * (2/(2:ℝ)^q) :=
            mul_le_mul_of_nonneg_right hdir (by positivity)
      _ = S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))) * ((q:ℝ)/(2:ℝ)^(q-1)) := by
            have hp : (2:ℝ)^q = (2:ℝ)^(q-1) * 2 := by rw [← pow_succ]; congr 1; omega
            rw [hp]; field_simp
  have hbound : ∏ k ∈ (Finset.Icc 1 q).erase k₁, S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ)))
      ≤ (q:ℝ)/(2:ℝ)^(q-1) := by
    have h3 : (∏ k ∈ (Finset.Icc 1 q).erase k₁, S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))))
        * S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))
        ≤ ((q:ℝ)/(2:ℝ)^(q-1)) * S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))) := by
      rw [mul_comm (S (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ)))) ((q:ℝ)/(2:ℝ)^(q-1))] at hkey
      exact hkey
    exact (mul_le_mul_iff_of_pos_right hpos).mp h3
  rw [show (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (x + (k:ℝ)*((p:ℝ)/(2*(q:ℝ)))))|)
      = (∏ k ∈ (Finset.Icc 1 q).erase k₁, S (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ)))) from
      Finset.prod_congr rfl (fun k _ => hA k)]
  exact hbound

/-- **The rational block product with one (minimal) factor removed, upper bound.**
For coprime `p, q` with `q ≥ 1` and any `k₁ ∈ {1,…,q}`, the product of the remaining
`|sin (2π (x + k p/(2q)))|` factors is at most `4 q² / 2^{q-1}`.  (The minimality hypothesis
`hmin` is not needed for the bound and is kept to match the interface of AJ §9.) -/
theorem rat_prod_erase_le {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    (x : ℝ) {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| ≥
        |Real.sin (2 * Real.pi * (x + (k₁ : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) :
    ∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| ≤
      4 * (q : ℝ) ^ 2 / 2 ^ (q - 1) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hcont : ContinuousAt (fun y : ℝ => ∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (y + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) x := by
    apply Continuous.continuousAt
    apply continuous_finsetProd
    intro k hk
    fun_prop
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨y, hyx, hybad⟩ := exists_nn_pos_shift ((k₁:ℝ)*((p:ℝ)/(q:ℝ))) x δ hδpos
  have hdist : dist y x < δ := by rw [Real.dist_eq]; exact hyx
  have hval := hδ hdist
  rw [Real.dist_eq] at hval
  have hspos : 0 < S (2*y + (k₁:ℝ)*((p:ℝ)/(q:ℝ))) := S_pos_of_not_int _ hybad
  have hFy : (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (y + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) ≤
      (q:ℝ)/(2:ℝ)^(q-1) := erase_prod_le_of_pos hq hcop y hk₁ hspos
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have h4 : (q:ℝ)/(2:ℝ)^(q-1) ≤ 4*(q:ℝ)^2/(2:ℝ)^(q-1) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [hq1]
  have hx_lt : (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) <
      4*(q:ℝ)^2/(2:ℝ)^(q-1) + ε := by
    have h1 := (abs_lt.mp hval).1
    linarith [hFy, h4]
  exact le_of_lt hx_lt

end Work.TMC16Core.Trig
