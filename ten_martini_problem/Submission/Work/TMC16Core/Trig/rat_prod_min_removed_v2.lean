import Mathlib
import Submission.Work.TMC16Core.Basic.rational_block_prod
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.Core.exists_nn_le
import Submission.Work.TMC16Core.Trig.sin_prod_classic

/-!
# The rational block product with the minimal factor removed: lower bound (AJ §9, (9.25))

Avila–Jitomirskaya, *The Ten Martini Problem*, §9, need the trigonometric product estimate
(their (9.25))

  `∏_{k ≠ k₁} |sin (2π (x + k p/(2q)))| ≥ q (2/π) / 2^{q-1}`

for `k₁ ∈ {1,…,q}` an index at which `k ↦ |sin (2π (x + k p/(2q)))|` is minimal (`p, q` coprime,
`q ≥ 1`).

**Proof.**  Write `v = 2x + k₁ p/q` and `d = nn v` (distance to the nearest integer), so that
the removed factor is `S v = sin (π d)`.

* The exact product identity `Basic/rational_block_prod` gives
  `∏_{k=1}^{q} S (2x + kp/q) = |sin (2π q x)| · 2/2^q`, and `S (q v) = |sin (2π q x)|`.
* Minimality of `k₁` forces `d ≤ 1/(2q)`: by `Core/exists_nn_le` some `k` has `nn ≤ 1/(2q)`,
  and `S v ≤ S (2x + kp/q) ≤ sin (π/(2q))`, so monotonicity of `sin` on `[-π/2, π/2]` gives
  `π d ≤ π/(2q)`.
* Dividing the product identity by the (nonzero) factor and using
  `sin (π q d) / sin (π d) ≥ 2q/π` (valid for `0 < d ≤ 1/(2q)`) yields the bound whenever
  `0 < d`.
* The degenerate case `d = 0` is handled by continuity: the left hand side is continuous in `x`,
  and moving `x` by a tiny amount makes `nn` positive while keeping it `≤ 1/(2q)`, after which
  the non-degenerate bound applies.
-/

namespace Work.TMC16Core.Trig

open Finset
open Work.TMC16Core.Basic

/-- **The sine-ratio bound.**  For `0 < d ≤ 1/(2q)` one has
`2q/π ≤ sin (π q d) / sin (π d)`. -/
lemma rpm_sin_ratio_ge (q : ℕ) (hq : 0 < q) {d : ℝ} (hd0 : 0 < d)
    (hd : d ≤ 1 / (2 * (q : ℝ))) :
    2 * (q : ℝ) / Real.pi ≤ Real.sin (Real.pi * ((q : ℝ) * d)) / Real.sin (Real.pi * d) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hd_le : d ≤ 1 / 2 := by
    have h1 : 1 / (2 * (q : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [hq1])
    linarith
  have hsin_d_pos : 0 < Real.sin (Real.pi * d) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, hd_le])
  have hsin_d_le : Real.sin (Real.pi * d) ≤ Real.pi * d := Real.sin_le (by positivity)
  have hqd : (q : ℝ) * d ≤ 1 / 2 := by
    have h2 : (q : ℝ) * d ≤ (q : ℝ) * (1 / (2 * (q : ℝ))) :=
      mul_le_mul_of_nonneg_left hd (le_of_lt hqR)
    have h3 : (q : ℝ) * (1 / (2 * (q : ℝ))) = 1 / 2 := by field_simp
    linarith
  have hu_le : Real.pi * ((q : ℝ) * d) ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hqd]
  have hu0 : 0 ≤ Real.pi * ((q : ℝ) * d) := by positivity
  have hkey : 2 / Real.pi * (Real.pi * ((q : ℝ) * d)) ≤
      Real.sin (Real.pi * ((q : ℝ) * d)) := Real.mul_le_sin hu0 hu_le
  rw [le_div_iff₀ hsin_d_pos]
  calc 2 * (q : ℝ) / Real.pi * Real.sin (Real.pi * d)
      ≤ 2 * (q : ℝ) / Real.pi * (Real.pi * d) :=
        mul_le_mul_of_nonneg_left hsin_d_le (by positivity)
    _ = 2 / Real.pi * (Real.pi * ((q : ℝ) * d)) := by ring
    _ ≤ Real.sin (Real.pi * ((q : ℝ) * d)) := hkey

/-- A single factor of the block product, written as `S` of the corresponding argument:
`|sin (2π (x + k p/(2q)))| = S (2x + k p/q)`. -/
lemma rpm_term_eq_S (p : ℤ) (q : ℕ) (x : ℝ) (k : ℕ) :
    |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| =
      S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
  refine congrArg (fun t : ℝ => |Real.sin t|) ?_
  field_simp
  try ring

/-- `S (n w) = sin (π n nn w)` as long as `n nn w ≤ 1/2`. -/
lemma rpm_S_nat_mul (n : ℕ) (w : ℝ) (h : (n : ℝ) * nn w ≤ 1 / 2) :
    S ((n : ℝ) * w) = Real.sin (Real.pi * ((n : ℝ) * nn w)) := by
  have h1 : (n : ℝ) * w = (n : ℝ) * (w - (round w : ℝ)) + ((n * round w : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h1, S_add_intCast]
  have habs : |(n : ℝ) * (w - (round w : ℝ))| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    exact h
  rw [S_eq_sin_abs ((n : ℝ) * (w - (round w : ℝ))) habs]
  congr 1
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  rfl

/-- `S w ≤ sin (π a)` as soon as `nn w ≤ a ≤ 1/2`. -/
lemma rpm_S_le_sin_of_nn_le {w a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (h : nn w ≤ a) :
    S w ≤ Real.sin (Real.pi * a) := by
  rw [S_eq_sin_nn]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two
    (by nlinarith [Real.pi_pos, nn_nonneg w, ha0])
    (by nlinarith [Real.pi_pos, ha])
    (by nlinarith [Real.pi_pos, h])

/-- **Minimality forces the distance to the nearest integer to be small.**  If `k₁` is a
minimiser of `k ↦ |sin (2π (x + k p/(2q)))|` on `k ∈ {1,…,q}`, then
`nn (2x + k₁ p/q) ≤ 1/(2q)`. -/
lemma rpm_nn_le_of_min {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (x : ℝ)
    {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| ≥
        |Real.sin (2 * Real.pi * (x + (k₁ : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) :
    nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤ 1 / (2 * (q : ℝ)) := by
  obtain ⟨k, hk, hknn⟩ := Work.Core.exists_nn_le p q hq hcop (2 * x)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have ha2 : 1 / (2 * (q : ℝ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [hq1])
  have h1 : S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) ≤
      Real.sin (Real.pi * (1 / (2 * (q : ℝ)))) :=
    rpm_S_le_sin_of_nn_le (by positivity) ha2 hknn
  have h2 : S (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤
      Real.sin (Real.pi * (1 / (2 * (q : ℝ)))) := by
    calc S (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)))
        = |Real.sin (2 * Real.pi * (x + (k₁ : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| :=
          (rpm_term_eq_S p q x k₁).symm
      _ ≤ |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| := hmin k hk
      _ = S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := rpm_term_eq_S p q x k
      _ ≤ Real.sin (Real.pi * (1 / (2 * (q : ℝ)))) := h1
  rw [S_eq_sin_nn] at h2
  have hmem1 : Real.pi * nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    exact ⟨by nlinarith [Real.pi_pos, nn_nonneg (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)))],
      by nlinarith [Real.pi_pos, nn_le_half (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)))]⟩
  have hmem2 : Real.pi * (1 / (2 * (q : ℝ))) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    exact ⟨by
      have hpos : (0 : ℝ) ≤ Real.pi * (1 / (2 * (q : ℝ))) := by positivity
      linarith [Real.pi_pos],
      by nlinarith [Real.pi_pos, ha2]⟩
  have h3 := (Real.strictMonoOn_sin.le_iff_le hmem1 hmem2).mp h2
  nlinarith [h3, Real.pi_pos]

/-- **The non-degenerate case** (AJ (9.25)): if the removed factor is nonzero and its
distance to the nearest integer is at most `1/(2q)`, the product of the remaining factors is
at least `q (2/π) / 2^{q-1}`. -/
lemma rpm_erase_prod_ge_of_nn_pos {q : ℕ} (hq : 0 < q) {p : ℤ}
    (hcop : Nat.Coprime p.natAbs q) (x : ℝ) {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hpos : 0 < nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))))
    (hle : nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤ 1 / (2 * (q : ℝ))) :
    (q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1) ≤
      ∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| := by
  set v : ℝ := 2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)) with hv
  set d : ℝ := nn v with hd
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hd0 : 0 < d := hpos
  have hdle : d ≤ 1 / (2 * (q : ℝ)) := hle
  have hd2 : d ≤ 1 / 2 := by
    have h1 : 1 / (2 * (q : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [hq1])
    linarith
  have hqd : (q : ℝ) * d ≤ 1 / 2 := by
    have h2 : (q : ℝ) * d ≤ (q : ℝ) * (1 / (2 * (q : ℝ))) :=
      mul_le_mul_of_nonneg_left hdle (le_of_lt hqR)
    have h3 : (q : ℝ) * (1 / (2 * (q : ℝ))) = 1 / 2 := by field_simp
    linarith
  have hterm : ∀ k : ℕ,
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| =
        S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := fun k => rpm_term_eq_S p q x k
  have hP : ∏ k ∈ Finset.Icc 1 q, S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) =
      |Real.sin (2 * Real.pi * ((q : ℝ) * x))| * (2 / (2 : ℝ) ^ q) := by
    rw [← rational_block_prod p q hq hcop x]
    exact Finset.prod_congr rfl (fun k _ => (hterm k).symm)
  have hSqv : S ((q : ℝ) * v) = |Real.sin (2 * Real.pi * ((q : ℝ) * x))| := by
    have h1 : (q : ℝ) * v = (q : ℝ) * (2 * x) + ((k₁ * p : ℤ) : ℝ) := by
      rw [hv]
      push_cast
      field_simp
    rw [h1, S_add_intCast]
    have harg : Real.pi * ((q : ℝ) * (2 * x)) = 2 * Real.pi * ((q : ℝ) * x) := by ring
    simp only [S, harg]
  have hsplit : (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))) * S v =
      ∏ k ∈ Finset.Icc 1 q, S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
    have h := Finset.prod_erase_mul (Finset.Icc 1 q)
      (fun k => S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))) hk₁
    simpa [hv] using h
  have hE1 : (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))) * S v =
      S ((q : ℝ) * v) * (2 / (2 : ℝ) ^ q) := by
    rw [hsplit, hP, hSqv]
  have hSv : S v = Real.sin (Real.pi * d) := by
    rw [S_eq_sin_nn, ← hd]
  have hSqvd : S ((q : ℝ) * v) = Real.sin (Real.pi * ((q : ℝ) * d)) := by
    rw [rpm_S_nat_mul q v hqd, ← hd]
  have hSvpos : 0 < S v := by
    rw [hSv]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith [Real.pi_pos, hd2])
  have hE : (∏ k ∈ (Finset.Icc 1 q).erase k₁,
        S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))) =
      S ((q : ℝ) * v) * (2 / (2 : ℝ) ^ q) / S v := by
    rw [eq_div_iff (ne_of_gt hSvpos)]
    exact hE1
  rw [Finset.prod_congr rfl (fun k _ => hterm k), hE]
  calc (q : ℝ) * (2 / Real.pi) / (2 : ℝ) ^ (q - 1)
      = (2 * (q : ℝ) / Real.pi) * (2 / (2 : ℝ) ^ q) := by
        have hpow : (2 : ℝ) ^ q = (2 : ℝ) ^ (q - 1) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hpow]
        field_simp
        try ring
    _ ≤ (Real.sin (Real.pi * ((q : ℝ) * d)) / Real.sin (Real.pi * d)) *
          (2 / (2 : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_right (rpm_sin_ratio_ge q hq hd0 hdle) (by positivity)
    _ = S ((q : ℝ) * v) * (2 / (2 : ℝ) ^ q) / S v := by
        rw [hSqvd, hSv]
        ring

/-- **AJ §9, (9.25).**  The rational block product with the minimal factor removed: for
coprime `p, q` with `q ≥ 1` and `k₁ ∈ {1,…,q}` an index at which `k ↦ |sin (2π (x + kp/(2q)))|`
is minimal, the product of the remaining factors is at least `q (2/π) / 2^{q-1}`. -/
theorem rat_prod_min_removed_v2 {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    (x : ℝ) {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| ≥
        |Real.sin (2 * Real.pi * (x + (k₁ : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) :
    (q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1) ≤
      ∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| := by
  set v : ℝ := 2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)) with hv
  have hle : nn v ≤ 1 / (2 * (q : ℝ)) := by
    rw [hv]
    exact rpm_nn_le_of_min hq hcop x hk₁ hmin
  by_cases hzero : nn v = 0
  · -- degenerate case: perturb `x` slightly to leave the locus `nn v = 0`
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hcont : ContinuousAt (fun y : ℝ => ∏ k ∈ (Finset.Icc 1 q).erase k₁,
        |Real.sin (2 * Real.pi * (y + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) x := by
      fun_prop
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
    set r : ℝ := min δ (1 / (4 * (q : ℝ))) with hr
    have hrpos : 0 < r := lt_min hδpos (by positivity)
    set y : ℝ := x + r / 2 with hydef
    have hyx : |y - x| = r / 2 := by
      rw [hydef, add_sub_cancel_left, abs_of_pos (by linarith)]
    have hydist : dist y x < δ := by
      rw [Real.dist_eq, hyx]
      have h : r ≤ δ := min_le_left _ _
      linarith
    have hval := hδ hydist
    rw [Real.dist_eq] at hval
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    set v' : ℝ := 2 * y + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)) with hv'
    have hW : v' - v = 2 * (y - x) := by
      rw [hv', hv, hydef]
      ring
    have hyle : nn v' ≤ 1 / (2 * (q : ℝ)) := by
      have hv'E : v' = v + 2 * (y - x) := by linarith [hW]
      rw [hv'E]
      have h3 : nn (v + 2 * (y - x)) ≤ nn v + |2 * (y - x)| := by
        have h1 := nn_add_le v (2 * (y - x))
        have h2 := nn_le_abs (2 * (y - x))
        linarith
      rw [hzero, zero_add] at h3
      have h4 : |2 * (y - x)| = r := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hyx]
        ring
      rw [h4] at h3
      have h6 : r ≤ 1 / (2 * (q : ℝ)) := by
        have h7 : r ≤ 1 / (4 * (q : ℝ)) := min_le_right _ _
        have h8 : 1 / (4 * (q : ℝ)) ≤ 1 / (2 * (q : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) (by linarith [hqR])
        linarith
      linarith
    have hypos : 0 < nn v' := by
      by_contra hcon
      have h0 : nn v' = 0 := le_antisymm (not_lt.mp hcon) (nn_nonneg _)
      obtain ⟨n, hn⟩ := (nn_eq_zero_iff v').mp h0
      obtain ⟨m, hm⟩ := (nn_eq_zero_iff v).mp hzero
      have h2 : 2 * (y - x) = ((n - m : ℤ) : ℝ) := by
        rw [← hW, hn, hm]
        push_cast
        ring
      have h5 : |(n - m : ℤ)| < 1 := by
        have h6 : ((|n - m| : ℤ) : ℝ) < 1 := by
          rw [Int.cast_abs, ← h2]
          have h7 : |2 * (y - x)| < 1 / 2 := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hyx]
            have h9 : (0 : ℝ) < 4 * (q : ℝ) := by positivity
            have h10 : 1 / (4 * (q : ℝ)) ≤ (1 : ℝ) / 4 :=
              one_div_le_one_div_of_le (by norm_num) (by linarith [hq1])
            have h11 : r ≤ 1 / 4 := le_trans (min_le_right _ _) h10
            linarith
          linarith
        exact_mod_cast h6
      have h8 : n - m = 0 := by
        have h1 := (abs_lt.mp h5).1
        have h2 := (abs_lt.mp h5).2
        omega
      have h9 : 2 * (y - x) = 0 := by
        rw [h2, h8]
        norm_num
      have : y - x = 0 := by linarith
      rw [hydef] at this
      linarith
    have hfin := rpm_erase_prod_ge_of_nn_pos (p := p) hq hcop y hk₁ hypos hyle
    have hgy : (∏ k ∈ (Finset.Icc 1 q).erase k₁,
          |Real.sin (2 * Real.pi * (y + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) <
        (∏ k ∈ (Finset.Icc 1 q).erase k₁,
          |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))|) + ε := by
      linarith [(abs_lt.mp hval).2]
    linarith
  · exact rpm_erase_prod_ge_of_nn_pos (p := p) hq hcop x hk₁
      (lt_of_le_of_ne (nn_nonneg v) (Ne.symm hzero)) (by rw [hv] at hle; exact hle)

end Work.TMC16Core.Trig
