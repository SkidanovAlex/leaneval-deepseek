import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Analysis.SpecialFunctions.Gamma.hasDerivAt_log_norm_Gamma_vertical

/-!
# An elementary explicit upper bound for the real log-Gamma function

We prove that on `[1/4, ∞)` one has

    `log Γ(x) ≤ (x + 2) · log (x + 2)`.

The argument uses only log-convexity of `Γ` (which gives `Γ ≤ 1` on `[1,2]`,
since `Γ(1) = Γ(2) = 1`), the functional equation `Γ(x+1) = x·Γ(x)`, and plain
monotonicity of `t ↦ t·log t` and of `log`:

1. On `[1,2]`: convexity gives `log Γ(x) ≤ 0 ≤ (x+2)·log(x+2)`.
2. From `y ≥ 1` the inequality propagates to `y+1` via the functional equation,
   because `log Γ(y+1) = log y + log Γ(y) ≤ log y + (y+2)·log(y+2)`
   and `log y ≤ (y+3)·log(y+3) − (y+2)·log(y+2)`.
   Induction over the cells `[n+1, n+2]` then covers all of `[1, ∞)`.
3. On `[1/4, 1]`: `Γ(x+1) ≤ 1` (as `x+1 ∈ [5/4,2]`), so
   `Γ(x) = Γ(x+1)/x ≤ 4`, hence `log Γ(x) ≤ log 4 ≤ (9/4)·log(9/4) ≤ (x+2)·log(x+2)`
   (the last step since `t ↦ t·log t` is increasing on `[9/4, ∞)`).
-/

open Set

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- The elementary bound `(x + 2) · log (x + 2)` appearing in the statement. -/
noncomputable def logGammaB (x : ℝ) : ℝ :=
  (x + 2) * Real.log (x + 2)

/-- `Γ x ≤ 1` on `[1, 2]`, by convexity of `Γ` on `(0, ∞)` and `Γ(1) = Γ(2) = 1`. -/
lemma Gamma_le_one_of_mem_Icc_one_two {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    Real.Gamma x ≤ 1 := by
  have h1 : (1 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
  have h2 : (2 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
  have ha : 0 ≤ 2 - x := by linarith [hx.2]
  have hb : 0 ≤ x - 1 := by linarith [hx.1]
  have hab : (2 - x) + (x - 1) = 1 := by ring
  have hmain := Real.convexOn_Gamma.le_on_segment' h1 h2 ha hb hab
  have hpoint : (2 - x) • (1 : ℝ) + (x - 1) • (2 : ℝ) = x := by
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [hpoint] at hmain
  rw [Real.Gamma_one, Real.Gamma_two] at hmain
  simpa using hmain

/-- `log Γ x ≤ 0` on `[1, 2]`. -/
lemma log_Gamma_nonpos_of_mem_Icc_one_two {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    Real.log (Real.Gamma x) ≤ 0 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  have hΓ1 : Real.Gamma x ≤ 1 := Gamma_le_one_of_mem_Icc_one_two hx
  have hle := Real.log_le_log hpos hΓ1
  simpa using hle

/-- The elementary bound holds on `[1, 2]` (the right hand side is non-negative there). -/
lemma log_Gamma_le_B_of_mem_Icc_one_two {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    Real.log (Real.Gamma x) ≤ logGammaB x := by
  have hA : Real.log (Real.Gamma x) ≤ 0 := log_Gamma_nonpos_of_mem_Icc_one_two hx
  have hB : 0 ≤ logGammaB x := by
    unfold logGammaB
    have hx2pos : 0 < x + 2 := by linarith [hx.1]
    have hlog : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith [hx.1])
    exact mul_nonneg (le_of_lt hx2pos) hlog
  linarith

/-- `t ↦ t·log t` is monotone on `[1, ∞)`. -/
lemma mul_log_mono {u v : ℝ} (hu1 : 1 ≤ u) (huv : u ≤ v) :
    u * Real.log u ≤ v * Real.log v := by
  have hu_pos : 0 < u := by linarith
  have hlog_le : Real.log u ≤ Real.log v := Real.log_le_log hu_pos huv
  have hlogv_nonneg : 0 ≤ Real.log v := Real.log_nonneg (le_trans hu1 huv)
  calc
    u * Real.log u ≤ u * Real.log v := by gcongr
    _ ≤ v * Real.log v := by gcongr

/-- `logGammaB` is monotone on `[1/4, ∞)`. -/
lemma logGammaB_mono {x y : ℝ} (hx : 1 / 4 ≤ x) (hxy : x ≤ y) :
    logGammaB x ≤ logGammaB y := by
  unfold logGammaB
  exact mul_log_mono (by linarith : 1 ≤ x + 2) (by linarith : x + 2 ≤ y + 2)

/-- Numeric input: `log 4 ≤ logGammaB (1 / 4)`. -/
lemma log_four_le_logGammaB_quarter : Real.log 4 ≤ logGammaB (1 / 4) := by
  unfold logGammaB
  have hfrac : 1 / 4 + 2 = (9 / 4 : ℝ) := by norm_num
  rw [hfrac]
  have hpow : (4 : ℝ) ^ 4 ≤ (9 / 4 : ℝ) ^ 9 := by norm_num
  have hlogpow : Real.log ((4 : ℝ) ^ 4) ≤ Real.log ((9 / 4 : ℝ) ^ 9) := by
    exact Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  norm_num at hlogpow
  nlinarith

/-- For `y ≥ 1`: `log y ≤ logGammaB (y + 1) − logGammaB y`. -/
lemma log_le_logGammaB_sub_one {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ logGammaB (y + 1) - logGammaB y := by
  unfold logGammaB
  have hnorm : y + 1 + 2 = y + 3 := by ring
  rw [hnorm]
  have hypos : 0 < y := by linarith
  have hA : (0 : ℝ) ≤ (y + 2) * (Real.log (y + 3) - Real.log (y + 2)) := by
    have hlg : Real.log (y + 2) ≤ Real.log (y + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_nonneg (by linarith : 0 ≤ y + 2) (sub_nonneg.mpr hlg)
  have hlg1 : Real.log y ≤ Real.log (y + 3) :=
    Real.log_le_log hypos (by linarith)
  calc
    Real.log y ≤ Real.log (y + 3) := hlg1
    _ ≤ Real.log (y + 3) + (y + 2) * (Real.log (y + 3) - Real.log (y + 2)) := by
      linarith
    _ = (y + 3) * Real.log (y + 3) - (y + 2) * Real.log (y + 2) := by
      ring

/-- The functional-equation step: the bound at `y ≥ 1` implies the bound at `y+1`. -/
lemma log_Gamma_add_one_le (y : ℝ) (hy : 1 ≤ y)
    (h : Real.log (Real.Gamma y) ≤ logGammaB y) :
    Real.log (Real.Gamma (y + 1)) ≤ logGammaB (y + 1) := by
  have hypos : 0 < y := by linarith
  have hΓy_pos : 0 < Real.Gamma y := Real.Gamma_pos_of_pos hypos
  have hlog : Real.log y ≤ logGammaB (y + 1) - logGammaB y :=
    log_le_logGammaB_sub_one hy
  calc
    Real.log (Real.Gamma (y + 1)) = Real.log (y * Real.Gamma y) := by
      rw [Real.Gamma_add_one (s := y) (ne_of_gt hypos)]
    _ = Real.log y + Real.log (Real.Gamma y) := by
      exact Real.log_mul (ne_of_gt hypos) (ne_of_gt hΓy_pos)
    _ ≤ Real.log y + logGammaB y := by linarith
    _ ≤ logGammaB (y + 1) := by linarith

/-- Induction over the cells `[n+1, n+2]` gives the bound on the whole of `[1, ∞)`. -/
lemma log_Gamma_le_B_of_le_cell : ∀ (n : ℕ) (x : ℝ), 1 ≤ x → x ≤ (n : ℝ) + 2 →
    Real.log (Real.Gamma x) ≤ logGammaB x := by
  intro n
  induction n with
  | zero =>
      intro x hx1 hxN
      have hmem : x ∈ Icc (1 : ℝ) 2 := by
        constructor
        · exact hx1
        · simpa using hxN
      exact log_Gamma_le_B_of_mem_Icc_one_two hmem
  | succ n ih =>
      intro x hx1 hxN
      by_cases h : x ≤ (n : ℝ) + 2
      · exact ih x hx1 h
      · have hxgt : (n : ℝ) + 2 < x := by linarith
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
        let y := x - 1
        have hy1 : 1 ≤ y := by
          dsimp [y]
          linarith
        have hxN3 : x ≤ (n : ℝ) + 3 := by
          have hcast : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by
            push_cast
            ring
          rwa [hcast] at hxN
        have hyN : y ≤ (n : ℝ) + 2 := by
          dsimp [y]
          linarith
        have hih : Real.log (Real.Gamma y) ≤ logGammaB y := ih y hy1 hyN
        have hstep : Real.log (Real.Gamma (y + 1)) ≤ logGammaB (y + 1) :=
          log_Gamma_add_one_le y hy1 hih
        have hyx : y + 1 = x := by dsimp [y]; ring
        simpa [hyx] using hstep

/-- The elementary bound holds on `[1/4, 1]`. -/
lemma log_Gamma_le_B_of_mem_Icc_quarter_one {x : ℝ} (hx1 : 1 / 4 ≤ x) (hx2 : x ≤ 1) :
    Real.log (Real.Gamma x) ≤ logGammaB x := by
  have hxpos : 0 < x := by linarith
  have hmem : x + 1 ∈ Icc (1 : ℝ) 2 := by constructor <;> linarith
  have hΓ1x : Real.Gamma (x + 1) ≤ 1 := Gamma_le_one_of_mem_Icc_one_two hmem
  have hΓadd : Real.Gamma (x + 1) = x * Real.Gamma x :=
    Real.Gamma_add_one (s := x) (ne_of_gt hxpos)
  rw [hΓadd] at hΓ1x
  have hΓx_le_inv : Real.Gamma x ≤ 1 / x := by
    rw [le_div_iff₀ hxpos]
    nlinarith
  have hinv_le : 1 / x ≤ 4 := by
    rw [div_le_iff₀ hxpos]
    nlinarith
  have hΓ4 : Real.Gamma x ≤ 4 := le_trans hΓx_le_inv hinv_le
  have hlog : Real.log (Real.Gamma x) ≤ Real.log 4 :=
    Real.log_le_log (Real.Gamma_pos_of_pos hxpos) hΓ4
  have hnum : Real.log 4 ≤ logGammaB (1 / 4) := log_four_le_logGammaB_quarter
  have hB : logGammaB (1 / 4) ≤ logGammaB x :=
    logGammaB_mono (x := 1 / 4) (y := x) (by norm_num) hx1
  exact le_trans (le_trans hlog hnum) hB

/-- An explicit elementary upper bound for the log-Gamma function on `[1/4, ∞)`:
`log Γ(x) ≤ (x + 2) · log (x + 2)`.  (The exact constant is flexible: any explicit bound of the
form `log Γ(x) ≤ (x + c) · log (x + d)` with explicit constants `c,d` that is correct on
`x ≥ 1/4` is acceptable; state it as generally as convenient.) -/
theorem log_Gamma_le {x : ℝ} (hx : 1 / 4 ≤ x) :
    Real.log (Real.Gamma x) ≤ (x + 2) * Real.log (x + 2) := by
  by_cases hx1 : 1 ≤ x
  · have hx_lt : x ≤ (Nat.ceil x : ℝ) + 2 := by
      have hc := Nat.le_ceil x
      linarith
    have h := log_Gamma_le_B_of_le_cell (Nat.ceil x) x hx1 hx_lt
    unfold logGammaB at h
    exact h
  · have hxlt1 : x < 1 := lt_of_not_ge hx1
    have hx2 : x ≤ 1 := le_of_lt hxlt1
    have h := log_Gamma_le_B_of_mem_Icc_quarter_one hx hx2
    unfold logGammaB at h
    exact h

end Commons.Analysis.SpecialFunctions.Gamma