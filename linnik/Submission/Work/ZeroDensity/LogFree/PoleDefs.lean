import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selberg_Q_eq_sum_theta

/-!
# `Work.ZeroDensity.LogFree.PoleDefs` — vocabulary for the pole-residue bound

The pole residue of the damped large sieve is

  `Q(1) = poleResidue W = Σ_{d,e ≤ ⌈W⌉} θ_d θ_e / [d,e]`,   `θ_d = thetaM W d`

with `θ_d = μ(d)·log(W/d)/log W` for `d ≤ W` and `θ_d = 0` beyond.  Because
`1/[d,e] = gcd(d,e)/(de)`, the Selberg diagonalization turns this into a sum of squares

  `poleResidue W · (log W)^2 = Σ_{l ≤ ⌈W⌉} φ(l) · (Σ_{l ∣ d} thetaL W d / d)^2`,

where `thetaL W d = θ_d·log W = μ(d)log(W/d)` for `d ≤ W` (and `0` beyond) is the Selberg weight
at the *real* cut-off `W`.  Comparing it with the Selberg weight `selLam z ·` at the integer
cut-off `z = ⌈W⌉₊` is a perturbation of size `log(z/W)`, which makes the sharp bound
`selQ z ≤ log z + O(1)` (`selberg_LambdaR_sq_sharp`, already proved in the workspace) applicable.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-- The Selberg weight at the real cut-off `W`, scaled back by `log W`:
`thetaL W d = μ(d)·log(W/d)` if `d ≤ W`, and `0` otherwise.  It is `log W · thetaM W d`. -/
def thetaL (W : ℝ) (d : ℕ) : ℝ :=
  if (d : ℝ) ≤ W then (ArithmeticFunction.moebius d : ℝ) * Real.log (W / (d : ℝ)) else 0

/-- The inner Selberg sum at the real cut-off `W`: `Σ_{l ∣ d ≤ ⌈W⌉} thetaL W d / d`. -/
def innerP (W : ℝ) (l : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d), thetaL W d / (d : ℝ)

/-- The inner Selberg sum at the integer cut-off `z`: `Σ_{l ∣ d ≤ z} selLam z d / d`.
This is exactly the inner sum of the classical Selberg diagonalization of `selQ z`. -/
def innerB (z l : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 z).filter (fun d => l ∣ d), Work.LinnikAreas.Density4.selLam z d / (d : ℝ)

/-- The pole residue in diagonalized (sum-of-squares) form. -/
def poleDiag (W : ℝ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ) * innerP W l ^ 2

/-! ## Elementary relations -/

/-- `thetaM W d = thetaL W d / log W` for `W > 1`. -/
lemma thetaM_eq_thetaL_div {W : ℝ} (hW : 1 < W) (d : ℕ) :
    Work.LinnikAreas.Density4.thetaM W d = thetaL W d / Real.log W := by
  have hlog : Real.log W ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hW)
  rw [thetaL, Work.LinnikAreas.Density4.thetaM]
  by_cases h : (d : ℝ) ≤ W
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_div]

/-- `selQ z` in terms of the inner sums `innerB`. -/
lemma selQ_eq_sum_innerB (z : ℕ) :
    Work.LinnikAreas.Density4.selQ z
      = ∑ l ∈ Finset.Icc 1 z, (Nat.totient l : ℝ) * innerB z l ^ 2 := by
  rw [Work.LinnikAreas.Density4.selQ_eq_sum_totient_inner z]
  apply Finset.sum_congr rfl
  intro l _
  rw [innerB]

/-- The Möbius function is at most `1` in modulus. -/
lemma abs_moebius_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- **The weight difference is at most `log (⌈W⌉/W)`.**  For `1 ≤ d ≤ ⌈W⌉₊` the real-cut-off
Selberg weight `thetaL W d` and the integer-cut-off Selberg weight `selLam ⌈W⌉₊ d` differ by at
most `log (⌈W⌉₊/W) ≤ 1/W`. -/
lemma thetaL_sub_selLam_abs_le {W : ℝ} (hW : 1 < W) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 ⌈W⌉₊) :
    |thetaL W d - Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d|
      ≤ Real.log ((⌈W⌉₊ : ℝ) / W) := by
  have hWpos : 0 < W := by linarith
  have hzpos : (0 : ℝ) < (⌈W⌉₊ : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr hWpos)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdz : d ≤ ⌈W⌉₊ := (Finset.mem_Icc.mp hd).2
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hzW : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil W
  have hlogzW : 0 ≤ Real.log ((⌈W⌉₊ : ℝ) / W) :=
    Real.log_nonneg (by rw [le_div_iff₀ hWpos]; linarith)
  have hmu := abs_moebius_le_one d
  have hsel : Work.LinnikAreas.Density4.selLam ⌈W⌉₊ d
      = (ArithmeticFunction.moebius d : ℝ) * Real.log ((⌈W⌉₊ : ℝ) / (d : ℝ)) := by
    rw [Work.LinnikAreas.Density4.selLam]
  by_cases hle : (d : ℝ) ≤ W
  · have h1 : thetaL W d
        = (ArithmeticFunction.moebius d : ℝ) * Real.log (W / (d : ℝ)) := by
      rw [thetaL, if_pos hle]
    rw [h1, hsel, ← mul_sub, abs_mul]
    have h3 : |Real.log (W / (d : ℝ)) - Real.log ((⌈W⌉₊ : ℝ) / (d : ℝ))|
        = Real.log ((⌈W⌉₊ : ℝ) / W) := by
      have hlog : Real.log (W / (d : ℝ)) - Real.log ((⌈W⌉₊ : ℝ) / (d : ℝ))
          = -Real.log ((⌈W⌉₊ : ℝ) / W) := by
        rw [Real.log_div (ne_of_gt hWpos) (ne_of_gt hd0),
          Real.log_div (ne_of_gt hzpos) (ne_of_gt hd0),
          Real.log_div (ne_of_gt hzpos) (ne_of_gt hWpos)]
        ring
      rw [hlog, abs_neg, abs_of_nonneg hlogzW]
    rw [h3]
    calc |(ArithmeticFunction.moebius d : ℝ)| * Real.log ((⌈W⌉₊ : ℝ) / W)
        ≤ 1 * Real.log ((⌈W⌉₊ : ℝ) / W) :=
          mul_le_mul_of_nonneg_right hmu hlogzW
      _ = Real.log ((⌈W⌉₊ : ℝ) / W) := one_mul _
  · have h1 : thetaL W d = 0 := by rw [thetaL, if_neg hle]
    have hWlt : W < (d : ℝ) := not_le.mp hle
    have hlogdz : 0 ≤ Real.log ((⌈W⌉₊ : ℝ) / (d : ℝ)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hd0, one_mul]; exact_mod_cast hdz)
    have hle2 : Real.log ((⌈W⌉₊ : ℝ) / (d : ℝ)) ≤ Real.log ((⌈W⌉₊ : ℝ) / W) := by
      apply Real.log_le_log (by positivity)
      have h1d : (1 : ℝ) / (d : ℝ) ≤ 1 / W := one_div_le_one_div_of_le hWpos hWlt.le
      calc (⌈W⌉₊ : ℝ) / (d : ℝ) = (⌈W⌉₊ : ℝ) * (1 / (d : ℝ)) := by ring
        _ ≤ (⌈W⌉₊ : ℝ) * (1 / W) := mul_le_mul_of_nonneg_left h1d hzpos.le
        _ = (⌈W⌉₊ : ℝ) / W := by ring
    rw [h1, hsel, zero_sub, abs_neg, abs_mul]
    calc |(ArithmeticFunction.moebius d : ℝ)| * |Real.log ((⌈W⌉₊ : ℝ) / (d : ℝ))|
        = |(ArithmeticFunction.moebius d : ℝ)| * Real.log ((⌈W⌉₊ : ℝ) / (d : ℝ)) := by
          rw [abs_of_nonneg hlogdz]
      _ ≤ 1 * Real.log ((⌈W⌉₊ : ℝ) / W) := mul_le_mul hmu hle2 hlogdz (by norm_num)
      _ = Real.log ((⌈W⌉₊ : ℝ) / W) := one_mul _

end Work.ZeroDensity.LogFree
