import Mathlib
import Submission.Work.KMTAreas.A7.exists_Lnat_le_of_bad

/-!
# The bad-scale squeeze for the `(2,2,1)` model tuple

The `MdlLpH` chapter splits the scales of the model slice according to whether the `l₁`-level is
"bad".  Here we prove that badness *bounds* `l₁` outright, by the same squeezing argument that
bounds the bad scales of the linear lacunary variational estimate
(`Work.KMTAreas.A7Hi.BadPart`).

Suppose `N₀` is admissible for the multi-index `(max l₁ l₂, 0, k₂)`, i.e.
`l₁ ≤ l_{(N₀)} = C₀ · LogLog N₀` (`inIndexSet`), and the "bad" inequality

`Log N₀ < Cρ · 2^{ρ l₁}`

holds.  Writing `M = Log N₀ = log₂ (max N₀ 2)` and using

* `l₁ ≤ C₀ LogLog N₀ ≤ C₀ log₂ (M + 2)` (the iterated logarithm is dominated by the logarithm,
  `Work.KMTAreas.A7.elb_natlog_add_two_le_logb`),
* `2^{ρ l₁} ≤ 2^{ρ l_{(N₀)}} ≤ √(M + 2)` (the exponential gain of the height scale,
  `Work.KMTAreas.A7.two_rpow_heightScale_le_sqrt`, valid because `ρ C₀ ≤ 1/2`),

we get `M < Cρ √(M+2)`.  With `x = √(M+2)` this reads `x² - Cρ x - 2 < 0`, which forces
`x ≤ Cρ + 2` (if `x > Cρ + 2` then `x - Cρ > 2` and `x > 2`, so `x(x - Cρ) > 4 > 2`, a
contradiction).  Hence `M + 2 ≤ (Cρ + 2)²` and

`l₁ ≤ C₀ log₂ (M + 2) = 2 C₀ log₂ x ≤ 2 C₀ log₂ (Cρ + 2)`,

which is the statement.  In particular the set of admissible bad scales is bounded by a constant
depending only on `ρ`, `C₀`, `Cρ`, so it can be discarded at the cost of a constant.
-/

namespace Work.KMTPlan.A6.MdlLpH

open Work.Analysis.EndVar

/-- **The bad-scale squeeze of the `MdlLpH` chapter.**  If `N₀` is admissible for
`(max l₁ l₂, 0, k₂)` and `Log N₀ < Cρ · 2^{ρ l₁}` then `l₁ ≤ 2 C₀ log₂ (Cρ + 2)`. -/
theorem mdlCore_bad_l_bound (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Cρ : ℝ)
    (N₀ l₁ l₂ k₂ : ℕ) (hρC : ρ * (C₀ : ℝ) ≤ 1 / 2)
    (hin : Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) 0 (k₂ : ℤ) N₀)
    (hbad : ((Work.Analysis.EndVar.logN N₀ : ℤ) : ℝ) < Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) :
    (l₁ : ℝ) ≤ 2 * (C₀ : ℝ) * Real.logb 2 (Cρ + 2) := by
  let M : ℕ := Nat.log 2 (max N₀ 2)
  let x : ℝ := Real.sqrt ((M : ℝ) + 2)
  -- `hbad` in terms of `M`
  have hbad' : (M : ℝ) < Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by
    simpa [M, Work.Analysis.EndVar.logN] using hbad
  -- `M ≥ 1`
  have hM1 : 1 ≤ M := by
    show 1 ≤ Nat.log 2 (max N₀ 2)
    have h : 0 < Nat.log 2 (max N₀ 2) :=
      Nat.log_pos_iff.mpr ⟨le_max_right N₀ 2, by norm_num⟩
    omega
  -- hence `Cρ > 0`
  have hxpow : 0 < (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hCρpos : 0 < Cρ := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have : (0 : ℕ) < M := by omega
      exact_mod_cast this
    exact pos_of_mul_pos_left (lt_of_lt_of_le hMpos (le_of_lt hbad')) hxpow.le
  -- admissibility: `l₁ ≤ l_{(N₀)}`
  have hl1Z : (l₁ : ℤ) ≤ (Work.Analysis.EndVar.heightScale C₀ N₀ : ℤ) :=
    le_trans (le_max_left _ _) hin.1
  have hl1R : (l₁ : ℝ) ≤ (Work.Analysis.EndVar.heightScale C₀ N₀ : ℝ) := by
    exact_mod_cast hl1Z
  -- the exponential is at most `x = √(M+2)`
  have hrpow : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ x := by
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hl1R hρ.le)).trans ?_
    exact Work.KMTAreas.A7.two_rpow_heightScale_le_sqrt (ρ := ρ) (C₀ := C₀) hρ hρC N₀
  have hxpos : 0 < x := by
    show 0 < Real.sqrt ((M : ℝ) + 2)
    rw [Real.sqrt_pos]
    positivity
  have hx2 : x ^ 2 = (M : ℝ) + 2 := by
    show Real.sqrt ((M : ℝ) + 2) ^ 2 = (M : ℝ) + 2
    exact Real.sq_sqrt (by positivity)
  -- the squeeze: `x ≤ Cρ + 2`
  have hxC : x ≤ Cρ + 2 := by
    by_contra hcon
    push_neg at hcon
    have hxineq : x ^ 2 < Cρ * x + 2 := by
      have h : (M : ℝ) < Cρ * x :=
        lt_of_lt_of_le hbad' (mul_le_mul_of_nonneg_left hrpow hCρpos.le)
      linarith [hx2, h]
    have h1 : 2 < x - Cρ := by linarith
    have h2 : 2 < x := by linarith
    have h3 : 2 * x < (x - Cρ) * x := mul_lt_mul_of_pos_right h1 hxpos
    have h4 : (x - Cρ) * x < 2 := by nlinarith [hxineq]
    have h5 : 4 < 2 * x := by linarith
    linarith [h3, h4, h5]
  -- `LogLog N₀ ≤ log₂ (M + 2)`
  have hlogLog : ((Work.Analysis.EndVar.logLogN N₀ : ℕ) : ℝ)
      ≤ Real.logb 2 ((M : ℝ) + 2) := by
    have h1 : Work.Analysis.EndVar.logLogN N₀ = Nat.log 2 (M + 2) := by
      show Nat.log 2 (Nat.log 2 (max N₀ 2) + 2) = Nat.log 2 (M + 2)
      rfl
    rw [h1]
    exact Work.KMTAreas.A7.elb_natlog_add_two_le_logb M
  -- `l₁ ≤ C₀ log₂ (M + 2)`
  have hl1_le : (l₁ : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) := by
    calc (l₁ : ℝ) ≤ (Work.Analysis.EndVar.heightScale C₀ N₀ : ℝ) := hl1R
      _ = (C₀ : ℝ) * ((Work.Analysis.EndVar.logLogN N₀ : ℕ) : ℝ) := by
            simp only [Work.Analysis.EndVar.heightScale, Nat.cast_mul]
      _ ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hlogLog (by positivity)
  -- `log₂ (M + 2) = 2 log₂ x ≤ 2 log₂ (Cρ + 2)`
  have hlogb_eq : Real.logb 2 ((M : ℝ) + 2) = 2 * Real.logb 2 x := by
    rw [← hx2, Real.logb_pow]
    norm_num
  have hlogb_mono : Real.logb 2 x ≤ Real.logb 2 (Cρ + 2) :=
    Real.logb_le_logb_of_le (by norm_num) hxpos hxC
  calc (l₁ : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) := hl1_le
    _ = (C₀ : ℝ) * (2 * Real.logb 2 x) := by rw [hlogb_eq]
    _ ≤ (C₀ : ℝ) * (2 * Real.logb 2 (Cρ + 2)) :=
          mul_le_mul_of_nonneg_left (by linarith [hlogb_mono]) (by positivity)
    _ = 2 * (C₀ : ℝ) * Real.logb 2 (Cρ + 2) := by ring

end Work.KMTPlan.A6.MdlLpH
