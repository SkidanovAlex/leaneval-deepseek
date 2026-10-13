import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.monoCount_bounds

/-!
# The slack `λ = N₁/m - 1` of the `v2` parameter choice is at least `8g+8`

The Siegel cardinality condition of the interpolation step is `N₁ ≥ (8g+9)·m`, where

* `m = monoCount μ b` is the number of rows (the number of exponent vectors of degree `≤ b`
  in `μ` variables), and
* `N₁ = monoCount (μ+1) d` is the number of columns, with `d = dV μ g b`.

The degree `d` is chosen precisely so that `d + 1` beats the `(μ+1)`-st root of
`RR μ g b = (μ+1)! · (8g+9) · (b+1)^μ`.  Hence `(d+1)^(μ+1) ≥ RR`, and the counting
hypothesis `(d+1)^n ≤ n! · monoCount n d` gives

`(μ+1)! · N₁ ≥ (d+1)^(μ+1) ≥ (μ+1)! · (8g+9) · (b+1)^μ`,

whence after cancelling `(μ+1)!` and using the elementary *upper* bound
`monoCount μ b ≤ (b+1)^μ` we get `N₁ ≥ (8g+9)·m`.  Dividing by `m` and subtracting `1`
yields `8g+8 ≤ λ`.

This is an arithmetic lemma about the explicit parameters `bV, dV, N1V, mV, lamV`
of `Work.WilkiesH.Interp.V2Params`; the analytic input is confined to the hypothesis
`hcount` on `monoCount`.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Interp.V2lam

open Work.WilkiesH

/-- `dV μ g b + 1` dominates the `(μ+1)`-st root of `RR μ g b = (μ+1)!·(8g+9)·(b+1)^μ`,
since `dV μ g b = ⌈RR^{1/(μ+1)}⌉ + 1`. -/
lemma RR_le_succ_dV_pow (μ g b : ℕ) :
    Interp.RR μ g b ≤ (Interp.dV μ g b + 1) ^ (μ + 1) := by
  have hRR : (0 : ℝ) ≤ (Interp.RR μ g b : ℝ) := Nat.cast_nonneg _
  set x : ℝ := (Interp.RR μ g b : ℝ) ^ (1 / ((μ : ℝ) + 1)) with hxdef
  -- `x` is the `(μ+1)`-st root of `RR μ g b`
  have hxpow : x ^ (μ + 1) = (Interp.RR μ g b : ℝ) := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hRR]
    have hmul : (1 / ((μ : ℝ) + 1)) * ((μ + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [hmul, Real.rpow_one]
  -- the cast of `dV μ g b + 1` is `⌈x⌉ + 2`
  have hdV : ((Interp.dV μ g b + 1 : ℕ) : ℝ) = (Nat.ceil x : ℝ) + 2 := by
    simp only [Interp.dV]
    rw [← hxdef]
    push_cast
    ring
  have hx_le : x ≤ ((Interp.dV μ g b + 1 : ℕ) : ℝ) := by
    rw [hdV]
    linarith [Nat.le_ceil x]
  have hpow : (Interp.RR μ g b : ℝ) ≤ (((Interp.dV μ g b + 1) ^ (μ + 1) : ℕ) : ℝ) := by
    rw [← hxpow, Nat.cast_pow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hRR _) hx_le (μ + 1)
  exact_mod_cast hpow

theorem lamV_ge (μ g H : ℕ)
    (hcount : ∀ n d : ℕ, (d + 1) ^ n ≤ n.factorial * Work.WilkiesH.monoCount n d) :
    8 * g + 8 ≤ Work.WilkiesH.Interp.lamV μ g H := by
  -- the counting hypothesis at `(μ+1, dV μ g (bV μ g H))`
  have h1 : (Interp.dV μ g (Interp.bV μ g H) + 1) ^ (μ + 1)
      ≤ (μ + 1).factorial *
        Work.WilkiesH.monoCount (μ + 1) (Interp.dV μ g (Interp.bV μ g H)) :=
    hcount (μ + 1) (Interp.dV μ g (Interp.bV μ g H))
  -- the elementary upper bound for the number of rows
  have h3 : Work.WilkiesH.monoCount μ (Interp.bV μ g H) ≤ (Interp.bV μ g H + 1) ^ μ :=
    (Interp.monoCount_bounds μ (Interp.bV μ g H) 0).1
  -- `RR μ g b = (μ+1)! · ((8g+9) · (b+1)^μ)`
  have hRR' : Interp.RR μ g (Interp.bV μ g H) =
      (μ + 1).factorial * ((8 * g + 9) * (Interp.bV μ g H + 1) ^ μ) := by
    simp only [Interp.RR]; ring
  -- `(μ+1)! · ((8g+9)·(b+1)^μ) ≤ (μ+1)! · N₁`
  have hcomb : (μ + 1).factorial * ((8 * g + 9) * (Interp.bV μ g H + 1) ^ μ)
      ≤ (μ + 1).factorial *
        Work.WilkiesH.monoCount (μ + 1) (Interp.dV μ g (Interp.bV μ g H)) := by
    rw [← hRR']
    exact (RR_le_succ_dV_pow μ g (Interp.bV μ g H)).trans h1
  -- cancel `(μ+1)!`
  have hcancel : (8 * g + 9) * (Interp.bV μ g H + 1) ^ μ
      ≤ Work.WilkiesH.monoCount (μ + 1) (Interp.dV μ g (Interp.bV μ g H)) :=
    Nat.le_of_mul_le_mul_left hcomb (Nat.factorial_pos (μ + 1))
  -- insert the upper bound on the row count
  have hkey : (8 * g + 9) * Work.WilkiesH.monoCount μ (Interp.bV μ g H)
      ≤ Work.WilkiesH.monoCount (μ + 1) (Interp.dV μ g (Interp.bV μ g H)) :=
    (Nat.mul_le_mul_left _ h3).trans hcancel
  have hmpos : 0 < Work.WilkiesH.monoCount μ (Interp.bV μ g H) :=
    Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, by simp⟩⟩
  -- division step
  have hdiv : 8 * g + 9 ≤
      Work.WilkiesH.monoCount (μ + 1) (Interp.dV μ g (Interp.bV μ g H)) /
        Work.WilkiesH.monoCount μ (Interp.bV μ g H) :=
    (Nat.le_div_iff_mul_le hmpos).mpr hkey
  have hlam : Interp.lamV μ g H =
      Work.WilkiesH.monoCount (μ + 1) (Interp.dV μ g (Interp.bV μ g H)) /
        Work.WilkiesH.monoCount μ (Interp.bV μ g H) - 1 := by
    simp only [Interp.lamV, Interp.N1V, Interp.mV]
  rw [hlam]
  omega

end Work.WilkiesH.Interp.V2lam
