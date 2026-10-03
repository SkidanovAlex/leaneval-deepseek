/-
# The modulated lacunary blocks of `Work.KMTAreas.A7.lacunaryModulatedDiffs_mikhlin`

This module fixes the vocabulary of `Work.KMTAreas.A7.lacunaryModulatedDiffs_mikhlin`, the
Mikhlin bound for *lacunary modulated differences*: the symbols

  `ξ ↦ ∑_{n < K} ε n · (Φ (σ (n+1) ξ) e (λ (n+1) ξ) - Φ (σ n ξ) e (λ n ξ))`

built from a `Lam`-lacunary scale sequence `σ` (`σ (n+1) ≥ Lam σ n`, `Lam > 1`), a modulation
`λ` with `|λ n| ≤ cbar σ n` and `|λ (n+1) - λ n| ≤ cbar σ n`, and a `C²` bump `Φ` which is
*flat* near the origin (`Φ = Φ 0` on `[-del, del]`) and vanishes off `[-1,1]`.

The single modulated block is

* `modBlock Φ s l = fun ξ => Φ (s ξ) · e (l ξ)`, with

and `modBlockD`, `modBlockD2` are its first and second derivatives in closed form:

* `modBlockD Φ s l ξ = s (deriv Φ) (s ξ) e (l ξ) + Φ (s ξ) · ((2 π i l) e (l ξ))`,
* `modBlockD2 Φ s l ξ = s (s (iteratedDeriv 2 Φ) (s ξ)) e (l ξ)
      + 2 · s (deriv Φ) (s ξ) · ((2 π i l) e (l ξ)) + Φ (s ξ) · ((2 π i l)² e (l ξ))`.

The file also collects the elementary estimates on the character `e` and the elementary fact that
a lacunary `ℕ`-indexed scale sequence gives a `LacunaryFam` on `Finset.range K` (so that the
already proved summation bound `Work.KMTAreas.A7.lacunarySum_norm_bound` applies).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux
import Submission.Work.KMTAreas.A7.lacunarySum_norm_bound

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped BigOperators

noncomputable section

/-! ## The modulated blocks -/

/-- The modulated block `ξ ↦ Φ (s ξ) · e (l ξ)`. -/
def modBlock (Φ : ℝ → ℂ) (s l : ℝ) : ℝ → ℂ := fun ξ => Φ (s * ξ) * ee (l * ξ)

/-- The first derivative of the modulated block, in closed form. -/
def modBlockD (Φ : ℝ → ℂ) (s l : ℝ) : ℝ → ℂ := fun ξ =>
  s * deriv Φ (s * ξ) * ee (l * ξ)
    + Φ (s * ξ) * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ))

/-- The second derivative of the modulated block, in closed form. -/
def modBlockD2 (Φ : ℝ → ℂ) (s l : ℝ) : ℝ → ℂ := fun ξ =>
  (s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)
    + (s * deriv Φ (s * ξ)) * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ))
    + (s * deriv Φ (s * ξ)) * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ))
    + Φ (s * ξ) *
        ((2 * Real.pi * Complex.I * (l : ℂ)) * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))

/-! ## Elementary estimates on the character -/

/-- The character `e` has modulus one. -/
lemma norm_ee_eq_one (x : ℝ) : ‖ee x‖ = 1 := by
  have h : ee x = Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ)) : ℂ)) := by
    simp only [ee]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

/-- `‖e x - 1‖ ≤ 2 π |x|`. -/
lemma norm_ee_sub_one_le (x : ℝ) : ‖ee x - 1‖ ≤ 2 * Real.pi * |x| := by
  have h1 : ee x = Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ)) : ℂ)) := by
    simp only [ee]; congr 1; push_cast; ring
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  have h2 : ‖(2 * Real.sin (Real.pi * x) : ℝ)‖ = 2 * |Real.sin (Real.pi * x)| := by
    rw [Real.norm_eq_abs, abs_mul]
    norm_num
  rw [h2]
  calc 2 * |Real.sin (Real.pi * x)| ≤ 2 * |Real.pi * x| := by
        have h := Real.abs_sin_le_abs (x := Real.pi * x)
        have h3 : (0:ℝ) ≤ |Real.pi * x| := abs_nonneg _
        linarith
    _ = 2 * Real.pi * |x| := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

/-- `‖e a - e b‖ ≤ 2 π |a - b|`. -/
lemma norm_ee_sub_le (a b : ℝ) : ‖ee a - ee b‖ ≤ 2 * Real.pi * |a - b| := by
  have hsplit : ee a = ee b * ee (a - b) := by
    simp only [ee]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h : ee a - ee b = ee b * (ee (a - b) - 1) := by rw [hsplit]; ring
  rw [h, norm_mul, norm_ee_eq_one, one_mul]
  exact norm_ee_sub_one_le (a - b)

/-- `‖e a - e b‖ ≤ 2`. -/
lemma norm_ee_sub_le_two (a b : ℝ) : ‖ee a - ee b‖ ≤ 2 := by
  have hsplit : ee a = ee b * ee (a - b) := by
    simp only [ee]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h : ee a - ee b = ee b * (ee (a - b) - 1) := by rw [hsplit]; ring
  rw [h, norm_mul, norm_ee_eq_one, one_mul]
  calc ‖ee (a - b) - 1‖ ≤ ‖ee (a - b)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_ee_eq_one, norm_one]; norm_num

/-! ## Lacunarity of an `ℕ`-indexed scale sequence -/

/-- A `Lam`-lacunary `ℕ`-indexed scale sequence gives a `LacunaryFam` on `Finset.range K`. -/
lemma lacunaryFam_range {Lam : ℝ} (hLam : 1 < Lam) {sigma : ℕ → ℝ} (hpos : ∀ n, 0 < sigma n)
    (hstep : ∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) (K : ℕ) :
    Work.Analysis.CzShift.LacunaryFam Lam (Finset.range K) sigma := by
  have hmono : StrictMono sigma := by
    refine strictMono_nat_of_lt_succ (fun n => ?_)
    have h : sigma n < Lam * sigma n := by nlinarith [hpos n, hLam]
    linarith [hstep n]
  refine ⟨fun i _ => hpos i, fun i _ j _ hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · rw [min_eq_left (hmono.monotone h.le), max_eq_right (hmono.monotone h.le)]
    calc Lam * sigma i ≤ sigma (i + 1) := hstep i
      _ ≤ sigma j := hmono.monotone (Nat.succ_le_of_lt h)
  · rw [min_eq_right (hmono.monotone h.le), max_eq_left (hmono.monotone h.le)]
    calc Lam * sigma j ≤ sigma (j + 1) := hstep j
      _ ≤ sigma i := hmono.monotone (Nat.succ_le_of_lt h)

end

end Work.KMTAreas.A7
