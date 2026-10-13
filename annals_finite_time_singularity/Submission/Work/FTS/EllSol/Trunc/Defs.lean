/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# A smooth cutoff used to reduce `flat2DAgmon` to its compactly-supported ("nice") case

`Work.FTS.EllSol.flat2DAgmon` is proved by first establishing the special case of data with
*uniformly compact support in `t`* (`Work.FTS.EllSol.FlatFT.flat2DAgmonNiceB`, packaged here as
`NiceBound`), and then passing to general data `g` by cutting off in `t`:
`g_N := (fun t θ => g t θ * chi N t)` with `chi N t = tk (t / N)`.

`tk t := Real.smoothTransition (2 - t^2)` is smooth, `0 ≤ tk ≤ 1`, `tk t = 1` for `|t| ≤ 1` and
`tk t = 0` for `2 ≤ |t|`; hence `chi N` is `1` on `[-N,N]`, `0` off `[-2N,2N]` (for `N ≥ 0`),
and `deriv (chi N) t = deriv tk (t/N)/N` — so the truncation errors all carry the factor
`1/N`.

This file only sets up the cutoff, the elementary pointwise algebra, and the *statement* of the
"nice" base case; the analytic passage is in `Trunc.Pass`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.FlatFT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The basic smooth cutoff: `= 1` for `|t| ≤ 1`, `= 0` for `2 ≤ |t|`. -/
def tk (t : ℝ) : ℝ := Real.smoothTransition (2 - t ^ 2)

theorem tk_contDiff (n : ℕ) : ContDiff ℝ n tk := by
  have h1 : ContDiff ℝ n (fun t : ℝ => 2 - t ^ 2) :=
    contDiff_const.sub (contDiff_id.pow 2)
  have h2 : ContDiff ℝ n (Real.smoothTransition : ℝ → ℝ) :=
    Real.smoothTransition.contDiff (n := (n : ℕ∞))
  exact h2.comp h1

theorem tk_nonneg (t : ℝ) : 0 ≤ tk t := Real.smoothTransition.nonneg _

theorem tk_le_one (t : ℝ) : tk t ≤ 1 := Real.smoothTransition.le_one _

/-- `tk t = 1` whenever `|t| ≤ 1`. -/
theorem tk_eq_one {t : ℝ} (h : |t| ≤ 1) : tk t = 1 := by
  unfold tk
  apply Real.smoothTransition.one_of_one_le
  have h2 : t ^ 2 ≤ 1 := by
    have := abs_le.mp h
    nlinarith [this.1, this.2]
  linarith

/-- `tk t = 0` whenever `2 ≤ |t|`. -/
theorem tk_eq_zero {t : ℝ} (h : 2 ≤ |t|) : tk t = 0 := by
  unfold tk
  apply Real.smoothTransition.zero_of_nonpos
  have h2 : (4:ℝ) ≤ t ^ 2 := by
    have h3 := sq_abs t
    nlinarith [abs_nonneg t, h, h3]
  linarith

/-- The cutoff at scale `N`: `chi N t = tk (t/N)`. -/
def chi (N : ℝ) (t : ℝ) : ℝ := tk (t / N)

theorem chi_contDiff (n : ℕ) (N : ℝ) : ContDiff ℝ n (chi N) := by
  have h1 : ContDiff ℝ n (fun t : ℝ => t / N) := contDiff_id.div_const N
  have h2 : ContDiff ℝ n (tk : ℝ → ℝ) := tk_contDiff n
  exact h2.comp h1

theorem chi_nonneg (N t : ℝ) : 0 ≤ chi N t := tk_nonneg _

theorem chi_le_one (N t : ℝ) : chi N t ≤ 1 := tk_le_one _

/-- For `N > 0` the cutoff is `1` on `[-N,N]`. -/
theorem chi_eq_one {N t : ℝ} (hN : 0 < N) (h : |t| ≤ N) : chi N t = 1 := by
  unfold chi
  apply tk_eq_one
  rw [abs_div, abs_of_pos hN]
  exact (div_le_one hN).mpr h

/-- For `N > 0` the cutoff vanishes off `[-2N,2N]`. -/
theorem chi_eq_zero {N t : ℝ} (hN : 0 < N) (h : 2 * N ≤ |t|) : chi N t = 0 := by
  unfold chi
  apply tk_eq_zero
  rw [abs_div, abs_of_pos hN]
  rw [le_div_iff₀ hN]
  linarith

/-- The derivative of the cutoff at scale `N`. -/
theorem deriv_chi_eq (N t : ℝ) : deriv (chi N) t = deriv tk (t / N) / N := by
  rw [show chi N = fun s : ℝ => tk (s / N) from rfl]
  change deriv (tk ∘ fun s : ℝ => s / N) t = deriv tk (t / N) / N
  rw [deriv_comp]
  · rw [deriv_div_const, deriv_id'', div_eq_mul_inv]
    ring
  · exact (tk_contDiff 1).differentiable (by norm_num) (t / N)
  · exact differentiableAt_id.div_const N

/-- `deriv tk` is bounded. -/
theorem exists_bound_deriv_tk : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv tk t| ≤ K := by
  have hcont : Continuous (deriv tk) := (tk_contDiff 1).continuous_deriv (by norm_num)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
  · exact le_trans (hK t ht) (le_max_left _ _)
  · have h0 : deriv tk t = 0 := by
      have hev : tk =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        have hopen : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
        have hmem : t ∈ {s : ℝ | 2 < |s|} := by
          rw [Set.mem_setOf_eq]
          exact lt_of_not_ge fun hle => ht (Set.mem_Icc.mpr (abs_le.mp hle))
        filter_upwards [hopen.mem_nhds hmem] with s hs
        exact tk_eq_zero (le_of_lt hs)
      rw [hev.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- The bound on the derivative of the cutoff at scale `N`. -/
theorem abs_deriv_chi_le {K N : ℝ} (hK : ∀ t : ℝ, |deriv tk t| ≤ K) (hN : 0 < N) (t : ℝ) :
    |deriv (chi N) t| ≤ K / N := by
  rw [deriv_chi_eq, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right (hK (t / N)) (le_of_lt hN)

/-! ## Elementary pointwise algebra -/

/-- `(a+b)² ≤ (1+δ)a² + (1+1/δ)b²`. -/
theorem sq_add_le (δ : ℝ) (hδ : 0 < δ) (a b : ℝ) :
    (a + b) ^ 2 ≤ (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 := by
  have hkey : 0 ≤ (1 / δ) * (δ * a - b) ^ 2 := by positivity
  have hexp : (1 / δ) * (δ * a - b) ^ 2
      = (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 - (a + b) ^ 2 := by
    field_simp
    ring
  linarith [hkey, hexp.symm.le, hexp.le]

/-- `(1-δ)a² - (1/δ)b² ≤ (a+b)²`. -/
theorem le_sq_add (δ : ℝ) (hδ : 0 < δ) (a b : ℝ) :
    (1 - δ) * a ^ 2 - (1 / δ) * b ^ 2 ≤ (a + b) ^ 2 := by
  have hkey : 0 ≤ (1 / δ) * (δ * a + b) ^ 2 + b ^ 2 := by positivity
  have hexp : (1 / δ) * (δ * a + b) ^ 2 + b ^ 2
      = (a + b) ^ 2 - ((1 - δ) * a ^ 2 - (1 / δ) * b ^ 2) := by
    field_simp
    ring
  linarith [hkey, hexp.symm.le, hexp.le]

/-- `(a+b+c)² ≤ 3(a²+b²+c²)` (Cauchy–Schwarz in `ℝ³`). -/
theorem three_sq_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-! ## The "nice" (compactly supported) case, as a predicate

`NiceBound C` is exactly the conclusion of `Work.FTS.EllSol.FlatFT.flat2DAgmonNiceB` (in
product-integral form): the `flat2DAgmon` inequality with constant `C` for data of class
`NiceFlat`.  `flat2DAgmon` is then obtained by `flat2DAgmon_of_nice`, which passes from
`NiceBound C₀` to the general data of the target. -/

/-- The `flat2DAgmon` inequality with constant `C` for `NiceFlat` (uniformly compactly supported
in `t`) data.  This is the conclusion of `flat2DAgmonNiceB`. -/
def NiceBound (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → FlatFT.NiceFlat g →
    IntegrableOn (fun p : ℝ × ℝ => (Spaces.pz (Spaces.pz g) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Spaces.pth (Spaces.pth g) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Spaces.pz g p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Spaces.pz (Spaces.pth g) p.1 p.2) ^ 2 * FlatFT.wA α p.2)
      (Set.univ ×ˢ Spaces.Iθ) ∧
    (∫ p in Set.univ ×ˢ Spaces.Iθ, (Spaces.pz (Spaces.pth g) p.1 p.2) ^ 2 * FlatFT.wA α p.2)
      ≤ C * ((∫ p in Set.univ ×ˢ Spaces.Iθ, (Spaces.pz g p.1 p.2) ^ 2 * FlatFT.wE p.2)
          + Real.sqrt ((∫ p in Set.univ ×ˢ Spaces.Iθ,
                (Spaces.pz (Spaces.pz g) p.1 p.2) ^ 2 * FlatFT.wE p.2)
              * (∫ p in Set.univ ×ˢ Spaces.Iθ,
                (Spaces.pth (Spaces.pth g) p.1 p.2) ^ 2 * FlatFT.wE p.2)))

end

end Work.FTS.EllSol.Trunc
