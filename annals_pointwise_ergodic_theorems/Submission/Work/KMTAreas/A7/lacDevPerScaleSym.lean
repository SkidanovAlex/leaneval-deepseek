/-
# The per-scale symbol identity of the deviation kernel

`Work.KMTAreas.A7.devKern K σ n` is the kernel of the `n`-th deviation operator
`devOp K σ n = bumpOp K σ n - (∫K) · triSmooth σ n`, i.e.

  `devKern K σ n j = (1/σ n) K (j/σ n) - (∫K) · triKernel (lacLev σ n) j`.

This file identifies its symbol (the `ℤ`-sum against the character `chr j θ = e^{2πijθ}` of
`Work.KMTAreas.ADev`) as the deviation symbol
`bumpSym K (σ n) θ - (∫K) · triSym (lacLev σ n) θ`:

* the bump part is the modulated Poisson summation `bumpSym_eq_tsum`
  (`∑'_j (1/m) K (j/m) · e^{2πijθ} = ∑'_k 𝓕K (m (k - θ))`);
* the triangular part is a *finite* sum, since `triKernel (lacLev σ n)` is supported in
  `[-2^{lacLev σ n}, 2^{lacLev σ n}]` and agrees there with `Work.KMTAreas.ADev.triK`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LacDevBasics

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal BigOperators FourierTransform

noncomputable section

/-- The triangular kernel times the character, summed over `ℤ`, is the triangular symbol
`Work.KMTAreas.ADev.triSym`: the sum is finite because `triKernel L` vanishes off
`[-2^L, 2^L]`, where it agrees with `ADev.triK`. -/
lemma triKernel_sym_eq_tsum (L : ℕ) (θ : ℝ) :
    (∑' z : ℤ, ((Work.Analysis.Hilbert.triKernel L z : ℝ) : ℂ)
        * Work.KMTAreas.ADev.chr z θ)
      = Work.KMTAreas.ADev.triSym L θ := by
  rw [tsum_eq_sum (s := Finset.Icc (-((2 : ℤ) ^ L)) ((2 : ℤ) ^ L))
    (fun z hz => by rw [triKernel_eq_zero_of_notMem L hz]; simp)]
  rfl

/-- **The symbol of the deviation kernel at a single scale.**  The `ℤ`-sum of the deviation kernel
against the character is the deviation symbol `bumpSym K (σ n) θ - (∫K) · triSym (lacLev σ n) θ`. -/
theorem lacDevSymK_eq_tsum (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (n : ℕ) (θ : ℝ) :
    (∑' j : ℤ, devKern K σ n j * Work.KMTAreas.ADev.chr j θ)
      = Work.KMTAreas.ADev.bumpSym K (σ n) θ
        - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ := by
  -- summability of the two parts against the character
  have hb : Summable (fun z : ℤ => bumpKern K σ n z * Work.KMTAreas.ADev.chr z θ) := by
    refine Summable.of_norm_bounded (f := fun z : ℤ =>
        bumpKern K σ n z * Work.KMTAreas.ADev.chr z θ)
      (g := fun z : ℤ => ‖bumpKern K σ n z‖) (bumpKern_summable K σ hσ1 n).norm ?_
    intro z
    rw [norm_mul, Work.KMTAreas.ADev.norm_chr, mul_one]
  have ht : Summable (fun z : ℤ => (lacConst K
      * ((Work.Analysis.Hilbert.triKernel (lacLev σ n) z : ℝ) : ℂ))
        * Work.KMTAreas.ADev.chr z θ) := by
    refine summable_of_ne_finset_zero
      (s := Finset.Icc (-((2 : ℤ) ^ (lacLev σ n))) ((2 : ℤ) ^ (lacLev σ n))) ?_
    intro z hz
    rw [triKernel_eq_zero_of_notMem (lacLev σ n) hz]
    simp
  -- the bump part is the modulated Poisson summation
  have hbump : (∑' z : ℤ, bumpKern K σ n z * Work.KMTAreas.ADev.chr z θ)
      = Work.KMTAreas.ADev.bumpSym K (σ n) θ := by
    rw [← Work.KMTAreas.ADev.bumpSym_eq_tsum K (σ n) (hσ1 n) θ]
    refine tsum_congr fun z => ?_
    simp [Work.KMTAreas.ADev.sampKern, bumpKern]
  -- the triangular part is a finite character sum
  have htri : (∑' z : ℤ, (lacConst K
      * ((Work.Analysis.Hilbert.triKernel (lacLev σ n) z : ℝ) : ℂ))
        * Work.KMTAreas.ADev.chr z θ)
      = lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ := by
    rw [show (∑' z : ℤ, (lacConst K
        * ((Work.Analysis.Hilbert.triKernel (lacLev σ n) z : ℝ) : ℂ))
          * Work.KMTAreas.ADev.chr z θ)
        = ∑' z : ℤ, lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLev σ n) z : ℝ) : ℂ)
            * Work.KMTAreas.ADev.chr z θ) from tsum_congr fun z => by ring]
    rw [tsum_mul_left, triKernel_sym_eq_tsum]
  -- split the deviation kernel into its two parts
  rw [show (∑' z : ℤ, devKern K σ n z * Work.KMTAreas.ADev.chr z θ)
      = (∑' z : ℤ, bumpKern K σ n z * Work.KMTAreas.ADev.chr z θ)
        - (∑' z : ℤ, (lacConst K
          * ((Work.Analysis.Hilbert.triKernel (lacLev σ n) z : ℝ) : ℂ))
            * Work.KMTAreas.ADev.chr z θ) from by
      rw [← Summable.tsum_sub hb ht]
      refine tsum_congr fun z => ?_
      rw [devKern]
      ring]
  rw [hbump, htri]

/-- **The per-scale deviation symbol identity** (the form requested for the lacunary bump-dilation
square function): the symbol of `devKern K σ n` is
`bumpSym K (σ n) θ - (∫K) · triSym (lacLev σ n) θ`. -/
theorem lacDevPerScaleSym (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (n : ℕ) (θ : ℝ) :
    (∑' j : ℤ, Work.KMTAreas.A7.devKern K σ n j * Work.KMTAreas.ADev.chr j θ)
      = Work.KMTAreas.ADev.bumpSym K (σ n) θ
        - Work.KMTAreas.A7.lacConst K * Work.KMTAreas.ADev.triSym (Work.KMTAreas.A7.lacLev σ n) θ :=
  lacDevSymK_eq_tsum K σ hσ1 n θ

end

end Work.KMTAreas.A7
