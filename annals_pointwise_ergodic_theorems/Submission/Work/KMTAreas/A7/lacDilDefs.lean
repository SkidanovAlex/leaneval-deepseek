/-
# The `ℤ`-model lacunary bump dilation variational estimate: vocabulary

This module fixes the objects of `Work.KMTAreas.A7.lacunaryBumpDilationVar` — the discrete
model lacunary variational estimate for a family of low-pass (bump) convolution operators on
`ℤ` — in the shape in which the two halves of the proof are stated.

* `lacLev σ n = ⌊log₂ (max (σ n) 2)⌋` — the *dyadic level* of the scale `σ n`.  For a
  `2`-lacunary `σ` it is monotone (indeed strictly increasing), so the dyadic scales
  `2 ^ lacLev σ n` are nested; and `σ n / 2 ≤ 2 ^ lacLev σ n ≤ 2 * σ n`, so the dyadic smoothing
  at level `lacLev σ n` is at the same scale as the bump at scale `σ n`.

* `lacConst K = ∫ K` — the mean of the Schwartz kernel; the low-frequency limit of the multiplier
  `m_σ(θ) = Σ_j (1/σ) K (j/σ) e^{-2πi j θ}` is `lacConst K`.

* `bumpKern K σ n j = (1/σ n) K (j/σ n)` — the *sampled kernel* of the `n`-th operator,
* `bumpOp K σ n f x = Σ'_j (1/σ n) K (j/σ n) f (x - j)` — the `n`-th operator itself.

* `triSmooth σ n f x = triConv (lacLev σ n) f x` — the *triangular (Fejér) smoothing* at the
  dyadic level `lacLev σ n` (the corpus's `Work.Analysis.Hilbert.triConv`: the convolution with the
  triangular kernel `triKernel`, a *finitely supported* kernel).  It is simultaneously

  - a **convolution** with a finitely supported kernel (hence its difference with `bumpOp` is
    again a kernel convolution), and
  - the **average over a complete period of shifts** of the lattice conditional expectations
    `latticeExp (lacLev σ n) τ` (the corpus's `lattice_exp_average`), hence the family
    `n ↦ triSmooth σ n f` inherits Lépingle's variational inequality from the reverse martingale
    `n ↦ latticeExp (lacLev σ n) τ f`, uniformly in the shift `τ`.

* `devOp K σ n f x = bumpOp K σ n f x - lacConst K * triSmooth σ n f x` — the *deviation* of the
  bump from its mean times the triangular smoothing, whose kernel
  `devKern K σ n j = bumpKern K σ n j - lacConst K * triKernel (lacLev σ n) j` is a *band-pass*
  kernel at scale `2 ^ lacLev σ n`.  The family is almost orthogonal, so its signed sums are
  `ℓᵖ`-bounded and its values square function is an `ℓᵖ`-bounded Littlewood–Paley square function.

The decomposition `bumpOp = lacConst K • triSmooth + devOp` is the pointwise identity
`bump_decomp` below; the target theorem is then the sum of the two halves `lacDilTriVar` (the
martingale/Lépingle half) and `lacDilDevSqSum` (the almost-orthogonality half).
-/
import Mathlib
import Submission.Work.Analysis.Hilbert.lattice_exp_defs
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The dyadic level of the scale `σ n`: `⌊log₂ (max (σ n) 2)⌋` (the natural-number form of the
corpus's `Work.Analysis.EndVar.logN`). -/
def lacLev (σ : ℕ → ℕ) (n : ℕ) : ℕ := Nat.log 2 (max (σ n) 2)

/-- The mean of the Schwartz kernel `K`, `∫ K`. -/
def lacConst (K : SchwartzMap ℝ ℂ) : ℂ := ∫ x : ℝ, (K : ℝ → ℂ) x

/-- The sampled kernel of the `n`-th low-pass operator: `j ↦ (1/σ n) K (j/(σ n))`. -/
def bumpKern (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (n : ℕ) : ℤ → ℂ :=
  fun j => (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n))

/-- The `n`-th low-pass (bump) convolution operator on `ℤ`,
`f ↦ (K_{σ n} * f)(x) = Σ'_j (1/σ n) K (j/σ n) f (x - j)`. -/
def bumpOp (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (n : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' j : ℤ, (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n)) * f (x - j)

/-- The triangular (Fejér) smoothing at the dyadic level `lacLev σ n`. -/
def triSmooth (σ : ℕ → ℕ) (n : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  Work.Analysis.Hilbert.triConv (lacLev σ n) f

/-- The deviation `K_{σ n} * f - (∫K) · (triangular smoothing)`. -/
def devOp (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (n : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  bumpOp K σ n f x - lacConst K * triSmooth σ n f x

/-- The kernel of the deviation operator of the `n`-th scale: the sampled bump kernel minus
`∫K` times the triangular kernel. -/
def devKern (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (n : ℕ) : ℤ → ℂ :=
  fun j => bumpKern K σ n j - lacConst K * (Work.Analysis.Hilbert.triKernel (lacLev σ n) j : ℂ)

/-- **The pointwise decomposition.**  The `n`-th bump operator is the mean `∫K` times the
triangular smoothing plus the deviation. -/
theorem bump_decomp (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (n : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    bumpOp K σ n f x = lacConst K * triSmooth σ n f x + devOp K σ n f x := by
  rw [devOp]; ring

/-- The level function of a `2`-lacunary scale sequence is monotone. -/
theorem lacLev_mono {σ : ℕ → ℕ} (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) :
    Monotone (lacLev σ) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
      refine le_trans ih ?_
      have h1 : max (σ k) 2 ≤ max (σ (k + 1)) 2 := by
        refine max_le (le_trans ?_ (Nat.le_max_left _ _)) (Nat.le_max_right _ _)
        have : σ k ≤ 2 * σ k := Nat.le_mul_of_pos_left _ (by norm_num)
        exact le_trans this (hσ2 k)
      exact Nat.log_mono_right h1

/-- The dyadic scale `2 ^ lacLev σ n` is within a factor `2` of `σ n` (from above): it is
`≤ 2 * σ n`. -/
theorem pow_lacLev_le {σ : ℕ → ℕ} (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) :
    2 ^ lacLev σ n ≤ 2 * σ n := by
  have h2 : (1 : ℕ) ≤ max (σ n) 2 := le_trans (by norm_num) (le_max_right _ _)
  have := Nat.pow_log_le_self 2 (by omega : max (σ n) 2 ≠ 0)
  calc 2 ^ lacLev σ n = 2 ^ Nat.log 2 (max (σ n) 2) := rfl
    _ ≤ max (σ n) 2 := this
    _ ≤ 2 * σ n := max_le (Nat.le_mul_of_pos_left _ (by norm_num))
      (by have h := hσ1 n; omega)

/-- The dyadic scale `2 ^ lacLev σ n` is within a factor `2` of `σ n` (from below). -/
theorem le_two_pow_lacLev {σ : ℕ → ℕ} (n : ℕ) :
    σ n ≤ 2 ^ (lacLev σ n + 1) := by
  have hlt : max (σ n) 2 < 2 ^ (Nat.log 2 (max (σ n) 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
  have h1 : σ n ≤ max (σ n) 2 := le_max_left _ _
  have h2 : Nat.log 2 (max (σ n) 2) = lacLev σ n := rfl
  rw [h2] at hlt
  exact le_of_lt (lt_of_le_of_lt h1 hlt)

end

end Work.KMTAreas.A7
