import Mathlib
import Submission.Work.A7Hi2.RealScaleAssembly

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

/-!
# The symbol of the linearised difference kernel `linDiffKernR`

`linDiffKernR K σ ρ U ω` is the *finite* signed sum `∑_{n ∈ U} ω_n (bumpKernR K (σ n) −
bumpKernR K (ρ n))` of the difference kernels, and `symDiffR K σ ρ θ` is the Fourier series of a
single difference kernel.  The lemma proved here is the bookkeeping identity

  `∑'_j linDiffKernR K σ ρ U ω j · e^{2πijθ}
     = ∑_{n ∈ U} ω_n · symDiffR K (σ n) (ρ n) θ`,

i.e. the symbol of the sum is the sum of the symbols: exchange the (finite) sum over `n ∈ U` with
the (absolutely convergent, by the Schwartz decay of `K`) series over `j : ℤ`, and then pull the
constant `ω_n` out of each series.

The only analytic input is the summability of the modulated difference kernels
`j ↦ (bumpKernR K s j − bumpKernR K r j) · chr j θ` for real scales `s, r ≥ 1`, which follows from
`summable_bumpKernR` (the port of `Work.KMTAreas.A7.bumpKern_summable` to real scales).
-/

/-- The modulated difference kernel `j ↦ (bumpKernR K s j − bumpKernR K r j) · chr j θ` is
summable, being the difference of two summable kernels times a unimodular character. -/
private lemma summable_diffKernR_mul_chr_auxSymb (K : SchwartzMap ℝ ℂ) (s r : ℝ)
    (hs : 1 ≤ s) (hr : 1 ≤ r) (θ : ℝ) :
    Summable (fun j : ℤ => diffKernR K s r j * Work.KMTAreas.ADev.chr j θ) := by
  have h1 : Summable (fun j : ℤ => bumpKernR K s j) := summable_bumpKernR K hs
  have h2 : Summable (fun j : ℤ => bumpKernR K r j) := summable_bumpKernR K hr
  have hd : Summable (fun j : ℤ => ‖diffKernR K s r j‖) := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => le_of_eq ?_)
      ((h1.sub h2).norm)
    rw [diffKernR]
  refine Summable.of_norm_bounded hd (fun j => ?_)
  rw [norm_mul, Work.KMTAreas.ADev.norm_chr, mul_one]

/-- Please keep all helpers `private`, or name them with the suffix `_auxSymb`, so this file does
not clash with the sibling file `Submission/Work/A7Hi2/linDiffKernR_summable.lean`. -/
theorem linDiffKernR_symbol (K : SchwartzMap ℝ ℂ) (σ ρ : ℕ → ℝ)
    (hσ1 : ∀ n, 1 ≤ σ n) (hρ1 : ∀ n, 1 ≤ ρ n) (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ) :
    (∑' j : ℤ, linDiffKernR K σ ρ U ω j * Work.KMTAreas.ADev.chr j θ)
      = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * symDiffR K (σ n) (ρ n) θ := by
  have hmem : ∀ n ∈ U, Summable (fun j : ℤ => Work.KMTAreas.ADev.bSign ω n *
      (diffKernR K (σ n) (ρ n) j * Work.KMTAreas.ADev.chr j θ)) :=
    fun n _ => (summable_diffKernR_mul_chr_auxSymb K (σ n) (ρ n) (hσ1 n) (hρ1 n) θ).mul_left _
  have hcongr : (fun j : ℤ => linDiffKernR K σ ρ U ω j * Work.KMTAreas.ADev.chr j θ)
      = fun j : ℤ => ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n *
          (diffKernR K (σ n) (ρ n) j * Work.KMTAreas.ADev.chr j θ) := by
    funext j
    rw [linDiffKernR, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hcongr, Summable.tsum_finsetSum hmem]
  exact Finset.sum_congr rfl fun n _ => by rw [tsum_mul_left]; rfl

end

end Work.A7Hi2
