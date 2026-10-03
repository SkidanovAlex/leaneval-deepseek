/-
# The scale/shift identity of the `cz_shift` instantiation (item 1, first step)

`Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos` is the `cz_shift` instantiation for the
Ionescu–Wainger bumps: `∑_{n∈U} ε n · varphiNt (⌊a n⌋) k₁ t` is an `L^p(ℝ)` multiplier with bound
`≲ (1+k₁)·C(Λ,p)`.  Its first step is to put each modulated bump in the Appendix-B shape of
`Work.Analysis.CzShift`: the *fixed* bump `F = kmtEta − kmtEta(2·)` evaluated at the scale
`σ = 2^{Log N − k₁}` and modulated at the shift `t σ = N t`.

This file proves that identity (`varphiNt_shiftForm`), together with the `F`-decomposition
(`kmtEta_sub_two_mul`) which is what makes the seed `ψ = F` independent of `k₁` and `N`.  Note
`F(0) = kmtEta 0 − kmtEta 0 = 0`: this is exactly the `k₁ ≥ 1` regime in which the symbols vanish
at the origin (for `k₁ = 0` the bump is `kmtEta(2^{Log N}·)` itself, whose mean does not vanish —
the configuration formally refuted in `NOTES_A7_lacunaryBump_mult_bound_FALSE.md`).
-/
import Mathlib
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators

/-- The fixed bump `F = η − η(2 ·)` of Appendix B of Krause–Mirek–Tao: the seed `ψ` of the
shifted Calderón–Zygmund theorem in the form used for the modulated bumps.  It is `k₁`- and
`N`-independent (so the `cz_shift` seed bounds are uniform in the scale family), and `F 0 = 0`. -/
noncomputable def bumpF (x : ℝ) : ℂ :=
  Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta (2 * x)

/-- `F 0 = 0` for the fixed bump `F = η − η(2 ·)`: this is the vanishing at the origin which the
shifted Calderón–Zygmund seed `ψ(0) = 0` needs, and it is exactly what fails at `k₁ = 0`. -/
theorem bumpF_zero : bumpF 0 = 0 := by
  simp [bumpF]

/-- **The scale/shift identity.**  For `k₁ ≥ 1` the modulated bump is the *fixed* bump `F` at the
scale `σ = 2^{Log N − k₁}`, modulated at the shift `t σ = N t`:

  `varphiNt N k₁ t ξ = F (σ ξ) · e (N t ξ)`,   `σ = 2^{Log N − k₁}`.

With `σ n = 2^{Log ⌊a n⌋ − k₁}` this exhibits the family as
`ξ ↦ ψ (σ n ξ) · e (tₙ σ n ξ)` with `ψ = F` fixed, `tₙ = ⌊a n⌋ t / σ n` and
`|tₙ| ≤ 2^{k₁+1}` — the hypotheses of `cz_shift_lp_scales` with `K = k₁ + 1`. -/
theorem varphiNt_shiftForm (k₁ : ℕ) (hk₁ : 1 ≤ k₁) (N : ℕ) (t : ℝ) :
    (fun ξ : ℝ => varphiNt N k₁ t ξ)
      = fun ξ : ℝ =>
          bumpF ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) * ξ)
            * ee (((N : ℝ) * t) * ξ) := by
  funext ξ
  rw [varphiNt, varphiN, if_neg (by omega : ¬ k₁ = 0), bumpF]

  congr 2
  congr 1
  have hsplit' : (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) + 1)
      = (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) * 2 := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [hsplit']
  ring

end Work.KMTAreas.A7
