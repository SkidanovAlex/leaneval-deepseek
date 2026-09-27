import Mathlib
import Submission.Work.EKLC6Core.box_iInter_conjBox

/-!
# `EKLC6Core.conjBy_mem_Box1` — the normalising box `B₁^U` is `aDiag t`-invariant

Let `U ≤ SL₃(ℝ)` be horospherical (`IsHoro U`, in particular `A`-normalised) and let
`t : Fin 3 → ℝ` be an exponent vector such that all *non-contracted* entries of `U` vanish:

`i ≠ j`, `t j < t i`  ⟹  `u i j = 0`   for every `u ∈ U`.

Then conjugation by `aDiag t` preserves the normalising box

`B₁^U = {g ∈ U | |g i j - δᵢⱼ| ≤ 1}`.

Concretely, `(aDiag t · g · (aDiag t)⁻¹)ᵢⱼ = e^{tᵢ - tⱼ} gᵢⱼ`, and `g ∈ B₁^U` gives
`|gᵢⱼ| ≤ 1` for `i ≠ j`.  If `t j < t i` this entry vanishes by hypothesis; otherwise
`t i ≤ t j`, so `e^{tᵢ - tⱼ} ≤ 1` and the entry can only shrink.  Membership in `U` is the
`A`-normalisation supplied by `IsHoro`.
-/

open Filter Topology
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- Conjugation by `aDiag t` preserves the normalising box `B₁^U`, provided the non-contracted
entries of `U` vanish (so that no entry of an element of `B₁^U` is *expanded*). -/
theorem conjBy_mem_Box1 {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hzero : ∀ u ∈ U, ∀ i j : Fin 3, i ≠ j → t j < t i → u i j = 0)
    {g : Work.EKLContract.SL3} (hg : g ∈ Work.EKLContract.Box1 U) :
    Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹ ∈
      Work.EKLContract.Box1 U := by
  -- membership in `U` is the `A`-normalisation of `IsHoro`
  refine ⟨hU.2.1 t g hg.1, fun i j => ?_⟩
  -- the entry formula for conjugation by `aDiag t`
  rw [Work.EKLC6Core.boxi_conj_apply]
  rcases eq_or_ne i j with rfl | hij
  · -- diagonal entries are unchanged
    rw [sub_self, Real.exp_zero, one_mul]
    simpa using hg.2 i i
  · rw [Matrix.one_apply_ne hij]
    rcases lt_or_ge (t j) (t i) with hlt | hle
    · -- the hypothesis kills the entries that would be expanded
      rw [hzero g hg.1 i j hij hlt, mul_zero, sub_zero, abs_zero]
      norm_num
    · -- otherwise the exponential factor is at most `1`, so the box bound is preserved
      have hb : |g i j| ≤ 1 := by
        have h := hg.2 i j
        rwa [Matrix.one_apply_ne hij, sub_zero] at h
      have hexp : Real.exp (t i - t j) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      rw [sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [abs_nonneg (g i j)]

end Work.EKLC6Core
