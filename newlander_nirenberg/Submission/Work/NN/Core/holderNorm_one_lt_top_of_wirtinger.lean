import Mathlib
import Submission.Work.NN.Core.holderNorm_le_wirtinger_coord_on
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.NN.Core.holderNorm_const_mul_le

/-!
# Finiteness of the `C^{1,α}` norm of a Wirtinger solution

Let `W : ℂⁿ → ℂ` be a compactly supported `C^1` function whose `∂̄`-derivatives are the
components of a form `F` (`∂̄_j W = F_j`) and whose `∂`-derivatives are proportional to those of
the Bochner–Martinelli potential of `F` (`∂_j W = γ⁻¹ ∂_j (bmPotential F)`, where `γ = bmGamma n`
is the normalising constant of the Bochner–Martinelli formula).  Assuming the `C^{0,α}` norms of
`F` and of `∂_j (bmPotential F)` are finite on all of `ℂⁿ`, the `C^{1,α}` norm of `W` is finite on
every polydisc `polydisc 0 ρ` with `ρ > 0` componentwise.

The proof is the two-dimensional Wirtinger estimate of
`Work.NN.Core.holderNorm_le_wirtinger_coord_on`:

  `‖W‖_{1,α} ≤ K (‖W‖_{0,α} + Σ_j (‖∂_j W‖_{0,α} + ‖∂̄_j W‖_{0,α}))`,

whose right hand side is finite: `W` has finite `C^{0,α}` norm on `ℂⁿ` because it is a compactly
supported `C^1` function (hence bounded and Lipschitz), `∂̄_j W = F_j` is finite by hypothesis,
and `∂_j W = γ⁻¹ ∂_j (bmPotential F)` is a constant multiple of a function with finite `C^{0,α}`
norm by hypothesis (`holderNorm_const_mul_le`, `holderNorm_mono_set`).
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

theorem holderNorm_one_lt_top_of_wirtinger {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : Fin n → (Fin n → ℂ) → ℂ} {W : (Fin n → ℂ) → ℂ}
    (hW : ContDiff ℝ 1 W) (hWc : HasCompactSupport W)
    (hBfin : ∀ i, Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
        (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ < ⊤)
    (hd : ∀ i z, Work.CR.Flat.dCoord i W z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z)
    (hdb : ∀ i z, Work.CR.Flat.dbarCoord i W z = F i z)
    (hFfin : ∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) :
    Work.CR.Flat.holderNorm 1 α W (Work.CR.Flat.polydisc 0 ρ) < ⊤ := by
  obtain ⟨K, hK0, hK⟩ := holderNorm_le_wirtinger_coord_on (n := n) 0 (α := α)
    (Ω := Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ) (Work.CR.Flat.isOpen_polydisc 0 ρ)
  set Ω : Set (Fin n → ℂ) := Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ with hΩdef
  have hΩ : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hmain : Work.CR.Flat.holderNorm 1 α W Ω
      ≤ ENNReal.ofReal K * (Work.CR.Flat.holderNorm 0 α W Ω
          + ∑ j : Fin n, (Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j W z) Ω
              + Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dbarCoord j W z) Ω)) :=
    hK W (by simpa using hW.contDiffOn (s := Ω))
  -- `W` itself has finite `C^{0,α}` norm on `Ω`
  have hWΩ : Work.CR.Flat.holderNorm 0 α W Ω < ⊤ := by
    refine lt_of_le_of_lt (Work.CR.Flat.Cauchy.holderNorm_le_univ_of_contDiff (X := Fin n → ℂ)
      (k := 0) (α := α) hΩu (hW.of_le (by norm_num))) ?_
    exact lt_top_iff_ne_top.mpr (Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
      (X := Fin n → ℂ) (k := 0) (α := α) (le_of_lt hα0) (le_of_lt hα1) hW hWc)
  -- the `∂`-derivatives
  have hzc : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j W z) Ω
      = Work.CR.Flat.holderNorm 0 α (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential F) z) Ω := fun j =>
    congrArg (fun g => Work.CR.Flat.holderNorm 0 α g Ω) (funext fun z => hd j z)
  have hB : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j W z) Ω < ⊤ := by
    intro j
    rw [hzc j]
    refine lt_of_le_of_lt (holderNorm_const_mul_le (X := Fin n → ℂ) (k := 0) (α := α) hΩu
      ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      (fun z => Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential F) z)) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_set (Ω := Set.univ) (Ω' := Ω)
      isOpen_univ hΩ (Set.subset_univ Ω) 0 α
      (fun z => Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential F) z)) (hBfin j)
  -- the `∂̄`-derivatives
  have hC : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dbarCoord j W z) Ω < ⊤ := by
    intro j
    have hcongr : Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dbarCoord j W z) Ω
        = Work.CR.Flat.holderNorm 0 α (F j) Ω :=
      congrArg (fun g => Work.CR.Flat.holderNorm 0 α g Ω) (funext fun z => hdb j z)
    rw [hcongr]
    exact lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_set (Ω := Set.univ) (Ω' := Ω)
      isOpen_univ hΩ (Set.subset_univ Ω) 0 α (F j)) (hFfin j)
  refine lt_of_le_of_lt hmain ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hWΩ,
    ENNReal.sum_lt_top.mpr fun j _ => ENNReal.add_lt_top.mpr ⟨hB j, hC j⟩⟩)

end Work.NN.Core
