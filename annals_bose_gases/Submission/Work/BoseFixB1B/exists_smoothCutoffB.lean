import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.BoseFixB1B.exists_smoothCutoff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.exists_smoothCutoffB`

A self-contained proof of the pointwise smooth-cutoff statement for the sliding box
`B(u) = dlBox ℓ d u` (the `B`-variant of `Work.BoseFixB1B.exists_smoothCutoff`; the
statement is identical and the proof here is independent of that lemma).

The cutoff is the product of six one-dimensional plateau factors
(`Submission.Work.BoseFixB1B.cutoffDefs`),

  `γ_δ = cutFun ((ℓ*d)•u) (plateau (ℓ/2) δ) (plateau (ℓ*d/2) δ)`,

where `plateau A δ t = σ((t+A)/δ)·σ((A-t)/δ)`, `σ = Real.smoothTransition`.  The four
properties are read off from the already-proved building blocks:

* smoothness from `contDiff_cutFun` and `plateau_basic`;
* `[0,1]`-range from `cutFun_Icc` and `plateau_basic`;
* `γ_δ = 1` on `{boxMargin ℓ d u · ≥ δ}` from `plateau_basic` (the plateau is `1` on
  `|t| ≤ A - δ`) together with the coordinate bounds `boxMargin_le_coord`,
  `boxMargin_le_transCoord`;
* the support from `cutFun_support_subset` (the plateau vanishes for `|t| ≥ A`).

The derivative bound is the only place where the *quantitative* statement is used: each
plateau factor is `(2K/δ)`-Lipschitz (`plateau_lip`) with `K` a Lipschitz constant of `σ`
(`smoothTransition_lipschitz`), the six factors have disjoint total variation because all of
them take values in `[0,1]` (`cutFun_lip`), so `γ_δ` is `(12K/δ)`-Lipschitz, and the
mean-value converse `norm_fderiv_le_of_lip'` gives `‖fderiv ℝ γ_δ x‖ ≤ 12K/δ`.  Hence the
constant `C = 12K` is independent of `δ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

set_option autoImplicit false

/-- The product plateau factors of the sliding box `B(u)`, and their elementary properties.
This is the pointwise package of the four requirements on the cutoff. -/
theorem exists_smoothCutoffB {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∃ γ : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiff ℝ (⊤ : ENat) γ ∧
      tsupport γ ⊆ Submission.BoseGases.dlBox ℓ d u ∧
      (∀ x, 0 ≤ γ x ∧ γ x ≤ 1) ∧
      (∀ x, Work.BoseFixB1B.boxMargin ℓ d u x ≥ δ → γ x = 1) ∧
      (∀ x, ‖fderiv ℝ γ x‖ ≤ C / δ) := by
  obtain ⟨K, hKpos, hK⟩ := smoothTransition_abs_sub_le
  refine ⟨12 * K, by positivity, fun δ hδ => ?_⟩
  -- the two one-dimensional plateau factors, and their properties
  obtain ⟨hfcd, hf01, hfzero, hfone⟩ := plateau_basic (A := ℓ / 2) (δ := δ) hδ
  obtain ⟨hgcd, hg01, hgzero, hgone⟩ := plateau_basic (A := ℓ * d / 2) (δ := δ) hδ
  refine ⟨cutFun ((ℓ * d) • u) (plateau (ℓ / 2) δ) (plateau (ℓ * d / 2) δ),
    contDiff_cutFun hfcd hgcd, ?_, ?_, ?_, ?_⟩
  · -- support: each plateau vanishes for `|t| ≥ A`
    exact cutFun_support_subset (ℓ := ℓ) (d := d) u hfzero hgzero
  · -- range: `cutFun` of `[0,1]`-valued factors is `[0,1]`-valued
    exact cutFun_Icc hf01 hg01
  · -- the value `1` on the inner box: each plateau is `1` on `|t| ≤ A - δ`
    intro x hx
    refine cutFun_eq_one (A := ℓ / 2) (B := ℓ * d / 2) (δ := δ) hfone hgone x ?_ ?_
    · intro i
      have h1 := boxMargin_le_coord (ℓ := ℓ) (d := d) u x i
      linarith
    · intro i
      have h2 := boxMargin_le_transCoord (ℓ := ℓ) (d := d) u x i
      linarith
  · -- the derivative bound, from the Lipschitz bound on `cutFun`
    intro x
    have hf_lip : ∀ t s : ℝ,
        |plateau (ℓ / 2) δ s - plateau (ℓ / 2) δ t| ≤ (2 * K / δ) * |s - t| :=
      fun t s => plateau_lip (K := K) (A := ℓ / 2) (δ := δ) hKpos.le hK hδ t s
    have hg_lip : ∀ t s : ℝ,
        |plateau (ℓ * d / 2) δ s - plateau (ℓ * d / 2) δ t| ≤ (2 * K / δ) * |s - t| :=
      fun t s => plateau_lip (K := K) (A := ℓ * d / 2) (δ := δ) hKpos.le hK hδ t s
    have hf_bd : ∀ t : ℝ, |plateau (ℓ / 2) δ t| ≤ 1 := fun t => by
      rw [abs_of_nonneg (hf01 t).1]; exact (hf01 t).2
    have hg_bd : ∀ t : ℝ, |plateau (ℓ * d / 2) δ t| ≤ 1 := fun t => by
      rw [abs_of_nonneg (hg01 t).1]; exact (hg01 t).2
    have hL : 0 ≤ 2 * K / δ := div_nonneg (by positivity) hδ.le
    have hlip := cutFun_lip (c := (ℓ * d) • u) (L := 2 * K / δ) (M := 2 * K / δ)
      hL hL hf_lip hg_lip hf_bd hg_bd
    have hconst : 3 * (2 * K / δ) + 3 * (2 * K / δ) = 12 * K / δ := by ring
    have hC : 0 ≤ 12 * K / δ := div_nonneg (by positivity) hδ.le
    apply norm_fderiv_le_of_lip' ℝ hC
    filter_upwards with y
    rw [Real.norm_eq_abs, ← hconst]
    exact hlip x y

end Work.BoseFixB1B
