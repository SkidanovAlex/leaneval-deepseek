/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# The multiplier product `(ρ₊ − 1)(ρ₋ − 1)` of the two split fixed points is real

Let `F = Work.EL.F c = (T_c)^[10]` be the second return map and `g = Work.PARIMPL.gtc c =
(T_c)^[5]` its antiholomorphic square root, `F = g ∘ g`.  Suppose that in a disc `ball z₁ R` the
fixed points of `F` are *exactly* the two roots of `(z − m)² = G`, i.e.

  `F z = z ↔ (z − m)² = G    (z ∈ ball z₁ R)`,   and   `δ² = G`.

Then the two fixed points are `α := m + δ` and `β := m − δ`, and **the product of their
`F`-multipliers shifted by `1`,

  `Υ = (deriv F α − 1) · (deriv F β − 1) = Q'(α)·Q'(β)`,   `Q := F − id`,

is a real number** — provided `g α` and `g β` still lie in the disc where the fixed points are
classified.

This is the field `wall_factorization`'s "Υ is real-valued" input (`Submission/Work/PARIMPL/
ParSplit/NOTES.md`, §2): on the *fix* side (`g α = α`, `g β = β`) both multipliers are squares
`‖K'(·)‖²` of complex numbers, hence non-negative reals
(`ParSplit.deriv_star_self_of_fix`); on the *swap* side (`g α = β`, `g β = α`) the two multipliers
are conjugate (`ParSplit.deriv_conj_of_swap`), so `Υ = |1 − ρ|²`.

**The dichotomy.**  Since `F α = α` and `F = g ∘ g`, applying `g` to `g (g α) = α` gives
`F (g α) = g (g (g α)) = g α`: the square root `g` maps the fixed-point set
`{α, β}` (the whole fixed-point set of `F` in the disc, by hypothesis) into itself.  Moreover `g`
is injective on it, since `g (g α) = α` and `g (g β) = β`; a self-map of a two-element set that is
injective is a bijection, so either it fixes both points or it swaps them.  The mixed cases
(`g α = β`, `g β = β`) force `α = β` by injectivity and reduce to the fixed case.

Nothing here uses the parabolic structure of `c` or `z₁`: the statement is the general
`F = g ∘ g` multiplier lemma, and `d : Work.EL.RootParabolic c₀` only fixes the vocabulary.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.phase_of_split
import Submission.Work.PARIMPL.ParSplit.deriv_conj_of_swap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-- **The general multiplier-product lemma.**  If the fixed points of `F = Work.EL.F c` in the
disc `ball z₁ R` are exactly `α` and `β`, and the antiholomorphic square root
`g = Work.PARIMPL.gtc c` of `F` (so `F = g ∘ g`) maps both of them back into the disc, then
`(deriv F α − 1) · (deriv F β − 1)` is real.

(`g` need not map `α`, `β` to themselves: it permutes them, and the two cases — `g` fixes both or
`g` swaps them — are handled by `deriv_star_self_of_fix` and `deriv_conj_of_swap`.) -/
theorem exists_real_multiplier_prod_of_fixed_pair {c z₁ : ℂ} {R : ℝ} {α β : ℂ}
    (hchar : ∀ z ∈ Metric.ball z₁ R, (Work.EL.F c z = z ↔ z = α ∨ z = β))
    (hα : α ∈ Metric.ball z₁ R) (hβ : β ∈ Metric.ball z₁ R)
    (hgα : Work.PARIMPL.gtc c α ∈ Metric.ball z₁ R)
    (hgβ : Work.PARIMPL.gtc c β ∈ Metric.ball z₁ R) :
    ∃ t : ℝ, (deriv (Work.EL.F c) α - 1) * (deriv (Work.EL.F c) β - 1) = (t : ℂ) := by
  -- `α` and `β` are fixed points of `F`, and `F = g ∘ g`.
  have hFα : Work.EL.F c α = α := (hchar α hα).mpr (Or.inl rfl)
  have hFβ : Work.EL.F c β = β := (hchar β hβ).mpr (Or.inr rfl)
  have hcomp : Work.EL.F c = Work.PARIMPL.gtc c ∘ Work.PARIMPL.gtc c :=
    Work.PARIMPL.Ft_eq_g_comp c
  -- `g (g z) = F z`, so `g (g z) = z` at a fixed point.
  have hgg : ∀ z : ℂ, Work.EL.F c z = z → Work.PARIMPL.gtc c (Work.PARIMPL.gtc c z) = z := by
    intro z hz
    have h' : (Work.PARIMPL.gtc c ∘ Work.PARIMPL.gtc c) z = z := by rw [← hcomp]; exact hz
    simpa [Function.comp_apply] using h'
  -- `F` commutes with `g`, because `F = g ∘ g`: a fixed point of `F` maps to a fixed point of `F`.
  have hperm : ∀ z : ℂ, Work.EL.F c z = z →
      Work.EL.F c (Work.PARIMPL.gtc c z) = Work.PARIMPL.gtc c z := by
    intro z hz
    have h1 := hgg z hz
    have h2 : Work.EL.F c (Work.PARIMPL.gtc c z) =
        Work.PARIMPL.gtc c (Work.PARIMPL.gtc c (Work.PARIMPL.gtc c z)) := by
      rw [hcomp]; rfl
    rw [h2, h1]
  -- Hence `g` maps each of `α`, `β` into the fixed-point set `{α, β}`.
  have hga : Work.PARIMPL.gtc c α = α ∨ Work.PARIMPL.gtc c α = β :=
    (hchar (Work.PARIMPL.gtc c α) hgα).mp (hperm α hFα)
  have hgb : Work.PARIMPL.gtc c β = α ∨ Work.PARIMPL.gtc c β = β :=
    (hchar (Work.PARIMPL.gtc c β) hgβ).mp (hperm β hFβ)
  -- `g` is injective on `{α, β}`: `g (g α) = α` and `g (g β) = β`.
  have hinj : Work.PARIMPL.gtc c α = Work.PARIMPL.gtc c β → α = β := by
    intro h
    have h1 := hgg α hFα
    have h2 := hgg β hFβ
    rw [h] at h1
    rw [h2] at h1
    exact h1.symm
  -- The dichotomy: either `g` fixes both points, or it swaps them.
  have hcase : (Work.PARIMPL.gtc c α = α ∧ Work.PARIMPL.gtc c β = β) ∨
      (Work.PARIMPL.gtc c α = β ∧ Work.PARIMPL.gtc c β = α) := by
    rcases hga with h1 | h1 <;> rcases hgb with h2 | h2
    · -- `g α = α`, `g β = α`: injectivity forces `α = β`, so `g` fixes both.
      have hαβ : α = β := hinj (h1.trans h2.symm)
      exact Or.inl ⟨h1, by rw [h2]; exact hαβ⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · -- `g α = β`, `g β = β`: injectivity forces `α = β`, so `g` fixes both.
      have hαβ : α = β := hinj (h1.trans h2.symm)
      exact Or.inl ⟨by rw [h1]; exact hαβ.symm, h2⟩
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- **Fix side**: both multipliers of `F` are non-negative real numbers.
    obtain ⟨r, -, hρα⟩ := deriv_star_self_of_fix h1
    obtain ⟨s, -, hρβ⟩ := deriv_star_self_of_fix h2
    refine ⟨(r - 1) * (s - 1), ?_⟩
    rw [hρα, hρβ]
    push_cast
    ring
  · -- **Swap side**: the two multipliers are conjugate, so the product is `|1 − ρ|²`.
    refine ⟨Complex.normSq (deriv (Work.EL.F c) β - 1), ?_⟩
    rw [deriv_conj_of_swap h1 h2]
    rw [show star (deriv (Work.EL.F c) β) - 1 = star (deriv (Work.EL.F c) β - 1) by simp]
    exact Complex.normSq_eq_conj_mul_self.symm

/-- **The multiplier product of the two split fixed points is real.**  Let `F = Work.EL.F c` be
the second return map, `g = Work.PARIMPL.gtc c` its antiholomorphic square root, and suppose that
inside `ball z₁ R` the fixed points of `F` are exactly the roots of `(z − m)² = G`, where
`G = δ²`.  If `m + δ`, `m − δ` and their images under `g` all lie in `ball z₁ R`, then the product
`(deriv F (m + δ) − 1) · (deriv F (m − δ) − 1)` is a real number. -/
theorem deriv_prod_real_of_char {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) {R : ℝ} (hR : 0 < R)
    {c m δ G : ℂ}
    (hchar : ∀ z ∈ Metric.ball d.z₁ R, (Work.EL.F c z = z ↔ (z - m) ^ 2 = G))
    (hδ : δ ^ 2 = G)
    (hplus : m + δ ∈ Metric.ball d.z₁ R) (hminus : m - δ ∈ Metric.ball d.z₁ R)
    (hgplus : Work.PARIMPL.gtc c (m + δ) ∈ Metric.ball d.z₁ R)
    (hgminus : Work.PARIMPL.gtc c (m - δ) ∈ Metric.ball d.z₁ R) :
    ∃ t : ℝ, (deriv (Work.EL.F c) (m + δ) - 1) * (deriv (Work.EL.F c) (m - δ) - 1) = (t : ℂ) := by
  -- The roots of `(z − m)² = δ²` are `m ± δ`: rewrite the fixed-point classification.
  apply exists_real_multiplier_prod_of_fixed_pair (c := c) (z₁ := d.z₁) (R := R)
    (α := m + δ) (β := m - δ)
  · intro z hz
    rw [hchar z hz]
    constructor
    · -- `(z − m)² = δ²` factors as `(z − m − δ)(z − m + δ) = 0`.
      intro h
      have h2 : (z - m - δ) * (z - m + δ) = 0 := by
        have h3 : (z - m) ^ 2 - δ ^ 2 = (z - m - δ) * (z - m + δ) := by ring
        rw [h, hδ, sub_self] at h3
        exact h3.symm
      rcases mul_eq_zero.mp h2 with h4 | h4
      · left; linear_combination h4
      · right; linear_combination h4
    · -- conversely `z = m ± δ` satisfies `(z − m)² = δ²`.
      rintro (rfl | rfl)
      · rw [show m + δ - m = δ by ring, hδ]
      · rw [show m - δ - m = -δ by ring, neg_sq, hδ]
  · exact hplus
  · exact hminus
  · exact hgplus
  · exact hgminus

end Work.PARIMPL.ParSplit
