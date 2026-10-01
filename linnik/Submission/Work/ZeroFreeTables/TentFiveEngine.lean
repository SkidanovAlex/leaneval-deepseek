/-
# ZeroFreeTables — TentFiveEngine

The **five-term engine** at the tent (HB §8.5 / Lemma 8.5, i.e. HB's second-number argument):
`∀ X > 0, ∀ ε > 0, ∀ δ ∈ (0,1), ∃ q₀, ∀ q ≥ q₀, TentFiveBodyAt X (11/24 + 4ε) ε δ q`.

This is `Work.ZeroFreeTables.lemma85pt_region_mixed` (HB's five-term combination with the *mixed*
constants `c₁ = 1/8` for the real `χ₁` and `c = 1/6` for the other three characters) instantiated
at the test function `tent X t = max (X − t) 0`.  The engine returns

  `0 ≤ ∫ e^{λ₂t}·tent − ∫ e^{(λ₂−λ₁)t}·tent − ∫ tent + tent X 0·(1/8 + 2·(1/6) + 4ε)`,

and the explicit Laplace transform (`TentLaplace`), `tent X 0 = X` and
`1/8 + 2·(1/6) + 4ε = 11/24 + 4ε` convert it into `0 ≤ tentFive X (11/24 + 4ε) λ₁ λ₂`.

The admissibility conditions for the tent (continuity, support `[X,∞)`, `C²` on `(0,X)`, `B = 0`
for the second derivative, positivity, and HB's Condition 2 — supplied by
`Work.LinnikAreas.triangle_hFnn`) are the same as in `TentSameEngine`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentIf
import Submission.Work.ZeroFreeTables.TentLaplace
import Submission.Work.ZeroFreeTables.lemma85pt_region_mixed
import Submission.Work.LinnikAreas.triangle_hFnn

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- The tent is affine on `(0,X)`, hence its second iterated derivative vanishes there. -/
private lemma iteratedDeriv_two_tent {X t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) X) :
    iteratedDeriv 2 (tent X) t = 0 := by
  have hcongr : Set.EqOn (tent X) (fun s : ℝ => X - s) (Set.Ioo (0:ℝ) X) :=
    fun s hs => by
      show max (X - s) 0 = X - s
      exact max_eq_left (by linarith [hs.2])
  have h1 := Set.EqOn.iteratedDeriv_of_isOpen hcongr isOpen_Ioo 2 ht
  rw [h1]
  simp [iteratedDeriv_succ, iteratedDeriv_const, iteratedDeriv_id]

theorem TentFiveEngine (X ε δ : ℝ) (hX : 0 < X) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → Work.ZeroFreeTables.TentFiveBodyAt X (11 / 24 + 4 * ε) ε δ q := by
  obtain ⟨q₀, hq₀⟩ := Work.ZeroFreeTables.lemma85pt_region_mixed X 0 (1 / 8) (1 / 6) hX le_rfl
    (f := tent X)
    (by
      have h : Continuous fun t : ℝ => max (X - t) 0 := by fun_prop
      exact h.continuousOn)
    (fun t ht => by simpa only [tent] using tent_supp ht)
    (by
      have haff : ContDiffOn ℝ 2 (fun t : ℝ => X - t) (Set.Ioo 0 X) :=
        (contDiffOn_const (c := X)).sub contDiffOn_id
      exact haff.congr (fun t ht => by
        show max (X - t) 0 = X - t
        exact max_eq_left (by linarith [ht.2])))
    (fun t ht => by rw [iteratedDeriv_two_tent ht]; norm_num)
    (by rw [tent_zero hX.le]; exact hX)
    (fun t => tent_nonneg X t)
    (fun z hz => by simpa only [tent] using Work.LinnikAreas.triangle_hFnn hX z hz)
    hε hδ0 hδ1
  refine ⟨q₀, fun q hq => ?_⟩
  intro inst χ₁ χ₂ instc₁ instc₂ instc₃ instc₄ β₁ β₂ γ₂ hχ₁ hχ₂ hχ₂χ₁ hχ₁χ₂ hχ₁χ₂' hβ₁ hβ₂
    hγ₂ hpt₁ hpt₂ hzero₁ hzero₂ hmaxA hmaxB hmaxC hmaxD hdivC hdivD H₁ H₂ H₃ H₄
  have h := hq₀ (q := q) hq χ₁ χ₂ hχ₁ hχ₂ hχ₂χ₁ hχ₁χ₂ hχ₁χ₂' hβ₁ hβ₂ hγ₂ hpt₁ hpt₂
    hzero₁ hzero₂ hmaxA hmaxB hmaxC hmaxD hdivC hdivD H₁ H₂ H₃ H₄
  rw [TentLaplace X (Real.log (q : ℝ) * (1 - β₂)) hX,
    TentLaplace X (-(Real.log (q : ℝ) * (1 - β₁) - Real.log (q : ℝ) * (1 - β₂))) hX,
    tent_integral hX.le,
    tent_zero hX.le,
    show (1 : ℝ) / 8 + 2 * (1 / 6) + 4 * ε = 11 / 24 + 4 * ε from by norm_num] at h
  have harg : -(Real.log (q : ℝ) * (1 - β₁) - Real.log (q : ℝ) * (1 - β₂))
      = Real.log (q : ℝ) * (1 - β₂) - Real.log (q : ℝ) * (1 - β₁) := by ring
  rw [harg] at h
  unfold tentFive
  exact h

end Work.ZeroFreeTables
