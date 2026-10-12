import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PairGc21Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc21_agree` — the box identity for the block II.1 fibre

The honest fibre `pairG21 p Θ A u y = ∫ x star (Θ x) A (x p.1) A (x p.2) Θ (x with p.1 ↦ y, p.2 ↦ u)`
only sees the values of `Θ` on the `n`-particle box (`Θ = 1_{abox}·Θ₀`), and on `abox` the two
configurations `x` and `x[p.1 ↦ y, p.2 ↦ u]` are simultaneously inside `abox` **provided the kernel
arguments `u`, `y` lie in the one-particle box**.  Hence on the box squared the fibre collapses to
the *clean* representative `pairGc21` of `Work.BoseBoxFock.pairGCore`, in which the state factor is
the smooth `Θ₀` and the integration runs over the compact triple box
`(boxL ℓ × boxL ℓ) × boxPiSet {k ≠ p.1, p.2} ℓ` (the image of `abox n ℓ` under the coordinate
insertion `(a, b, x'') ↦ insertCoord2 p a b x''`).

The proof is the pointwise indicator identity (`abox.indicator (clean integrand)` for the honest
integrand) followed by the Bochner change of variables `integral_abox_eq_integral_triBox` of
`Work.BoseBoxFock.PairGc21Aux`.

Axiom-clean (no `sorryAx`, no new axioms).
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- **The two-fold slot update of a box configuration stays in the box.**  (Used only in the
`p.1`, `p.2` slots with the kernel arguments `y`, `u`; stated for arbitrary slots.) -/
theorem update_update_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {x : Work.BoseDict.Xn n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) {i j : Fin n} {a b : E3}
    (ha : a ∈ boxL ℓ) (hb : b ∈ boxL ℓ) :
    Function.update (Function.update x i a) j b ∈ Submission.BoseGases.abox n ℓ := by
  have ha' : a ∈ Submission.BoseGases.acube ℓ := by rwa [← corpusBox_boxL_eq_acube hℓ]
  have hb' : b ∈ Submission.BoseGases.acube ℓ := by rwa [← corpusBox_boxL_eq_acube hℓ]
  intro k
  by_cases hkj : k = j
  · subst hkj; rw [Function.update_self]; exact hb'
  · rw [Function.update_of_ne hkj]
    by_cases hki : k = i
    · subst hki; rw [Function.update_self]; exact ha'
    · rw [Function.update_of_ne hki]; exact hx k

theorem pairGc21_agree {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ}
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA) (hcA : 0 ≤ cA) :
    ∀ u y : EuclideanSpace ℝ (Fin 3), u ∈ Work.BoseK15.corpusBox.boxL ℓ →
      y ∈ Work.BoseK15.corpusBox.boxL ℓ → pairG21 p Θ A u y = pairGc21 ℓ p hp Θ₀ A u y := by
  intro u y hu hy
  rw [pairG21, pairGc21]
  -- On the box the honest integrand is the `abox`-indicator of the clean integrand.
  have key : (fun x : Work.BoseDict.Xn n => star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = Set.indicator (Submission.BoseGases.abox n ℓ)
          (fun x : Work.BoseDict.Xn n => star (Θ₀ x) * A (x p.1) * A (x p.2)
            * Θ₀ (Function.update (Function.update x p.1 y) p.2 u)) := by
    funext x
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · have hx' : Function.update (Function.update x p.1 y) p.2 u
          ∈ Submission.BoseGases.abox n ℓ := update_update_mem_abox hℓ hx hy hu
      rw [Set.indicator_of_mem hx, hΘ x,
        hΘ (Function.update (Function.update x p.1 y) p.2 u),
        Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · simp only [hΘ x, Set.indicator_of_notMem hx, star_zero, zero_mul]
  rw [key, integral_indicator (Submission.BoseGases.abox_measurable n ℓ)]
  -- Change of variables to the triple box, then the coordinate identities `insertCoord2`.
  rw [integral_abox_eq_integral_triBox hℓ p hp]
  refine setIntegral_congr_fun (triBox_measurableSet ℓ p) (fun z _ => ?_)
  simp only [insertCoord2_apply_self, insertCoord2_apply_other hp, insertCoord2_update hp]

end Work.BoseBoxFock
