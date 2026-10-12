import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.blockIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowShape_pinCond_gen` — the pair shapes at a generalised pinned condensate

The two block-II shapes `rowShape21`, `rowShape23` at the **generalised pinned condensate**
`y ↦ c * thetaFun ℓ y` (the sharp indicator of the box `boxL ℓ`, scaled by `c`), with the state
`Θ` supported in the `n`-particle box `Work.MB.boxPow n ℓ`.

The mechanism is identical to `rowShape_pinCond` (which is the special case
`ℓ = ellH v μ` of `pinCond v μ c = fun y => c * thetaFun (ellH v μ) y`): each condensate
factor `c * thetaFun ℓ z` is either `c` (when `z ∈ boxL ℓ`) or killed by the vanishing of `Θ`
(either `Θ x = 0` because `x ∉ boxPow n ℓ`, or `Θ (updated) = 0` because the updated configuration
has the offending variable in one of the two slots `p.1 ≠ p.2`).  Hence the whole triple integral
collapses onto the weightless form with the scalar `c·c` (resp. `star c · star c`).

Nothing here needs the strict positivity of `ℓ`; `hℓ` is kept for the interface only.
-/

noncomputable section

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.BoseBoxFock

theorem rowShape_pinCond_gen {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℂ}
    {Θ : Work.BoseDict.Xn n → ℂ}
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    (Work.BoseBoxFock.rowShape21 Θ
        (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) K p
      = (c * c) * (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
          ∫ u : EuclideanSpace ℝ (Fin 3), star (Θ x) * K u y
            * Θ (Function.update (Function.update x p.1 y) p.2 u)))
    ∧ (Work.BoseBoxFock.rowShape23 Θ
        (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
        (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) K p
      = ((starRingEnd ℂ) c * (starRingEnd ℂ) c)
          * (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
              ∫ u : EuclideanSpace ℝ (Fin 3), star (Θ x) * K (x p.1) (x p.2)
                * Θ (Function.update (Function.update x p.1 y) p.2 u))) := by
  classical
  -- `Θ` vanishes off the `n`-particle box
  have hz : ∀ z : Work.BoseDict.Xn n, z ∉ Work.MB.boxPow n ℓ → Θ z = 0 := by
    intro z hz'
    by_contra h
    exact hz' (hΘs (Function.mem_support.mpr h))
  -- the box membership is coordinatewise
  have hnotpow : ∀ z : Work.BoseDict.Xn n,
      z ∉ Work.MB.boxPow n ℓ ↔ ¬ (∀ i, z i ∈ Work.BoseK15.corpusBox.boxL ℓ) := by
    intro z
    rw [Work.MB.boxPow, Set.mem_univ_pi]
  -- the two slots of the twice-updated configuration
  have hupd1 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      Function.update (Function.update x p.1 y) p.2 u p.1 = y := by
    intro x y u; simp [hp]
  have hupd2 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      Function.update (Function.update x p.1 y) p.2 u p.2 = u := by
    intro x y u; simp
  -- the condensate factor at a point of the box is `c`
  have hA : ∀ z : EuclideanSpace ℝ (Fin 3),
      z ∈ Work.BoseK15.corpusBox.boxL ℓ → c * Work.BoseK15.corpusBox.thetaFun ℓ z = c := by
    intro z hz'
    simp only [Work.BoseB4.BoxData.thetaFun_apply, hz', if_true, mul_one]
  have hA0 : ∀ z : EuclideanSpace ℝ (Fin 3),
      z ∉ Work.BoseK15.corpusBox.boxL ℓ → c * Work.BoseK15.corpusBox.thetaFun ℓ z = 0 := by
    intro z hz'
    simp only [Work.BoseB4.BoxData.thetaFun_apply, hz', if_false, mul_zero]
  -- ### the two pointwise identities
  have h21 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      star (Θ x) * (c * Work.BoseK15.corpusBox.thetaFun ℓ (x p.1))
        * (c * Work.BoseK15.corpusBox.thetaFun ℓ (x p.2)) * K u y
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = (c * c) * (star (Θ x) * K u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x y u
    by_cases hx1 : x p.1 ∈ Work.BoseK15.corpusBox.boxL ℓ
    · by_cases hx2 : x p.2 ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [hA _ hx1, hA _ hx2]; ring
      · have h0 : Θ x = 0 := hz x (by rw [hnotpow]; intro hall; exact hx2 (hall p.2))
        rw [h0, star_zero]; ring
    · have h0 : Θ x = 0 := hz x (by rw [hnotpow]; intro hall; exact hx1 (hall p.1))
      rw [h0, star_zero]; ring
  have h23 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      star (Θ x) * K (x p.1) (x p.2) * star (c * Work.BoseK15.corpusBox.thetaFun ℓ y)
        * star (c * Work.BoseK15.corpusBox.thetaFun ℓ u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = ((starRingEnd ℂ) c * (starRingEnd ℂ) c) * (star (Θ x) * K (x p.1) (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x y u
    by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ
    · by_cases hu : u ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [hA _ hy, hA _ hu, show (starRingEnd ℂ) c = star c from rfl]
        ring
      · have hu0 : c * Work.BoseK15.corpusBox.thetaFun ℓ u = 0 := hA0 _ hu
        have hupd : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
          apply hz
          rw [hnotpow]
          intro hall
          exact hu (hupd2 x y u ▸ hall p.2)
        rw [hu0, star_zero, hupd]; ring
    · have hy0 : c * Work.BoseK15.corpusBox.thetaFun ℓ y = 0 := hA0 _ hy
      have hupd : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
        apply hz
        rw [hnotpow]
        intro hall
        exact hy (hupd1 x y u ▸ hall p.1)
      rw [hy0, star_zero, hupd]; ring
  -- ### assembly: rewrite pointwise, then pull the constant out of the iterated integrals
  refine ⟨?_, ?_⟩
  · rw [Work.BoseBoxFock.rowShape21]
    simp only [h21]
    simp_rw [MeasureTheory.integral_const_mul]
  · rw [Work.BoseBoxFock.rowShape23]
    simp only [h23]
    simp_rw [MeasureTheory.integral_const_mul]

end Work.BoseBoxFock
