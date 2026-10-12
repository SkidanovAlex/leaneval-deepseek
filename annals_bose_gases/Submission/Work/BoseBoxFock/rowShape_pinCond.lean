import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairRowS2Row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowShape_pinCond` — the three pair shapes at the pinned condensate

The state factor `A = B = pinCond v μ c = c·θ_Λ` is the pinned condensate, where
`θ_Λ = thetaFun (ellH v μ)` is the **sharp indicator** of the one-particle box
`Work.BoseK15.corpusBox.boxL (ellH v μ)`, and the state `Θ` is supported in the `n`-particle box
`Work.MB.boxPow n (ellH v μ)`.

Consequently each of the three shapes collapses onto the *weightless* triple integral: the two
condensate factors contribute exactly the scalar `c·c̄` (resp. `c²`, resp. `c̄²`), and neither the
theta-factor nor the box restriction survives.  Pointwise, for every `x y u`:

* if `x p.1 ∉ boxL` (resp. `x p.2 ∉ boxL`), then `x ∉ boxPow` and hence `Θ x = 0` by the support
  hypothesis, killing the term;
* if `y ∉ boxL` (resp. `u ∉ boxL`), then `Θ (x[p.1↦y][p.2↦u]) = 0` because the updated
  configuration has `y` in slot `p.1` (here `p.1 ≠ p.2` is used) and `u` in slot `p.2`;
* otherwise all the indicator factors equal `1`.
-/

namespace Work.BoseBoxFock

theorem rowShape_pinCond {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {c : ℂ}
    {Θ : Work.BoseDict.Xn n → ℂ} {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ)) :
    Work.BoseBoxFock.rowShape13 Θ (Work.BoseBoxFock.pinCond v μ c) (Work.BoseBoxFock.pinCond v μ c) K p
        = (c * (starRingEnd ℂ) c)
          * (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
              star (Θ x) * K (x p.2) y
                * Θ (Function.update (Function.update x p.1 y) p.2 u))
      ∧ Work.BoseBoxFock.rowShape21 Θ (Work.BoseBoxFock.pinCond v μ c) K p
        = (c * c)
          * (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
              star (Θ x) * K u y
                * Θ (Function.update (Function.update x p.1 y) p.2 u))
      ∧ Work.BoseBoxFock.rowShape23 Θ (Work.BoseBoxFock.pinCond v μ c) (Work.BoseBoxFock.pinCond v μ c) K p
        = ((starRingEnd ℂ) c * (starRingEnd ℂ) c)
          * (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
              star (Θ x) * K (x p.1) (x p.2)
                * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
  classical
  -- `Θ` vanishes off the `n`-particle box
  have hz : ∀ z : Work.BoseDict.Xn n, z ∉ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ) → Θ z = 0 := by
    intro z hz'
    by_contra h
    exact hz' (hΘs (Function.mem_support.mpr h))
  -- the box membership is coordinatewise
  have hnotpow : ∀ z : Work.BoseDict.Xn n,
      z ∉ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ) ↔
        ¬ (∀ i, z i ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) := by
    intro z
    rw [Work.MB.boxPow, Set.mem_univ_pi]
  -- the two slots of the twice-updated configuration
  have hupd1 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      Function.update (Function.update x p.1 y) p.2 u p.1 = y := by
    intro x y u; simp [hp]
  have hupd2 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      Function.update (Function.update x p.1 y) p.2 u p.2 = u := by
    intro x y u; simp
  -- ### the three pointwise identities
  have h13 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      star (Θ x) * Work.BoseBoxFock.pinCond v μ c (x p.1) * K (x p.2) y
        * star (Work.BoseBoxFock.pinCond v μ c u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = (c * star c) * (star (Θ x) * K (x p.2) y
          * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x y u
    by_cases hx : x p.1 ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
    · have hx1 : Work.BoseBoxFock.pinCond v μ c (x p.1) = c := by
        simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hx, if_true,
          mul_one]
      by_cases hu : u ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
      · have hu1 : Work.BoseBoxFock.pinCond v μ c u = c := by
          simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hu, if_true,
            mul_one]
        rw [hx1, hu1]; ring
      · have hu0 : Work.BoseBoxFock.pinCond v μ c u = 0 := by
          simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hu, if_false,
            mul_zero]
        have hupd : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
          apply hz
          rw [hnotpow]
          intro hall
          exact hu (hupd2 x y u ▸ hall p.2)
        rw [hu0, hupd]; simp
    · have hx0 : star (Θ x) = 0 := by
        have h0 : Θ x = 0 := hz x (by rw [hnotpow]; intro hall; exact hx (hall p.1))
        rw [h0, star_zero]
      rw [hx0]; ring
  have h21 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      star (Θ x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
        * Work.BoseBoxFock.pinCond v μ c (x p.2) * K u y
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = (c * c) * (star (Θ x) * K u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x y u
    have hx0 : star (Θ x) = 0 → star (Θ x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
        * Work.BoseBoxFock.pinCond v μ c (x p.2) * K u y
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
        = (c * c) * (star (Θ x) * K u y
            * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
      intro h; rw [h]; ring
    by_cases hx1 : x p.1 ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
    · by_cases hx2 : x p.2 ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
      · have h1 : Work.BoseBoxFock.pinCond v μ c (x p.1) = c := by
          simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hx1, if_true,
            mul_one]
        have h2 : Work.BoseBoxFock.pinCond v μ c (x p.2) = c := by
          simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hx2, if_true,
            mul_one]
        rw [h1, h2]; ring
      · apply hx0
        have h0 : Θ x = 0 := hz x (by rw [hnotpow]; intro hall; exact hx2 (hall p.2))
        rw [h0, star_zero]
    · apply hx0
      have h0 : Θ x = 0 := hz x (by rw [hnotpow]; intro hall; exact hx1 (hall p.1))
      rw [h0, star_zero]
  have h23 : ∀ (x : Work.BoseDict.Xn n) (y u : EuclideanSpace ℝ (Fin 3)),
      star (Θ x) * K (x p.1) (x p.2) * star (Work.BoseBoxFock.pinCond v μ c y)
        * star (Work.BoseBoxFock.pinCond v μ c u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = (star c * star c) * (star (Θ x) * K (x p.1) (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x y u
    by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
    · by_cases hu : u ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
      · have h1 : Work.BoseBoxFock.pinCond v μ c y = c := by
          simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hy, if_true,
            mul_one]
        have h2 : Work.BoseBoxFock.pinCond v μ c u = c := by
          simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hu, if_true,
            mul_one]
        rw [h1, h2]; ring
      · have hu0 : Work.BoseBoxFock.pinCond v μ c u = 0 := by
          simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hu, if_false,
            mul_zero]
        have hupd : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
          apply hz
          rw [hnotpow]
          intro hall
          exact hu (hupd2 x y u ▸ hall p.2)
        rw [hu0, hupd]; ring
    · have hy0 : Work.BoseBoxFock.pinCond v μ c y = 0 := by
        simp only [Work.BoseBoxFock.pinCond, Work.BoseB4.BoxData.thetaFun_apply, hy, if_false,
          mul_zero]
      have hupd : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
        apply hz
        rw [hnotpow]
        intro hall
        exact hy (hupd1 x y u ▸ hall p.1)
      rw [hy0, hupd]; ring
  -- ### assembly: rewrite pointwise, then pull the constant out of the iterated integrals
  refine ⟨?_, ?_, ?_⟩
  · rw [Work.BoseBoxFock.rowShape13]
    simp only [h13]
    simp_rw [MeasureTheory.integral_const_mul]
    -- identify `star c` with `starRingEnd ℂ c`
    rfl
  · rw [Work.BoseBoxFock.rowShape21]
    simp only [h21]
    simp_rw [MeasureTheory.integral_const_mul]
  · rw [Work.BoseBoxFock.rowShape23]
    simp only [h23]
    simp_rw [MeasureTheory.integral_const_mul]
    -- identify `star c` with `starRingEnd ℂ c`
    rfl

end Work.BoseBoxFock
