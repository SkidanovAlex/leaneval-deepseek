import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.rowShape_pinCond
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The block-I pair shape at the pinned condensate, at a free box side `ℓ`.**  This is the first conjunct of the PROVED `Work.BoseBoxFock.rowShape_pinCond` with `ellH v μ` replaced by an arbitrary `0 < ℓ` and `pinCond v μ c` replaced by the (definitionally equal) `fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y`.  The proof is a verbatim copy of that conjunct: for every `x y u`, if `x p.1 ∉ boxL ℓ` (resp. `u ∉ boxL ℓ`) then `Θ x = 0` (resp. `Θ (x[p.1↦y][p.2↦u]) = 0`) by the support hypothesis, and otherwise the two indicator factors equal `1` and contribute the scalar `c·c̄`; then pull the constant out of the iterated integral.  (`hℓ` is not actually used, as in the source.) -/
theorem rowShape13_pinCond_gen {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Work.BoseDict.Xn n → ℂ} {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ} {c : ℂ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) : Work.BoseBoxFock.rowShape13 Θ (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) K p = (c * (starRingEnd ℂ) c) * (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3), star (Θ x) * K (x p.2) y * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
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
  have hupd1 : ∀ (x : Work.BoseDict.Xn n) (y u : E3),
      Function.update (Function.update x p.1 y) p.2 u p.1 = y := by
    intro x y u; simp [hp]
  have hupd2 : ∀ (x : Work.BoseDict.Xn n) (y u : E3),
      Function.update (Function.update x p.1 y) p.2 u p.2 = u := by
    intro x y u; simp
  -- ### the pointwise identity
  have h13 : ∀ (x : Work.BoseDict.Xn n) (y u : E3),
      star (Θ x) * (c * Work.BoseK15.corpusBox.thetaFun ℓ (x p.1)) * K (x p.2) y
        * star (c * Work.BoseK15.corpusBox.thetaFun ℓ u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = (c * star c) * (star (Θ x) * K (x p.2) y
          * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x y u
    by_cases hx : x p.1 ∈ Work.BoseK15.corpusBox.boxL ℓ
    · have hx1 : Work.BoseK15.corpusBox.thetaFun ℓ (x p.1) = 1 := by
        rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos hx]
      by_cases hu : u ∈ Work.BoseK15.corpusBox.boxL ℓ
      · have hu1 : Work.BoseK15.corpusBox.thetaFun ℓ u = 1 := by
          rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos hu]
        rw [hx1, hu1, mul_one]
        ring
      · have hu0 : Work.BoseK15.corpusBox.thetaFun ℓ u = 0 := by
          rw [Work.BoseB4.BoxData.thetaFun_apply, if_neg hu]
        have hupd : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
          apply hz
          rw [hnotpow]
          intro hall
          exact hu (hupd2 x y u ▸ hall p.2)
        rw [hu0, hupd]
        simp
    · have hx0 : star (Θ x) = 0 := by
        have h0 : Θ x = 0 := hz x (by rw [hnotpow]; intro hall; exact hx (hall p.1))
        rw [h0, star_zero]
      rw [hx0]; ring
  -- ### assembly: rewrite pointwise, then pull the constant out of the iterated integrals
  rw [Work.BoseBoxFock.rowShape13]
  simp only [h13]
  simp_rw [MeasureTheory.integral_const_mul]
  -- identify `star c` with `starRingEnd ℂ c`
  rfl

end Work.BoseBoxFock
