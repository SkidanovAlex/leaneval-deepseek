import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pin_e0_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinCond_conj_real` — the θ-pin forces the condensate coefficient to be real

The `Q₂`-row dictionary (half **(A)** `pairRowNice_le_wordParts`, `FINDING_PotPairRows_exists.md`
§14.5) needs the condensate coefficient `c` of the honest mode family to be real
(`(starRingEnd ℂ) c = c`): with `c = ℓ^{-3/2}e^{iφ}` the row's blocks are `c·c̄`, `c²`, `c̄²`-weighted,
so the comparison with FS's `T₁`/`T₄` can only hold at `φ = 0`.

The node's pin hypotheses are

* `(starRingEnd ℂ) c * c = (ℓ³)⁻¹` and `e 0 =ᵐ c · θ_Λ` (the pin `hpin`), and
* `∫ conj(e 0)·θ_Λ = ℓ^{3/2}` (the θ-pin `hθp`).

Since `conj θ_Λ · θ_Λ = 1_Λ` and `|Λ| = ℓ³`, the θ-pin reads `conj c · ℓ³ = ℓ^{3/2}`, i.e.
`conj c = ℓ^{-3/2}` — **real** — whence `c = conj(conj c) = ℓ^{-3/2} = conj c`, i.e.
`(starRingEnd ℂ) c = c`.

Same computation as `Work.BoseBoxFock.pin_e0_eq` (which concludes `e 0 =ᵐ (√(ℓ³))⁻¹·θ_Λ`); here we
keep only the conclusion about `c`.  (A sibling statement `pinCond_conj_eq` exists at
`Submission/Work/BoseBoxFock/pinCond_conj_eq.lean`; this module is self-contained and independent of
it.)
-/

namespace Work.BoseBoxFock

open MeasureTheory

set_option linter.unusedVariables false

theorem pinCond_conj_real {m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} {c : ℂ}
    (hcc : (starRingEnd ℂ) c * c = ((ℓ ^ 3 : ℝ))⁻¹)
    (hec : e 0 =ᵐ[MeasureTheory.volume] fun z => c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hpair : (∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e 0 z) * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ)) :
    (starRingEnd ℂ) c = c := by
  have hself : (∫ z : EuclideanSpace ℝ (Fin 3),
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
        * Work.BoseK15.corpusBox.thetaFun ℓ z) = ((ℓ ^ 3 : ℝ) : ℂ) :=
    thetaFun_self_integral hℓ
  have hInt1 : (∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e 0 z) * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (c * Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hec] with z hz
    rw [hz]
  have hInt2 : (∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (c * Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = (starRingEnd ℂ) c * ∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    simp only [map_mul]
    ring
  have hkey : (starRingEnd ℂ) c * ((ℓ ^ 3 : ℝ) : ℂ) = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ) := by
    rw [← hself, ← hInt2, ← hInt1, hpair]
  have hsne : ((ℓ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    positivity
  have hval : (starRingEnd ℂ) c = (((ℓ ^ (3 / 2 : ℝ) / ℓ ^ 3 : ℝ)) : ℂ) := by
    have h1 : (starRingEnd ℂ) c = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ) / (((ℓ ^ 3 : ℝ)) : ℂ) := by
      rw [eq_div_iff hsne]
      exact hkey
    rw [h1, ← Complex.ofReal_div]
  have hcval : c = (((ℓ ^ (3 / 2 : ℝ) / ℓ ^ 3 : ℝ)) : ℂ) := by
    calc c = (starRingEnd ℂ) ((starRingEnd ℂ) c) := (Complex.conj_conj c).symm
      _ = (starRingEnd ℂ) ((((ℓ ^ (3 / 2 : ℝ) / ℓ ^ 3 : ℝ)) : ℂ)) := by rw [hval]
      _ = (((ℓ ^ (3 / 2 : ℝ) / ℓ ^ 3 : ℝ)) : ℂ) := by rw [Complex.conj_ofReal]
  rw [hval, hcval]

end Work.BoseBoxFock
