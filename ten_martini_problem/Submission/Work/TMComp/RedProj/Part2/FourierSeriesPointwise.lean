import Mathlib

set_option linter.style.haveILetI false

namespace Work.TMComp.RedProj.Part2

open MeasureTheory
open scoped ComplexConjugate Real

/-- `fourierCoeffOn` only depends on the interval endpoints, not on the proof of `a < b`. -/
private lemma fourierCoeffOn_irrel {a b : ℝ} (h1 h2 : a < b) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn h1 f n = fourierCoeffOn h2 f n :=
  congrArg (fun h => fourierCoeffOn h f n) (Subsingleton.elim h1 h2)

/-- `fourierCoeffOn` transports across equality of the interval endpoints. -/
private lemma fourierCoeffOn_congr_hyp {a b a' b' : ℝ} (ha : a = a') (hb : b = b')
    (h : a < b) (h' : a' < b') (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn h f n = fourierCoeffOn h' f n := by
  subst a'
  subst b'
  exact fourierCoeffOn_irrel h h' f n

theorem FourierSeriesPointwise (φ : ℝ → ℂ) (hφ : Continuous φ) (hper : ∀ x, φ (x + 1) = φ x)
    (hsum : Summable (fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ)) (x : ℝ) :
    HasSum (fun k : ℤ => fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k *
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) (φ x) := by
  haveI hT : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  -- The continuous 1-periodic function `φ` descends to the circle `ℝ / ℤ`.
  let f : C(AddCircle (1 : ℝ), ℂ) :=
    { toFun := AddCircle.liftIco (1 : ℝ) 0 φ
      continuous_toFun :=
        AddCircle.liftIco_zero_continuous (by simpa using (hper 0).symm) hφ.continuousOn }
  have hcoeff : ∀ k : ℤ, fourierCoeff (⇑f) k
      = fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k := by
    intro k
    change fourierCoeff (AddCircle.liftIco (1 : ℝ) 0 φ) k = _
    rw [fourierCoeff_liftIco_eq φ k]
    exact fourierCoeffOn_congr_hyp rfl (by norm_num) _ _ φ k
  have hsum' : Summable (fourierCoeff (⇑f)) := by
    rw [show fourierCoeff (⇑f)
        = fun k => fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k from funext hcoeff]
    exact hsum
  have hmain := has_pointwise_sum_fourier_series_of_summable (f := f) hsum' (x : AddCircle (1 : ℝ))
  -- Value at the point.
  have hpt : f (x : AddCircle (1 : ℝ)) = φ x := by
    let y : Set.Ico (0 : ℝ) (0 + (1 : ℝ)) := AddCircle.equivIco (1 : ℝ) 0 (x : AddCircle (1 : ℝ))
    have hy_mem : (y : ℝ) ∈ Set.Ico (0 : ℝ) (0 + (1 : ℝ)) := y.2
    have hy_eq : ((y : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := AddCircle.coe_equivIco
    have h1 : f (x : AddCircle (1 : ℝ))
        = AddCircle.liftIco (1 : ℝ) 0 φ ((y : ℝ) : AddCircle (1 : ℝ)) := by
      show AddCircle.liftIco (1 : ℝ) 0 φ (x : AddCircle (1 : ℝ))
        = AddCircle.liftIco (1 : ℝ) 0 φ ((y : ℝ) : AddCircle (1 : ℝ))
      rw [← hy_eq]
    have h2 : AddCircle.liftIco (1 : ℝ) 0 φ ((y : ℝ) : AddCircle (1 : ℝ)) = φ (y : ℝ) :=
      AddCircle.liftIco_coe_apply hy_mem
    rw [h1, h2]
    have hz : (((y : ℝ) - x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hy_eq, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    have hyn : (y : ℝ) = x + n • (1 : ℝ) := by rw [hn]; ring
    rw [hyn]
    exact (Function.Periodic.zsmul hper n) x
  -- The summands agree.
  have hfun : (fun i : ℤ => fourierCoeff (⇑f) i • fourier i (x : AddCircle (1 : ℝ)))
      = (fun k : ℤ => fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) := by
    funext k
    rw [hcoeff k, fourier_coe_apply]
    simp only [smul_eq_mul, Complex.ofReal_one, div_one]
  rw [hfun, hpt] at hmain
  exact hmain

end Work.TMComp.RedProj.Part2
