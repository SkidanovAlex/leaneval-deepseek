import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea7.P231

/-- Auxiliary arithmetic fact: if `a, b` are coprime integers with `a` odd and `b` even, then
`a² - b²` is coprime to `2ab`.

Indeed `a² - b² = (a + b)(a - b)`, and each of `a + b`, `a - b` is coprime to both `a` and `b`
(the Bézout coefficients for `IsCoprime a b` are transported directly), hence `a² - b²` is coprime
to `ab`; finally `a² - b²` is odd, so it is coprime to `2` as well. -/
private lemma isCoprime_sq_int {a b : ℤ} (h : IsCoprime a b) (ha : Odd a) (hb : Even b) :
    IsCoprime (a ^ 2 - b ^ 2) (2 * a * b) := by
  obtain ⟨u, v, huv⟩ := h
  -- `a + b` is coprime to both `a` and `b` (Bézout coefficients transported along `a = (a+b) - b`)
  have hp1 : IsCoprime (a + b) a := by
    refine ⟨v, u - v, ?_⟩
    linear_combination huv
  have hp2 : IsCoprime (a + b) b := by
    refine ⟨u, v - u, ?_⟩
    linear_combination huv
  have hm1 : IsCoprime (a - b) a := by
    refine ⟨-v, u + v, ?_⟩
    linear_combination huv
  have hm2 : IsCoprime (a - b) b := by
    refine ⟨u, v + u, ?_⟩
    linear_combination huv
  have h1 : IsCoprime (a + b) (a * b) := hp1.mul_right hp2
  have h2 : IsCoprime (a - b) (a * b) := hm1.mul_right hm2
  -- `a² - b² = (a + b)(a - b)` is coprime to `a * b`
  have hab : IsCoprime (a ^ 2 - b ^ 2) (a * b) := by
    have hh : IsCoprime ((a + b) * (a - b)) (a * b) := h1.mul_left h2
    rw [show (a + b) * (a - b) = a ^ 2 - b ^ 2 by ring] at hh
    exact hh
  -- `a² - b²` is odd, hence coprime to `2`
  have hodd : Odd (a ^ 2 - b ^ 2) :=
    ha.pow.sub_even (Even.pow_of_ne_zero hb (by norm_num))
  have h2c : IsCoprime (a ^ 2 - b ^ 2) 2 := by
    obtain ⟨k, hk⟩ := hodd
    refine ⟨1, -k, ?_⟩
    linear_combination hk
  have hfin : IsCoprime (a ^ 2 - b ^ 2) (a * b * 2) := hab.mul_right h2c
  rw [show a * b * 2 = 2 * a * b by ring] at hfin
  exact hfin

theorem isCoprime_sq {e : GaussianInt} (hp : Work.FIPlan.IsPrimary e)
    (h : IsCoprime e.re e.im) : IsCoprime (e * e).re (e * e).im := by
  obtain ⟨ha, hb, _⟩ := hp
  have h2 := isCoprime_sq_int h ha hb
  rw [Zsqrtd.re_mul, Zsqrtd.im_mul]
  convert h2 using 2 <;> ring

end Work.FIArea7.P231
