import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

/-- **The order-six flat bound of the reassociated `EVz`-field, *linear* in the two block
bounds.**

`EVzR Y = 2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY` is a sum of two products of a smooth angular
coefficient with one of the two blocks `Y`, `∂_θY`:

`EVzR Y = (2·(cos²θ − 2 sin²θ))·Y + sin(2θ)·∂_θY`.

Let `A ≥ 1` be the universal constant of `CoefBundle6s`, so that each of the two coefficients is
`F0 6 A` and `SmoothOpen`.  The Leibniz estimate `F0_mul` (which is *bilinear*, hence never
squares `K`) gives

* `F0 6 (2⁶·(2A)·K) (2(cos²θ − 2 sin²θ)·Y)` — coefficient constant `2A`;
* `F0 6 (2⁶·A·KY) (sin(2θ)·∂_θY)` — coefficient constant `A`, upgraded to `2⁶·(2A)·KY` by
  monotonicity since `A·KY ≥ 0`.

`F0_add` adds the two constants `2⁶(2A)K + 2⁶(2A)KY = 128·A·(K + KY)`, and `F0_congr` transfers
the bound to `EVzR Y` itself.  Hence `C = 128·A` works and is linear in `K + KY`, as required.

Everything here is `sorry`-free. -/
theorem F0SixEVzR : ∃ C : ℝ, 0 < C ∧ ∀ (K KY : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → 0 ≤ KY → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 K Y → Work.FTS.PhiStar.F0 6 KY (Work.Spaces.pth Y) →
    Work.FTS.PhiStar.F0 6 (C * (K + KY)) (Work.FTS.StrongPersist.SP6.EVzR Y) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  refine ⟨128 * A, by nlinarith, ?_⟩
  intro K KY Y hK hKY hYs hY hdY
  have hphi := hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])
  have hs2 := hcoef (fun _ θ : ℝ => Real.sin (2 * θ)) (by simp [coefFun])
  have s2phi : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hphi.2 2
  have h2phi : Work.FTS.PhiStar.F0 6 (2 * A)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hphi.1
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2] at h
    exact h
  -- the `Y`-slot
  have ht1 : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * (2 * A) * K)
      ((fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Y) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (mul_nonneg (by norm_num) hA0) hK s2phi hYs h2phi hY
  -- the `∂_θY`-slot
  have ht2 : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * A * KY)
      ((fun _ θ : ℝ => Real.sin (2 * θ)) * Work.Spaces.pth Y) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hKY hs2.2 hYs.pth hs2.1 hdY
  have hAKY : (0 : ℝ) ≤ A * KY := mul_nonneg hA0 hKY
  have ht2' : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * (2 * A) * KY)
      ((fun _ θ : ℝ => Real.sin (2 * θ)) * Work.Spaces.pth Y) :=
    ht2.mono le_rfl (by nlinarith [hAKY])
  have hsum := Work.FTS.PhiStar.CoreAux.F0_add
    (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2phi hYs)
    (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hs2.2 hYs.pth) ht1 ht2'
  have hcc : (2 : ℝ) ^ 6 * (2 * A) * K + (2 : ℝ) ^ 6 * (2 * A) * KY
      = 128 * A * (K + KY) := by ring
  rw [hcc] at hsum
  exact Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => rfl) hsum

end Work.FTS.StrongPersist.SP6
