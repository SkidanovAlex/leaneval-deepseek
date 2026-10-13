import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

set_option maxHeartbeats 1600000

/-- **The order-five flat bound of the `∂_θ`-derivative expression `EVzD` of the `EVz`-field.**

`EVzD Y = 2·(cos²θ − 2 sin²θ)'·Y + 2·(cos²θ − 2 sin²θ)·∂_θY + (sin 2θ)'·∂_θY + D_θ(∂_θY)`
is the sum of three products of a *universal* smooth angular coefficient with one of the two
blocks `Y`, `∂_θY`, plus the angular block `D_θ(∂_θY)`.  With `A ≥ 1` the constant of
`CoefBundle6s`:

* `F0 5 (2⁵·(2A)·K) (2·(cos²θ − 2 sin²θ)'·Y)` — Leibniz (`F0_mul`);
* `F0 5 (2⁵·(2A)·KY) (2·(cos²θ − 2 sin²θ)·∂_θY)` — Leibniz;
* `F0 5 (2⁵·A·KY) ((sin 2θ)'·∂_θY)` — Leibniz;
* `F0 5 KY (D_θ(∂_θY))` — `F0_Dth` (one more angular derivative of the `F0 6 KY (∂_θY)` datum);

the four constants sum to `64AK + 96AKY + KY ≤ (160A+1)·(K+KY)`, and `F0_congr` transfers the
bound to `EVzD Y` itself.  Everything is `sorry`-free. -/
theorem F0FiveEVzD : ∃ C : ℝ, 0 < C ∧ ∀ (K KY : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → 0 ≤ KY → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 K Y → Work.FTS.PhiStar.F0 6 KY (Work.Spaces.pth Y) →
    Work.FTS.PhiStar.F0 5 (C * (K + KY)) (Work.FTS.StrongPersist.SP6.EVzD Y) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  refine ⟨160 * A + 1, by linarith, ?_⟩
  intro K KY Y hK hKY hYs hY hdY
  -- the three angular coefficients
  have hphi := hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])
  have hdPhi := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
    (by simp [coefFun])
  have hdSin := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) (by simp [coefFun])
  -- lower everything to order `5`
  have hY5 : Work.FTS.PhiStar.F0 5 K Y :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := K) (K' := K) (f := Y)
      (by norm_num) le_rfl hY
  have hdY5 : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.pth Y) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := KY) (K' := KY)
      (f := Work.Spaces.pth Y) (by norm_num) le_rfl hdY
  have hphi5 : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := A) (K' := A)
      (f := fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by norm_num) le_rfl hphi.1
  have hdPhi5 : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := A) (K' := A)
      (f := fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
      (by norm_num) le_rfl hdPhi.1
  have hdSin5 : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := A) (K' := A)
      (f := fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) (by norm_num) le_rfl hdSin.1
  -- the coefficients `2·(cos²−2sin²)` and `2·(cos²−2sin²)'`
  have h2phi : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hphi5
    simpa using h
  have h2dPhi : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hdPhi5
    simpa using h
  -- smoothness of the coefficients
  have s2phi : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hphi.2 2
  have s2dPhi : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hdPhi.2 2
  have sdsin : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) := hdSin.2
  -- the four summands
  have hX1 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * K)
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_mul (n := 5)
      (K := 2 * A) (K' := K)
      (f := fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
      (g := Y) (by linarith) hK s2dPhi hYs h2dPhi hY5
    simpa using h
  have hX2 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * KY)
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_mul (n := 5)
      (K := 2 * A) (K' := KY)
      (f := fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2))
      (g := Work.Spaces.pth Y) (by linarith) hKY s2phi hYs.pth h2phi hdY5
    simpa using h
  have hX3 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_mul (n := 5)
      (K := A) (K' := KY)
      (f := fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ)
      (g := Work.Spaces.pth Y) hA0 hKY sdsin hYs.pth hdSin5 hdY5
    simpa using h
  have hX4 : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_Dth (n := 5) hdY
  -- smoothness of the summands
  have sm1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2dPhi hYs
  have sm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2phi hYs.pth
  have sm3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul sdsin hYs.pth
  have sm4 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    hYs.pth.Dth
  -- assemble
  have hX23 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
          + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_add sm2 sm3 hX2 hX3
    simpa using h
  have sm23 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
          + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add sm2 sm3
  have hX123 : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY))
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ
          + ((2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
            + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_add sm1 sm23 hX1 hX23
    simpa using h
  have sm123 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ
          + ((2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
            + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add sm1 sm23
  have htot : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY) + KY)
      (fun z θ : ℝ =>
        ((2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ
          + ((2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
            + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ))
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_add sm123 sm4 hX123 hX4
    simpa using h
  -- normalise the constant
  have hconst : (2 : ℝ) ^ 5 * (2 * A) * K
      + ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY) + KY
      ≤ (160 * A + 1) * (K + KY) := by
    nlinarith [hA0, hK, hKY, mul_nonneg hA0 hK, mul_nonneg hA0 hKY]
  have htot' := htot.mono le_rfl hconst
  refine Work.FTS.PhiStar.CoreAux.F0_congr (f := Work.FTS.StrongPersist.SP6.EVzD Y) ?_ htot'
  intro z θ _ _ _
  simp only [Work.FTS.StrongPersist.SP6.EVzD, Work.Spaces.Dth, Work.Spaces.pth]
  ring

end Work.FTS.StrongPersist.SP6
