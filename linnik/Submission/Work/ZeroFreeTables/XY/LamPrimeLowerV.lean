/-
# ZeroFreeTables/XY/LamPrimeLowerV

The order-2 `λ'`-estimate, **height-restricted to `|Im u| ≤ 5`**: every zero `u ≠ ρ₁, ρ̄₁` of a
real character `χ₁` inside the strip `|Im| ≤ 5` satisfies `λ(u) ≥ 1`, provided the exceptional
zero `ρ₁` (the `λ`-minimiser over the strip `|Im| ≤ 10` of *all* non-principal characters) has
`λ₁ ≤ 0.628`.

Same reduction as `XY/LamPrimeLower.lean`, but with the height-10-safe `Nebenfall`
`XY.NebenfallOrd2V` (the sibling statement at `|u.im| ≤ 10` is FALSE: its windows reach height
`12 + δ`).  The height `5` is what the F-method `λ₁`-inequality `XY.FMethodOrd2` needs (its
windows sit at heights `≤ 3 + δ < 4`).

Numerics: `LamPrimeSup` gives `sup G ≤ 1/25`, `sup H ≤ 1/25`; `LamPrimeFVal` gives
`F(-0.628) ≤ 1.16`, `F(0.372) ≥ 0.77`, `F 0 = 8/9`, `f 0 = 64/45`; `LamPrime_mono` gives
`F(-λ₁) - F(1-λ₁) ≤ F(-0.628) - F(0.372) ≤ 0.39`; so the Nebenfall inequality reads
`0 ≤ 117/200 - 16/9 + 32/45 + 3/25 + 1/4 = -697/5400 < 0`, a contradiction.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.LamPrimeDefs
import Submission.Work.ZeroFreeTables.XY.LamPrimeFVal
import Submission.Work.ZeroFreeTables.XY.LamPrimeSup
import Submission.Work.ZeroFreeTables.XY.NebenfallOrd2V
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

open Work.LinnikContract
open MeasureTheory

theorem mono_aux {lam lam' t : ℝ} (hl : lam ≤ lam') (ht : 0 ≤ t) :
    Real.exp (lam * t) - Real.exp ((lam - 1) * t) ≤ Real.exp (lam' * t) - Real.exp ((lam' - 1) * t) := by
  have h1 : Real.exp (lam * t) ≤ Real.exp (lam' * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (0:ℝ) ≤ 1 - Real.exp (-t) := by
    have h3 : Real.exp (-t) ≤ 1 := by
      have := Real.exp_le_exp.mpr (show (-t : ℝ) ≤ 0 by linarith)
      simpa using this
    linarith
  have f1 : Real.exp (lam * t) - Real.exp ((lam - 1) * t) = Real.exp (lam * t) * (1 - Real.exp (-t)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  have f2 : Real.exp (lam' * t) - Real.exp ((lam' - 1) * t) = Real.exp (lam' * t) * (1 - Real.exp (-t)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [f1, f2]
  exact mul_le_mul_of_nonneg_right h1 h2

/-- `λ ↦ F(-λ) - F(1-λ)` is monotone on `[0,1]` — the joint monotonicity that lets the
Nebenfall inequality be read at the right end of the `λ₁`-interval. -/
theorem LamPrime_mono {lam lam' : ℝ} (_h0 : 0 ≤ lam) (hl : lam ≤ lam') (_hl' : lam' ≤ 1) :
    xyF (-lam) - xyF (1 - lam) ≤ xyF (-lam') - xyF (1 - lam') := by
  have hx : (0:ℝ) ≤ xyT.x₀ := le_of_lt xyT.x₀_pos
  have hcont : ∀ c : ℝ, ContinuousOn (fun t : ℝ => Real.exp (-(c * t)) * xyT.f t)
      (Set.Icc 0 xyT.x₀) := by
    intro c
    refine (Continuous.continuousOn (by fun_prop)).mul (xyT.f_cont.mono ?_)
    intro t ht; exact ht.1
  have hI : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (-(c * t)) * xyT.f t)
      volume 0 xyT.x₀ :=
    fun c => ContinuousOn.intervalIntegrable_of_Icc hx (hcont c)
  have h1 : xyF (-lam) = ∫ t in (0:ℝ)..xyT.x₀, Real.exp (-((-lam) * t)) * xyT.f t :=
    TestFn_F_eq_integral xyT (-lam)
  have h2 : xyF (1 - lam) = ∫ t in (0:ℝ)..xyT.x₀, Real.exp (-((1 - lam) * t)) * xyT.f t :=
    TestFn_F_eq_integral xyT (1 - lam)
  have h3 : xyF (-lam') = ∫ t in (0:ℝ)..xyT.x₀, Real.exp (-((-lam') * t)) * xyT.f t :=
    TestFn_F_eq_integral xyT (-lam')
  have h4 : xyF (1 - lam') = ∫ t in (0:ℝ)..xyT.x₀, Real.exp (-((1 - lam') * t)) * xyT.f t :=
    TestFn_F_eq_integral xyT (1 - lam')
  rw [h1, h2, h3, h4,
    ← intervalIntegral.integral_sub (hI (-lam)) (hI (1 - lam)),
    ← intervalIntegral.integral_sub (hI (-lam')) (hI (1 - lam'))]
  apply intervalIntegral.integral_mono_on hx ((hI (-lam)).sub (hI (1 - lam)))
    ((hI (-lam')).sub (hI (1 - lam')))
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hf : 0 ≤ xyT.f t := xyT.f_nonneg t
  have hkey : Real.exp (-(-lam * t)) - Real.exp (-((1 - lam) * t))
      ≤ Real.exp (-(-lam' * t)) - Real.exp (-((1 - lam') * t)) := by
    have a1 : Real.exp (-(-lam * t)) = Real.exp (lam * t) := by congr 1; ring
    have a2 : Real.exp (-((1 - lam) * t)) = Real.exp ((lam - 1) * t) := by congr 1; ring
    have a3 : Real.exp (-(-lam' * t)) = Real.exp (lam' * t) := by congr 1; ring
    have a4 : Real.exp (-((1 - lam') * t)) = Real.exp ((lam' - 1) * t) := by congr 1; ring
    rw [a1, a2, a3, a4]
    exact mono_aux hl ht0
  have hgl : Real.exp (-(-lam * t)) * xyT.f t - Real.exp (-((1 - lam) * t)) * xyT.f t
      = (Real.exp (-(-lam * t)) - Real.exp (-((1 - lam) * t))) * xyT.f t := by ring
  have hgr : Real.exp (-(-lam' * t)) * xyT.f t - Real.exp (-((1 - lam') * t)) * xyT.f t
      = (Real.exp (-(-lam' * t)) - Real.exp (-((1 - lam') * t))) * xyT.f t := by ring
  rw [hgl, hgr]
  exact mul_le_mul_of_nonneg_right hkey hf

theorem LamPrimeLowerV : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
    Work.LinnikContract.lamOf q ρ₁ ≤ 628/1000 →
    ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 5 → u ≠ ρ₁ →
      u ≠ starRingEnd ℂ ρ₁ → 1 ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨hsupG, hsupH⟩ := LamPrimeSup
  obtain ⟨qN, hN⟩ := NebenfallOrd2V
  obtain ⟨hF1, hF2, hF0, hf0⟩ := LamPrimeFVal
  refine ⟨max qN 2, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hsq him hle u hu huim hur huc
  have hqN : qN ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hIsZ : IsZ χ₁ ρ₁ := hm.1.1
  have hlam1nn : 0 ≤ lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hIsZ
  by_contra hcon
  push_neg at hcon
  have hle1 : lamOf q u ≤ 1 := le_of_lt hcon
  have hineq := hN q hqN χ₁ ρ₁ u hm hsq him hu huim hur huc hlam1nn hle1 hle
  -- the two suprema are bounded by `1/25`
  have hSupG : sSup (Set.range (fun t : ℝ => Gfun 1 (lamOf q ρ₁) t)) ≤ 1/25 :=
    csSup_le (Set.range_nonempty _) (fun x hx => by
      obtain ⟨t, rfl⟩ := hx
      exact hsupG _ hlam1nn hle t)
  have hSupH : sSup (Set.range (fun t : ℝ => Hfun 1 (lamOf q ρ₁) t)) ≤ 1/25 :=
    csSup_le (Set.range_nonempty _) (fun x hx => by
      obtain ⟨t, rfl⟩ := hx
      exact hsupH _ hlam1nn hle t)
  -- `F(λ_u - λ₁) ≥ F(1 - λ₁)`
  have hmon2 : xyF (1 - lamOf q ρ₁) ≤ xyF (lamOf q u - lamOf q ρ₁) := by
    have hab : lamOf q u - lamOf q ρ₁ ≤ 1 - lamOf q ρ₁ := by linarith
    exact TestFn_F_antitone xyT hab
  -- `F(-λ₁) - F(1-λ₁) ≤ F(-628/1000) - F(372/1000)`
  have hmon3 : xyF (-(lamOf q ρ₁)) - xyF (1 - lamOf q ρ₁)
      ≤ xyF (-(628/1000)) - xyF (372/1000) := by
    have hnum : (372:ℝ)/1000 = 1 - 628/1000 := by norm_num
    have hmono := LamPrime_mono hlam1nn hle (by norm_num : (628:ℝ)/1000 ≤ 1)
    rw [hnum]
    exact hmono
  have hfin : 3/2 * (xyF (-(628/1000)) - xyF (372/1000)) - 2 * xyF 0 + (xyT.f 0)/2
      + 2 * (1/25:ℝ) + 1/25 + 1/4 < 0 := by
    rw [hF0, hf0]
    linarith [hF1, hF2]
  have hstep : 3/2 * (xyF (-(lamOf q ρ₁)) - xyF (lamOf q u - lamOf q ρ₁)) - 2 * xyF 0
      + (xyT.f 0)/2 + 2 * (1/25:ℝ) + 1/25 + 1/4 < 0 := by
    have h1 : (3:ℝ)/2 * (xyF (-(lamOf q ρ₁)) - xyF (lamOf q u - lamOf q ρ₁))
        ≤ 3/2 * (xyF (-(628/1000)) - xyF (372/1000)) := by
      have ha : xyF (-(lamOf q ρ₁)) - xyF (1 - lamOf q ρ₁)
          ≤ xyF (-(628/1000)) - xyF (372/1000) := hmon3
      linarith
    linarith [h1, hfin]
  linarith [hineq, hSupG, hSupH, hstep]

end Work.ZeroFreeTables.XY
