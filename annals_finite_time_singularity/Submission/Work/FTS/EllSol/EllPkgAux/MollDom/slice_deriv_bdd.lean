/-
# Boundedness of the angular derivative of a trace-class slice

For a trace-class datum `G` (`Work.FTS.EllSol.EllPkgAux.TraceClass G`) and a fixed radius
`w > 0`, the angular derivative of the slice `s ↦ G w s` is bounded on `(0, π/2)`.

The two ingredients are

* the *honesty* of the `∂_θ²`-slice (`SliceHonestOpen`, the last conjunct of `TraceClass`),
  which makes `θ ↦ (∂_θ² G)(w,θ)² · sin(2θ)^{-η}` integrable on `Iθ`; and
* the fundamental theorem of calculus for the slice, which writes
  `∂_θG(w,s) = ∂_θG(w,π/4) ∓ ∫_{s}^{π/4} ∂_θ²G(w,t) dt`, together with the interval
  Cauchy–Schwarz bound `|∫ f| ≤ √(∫ f²)·√(length)`.

Since `η = 99/100 < 1`, `sin(2θ)^{-η}` is an *integrable* weight at the two endpoints, and
the uniform bound in `s` is precisely the statement that `s ↦ ∫_s^{π/4} |∂_θ²G|` stays
bounded as `s → 0⁺` (and symmetrically at `π/2`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.Base
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

theorem slice_deriv_bdd (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun s' : ℝ => G w s') s| ≤ M := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hhon⟩ := hT
  -- ## The `C²`-regularity of the slice and the weighted `L²`-bound on `∂_θ²G`
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G w θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm.curry_θ hw).of_le hsmo
  have hInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    have hc : (0 : ℝ) < (Work.Spaces.w w) ^ 2 := by
      rw [Work.Spaces.w]; positivity
    have h0' := hhon.1 w hw
    have hEq : ∀ θ : ℝ, ((Work.Spaces.w w) ^ 2)⁻¹ *
        (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      intro θ
      rw [show Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2 * (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
            * Work.FTS.EllipticEst.thEta θ) from by ring]
      exact inv_mul_cancel_left₀ (ne_of_gt hc) _
    rw [show (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.w w) ^ 2)⁻¹ *
          (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ) from funext (fun θ => (hEq θ).symm)]
    exact h0'.const_mul _
  -- ## The two landmark points and the uniform estimate on compact subintervals
  have hq0 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hq1 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hkey : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 → b - a ≤ Real.pi / 4 →
      |∫ t in a..b, deriv (deriv (fun θ' : ℝ => G w θ')) t|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * Real.sqrt (Real.pi / 4) := by
    intro a b ha hab hb hlen
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    have hcg : ContinuousOn (deriv (deriv (fun θ' : ℝ => G w θ'))) (Set.uIcc a b) :=
      (Work.FTS.EllSol.c2_continuousOn_deriv_deriv hf2).mono hsub
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab
      (f := fun t : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) t)
      (g := fun _ : ℝ => (1 : ℝ)) hcg continuous_const.continuousOn
    have hone : ∫ t in a..b, (1 : ℝ) ^ 2 = b - a := by
      rw [show (1 : ℝ) ^ 2 = 1 by norm_num, intervalIntegral.integral_const]
      simp
    have hsq : ∫ t in a..b, (deriv (deriv (fun θ' : ℝ => G w θ')) t) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      interval_sq_le_Itheta (h := fun θ : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) θ)
        hInt ha hab hb
    calc |∫ t in a..b, deriv (deriv (fun θ' : ℝ => G w θ')) t|
        = |∫ t in a..b, deriv (deriv (fun θ' : ℝ => G w θ')) t * 1| := by
          congr 1
          exact intervalIntegral.integral_congr (fun t _ => (mul_one _).symm)
      _ ≤ Real.sqrt (∫ t in a..b, (deriv (deriv (fun θ' : ℝ => G w θ')) t) ^ 2)
            * Real.sqrt (∫ t in a..b, (1 : ℝ) ^ 2) := hcs
      _ = Real.sqrt (∫ t in a..b, (deriv (deriv (fun θ' : ℝ => G w θ')) t) ^ 2)
            * Real.sqrt (b - a) := by rw [hone]
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * Real.sqrt (Real.pi / 4) :=
          mul_le_mul (Real.sqrt_le_sqrt hsq) (Real.sqrt_le_sqrt hlen)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## The bound
  refine ⟨|deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
      + Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * Real.sqrt (Real.pi / 4), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * Real.sqrt (Real.pi / 4) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  · intro s hs
    have hs0 : 0 < s := hs.1
    have hs1 : s < Real.pi / 2 := hs.2
    rcases le_total s (Real.pi / 4) with hle | hge
    · -- ## `s ≤ π/4`: run the fundamental theorem from `s` up to the landmark `π/4`
      have hFTC : ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t
          = deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            - deriv (fun θ' : ℝ => G w θ') s := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := deriv (fun θ' : ℝ => G w θ'))
          (f' := fun t : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) t) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hle] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hs0 ht.1, lt_of_le_of_lt ht.2 hq1⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hs0 hle hq1
      have hs_eq : deriv (fun θ' : ℝ => G w θ') s
          = deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + (- ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t) := by
        rw [hFTC]; ring
      have hbnd := hkey s (Real.pi / 4) hs0 hle hq1 (by linarith [hs0])
      rw [hs_eq]
      calc |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + (- ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t)|
          ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + |∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t| := by
            simpa only [abs_neg] using
              abs_add_le (deriv (fun θ' : ℝ => G w θ') (Real.pi / 4))
                (- ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t)
        _ ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * Real.sqrt (Real.pi / 4) := by linarith [hbnd]
    · -- ## `π/4 ≤ s`: run the fundamental theorem from the landmark `π/4` up to `s`
      have hFTC : ∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t
          = deriv (fun θ' : ℝ => G w θ') s
            - deriv (fun θ' : ℝ => G w θ') (Real.pi / 4) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := deriv (fun θ' : ℝ => G w θ'))
          (f' := fun t : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) t) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hge] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hq0 ht.1, lt_of_le_of_lt ht.2 hs1⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hq0 hge hs1
      have hs_eq : deriv (fun θ' : ℝ => G w θ') s
          = deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + ∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t := by
        rw [hFTC]; ring
      have hbnd := hkey (Real.pi / 4) s hq0 hge hs1 (by linarith [hs1])
      rw [hs_eq]
      calc |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + ∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t|
          ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + |∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t| :=
            abs_add_le _ _
        _ ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * Real.sqrt (Real.pi / 4) := by linarith [hbnd]

end Work.FTS.EllSol.EllPkgAux.MollDom
