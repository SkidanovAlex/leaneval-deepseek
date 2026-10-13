import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.eaTaylor_remainder

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-- First step of the `(⇒)` direction of `E3_taylor_closure`: every point of the basic EA set near
`y` satisfies the *equation* part of the Taylor conditions, i.e. the order-`κ ^ 2` Taylor polynomial
of each equation is bounded by `dist x y ^ (κ ^ 2)`.

The Taylor conditions of `taylorSet` (`Defs.lean` §4) are `∀ f ∈ B.eqs, |eaTaylor c f (κ^2) y x| ≤
dist x y ^ (κ ^ 2)` together with the strict inequalities `dist x y ^ κ < eaTaylor c g κ y x`.  This
statement is the equation half.  It follows from the effective Taylor remainder bound
`Work.WilE3.API.eaTaylor_remainder`: on `B.holds` the equations vanish, so
`|T (x)| = |T (x) - f (x)| ≤ C · dist x y ^ (κ^2 + 1)`, and `dist x y ≤ 1 / C` makes this
`≤ dist x y ^ (κ ^ 2)`.  (The inequality half of the Taylor conditions is *not* implied by
`B.holds` on the nose — that is exactly why the `(⇒)` direction has to go through Gabrielov's
critical-set/maximal-`ψ` argument, `NOTES.md` §4 — so only the equations are claimed here.) -/
theorem taylor_conditions_of_holds {k r : ℕ} (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ)
    (κ : ℕ) :
    ∀ᶠ x in 𝓝 y, B.holds c x →
      ∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2) := by
  classical
  -- the effective Taylor remainder bound, for every atom
  have hrem : ∀ f : EAPoly k r, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 y,
      |eaEval c f x - eaTaylor c f (κ ^ 2) y x| ≤ C * dist x y ^ (κ ^ 2 + 1) :=
    fun f => Work.WilE3.API.eaTaylor_remainder c f (κ ^ 2) y
  choose C hCpos hCb using hrem
  -- a single constant dominating all the atoms of the set
  set S : Finset (EAPoly k r) := B.eqs.toFinset with hS
  set T : ℝ := ∑ f ∈ S, C f with hT
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg fun f _ => hCpos f
  have hTpos : 0 < T + 1 := by linarith
  -- all the remainder bounds at once, and the ball in which the constant is absorbed
  have hev : ∀ᶠ x in 𝓝 y, ∀ f ∈ S,
      |eaEval c f x - eaTaylor c f (κ ^ 2) y x| ≤ C f * dist x y ^ (κ ^ 2 + 1) := by
    rw [Finset.eventually_all]
    intro f _
    exact hCb f
  filter_upwards [hev, Metric.ball_mem_nhds y (one_div_pos.mpr hTpos)] with x hx hball
  intro hholds f hf
  have hfS : f ∈ S := List.mem_toFinset.mpr hf
  -- on `B.holds` the atom itself vanishes, so the Taylor polynomial is the remainder
  have h1 := hx f hfS
  rw [hholds.1 f hf, zero_sub, abs_neg] at h1
  have h2 : C f ≤ T := Finset.single_le_sum (fun i _ => hCpos i) hfS
  have hdb : dist x y ≤ 1 / (T + 1) := le_of_lt (Metric.mem_ball.mp hball)
  -- inside the ball, `C f * dist x y ≤ 1`
  have hCd : C f * dist x y ≤ 1 := by
    have h3 : C f * dist x y ≤ C f * (1 / (T + 1)) :=
      mul_le_mul_of_nonneg_left hdb (hCpos f)
    have h4 : C f * (1 / (T + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hTpos]
      linarith
    linarith
  -- hence `C f * dist x y ^ (κ ^ 2 + 1) ≤ dist x y ^ (κ ^ 2)`
  have h5 : C f * dist x y ^ (κ ^ 2 + 1) ≤ dist x y ^ (κ ^ 2) := by
    calc C f * dist x y ^ (κ ^ 2 + 1)
        = (C f * dist x y) * dist x y ^ (κ ^ 2) := by rw [pow_succ]; ring
      _ ≤ 1 * dist x y ^ (κ ^ 2) :=
          mul_le_mul_of_nonneg_right hCd (pow_nonneg dist_nonneg _)
      _ = dist x y ^ (κ ^ 2) := one_mul _
  linarith

end Work.WilE3.Taylor
