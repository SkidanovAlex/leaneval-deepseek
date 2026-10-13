import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.MaximalPsi
import Submission.Work.WilE3.Taylor.hasLoj_of_multiplicity
import Submission.Work.WilE3.Taylor.E3_remainder_uniform
import Submission.Work.WilE3.Taylor.eaTaylor_remainder_list
import Submission.Work.WilE3.Taylor.E3_taylor_closure_backward_of_hasLoj

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology Filter
open WilkiesDesign.E

/-! ## The two directions

The frozen `E3_taylor_closure` is a biconditional, and the two directions have genuinely different
inputs:

* `(⇒)` `y ∈ closure {x | B.holds c x} → y ∈ closure (taylorSet c B y κ)` uses Gabrielov's
  non-directional maximal-`ψ` node (`Work.WilE3.MaximalPsiNode`, the hypothesis `hM`): it produces
  points `z` at which the *true* equations are small to order `κ ^ 2` and the *true* strict
  inequalities exceed `dist (z,y) ^ κ`, both with margins (`1/2` and `2`).  The effective Taylor
  remainder (`Work.WilE3.Taylor.eaTaylor_remainder_list` at order `κ ^ 2` for the equations and
  `Work.WilE3.Taylor.E3_remainder_uniform` at order `κ` for the positives) then converts these into
  the Taylor conditions of `taylorSet`: each margin pays for exactly one remainder term.
  This argument needs no exact vanishing of the equations, so it does *not* pass through the
  intermediate statement `hG` of `Work.WilE3.Taylor.E3_taylor_closure_proved` (which asks for
  points where the equations vanish identically); this is the only place where `hM` is used.
* `(⇐)` `y ∈ closure (taylorSet c B y κ) → y ∈ closure {x | B.holds c x}` uses the residual
  Łojasiewicz inequality `hL`, which `hMB` supplies through
  `Work.WilE3.Taylor.hasLoj_of_multiplicity`.  It is the lemma
  `Work.WilE3.Taylor.E3_taylor_closure_backward_of_hasLoj`.

The assembly below pads the two polynomials so that a single `K` satisfies both thresholds. -/

/-- **The `(⇒)` direction of `E3_taylor_closure` from Gabrielov's maximal-`ψ` node.**

`Work.WilE3.MaximalPsiNode F` supplies, for every limit point `y` of `B.holds` and every `κ` above
the format threshold, points `z` with `2 |f z| ≤ dist (z,y) ^ (κ ^ 2)` for the equations and
`2 · dist (z,y) ^ κ < g z` for the strict inequalities.  The effective Taylor remainder converts
these into the Taylor conditions of `taylorSet`: writing `d := dist z y`,

* `|T_{κ^2} f (z)| ≤ |f z| + C d ^ (κ^2 + 1) ≤ d ^ (κ^2) / 2 + d ^ (κ^2) / 2 = d ^ (κ^2)`, once
  `2 C d ≤ 1`;
* `T_κ g (z) ≥ g z - C' d ^ (κ + 1) > 2 d ^ κ - d ^ κ = d ^ κ`, once `C' d ≤ 1`,

and both smallness conditions are imposed by choosing `z` within `min ε δ`. -/
theorem E3_taylor_closure_forward_of_maximalPsi
    (hM : ∀ F : ℕ, Work.WilE3.MaximalPsiNode F) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
      (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
      y ∈ closure {x | B.holds c x} → y ∈ closure (taylorSet c B y κ) := by
  intro F
  obtain ⟨K_M, hKM⟩ := hM F
  refine ⟨K_M + 1, ?_⟩
  intro k r c B y κ hkr hκ hcl
  have hκM : K_M.eval B.deg < κ := by
    have h := hκ
    rw [Polynomial.eval_add, Polynomial.eval_one] at h
    omega
  obtain ⟨Ce, Re, hCe0, hRe, hRemE⟩ := eaTaylor_remainder_list c B.eqs y (κ ^ 2)
  obtain ⟨Cp, Rp, hCp0, hRp, hRemP⟩ := E3_remainder_uniform c B y κ
  -- one neighbourhood of `y` on which all the smallness conditions hold
  have hnev : ∀ᶠ w in 𝓝 y, dist w y < Re ∧ dist w y < Rp ∧
      dist w y < 1 / (2 * Ce + 2) ∧ dist w y < 1 / (Cp + 1) := by
    filter_upwards [Metric.ball_mem_nhds y hRe, Metric.ball_mem_nhds y hRp,
      Metric.ball_mem_nhds y (show (0 : ℝ) < 1 / (2 * Ce + 2) by positivity),
      Metric.ball_mem_nhds y (show (0 : ℝ) < 1 / (Cp + 1) by positivity)]
      with w h1 h2 h3 h4
    exact ⟨Metric.mem_ball.mp h1, Metric.mem_ball.mp h2, Metric.mem_ball.mp h3,
      Metric.mem_ball.mp h4⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hnev
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨z, hzδ', heqs, hpos⟩ :=
    hKM k r c B y κ hkr hκM hcl (min ε δ) (lt_min hε hδpos)
  have hzδ : dist z y < δ := lt_of_lt_of_le hzδ' (min_le_right _ _)
  have hzε : dist y z < ε := by
    rw [dist_comm]
    exact lt_of_lt_of_le hzδ' (min_le_left _ _)
  obtain ⟨hdRe, hdRp, hdCe, hdCp⟩ := hδ z (Metric.mem_ball.mpr hzδ)
  have hd0 : 0 ≤ dist z y := dist_nonneg
  -- the equation half of the Taylor conditions
  have heqT : ∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y z| ≤ dist z y ^ (κ ^ 2) := by
    intro f hf
    have hrem := hRemE f hf z hdRe
    have hfz : 2 * |eaEval c f z| ≤ dist z y ^ (κ ^ 2) := heqs f hf
    have hmul : dist z y * (2 * Ce + 2) < 1 :=
      (lt_div_iff₀ (show (0 : ℝ) < 2 * Ce + 2 by linarith)).mp hdCe
    have h2Ce : 2 * Ce * dist z y ≤ 1 := by nlinarith
    have hCd : Ce * dist z y ^ (κ ^ 2 + 1) ≤ dist z y ^ (κ ^ 2) / 2 := by
      have h1 : Ce * dist z y ^ (κ ^ 2 + 1) = (Ce * dist z y) * dist z y ^ (κ ^ 2) := by
        rw [pow_succ]; ring
      rw [h1]
      have h2 : Ce * dist z y ≤ 1 / 2 := by nlinarith
      calc (Ce * dist z y) * dist z y ^ (κ ^ 2)
          ≤ (1 / 2) * dist z y ^ (κ ^ 2) :=
            mul_le_mul_of_nonneg_right h2 (pow_nonneg hd0 _)
        _ = dist z y ^ (κ ^ 2) / 2 := by ring
    have h1 : |eaTaylor c f (κ ^ 2) y z|
        ≤ |eaEval c f z| + |eaEval c f z - eaTaylor c f (κ ^ 2) y z| := by
      have he : eaEval c f z + -(eaEval c f z - eaTaylor c f (κ ^ 2) y z)
          = eaTaylor c f (κ ^ 2) y z := by ring
      calc |eaTaylor c f (κ ^ 2) y z|
          = |eaEval c f z + -(eaEval c f z - eaTaylor c f (κ ^ 2) y z)| := by rw [he]
        _ ≤ |eaEval c f z| + |-(eaEval c f z - eaTaylor c f (κ ^ 2) y z)| := abs_add_le _ _
        _ = |eaEval c f z| + |eaEval c f z - eaTaylor c f (κ ^ 2) y z| := by rw [abs_neg]
    linarith
  -- the strict inequality half
  have hposT : ∀ g ∈ B.pos, dist z y ^ κ < eaTaylor c g κ y z := by
    intro g hg
    have hrem := hRemP g hg z hdRp
    have hgz : 2 * dist z y ^ κ < eaEval c g z := hpos g hg
    have hmul : dist z y * (Cp + 1) < 1 :=
      (lt_div_iff₀ (show (0 : ℝ) < Cp + 1 by linarith)).mp hdCp
    have hCpd : Cp * dist z y ^ (κ + 1) ≤ dist z y ^ κ := by
      have h1 : Cp * dist z y ^ (κ + 1) = (Cp * dist z y) * dist z y ^ κ := by
        rw [pow_succ]; ring
      rw [h1]
      have h2 : Cp * dist z y ≤ 1 := by nlinarith
      calc (Cp * dist z y) * dist z y ^ κ ≤ 1 * dist z y ^ κ :=
            mul_le_mul_of_nonneg_right h2 (pow_nonneg hd0 _)
        _ = dist z y ^ κ := one_mul _
    have hle : eaEval c g z - eaTaylor c g κ y z ≤ Cp * dist z y ^ (κ + 1) :=
      (abs_le.mp hrem).2
    linarith
  exact ⟨z, ⟨heqT, hposT⟩, hzε⟩

/-- The frozen `E3_taylor_closure` from `MultiplicityBound` and Gabrielov's non-directional
maximal-`ψ` node.  `hMB` gives the residual Łojasiewicz inequality
(`Work.WilE3.Taylor.hasLoj_of_multiplicity`), hence `(⇐)`; `hM = Work.WilE3.MaximalPsiNode` gives
good approximating points for the *true* functions with margins (`a = 1/2`, `b = 2`), which
`Work.WilE3.API.eaTaylor_remainder` converts into the Taylor conditions of `taylorSet`, hence
`(⇒)`. -/
theorem E3_taylor_closure_proved_of_multiplicity
    (hMB : Work.WilE3.MultiplicityBound) (hM : ∀ F : ℕ, Work.WilE3.MaximalPsiNode F) :
    (∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
      (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
      (y ∈ closure {x | B.holds c x} ↔ y ∈ closure (taylorSet c B y κ))) := by
  intro F
  obtain ⟨K_B, hB⟩ := E3_taylor_closure_backward_of_hasLoj (hasLoj_of_multiplicity hMB) F
  obtain ⟨K_F, hF⟩ := E3_taylor_closure_forward_of_maximalPsi hM F
  refine ⟨K_B + K_F + 1, ?_⟩
  intro k r c B y κ hkr hκ
  have hsum : (K_B + K_F + 1).eval B.deg = K_B.eval B.deg + K_F.eval B.deg + 1 := by
    rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_one]
  have hKB : K_B.eval B.deg < κ := by rw [hsum] at hκ; omega
  have hKF : K_F.eval B.deg < κ := by rw [hsum] at hκ; omega
  exact ⟨hF k r c B y κ hkr hKF, hB k r c B y κ hkr hKB⟩

end Work.WilE3.Taylor
