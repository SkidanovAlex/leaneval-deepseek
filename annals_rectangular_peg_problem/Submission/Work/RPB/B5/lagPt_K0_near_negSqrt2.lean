import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.lagData_K0_lagPt
import Submission.Work.RPB.B5.sig_abs_le_kappa

/-!
# `Work.RPB.B5.lagPt_K0_near_negSqrt2`

Near the blown-up diagonal `x = -√2` the assembled family `ℓ = lagPt W Γc Ac rho` has level
`K₀ (ℓ τ (x,t)) = -x²/2` on *both* sides of `x = -√2`:

* for `x ≤ -√2` this is the collar branch: `ℓ = levelPt (Γc τ σ t) σ (Ac τ σ t)` with
  `σ = sig x = x²/2 - 1 ≥ 0`, and `K₀ (levelPt u σ a) = -1 - σ = -x²/2`
  (`Work.RPB.B5.lagData_K0_lagPt`);
* for `-√2 < x ≤ 0` the junction hypothesis `D.hrhonearδ` gives `rho τ x t = ρh τ t (sig x)`,
  and the level identity `D.hρhl` of the chart gives
  `K₀ (W τ t (ρh τ t σ)) + 1 = -σ`, i.e. `K₀ = -sig x - 1 = -x²/2`;
  here the junction hypothesis is only available for `|x + √2| < δ` and the level identity needs
  `σ = sig x ∈ (-κ, κ)`, which holds because `|sig x| ≤ κ/4` by
  `Work.RPB.B5.sig_abs_le_kappa` (from `δ ≤ κ/(4√2)`).

This is the two-sided, quantitative form of the level computation at the junction: the collar
branch and the chart branch agree to second order at `x = -√2`, as they must for the assembled
family to be glued there.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.RPB.B5

private lemma sqrt_two_pos' : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)

/-- On `x ≤ 0`, `lagPt` is its base half. -/
private lemma lagPt_eq_basePt_of_nonpos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : x ≤ 0) :
    lagPt W Γc Ac rho τ x t = basePt W Γc Ac rho τ x t := by
  rw [lagPt, ite_eq_left hx]

/-- On `-√2 < x`, the base half is the chord chart `W τ t (rho τ x t)`. -/
private lemma basePt_eq_chart_of_gt (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : -Real.sqrt 2 < x) :
    basePt W Γc Ac rho τ x t = W τ t (rho τ x t) := by
  rw [basePt, ite_eq_right (not_le.mpr hx)]

theorem lagPt_K0_near_negSqrt2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ,
      |y + Real.sqrt 2| < ε →
        Work.RPV.K0 (Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ y t) = -y ^ 2 / 2 := by
  intro τ hτ t
  obtain ⟨δ, hδpos, hδ14, hδκ, hρheq, _⟩ := D.hrhonearδ
  refine ⟨min δ 1, lt_min hδpos one_pos, ?_⟩
  intro y hy
  have hyδ : |y + Real.sqrt 2| < δ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy1 : |y + Real.sqrt 2| < 1 := lt_of_lt_of_le hy (min_le_right _ _)
  have hyt := abs_lt.mp hyδ
  have hy1t := abs_lt.mp hy1
  by_cases hyle : y ≤ -Real.sqrt 2
  · -- the collar branch: `K₀ (levelPt … (sig y) …) = -1 - sig y = -y²/2`
    have hge : Real.sqrt 2 ≤ |y| := by
      rw [abs_of_nonpos (by linarith [sqrt_two_pos', hyle] : y ≤ 0)]
      linarith [sqrt_two_pos', hyle]
    exact (lagData_K0_lagPt CI a ha D).1 τ hτ y t hge
  · -- the chart branch: `ℓ = W τ t (rho τ y t) = W τ t (ρh τ t (sig y))`
    have hygt : -Real.sqrt 2 < y := not_le.mp hyle
    have hy0 : y ≤ 0 := by
      have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
        have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        nlinarith [hsq, sqrt_two_pos']
      linarith [hy1t.2]
    have hlag : lagPt D.W D.Γc D.Ac D.rho τ y t = D.W τ t (D.rho τ y t) := by
      rw [lagPt_eq_basePt_of_nonpos D.W D.Γc D.Ac D.rho hy0,
        basePt_eq_chart_of_gt D.W D.Γc D.Ac D.rho hygt]
    rw [hlag]
    -- the junction hypothesis: `rho` is the level inverse `ρh ∘ sig` near `-√2`
    have hmem : y ∈ Set.Ioo (-Real.sqrt 2 - δ) (-Real.sqrt 2 + δ) := by
      rw [Set.mem_Ioo]
      exact ⟨by linarith [hyt.1], by linarith [hyt.2]⟩
    have hρ : D.rho τ y t = D.ρh τ t (sig y) := hρheq τ hτ y hmem t
    rw [hρ]
    -- the level `sig y` lies in the domain of the level identity
    have h4 : Real.sqrt 2 * δ ≤ D.κ / 4 := by
      have h2p : (0 : ℝ) < 4 * Real.sqrt 2 := by positivity
      have h := hδκ
      rw [le_div_iff₀ h2p] at h
      linarith
    have hsig : |sig y| ≤ D.κ / 4 :=
      sig_abs_le_kappa D.hκ h4 ⟨hygt, hy0⟩ (le_of_lt hyt.2)
    have hσmem : sig y ∈ Set.Ioo (-D.κ) D.κ := by
      have habs := abs_le.mp hsig
      rw [Set.mem_Ioo]
      exact ⟨by linarith [habs.1, D.hκ], by linarith [habs.2, D.hκ]⟩
    have hlev := D.hρhl τ hτ t (sig y) hσmem
    have hsigval : sig y = y ^ 2 / 2 - 1 := rfl
    linarith [hlev, hsigval]

end Work.RPB.B5
