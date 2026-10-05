import Mathlib
import Submission.Work.RPB.B5.lagData_imm_aux
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.lagData_K0_lagPt
import Submission.Work.RPB.B5.lagPt_K0_near_negSqrt2

/-!
# B5: the level `K₀` of the assembled family on the collar half `x ≤ -√2`

`Work.RPB.B5.lagPt_collar_level_derivs`: on the collar half `x ≤ -√2` the level `K₀` of the
assembled family `ℓ = lagPt W Γc Ac rho` has the derivatives

`∂_x K₀ (ℓ τ (x,t)) = -x`,     `∂_t K₀ (ℓ τ (x,t)) = 0`.

This is the "the level function separates the two tangents" fact used in
`Work.RPB.B5.lagData_imm`: the differential of `K₀` is nonzero on both tangents of the collar.

## The mathematics

For `y ≤ -√2` the family is the collar point
`levelPt (Γc τ (sig y) t) (sig y) (Ac τ (sig y) t)` with `sig y = y²/2 - 1 ≥ 0`, and since
`K₀ (levelPt u σ a) = -1 - σ` this gives, *unconditionally*,

`K₀ (ℓ τ (y,t)) = -1 - sig y = -y²/2`      (`lagData_K0_lagPt`, `K0_lagPt_of_le_negSqrt2`).

The second derivative is then immediate: for fixed `x ≤ -√2` the function `s ↦ K₀ (ℓ τ (x,s))` is
constant, equal to `-x²/2`.

The first derivative needs the same *value* on a whole two-sided neighbourhood of `x`.  For
`x < -√2` this is the collar formula above (take a window of radius `(-√2 - x)/2`, inside which
still `y ≤ -√2`).  At the junction `x = -√2` the chord chart takes over for `-√2 < y`; there the
junction hypothesis `hrhonearδ` (`rho τ y t = ρh τ t (sig y)` on a two-sided window) together with
the chart's level identity `hρhl` gives the same value `-y²/2`.  That two-sided statement is the
companion lemma `Work.RPB.B5.lagPt_K0_near_negSqrt2`.

So `y ↦ K₀ (ℓ τ (y,t))` agrees with `y ↦ -y²/2` on a neighbourhood of every `x ≤ -√2`, and the
first derivative follows from `Filter.EventuallyEq.deriv_eq` (the derivative of the quadratic is
`-x`).  No differentiability hypothesis is needed: `K₀ ∘ ℓ` is differentiable there *because* it
agrees with the quadratic.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

private lemma sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)

/-- On the collar half `x ≤ -√2` we have `√2 ≤ |x|`, so the collar form of the level applies. -/
private lemma sqrt_two_le_abs_of_le_neg_sqrt_two {x : ℝ} (hx : x ≤ -Real.sqrt 2) :
    Real.sqrt 2 ≤ |x| := by
  rw [abs_of_nonpos (by linarith [sqrt2_pos, hx])]
  linarith [sqrt2_pos]

/-- On the whole collar half `x ≤ -√2` (in particular at the junction `x = -√2`) the level of the
assembled family is `-x²/2`: the collar half of `lagData_K0_lagPt`. -/
private lemma K0_lagPt_of_le_negSqrt2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    {τ x t : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hx : x ≤ -Real.sqrt 2) :
    Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ x t) = -x ^ 2 / 2 :=
  (lagData_K0_lagPt CI a ha D).1 τ hτ x t (sqrt_two_le_abs_of_le_neg_sqrt_two hx)

/-! ## The statement -/

theorem lagPt_collar_level_derivs (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (hsm : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, x ≤ -Real.sqrt 2 → ∀ t : ℝ,
      deriv (fun y : ℝ => Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ y t)) x = -x
      ∧ deriv (fun s : ℝ => Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ x s)) t = 0 := by
  intro τ hτ x hx t
  -- the derivative of the quadratic `y ↦ -y²/2`
  have hquad : deriv (fun y : ℝ => -y ^ 2 / 2) x = -x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have h3 := (h1.neg).div_const 2
      rw [show -(2 * x) / 2 = -x by ring] at h3
      exact h3
    exact h2.deriv
  refine ⟨?_, ?_⟩
  · -- `∂_x`
    rcases lt_or_eq_of_le hx with hlt | heq
    · -- strictly inside the collar half: a whole window still lies in `x ≤ -√2`
      have hev : (fun y : ℝ => Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ y t))
          =ᶠ[nhds x] (fun y : ℝ => -y ^ 2 / 2) := by
        have hmem : Set.Ioo (x - (-Real.sqrt 2 - x) / 2) (x + (-Real.sqrt 2 - x) / 2)
            ∈ nhds x :=
          isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
        filter_upwards [hmem] with y hy
        refine K0_lagPt_of_le_negSqrt2 CI a ha D hτ ?_
        have hyu : y < x + (-Real.sqrt 2 - x) / 2 := hy.2
        rw [show x + (-Real.sqrt 2 - x) / 2 = (x - Real.sqrt 2) / 2 by ring] at hyu
        linarith
      rw [hev.deriv_eq, hquad]
    · -- at the junction: the two-sided window of `hrhonearδ`
      obtain ⟨ε, _hεpos, hε⟩ := lagPt_K0_near_negSqrt2 CI a ha D τ hτ t
      have hev : (fun y : ℝ => Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ y t))
          =ᶠ[nhds x] (fun y : ℝ => -y ^ 2 / 2) := by
        have hmem : Set.Ioo (-Real.sqrt 2 - ε) (-Real.sqrt 2 + ε) ∈ nhds x := by
          rw [heq]
          exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
        filter_upwards [hmem] with y hy
        refine hε y ?_
        rw [abs_lt]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      rw [hev.deriv_eq, hquad]
  · -- `∂_t`: for `x ≤ -√2` the level is independent of `t`
    have hconst : (fun s : ℝ => Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ x s))
        = fun _ : ℝ => -x ^ 2 / 2 :=
      funext fun s => K0_lagPt_of_le_negSqrt2 CI a ha D hτ hx
    rw [hconst, deriv_const]

end Work.RPB.B5
