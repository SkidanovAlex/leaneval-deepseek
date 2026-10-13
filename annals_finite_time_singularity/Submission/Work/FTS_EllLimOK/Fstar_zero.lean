/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Fstar_zero` — the angular moment of a box-regular homogeneous solution vanishes

Let `δ` be jointly `C²` on every closed box `[a,b] × [0,π/2]` (`0 < a ≤ b`) — the finite-order
regularity class `Work.FTS_EllLimOK.BoxReg` of this area — solving the homogeneous elliptic
problem `L δ = 0` on the open quadrant, with the Dirichlet values `δ z 0 = δ z (π/2) = 0`, and
with finite `ℋ⁰`-mass `Work.Spaces.HkMem α 0 δ`.  Then the angular moment

  `F_*δ(z) = ∫_0^{π/2} δ(z,θ) sin θ cos²θ dθ`

vanishes identically on `(0,∞)`.

Proof.  `Work.FTS_EllLimOK.Fstar_ode_of_bslOp_zero` shows that `F_*δ` is `C²` on `(0,∞)` and
solves the equidimensional (Euler) equation

  `α²z² (F_*δ)'' + α(5+α) z (F_*δ)' = 0`,

whose general solution is `A z^{-5/α} + B` — this is
`Work.FTS_EllLimOK.FstarOde.rigidity_form_of_ode`.  The `ℋ⁰`-mass supplies, by Cauchy–Schwarz
against the angular weight `sin θ cos²θ` (`Work.FTS_EllLimOK.FstarOde.Fstar_sq_HkIntegrand_le`),

  `(F_*δ z)² ≤ (π/2) z⁴ · ∫_θ HkIntegrand α 0 δ z θ`   for `z > 0`,

and `z ↦ ∫_θ HkIntegrand α 0 δ z θ` is integrable on `[0,∞)` by `HkMem`.  Now `A z^{-5/α} + B`
cannot satisfy this unless `A = B = 0`: if `A ≠ 0` (or if `A = 0` and `B ≠ 0`) the pointwise
bound forces `z ↦ ∫_θ HkIntegrand α 0 δ z θ` to dominate a positive multiple of the
non-integrable weight `z^{-4}` on a right-neighbourhood of `0`
(`Work.FTS_EllLimOK.FstarOde.not_integrableOn_of_rpow_lower`), contradiction.  Hence
`F_*δ ≡ 0`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.UniqDefs
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.Fstar_ode_of_bslOp_zero
import Submission.Work.FTS_EllLimOK.integrableOn_Fstar_sq_zpow
import Submission.Work.FTS_EllLimOK.FstarOde.rigidity_form_of_ode
import Submission.Work.FTS_EllLimOK.FstarOde.not_integrableOn_of_rpow_lower
import Submission.Work.FTS_EllLimOK.FstarOde.Fstar_sq_HkIntegrand_le
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- Auxiliary algebra: if `x ≤ (π/2) z⁴ f` with `z > 0`, then `(2/π) x z⁻⁴ ≤ f`. -/
private lemma two_div_pi_mul_le {x f z : ℝ} (hz : 0 < z)
    (h : x ≤ (π / 2) * z ^ 4 * f) :
    (2 / π) * x * z ^ (-4 : ℝ) ≤ f := by
  have hz4ne : z ^ 4 ≠ 0 := ne_of_gt (pow_pos hz 4)
  have hzi : z ^ (-4 : ℝ) = (z ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz),
      Real.rpow_natCast]
  rw [hzi]
  have hk : 0 ≤ (z ^ 4)⁻¹ := inv_nonneg.mpr (le_of_lt (pow_pos hz 4))
  have h1 := mul_le_mul_of_nonneg_right h hk
  have h2 : (π / 2) * z ^ 4 * f * (z ^ 4)⁻¹ = (π / 2) * f := by
    rw [show (π / 2) * z ^ 4 * f * (z ^ 4)⁻¹ = (π / 2) * (z ^ 4 * (z ^ 4)⁻¹) * f by ring]
    rw [mul_inv_cancel₀ hz4ne, mul_one]
  rw [h2] at h1
  calc (2 / π) * x * (z ^ 4)⁻¹ = (2 / π) * (x * (z ^ 4)⁻¹) := by ring
    _ ≤ (2 / π) * ((π / 2) * f) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = f := by field_simp

theorem Fstar_zero {α : ℝ} (hα : 0 < α) {δ : ℝ → ℝ → ℝ}
    (hbox : Work.FTS_EllLimOK.BoxReg δ)
    (hsol : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.bslOp α δ z θ = 0)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z (π / 2) = 0)
    (hHk : Work.Spaces.HkMem α 0 δ) :
    ∀ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar δ z = 0 := by
  -- the angular moment is `C²` and solves the Euler equation
  obtain ⟨hC2, hode⟩ := Work.FTS_EllLimOK.Fstar_ode_of_bslOp_zero hα hsol hbox h0 h1
  have hg1 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar δ) (deriv (Work.Elliptic.Fstar δ) z) z := fun z hz =>
    ((hC2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hdc : ContDiffOn ℝ 1 (deriv (Work.Elliptic.Fstar δ)) (Set.Ioi (0 : ℝ)) :=
    hC2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hg2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (deriv (Work.Elliptic.Fstar δ))
        (deriv (deriv (Work.Elliptic.Fstar δ)) z) z := fun z hz =>
    ((hdc.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- hence `F_*δ z = A z^{-5/α} + B`
  obtain ⟨A, B, hform⟩ :=
    Work.FTS_EllLimOK.FstarOde.rigidity_form_of_ode α hα hg1 hg2 hode
  -- the `ℋ⁰`-mass bounds the moment by the weighted angular energy
  have hbnd : ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.Fstar δ z) ^ 2
      ≤ (π / 2) * z ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) :=
    Work.FTS_EllLimOK.FstarOde.Fstar_sq_HkIntegrand_le hbox hHk
  have hfint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ)
      Work.Spaces.Iz := hHk.2
  -- ... so no point of `(0,∞)` can be a non-zero value of `F_*δ`
  have key : ¬ ∃ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar δ z ≠ 0 := by
    rintro ⟨z₀, hz₀, hne₀⟩
    have hAB : A ≠ 0 ∨ B ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne₀ (by rw [hform z₀ hz₀, h.1, h.2]; ring)
    have hmain : ∃ m b : ℝ, 0 < m ∧ 0 < b ∧
        ∀ z ∈ Set.Ioo (0 : ℝ) b, m * z ^ (-4 : ℝ)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) := by
      by_cases hA : A = 0
      · -- `A = 0`, hence `B ≠ 0`: the moment is the constant `B`
        have hB : B ≠ 0 := by
          rcases hAB with h | h
          · exact absurd (h hA) (not_false)
          · exact h
        have hB2 : 0 < B ^ 2 := by
          have hBpos : 0 < |B| := abs_pos.mpr hB
          rw [← sq_abs B]
          exact pow_pos hBpos 2
        refine ⟨(2 / π) * B ^ 2, 1, ?_, by norm_num, ?_⟩
        · exact mul_pos (by positivity) hB2
        · intro z hz
          have hzp : 0 < z := hz.1
          have hgz : Work.Elliptic.Fstar δ z = B := by
            rw [hform z hz.1, hA]; ring
          have h1' := hbnd z hz.1
          rw [hgz] at h1'
          exact two_div_pi_mul_le hzp h1'
      · -- `A ≠ 0`: the moment blows up like `z^{-5/α}`, hence dominates `1` near `0`
        have hApos : 0 < |A| := abs_pos.mpr hA
        have hCpos : 0 < (2 * |B| + 1) / |A| :=
          div_pos (by positivity) hApos
        refine ⟨2 / π, ((2 * |B| + 1) / |A|) ^ (-(α / 5)), ?_, ?_, ?_⟩
        · positivity
        · exact Real.rpow_pos_of_pos hCpos _
        · intro z hz
          have hzp : 0 < z := hz.1
          have hbC' : (((2 * |B| + 1) / |A|) ^ (-(α / 5))) ^ (-(5 / α))
              = (2 * |B| + 1) / |A| := by
            rw [← Real.rpow_mul (le_of_lt hCpos)]
            have he : (-(α / 5)) * (-(5 / α)) = 1 := by field_simp
            rw [he, Real.rpow_one]
          have hzpow : (2 * |B| + 1) / |A| < z ^ (-(5 / α)) := by
            have h5 : (-(5 / α)) < 0 := by
              have : 0 < 5 / α := by positivity
              linarith
            have hlt := Real.rpow_lt_rpow_of_neg hzp hz.2 h5
            rwa [hbC'] at hlt
          have hAZ : 2 * |B| + 1 < |A| * z ^ (-(5 / α)) := by
            have h1 := mul_lt_mul_of_pos_left hzpow hApos
            have h2 : |A| * ((2 * |B| + 1) / |A|) = 2 * |B| + 1 := by
              rw [mul_comm]
              exact div_mul_cancel₀ (2 * |B| + 1) (ne_of_gt hApos)
            rwa [h2] at h1
          have hgz : 1 ≤ |Work.Elliptic.Fstar δ z| := by
            have hgv : Work.Elliptic.Fstar δ z = A * z ^ (-(5 / α)) + B :=
              hform z hz.1
            rw [hgv]
            have hzpowpos : 0 < z ^ (-(5 / α)) := Real.rpow_pos_of_pos hzp _
            have hkey := abs_sub_abs_le_abs_sub (A * z ^ (-(5 / α))) (-B)
            rw [abs_mul, abs_of_pos hzpowpos, abs_neg] at hkey
            have hsub : A * z ^ (-(5 / α)) - (-B) = A * z ^ (-(5 / α)) + B := by ring
            rw [hsub] at hkey
            linarith [abs_nonneg B]
          have hsq : 1 ≤ (Work.Elliptic.Fstar δ z) ^ 2 := by
            have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hgz 2
            simpa [sq_abs] using h
          have h1' := hbnd z hz.1
          have h1'' : (1 : ℝ) ≤ (π / 2) * z ^ 4
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) :=
            le_trans hsq h1'
          simpa using two_div_pi_mul_le hzp h1''
    obtain ⟨m, b, hm, hb, hlow⟩ := hmain
    exact (Work.FTS_EllLimOK.FstarOde.not_integrableOn_of_rpow_lower hm hb
      (by norm_num) hlow)
      (hfint.mono_set fun x hx => le_of_lt hx.1)
  intro z hz
  by_contra hne
  exact key ⟨z, hz, hne⟩

end Work.FTS_EllLimOK
