/-
# `Work.FTS_RegExport.RX0.hzmodp_ext_c4` — the `z`-modulus of `∂_zg̃`, with the
interior smoothness hypothesis weakened to `C⁴` on the open quadrant

This is `Work.FTS.RegPkgGal.Der.hzmodp` / `hzmodp_ext` with the *interior* smoothness clause
(`SmoothQuad`, i.e. `C^∞` on `(-1,∞) × (0,π/2)`) replaced by the much weaker

  `hc4 : ∀ τ ∈ Icc 0 S, ContDiffOn ℝ 4 (Function.uncurry (gSlice g τ)) Q0`,

`Q0 = (0,∞) × (0,π/2)` being the open quadrant.  The argument is unchanged:

Fix `(τ,θ)`.  On `(0,∞)` the function `z ↦ ∂_zg̃(z,θ,τ)` coincides with `z ↦ ∂_zg(z,θ,τ)`, hence
is differentiable there with derivative `∂_z²g̃(z,θ,τ)`, which is bounded by `M₂` (`hsup2`).  The
mean value theorem on the convex set `Ioi 0` gives the global Lipschitz bound with constant `M₂`
on `(0,∞)`; continuity at `0` (from `hcont`, since `g̃ ≡ 0` on `z ≤ 0`) turns it into a Lipschitz
bound on `[0,∞)` (`Lib.lip_of_bounded_deriv`).  Adding the sup bound `M` of `hsup` gives
`α`-Hölder with constant `max M₂ (2M)` (`Lib.holder_of_lipschitz_of_bounded`): for `|z-z'| ≤ 1`
one uses `|z-z'| ≤ |z-z'|^α`, and for `|z-z'| ≥ 1` the boundedness bound together with
`|z-z'|^α ≥ 1`.

At the two angular endpoints `θ = 0, π/2` the whole slice vanishes (`hvan`), so both sides of the
estimate are `0`.

The only spot where `hzmodp_ext` used `SmoothQuad` is the differentiability of the slice
`z ↦ g z θ τ` on `(0,∞)`; here it is supplied by `hc4` (only order `2` of it is needed: the slice
is `C²` on `Ioi 0` for `θ ∈ Ioo 0 (π/2)`, so its derivative is `C¹`, hence differentiable, there).
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegPkgGal.Der.hzmodp_ext
import Submission.Work.FTS.RegPkgGal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RX0

theorem hzmodp_ext_c4 {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hc4 : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Regularity.gSlice g τ)) Work.FTS.EllipticEst.Q0)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M)
    (hsup2 : ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ| ≤ M₂) :
    ∃ Nz : ℝ, 0 ≤ Nz ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ|
          ≤ Nz * |z - z'| ^ α := by
  obtain ⟨M, hM0, hM⟩ := hsup
  obtain ⟨M₂, hM₂0, hM₂⟩ := hsup2
  have hN0 : 0 ≤ max M₂ (2 * M) := le_trans hM₂0 (le_max_left _ _)
  refine ⟨max M₂ (2 * M), hN0, ?_⟩
  intro τ hτ z z' hz hz' θ hθ
  set F : ℝ → ℝ → ℝ := fun z θ => Work.FTS.RegPkgGal.extG g z θ τ with hF
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · -- the angular interior: everything happens at `θ ∈ (0,π/2)`
    set f : ℝ → ℝ := fun z => Work.Spaces.pz F z θ with hf
    change |f z - f z'| ≤ max M₂ (2 * M) * |z - z'| ^ α
    -- `f` is continuous at `0`, because `g̃` is `C¹` jointly near `(0,τ)` and vanishes for `z ≤ 0`
    have hcont_f : ContinuousAt f 0 := by
      have hslice1 : ContDiffOn ℝ 1 (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ)
          (Set.Ioi (-1)) := by
        have hcomp := (hcont θ hθ).comp (f := fun z : ℝ => (z, τ)) (by fun_prop)
          (fun z hz => ⟨hz, ⟨by linarith [hτ.1], by linarith [hτ.2, hS]⟩⟩)
        simpa [Function.comp_def] using hcomp
      have hcd : ContinuousOn (deriv (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ))
          (Set.Ioi (-1)) :=
        hslice1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
      have h0 : (0 : ℝ) ∈ Set.Ioi (-1) := by norm_num
      have hca : ContinuousAt (deriv (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ)) 0 :=
        hcd.continuousAt (isOpen_Ioi.mem_nhds h0)
      have hfeq : f = deriv (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ) := by
        funext x
        simp only [hf, hF, Work.Spaces.pz]
      rwa [hfeq]
    -- on `(0,∞)` the function `f` is the `z`-derivative of the smooth slice `g(·,θ,τ)`
    have hEqOn : Set.EqOn f (deriv (fun z : ℝ => g z θ τ)) (Set.Ioi 0) := by
      intro x hx
      have hev : (fun z' => F z' θ) =ᶠ[𝓝 x] (fun z' => g z' θ τ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
        rw [hF]
        exact Work.FTS.RegPkgGal.extG_of_pos hu hτ.1
      have h1 : f x = deriv (fun z' => F z' θ) x := by rw [hf]; rfl
      rw [h1]
      exact hev.deriv_eq
    -- the slice `z ↦ g z θ τ` is `C²` on `(0,∞)`: this is the only use of `hc4`
    have hcomp4 : ContDiffOn ℝ 4 (fun z : ℝ => g z θ τ) (Set.Ioi 0) := by
      have hs : ContDiffOn ℝ 4 (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
        (contDiffOn_id : ContDiffOn ℝ 4 (fun z : ℝ => z) (Set.Ioi 0)).prodMk contDiffOn_const
      have h := (hc4 τ hτ).comp hs (fun z hz => by
        rw [Work.FTS.EllipticEst.mem_Q0]
        exact ⟨hz, hθi.1, hθi.2⟩)
      simpa [Function.uncurry, Function.comp_def, Work.FTS.Regularity.gSlice] using h
    have hsl : ContDiffOn ℝ 2 (fun z : ℝ => g z θ τ) (Set.Ioi 0) :=
      hcomp4.of_le (by norm_num)
    have hd1 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => g z θ τ)) (Set.Ioi 0) :=
      hsl.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have hdiff_deriv : DifferentiableOn ℝ (deriv (fun z : ℝ => g z θ τ)) (Set.Ioi 0) :=
      hd1.differentiableOn_one
    have hdiff_f : DifferentiableOn ℝ f (Set.Ioi (0 : ℝ)) := hdiff_deriv.congr hEqOn
    have hdiff : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ f x := by
      intro x hx
      exact (hdiff_f x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
    have hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |deriv f x| ≤ M₂ := by
      intro x hx
      have h1 : deriv f x = Work.Spaces.pz (Work.Spaces.pz F) x θ := by rw [hf]; rfl
      rw [h1, hF]
      exact hM₂ τ hτ x θ hx hθ
    have hbdd : ∀ x : ℝ, 0 ≤ x → |f x| ≤ M := by
      intro x hx
      have h1 : f x = Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) x θ := by
        rw [hf, hF]
      rw [h1]
      exact hM τ hτ x θ hx hθ
    have hlip : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ M₂ * |z - z'| :=
      Work.FTS.RegPkgGal.Der.Lib.lip_of_bounded_deriv hM₂0 hdiff hbd hcont_f
    exact Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded hα hα1 hM₂0 hM0 hlip hbdd
      z z' hz hz'
  · -- the two angular endpoints: the whole slice vanishes
    have hθ0 : θ = 0 ∨ θ = π / 2 := by
      by_cases h1 : θ = 0
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact hθi ⟨lt_of_le_of_ne hθ.1 (Ne.symm h1), lt_of_le_of_ne hθ.2 h2⟩
    have hgz : ∀ w : ℝ, Work.FTS.RegPkgGal.extG g w θ τ = 0 := by
      intro w
      by_cases hw : w ≤ 0
      · exact Work.FTS.RegPkgGal.extG_of_nonpos hw
      · rw [Work.FTS.RegPkgGal.extG_of_pos (not_le.mp hw) hτ.1]
        rcases hθ0 with rfl | rfl
        · exact (hvan τ hτ w (le_of_lt (not_le.mp hw))).1
        · exact (hvan τ hτ w (le_of_lt (not_le.mp hw))).2
    have hFz : ∀ w : ℝ, F w θ = 0 := by
      intro w
      rw [hF]
      exact hgz w
    have hfz : ∀ w : ℝ, Work.Spaces.pz F w θ = 0 := by
      intro w
      have hz : (fun w' => F w' θ) = fun _ => (0 : ℝ) := funext hFz
      change deriv (fun w' => F w' θ) w = 0
      rw [hz]; simp
    change |Work.Spaces.pz F z θ - Work.Spaces.pz F z' θ| ≤ max M₂ (2 * M) * |z - z'| ^ α
    rw [hfz z, hfz z']
    simp only [sub_self, abs_zero]
    exact mul_nonneg hN0 (Real.rpow_nonneg (abs_nonneg _) α)

end Work.FTS_RegExport.RX0
