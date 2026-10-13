/-
# `E1Parts/ContE1` — the `C³`-regularity of the two transfer pieces on the open quadrant

The transfer of the coercivity of `𝓛̂ = 𝓛 − Transport` to the paper's operator
`𝓛_Γ^T = 𝓛̂ + Corr` runs on the *first jet* decomposition
`D_θ (𝓛_Γ^T f) = 𝓛̂ (D_θ f) + E1 α f`, whose two terms are

* `E1 α f = (sin 2θ · Γ'(θ)) · radA α f z` — a **separated product** of an angular factor
  `B(θ) = sin 2θ · Γ'(θ)`, which is `C³` on `(0,π/2)` (`sinGam_contDiffOn_Ioo`), and a radial
  factor `radA α f z`, which is `C³` on `(0,∞)` because `L₁₂ f` is (`radA_contDiffOn`
  + `L12f_contDiffOn`, the latter using `SmoothQuad f` and `HkMem α 4 f` of the `CoerAdm`
  ledger);
* `𝓛̂ (D_θ f) = D_θ f + D_z(D_θ f) − 2 D_θ f/(1+z) − 3 D_θ(D_θ f)/(1+z)` — an expression in
  the curried partials `D_θ f`, `pz (D_θ f)`, `D_θ (D_θ f)` of the datum, each of which is
  `C^∞` on the open quadrant for `SmoothQuad f` (the calculus of `LocData.SmoothChain`,
  `contDiffOn_pz`/`contDiffOn_Dth`), divided by the nowhere-vanishing `1+z`.

This file provides both conjuncts separately (`contDiffOn_uncurry_E1`,
`contDiffOn_uncurry_Lhat_Dth`) and assembles the requested `ContE1`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1_blocks
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.Construction.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **`E1 α f` is `C³` on the open quadrant** for a datum `f` which is `C^∞` on the open
half-strip `z > -1`, `0 < θ < π/2` and lies in `ℋ⁴`.  It is the product of the angular factor
`sin 2θ·Γ'(θ)` (a function of `θ` alone, `C³` on `(0,π/2)`) and the radial factor
`radA α f` (a function of `z` alone, `C³` on `(0,∞)`, since `L₁₂ f` is). -/
theorem contDiffOn_uncurry_E1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : Fn)
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem4 : Work.Spaces.HkMem α 4 f) :
    ContDiffOn ℝ 3 (Function.uncurry (E1 α f)) Work.Construction.Qd := by
  have hB : ContDiffOn ℝ 3
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) (Set.Ioo 0 (π / 2)) :=
    sinGam_contDiffOn_Ioo α
  have h12 : ContDiffOn ℝ 3 (Work.Coercivity.L12f f) (Set.Ioi 0) :=
    L12f_contDiffOn α hα hα1 f hsm hmem4
  have hR : ContDiffOn ℝ 3 (radA α f) (Set.Ioi 0) := radA_contDiffOn α hα hα1 f h12
  have hfun : Function.uncurry (E1 α f)
      = (fun p : ℝ × ℝ => Real.sin (2 * p.2) * deriv (Work.Spaces.Gam α) p.2)
        * (fun p : ℝ × ℝ => radA α f p.1) := by
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  rw [hfun]
  exact (hB.comp contDiffOn_snd (fun p hp => hp.2)).mul
    (hR.comp contDiffOn_fst (fun p hp => hp.1))

/-- **`𝓛̂ (D_θ f)` is `C³` on the open quadrant** for a datum which is `C^∞` on the open
half-strip `z > -1`, `0 < θ < π/2`.  The order `3` is what the transfer-coercivity induction
consumes; the proof actually produces `smoothOrder`, and `3` is obtained by `of_le`.

`𝓛̂ g = g + D_z g − 2g/(1+z) − 3 D_θ g/(1+z)` with `g = D_θ f`, so every summand is a partial
derivative of the datum (`D_θ f`, `D_θ(D_θ f)` by `contDiffOn_Dth`, `pz (D_θ f)` by
`contDiffOn_pz`) divided by the nowhere-vanishing `1+z`. -/
theorem contDiffOn_uncurry_Lhat_Dth (f : Fn) (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)))
      Work.Construction.Qd := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- `Qd = (0,∞) × (0,π/2)` sits inside the `SmoothQuad` half-strip `(-1,∞) × (0,π/2)`.
  have hsub : Work.Construction.Qd ⊆ Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    exact ⟨by show (-1 : ℝ) < p.1; linarith, hp.2⟩
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.Construction.Qd := hsm.mono hsub
  have hDth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV hf
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dth f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_pz hV hDth
  have hDthDth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dth f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV hDth
  have hne : ∀ p ∈ Work.Construction.Qd, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    linarith
  have hmain : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)))
      Work.Construction.Qd := by
    have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
        = fun p : ℝ × ℝ =>
            Function.uncurry (Work.Spaces.Dth f) p
              + p.1 * Function.uncurry (Work.Spaces.pz (Work.Spaces.Dth f)) p
              - 2 * Function.uncurry (Work.Spaces.Dth f) p / (1 + p.1)
              - 3 * Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dth f)) p / (1 + p.1) := by
      funext p
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      rw [Work.FTS.CoercivityFix.Lhat_eq]
      simp only [Work.Spaces.Dz]
    rw [hfun]
    exact (((hDth.add (contDiffOn_fst.mul hpz)).sub
        ((contDiffOn_const.mul hDth).div (contDiffOn_const.add contDiffOn_fst) hne)).sub
      ((contDiffOn_const.mul hDthDth).div (contDiffOn_const.add contDiffOn_fst) hne))
  exact hmain.of_le (m := 3) (WithTop.coe_le_coe.mpr le_top)

/-- **The requested `C³`-regularity of the two transfer pieces on the open quadrant.**  The
datum is `CoerAdm α f`, whose ledger supplies `SmoothQuad f` and `HkMem α 5 f` (hence
`HkMem α 4 f`); no further hypothesis is used. -/
theorem ContE1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.Transfer.E1 α f))
      Work.Construction.Qd ∧
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)))
      Work.Construction.Qd := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.reg.2.1
  have hmem4 : Work.Spaces.HkMem α 4 f := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  exact ⟨contDiffOn_uncurry_E1 α hα hα1 f hsm hmem4, contDiffOn_uncurry_Lhat_Dth f hsm⟩

end Work.FTS.CoercivityFix.Transfer.E1Parts
