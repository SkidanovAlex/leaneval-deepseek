/-
# `Work.FTS.LocData.SmoothQuad_locG` — the localised perturbation `g` is `C^∞` on the quadrant

The target lemma of this module is

  `SmoothQuad_locG : SmoothQuad h → SmoothQuad (locG α L β h)`,

i.e. **the localised perturbation `g = locG α L β h = -zfar L F_* + β·h` of the self-similar
profile is `C^∞` on the open quadrant `z > -1, 0 < θ < π/2` whenever the bump `h` is.**

(`SmoothQuad`, defined in `Submission.Work.FTS.LocData.Defs`, is *genuine* `C^∞` — the order
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)` — *not* `ContDiffOn ℝ ⊤`, which in this
Mathlib is analyticity and would be preserved by neither a cut-off nor the profile.)

This is the smoothness input of `dataAdm_locG`, the statement that the localised datum of the
route is admissible (`DataAdm`): `locG α L β h = -zfar L F_* + β h` is a *difference of two
products* of the two basic `C^∞` profiles of the chapter,

* `F_*(z,θ) = α·(Γ(θ)/c)·2z/(1+z)²` — smooth because `Γ(θ) = (sinθcos²θ)^{α/3}` has a
  *positive* base on the open quadrant and `2z/(1+z)²` is a rational function with no pole on
  `z > -1`;
* `χ(z/L)` — smooth because `χ = smoothTransition(2 - ‖·‖)` is `C^∞` on `ℝ`
  (`Work.Stability.chi_contDiff`) and `z ↦ z/L` is smooth.

The main theorem is assembled from the closure properties of `SmoothQuad` proved below
(closure under `+`, `-`, `·`, negation, multiplication by a constant) together with the
smoothness of the two profiles.  Note that the statement's hypotheses `0 < α`, `α ≤ 1` are
*not* needed: the claim holds for every real `α` (and every real `L`, `L = 0` included, where
`χ(z/L) = χ 0` is constant).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open Set
open scoped Real Topology

namespace Work.FTS.LocData

noncomputable section

/-! ## The class `SmoothQuad` is closed under the pointwise operations

Each of these is the corresponding `ContDiffOn` closure rule read through the definition of
`SmoothQuad` (`Function.uncurry` commutes with the pointwise operations up to definitional
equality). -/

theorem SmoothQuad_neg {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) :
    SmoothQuad (fun z θ => -f z θ) := by
  unfold SmoothQuad at *
  exact hf.neg

theorem SmoothQuad_add {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g) :
    SmoothQuad (fun z θ => f z θ + g z θ) := by
  unfold SmoothQuad at *
  exact hf.add hg

theorem SmoothQuad_sub {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g) :
    SmoothQuad (fun z θ => f z θ - g z θ) := by
  unfold SmoothQuad at *
  exact hf.sub hg

theorem SmoothQuad_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g) :
    SmoothQuad (fun z θ => f z θ * g z θ) := by
  unfold SmoothQuad at *
  exact hf.mul hg

theorem SmoothQuad_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) :
    SmoothQuad (fun z θ => c * f z θ) := by
  unfold SmoothQuad at *
  have hc : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_const
  exact hc.mul hf

/-! ## The two basic `C^∞` profiles of the chapter -/

/-- The cut-off factor `(z,θ) ↦ χ(z/L)` is `C^∞` on the quadrant, for every real `L` (for
`L = 0` the function is the constant `χ 0`, since Lean's division by zero is `0`). -/
theorem SmoothQuad_chi_div (L : ℝ) :
    SmoothQuad (fun z θ : ℝ => Work.Stability.chi (z / L)) := by
  unfold SmoothQuad
  have hchi : ContDiff ℝ Work.Stability.smoothOrder Work.Stability.chi :=
    Work.Stability.chi_contDiff
  have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 / L)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    contDiffOn_fst.div_const L
  exact hchi.comp_contDiffOn hdiv

/-- **The model profile `F_*` is `C^∞` on the quadrant.**  It is the product of the angular
factor `Γ(θ)/c` — smooth because the base `sinθ·cos²θ` is strictly positive on `0 < θ < π/2` —
with the rational radial factor `2z/(1+z)²`, whose only pole `z = -1` lies outside `z > -1`.
No hypothesis on `α` is needed. -/
theorem Fstar_smoothQuad (α : ℝ) : SmoothQuad (Work.Construction.Fstar α) := by
  unfold SmoothQuad
  -- the angular factor `Γ(θ)`
  have hGam : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
      have h : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => Real.sin (Prod.snd p) * Real.cos (Prod.snd p) ^ 2)
          (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
        (Real.contDiff_sin.mul (Real.contDiff_cos.pow 2)).comp_contDiffOn
          (contDiffOn_snd (E := ℝ) (F := ℝ))
      simpa using h
    have hne : ∀ p : ℝ × ℝ, p ∈ Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2) →
        Real.sin p.2 * Real.cos p.2 ^ 2 ≠ 0 := by
      rintro ⟨z, θ⟩ hp
      have hθ := hp.2
      have h1 : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    have hexp : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => α / 3)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_const
    have hrpow : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (Real.sin p.2 * Real.cos p.2 ^ 2) ^ (α / 3))
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
      hbase.rpow hexp hne
    simpa only [Work.Spaces.Gam] using hrpow
  -- the radial factor `2z/(1+z)²`
  have hrad : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.FM.Fstar p.1) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    have hz : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
      have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
        contDiffOn_const.mul contDiffOn_id
      have hden : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
        (contDiffOn_const.add contDiffOn_id).pow 2
      exact hnum.div hden (fun z hz =>
        pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
    exact hz.comp contDiffOn_fst (fun p hp => hp.1)
  -- the product `α·(Γ(θ)/c)·F_*(z)`
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    have hc : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => α)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_const
    exact hc.mul (hGam.div_const _)
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ =>
        α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * Work.FM.Fstar p.1)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    h1.mul hrad
  simpa only [Function.uncurry_def, Work.Construction.Fstar] using h2

/-! ## The target -/

/-- **The localised perturbation is `C^∞` on the quadrant whenever the bump is**, i.e.
`locG α L β h = -zfar L F_* + β h = F_*·χ(z/L) + β h - F_*` is a combination of the two
`C^∞` profiles of the chapter.  The hypotheses `0 < α`, `α ≤ 1` of the route are not used. -/
theorem SmoothQuad_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    (hsh : SmoothQuad h) : SmoothQuad (locG α L β h) := by
  have hchi := SmoothQuad_chi_div L
  have hF := Fstar_smoothQuad α
  have hβ : SmoothQuad (fun z θ => β * h z θ) := SmoothQuad_const_mul β hsh
  have hmain : SmoothQuad (fun z θ => Work.Construction.Fstar α z θ * Work.Stability.chi (z / L)
      + β * h z θ - Work.Construction.Fstar α z θ) :=
    ((hF.mul hchi).add hβ).sub hF
  unfold SmoothQuad at hmain ⊢
  refine hmain.congr (fun p hp => ?_)
  simp only [Function.uncurry_def, locG_apply, locData_apply]

end

end Work.FTS.LocData
