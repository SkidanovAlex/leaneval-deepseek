/-
# `FTS/PhiStar/CoreAux/fields_ident.lean` — the `Ŷ`-form of the six transport fields

`Work.FTS.VocabO2.StarPkgo2 α Cs Φs` bounds the six transported fields
`((z+1)/z)·ℛ(Φ̃_*)`, `𝒱(Φ̃_*)`, `((z+1)/z)·𝒱(Φ̃_*)`, `𝒰(Φ̃_*)/σ`, `((z+1)/z)·𝒰(Φ̃_*)/σ`,
`∂_θ𝒰(Φ̃_*)` of the self-similar vorticity equation, where `Φ̃_* = PhiTs α Φs`,
`σ = sin 2θ`.  This file proves that each of them is, *on the open quadrant*, the
corresponding `Ŷ`-expression of `CoreAux/FieldsDefs.lean`,
`Ŷ = Ycheck α Φs = ((z+1)/z)·(Φ̃_*/σ)`.

## The route

Write `Φ̆ = Φ̃_*/σ` and `Ψ = (z/(z+1))·Ŷ`, so that on the open quadrant

* `Φ̃_* = sin 2θ · Ψ` and `Φ̆ = (z/(z+1))·Ŷ`.

The four substitution identities of `Work.FTS.H2.StarPkg.Subst` are stated for an abstract
`Φ` in the form `ℛ(sin 2θ·Φ) = 2Φ + 2α sin²θ·D_zΦ + sin 2θ·∂_θΦ`, etc.  Applying them to
`Ψ` and rewriting `Ψ = (z/(z+1))Ŷ` gives the six identities of `FieldsDefs`; the only
calculus needed are the two product rules

* `∂_zΨ = (1/(z+1)²)Ŷ + (z/(z+1))·∂_zŶ`,
* `∂_θ(D_zΨ) = (z/(z+1))·(∂_θŶ/(z+1) + z·∂_z∂_θŶ)`  (Clairaut + product rule),

and the pointwise identity `sin 2θ·Ψ = Φ̃_*` on `Q0 = (0,∞) × (0,π/2)`.

Since the consumer mentions `Φ̃_*` and not `sin 2θ·Ψ`, the identities are transported back
from `sin 2θ·Ψ` to `Φ̃_*` by *locality* of `∂_z` and `∂_θ` on the open quadrant
(`fi_pz_congr`, `fi_pth_congr`): the two functions agree on the open neighbourhood `Q0` of
every point of `Q0`, and `deriv` depends only on the germ.

## Relation to the delegated siblings

The two general-purpose calculus lemmas used here are also delivered separately as
`Work.FTS.PhiStar.CoreAux.pth_Uop_sin_two_mul_weak` (the `∂_θ`-substitution for `𝒰`, with
the unused `∀θ'`-differentiability hypothesis of `Subst.pth_Uop_sin_two_mul` dropped) and
`Work.FTS.PhiStar.CoreAux.pth_Dz_zdiv_mul`; the local copies below (`fi_pth_Uop_sin_two_mul`,
`fi_pz_zdiv_mul`) keep this file self-contained.  Their names are prefixed `fi_` so that they
never clash with those siblings.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.H2.StarPkg.Subst
import Submission.Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The substituted unknown `Ψ` and the auxiliary function `sin 2θ · Ψ` -/

/-- `Ψ = (z/(z+1))·Ŷ`; on the open quadrant `sin 2θ · Ψ = Φ̃_*` and `Ψ = (z/(z+1))·Φ̆`. -/
abbrev fiSubs (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => z / (z + 1) * Work.FTS.VocabO2.Ycheck α Φs z θ

/-- `sin 2θ · Ψ`: the function to which the `sin 2θ`-substitution identities apply. -/
abbrev fiPsiF (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Real.sin (2 * θ) * fiSubs α Φs z θ

/-! ## Elementary facts on the open quadrant -/

theorem fi_sin_two_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

theorem fi_cos_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-! ## Locality of `∂_z`, `∂_θ` on the open quadrant -/

theorem fi_pz_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_left θ).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hs : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h z' θ hz'.1 hz'.2.1 hz'.2.2
  simp only [Work.Spaces.pz]
  exact hs.deriv_eq

theorem fi_pth_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' hz hθ'.1 hθ'.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

/-! ## The pointwise identity `sin 2θ · Ψ = Φ̃_*` on the open quadrant -/

theorem fi_PsiF_eq_phi {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ := by
  have hs : Real.sin (2 * θ) ≠ 0 := fi_sin_two_ne_zero ⟨hθ0, hθ1⟩
  simp only [fiPsiF, fiSubs, Work.FTS.VocabO2.Ycheck, Work.Construction.s2]
  field_simp

/-! ## Transporting `ℛ`, `𝒱`, `𝒰` from `Φ̃_*` to `sin 2θ · Ψ` -/

theorem fi_Rop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.Construction.Rop α (fiPsiF α Φs) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  have h1 := fi_pz_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h2 := fi_pth_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h3 := hloc z θ hz hθ.1 hθ.2
  simp only [Work.Construction.Rop, ← h1, ← h2, h3]

theorem fi_Vop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.Construction.Vop (fiPsiF α Φs) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  have h2 := fi_pth_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h3 := hloc z θ hz hθ.1 hθ.2
  simp only [Work.Construction.Vop, ← h2, h3]

theorem fi_Uop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.Construction.Uop α (fiPsiF α Φs) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  have h1 := fi_pz_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h3 := hloc z θ hz hθ.1 hθ.2
  simp only [Work.Construction.Uop, ← h1, h3]

theorem fi_pth_Uop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) z θ
      = Work.Spaces.pth (Work.Construction.Uop α (fiPsiF α Φs)) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  refine fi_pth_congr (f := Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))
    (g := Work.Construction.Uop α (fiPsiF α Φs)) ?_ hz hθ
  intro z θ hz h0 h1
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h0, h1⟩
  have h1' := fi_pz_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ'
  have h3 := hloc z θ hz h0 h1
  simp only [Work.Construction.Uop, ← h1', ← h3]

/-! ## `SmoothOpen` of `z/(z+1)` and of `Ψ` -/

theorem fi_smoothOpen_selfun :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => z / (z + 1)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry (fun z θ : ℝ => z / (z + 1))
      = fun p : ℝ × ℝ => p.1 / (p.1 + 1) := rfl
  rw [h]
  exact ContDiffOn.div contDiffOn_fst (contDiffOn_fst.add contDiffOn_const)
    (fun p hp => by
      have hz := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      positivity)

theorem fi_smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).mul (hg.forall n)

theorem fi_smoothOpen_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs)) :
    Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) :=
  fi_smoothOpen_mul fi_smoothOpen_selfun hY

/-- The `θ`-slice of `Ψ` is differentiable at an interior angle (from `SmoothOpen`). -/
theorem fi_diffAt_theta_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => fiSubs α Φs z θ') θ :=
  ((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-! ## The two product rules for `Ψ = (z/(z+1))·Ŷ` -/

/-- `∂_θΨ = (z/(z+1))·∂_θŶ` (the coefficient is constant in `θ`). -/
theorem fi_pth_Subs_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    Work.Spaces.pth (fiSubs α Φs) z θ
      = z / (z + 1) * Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  simp only [Work.Spaces.pth, fiSubs]
  exact deriv_const_mul_field (z / (z + 1))

/-- The same identity, at the level of functions. -/
theorem fi_pth_Subs (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) :
    Work.Spaces.pth (fiSubs α Φs)
      = fun z θ => z / (z + 1) * Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  funext z θ
  exact fi_pth_Subs_apply α Φs z θ

theorem fi_hasDerivAt_zdiv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => z' / (z' + 1)) (1 / (z + 1) ^ 2) z := by
  have h : HasDerivAt (fun z' : ℝ => z' / (z' + 1))
      ((1 * (z + 1) - z * 1) / (z + 1) ^ 2) z :=
    (hasDerivAt_id z).div ((hasDerivAt_id z).add_const 1) (by linarith)
  convert h using 1
  ring

/-- Product rule for the multiplier `z/(z+1)`. -/
theorem fi_pz_zdiv_mul {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hF : HasDerivAt (fun z' : ℝ => F z' θ) (Work.Spaces.pz F z θ) z) :
    Work.Spaces.pz (fun z θ => z / (z + 1) * F z θ) z θ
      = 1 / (z + 1) ^ 2 * F z θ + z / (z + 1) * Work.Spaces.pz F z θ := by
  have hmul := (fi_hasDerivAt_zdiv hz).mul hF
  simp only [Work.Spaces.pz]
  exact hmul.deriv

/-- `∂_zΨ = (1/(z+1)²)Ŷ + (z/(z+1))·∂_zŶ`. -/
theorem fi_pz_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (fiSubs α Φs) z θ
      = 1 / (z + 1) ^ 2 * Work.FTS.VocabO2.Ycheck α Φs z θ
        + z / (z + 1) * Work.Spaces.pz (Work.FTS.VocabO2.Ycheck α Φs) z θ :=
  fi_pz_zdiv_mul hz (hY.hasDerivAt_slice hθ hz)

/-- `∂_θ(D_zΨ) = (z/(z+1))·(∂_θŶ/(z+1) + z·∂_z∂_θŶ)` (Clairaut + product rule). -/
theorem fi_pth_Dz_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.Dz (fiSubs α Φs)) z θ
      = z / (z + 1) * (Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs) z θ / (z + 1)
          + z * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs)) z θ) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry (fiSubs α Φs)) (z, θ) :=
    (hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  -- `∂_θ(D_zΨ) = z·∂_θ(∂_zΨ)`
  have h1 : Work.Spaces.pth (Work.Spaces.Dz (fiSubs α Φs)) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz (fiSubs α Φs)) z θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pth]
    exact deriv_const_mul_field z
  rw [h1, (Work.Spaces.pz_pth_comm hcd).symm]
  -- `∂_z(∂_θΨ) = ∂_z((z/(z+1))·∂_θŶ)`
  rw [fi_pth_Subs]
  rw [fi_pz_zdiv_mul hz ((hY.pth).hasDerivAt_slice hθ hz)]
  field_simp
  try ring

/-! ## The `∂_θ`-substitution identity for `𝒰`, without the unused `∀θ'`-hypothesis -/

theorem fi_pth_Uop_sin_two_mul (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : DifferentiableAt ℝ (fun θ' => Φ z θ') θ)
    (hzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz Φ z θ') θ) :
    Work.Spaces.pth (Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ)) z θ
      = -(2 * Real.cos (2 * θ) * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)
          + Real.sin (2 * θ) * (3 * Work.Spaces.pth Φ z θ
            + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ)) := by
  have hU : (fun θ' : ℝ =>
        Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ')
      = fun θ' => -(Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')) := by
    funext θ'
    exact Work.FTS.H2.StarPkg.Uop_sin_two_mul α Φ z θ'
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have hinner : HasDerivAt (fun θ' : ℝ => 3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')
      (3 * Work.Spaces.pth Φ z θ + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Φ z θ') (Work.Spaces.pth Φ z θ) θ := hθ.hasDerivAt
    have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.Dz Φ z θ')
        (Work.Spaces.pth (Work.Spaces.Dz Φ) z θ) θ := hzθ.hasDerivAt
    exact ((h1.const_mul 3).add (h2.const_mul α))
  have hprod : HasDerivAt
      (fun θ' : ℝ => Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ'))
      (Real.cos (2 * θ) * 2 * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)
        + Real.sin (2 * θ) * (3 * Work.Spaces.pth Φ z θ
          + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ)) θ :=
    hsin2'.mul hinner
  rw [Work.Spaces.pth, hU]
  have hneg : (fun θ' : ℝ => -(Real.sin (2 * θ')
        * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ'))) = -(fun θ' : ℝ =>
      Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')) := by
    funext θ'; rfl
  rw [hneg, deriv.neg, hprod.deriv]
  simp only [Work.Spaces.Dz]
  ring_nf

/-! ## The six identities -/

theorem fi_EH {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.FTS.PhiStar.EH α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hcos := fi_cos_ne_zero hθ
  rw [fi_Rop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Rop_sin_two_mul α (fiSubs α Φs) z θ hcos hdθ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ, fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EH, Work.FTS.PhiStar.Tblk, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EV {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.FTS.PhiStar.EV (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hcos := fi_cos_ne_zero hθ
  rw [fi_Vop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Vop_sin_two_mul (fiSubs α Φs) z θ hcos hdθ]
  rw [fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EV, Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EVz {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.FTS.PhiStar.EVz (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hcos := fi_cos_ne_zero hθ
  rw [fi_Vop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Vop_sin_two_mul (fiSubs α Φs) z θ hcos hdθ]
  rw [fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EU {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ
      = Work.FTS.PhiStar.EU α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hs2 := fi_sin_two_ne_zero hθ
  rw [fi_Uop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Uop_sin_two_mul α (fiSubs α Φs) z θ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ]
  simp only [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EUz {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)
      = Work.FTS.PhiStar.EUz α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hs2 := fi_sin_two_ne_zero hθ
  rw [fi_Uop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Uop_sin_two_mul α (fiSubs α Φs) z θ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ]
  simp only [Work.FTS.PhiStar.EUz, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EPU {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) z θ
      = Work.FTS.PhiStar.EPU α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hdθ₂ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz (fiSubs α Φs) z θ') θ :=
    (((hsm.Dz).curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  rw [fi_pth_Uop_transfer hz hθ]
  rw [fi_pth_Uop_sin_two_mul α (fiSubs α Φs) z θ hdθ hdθ₂]
  rw [fi_pth_Dz_Subs hY hz hθ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ, fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EPU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

/-! ## The target -/

theorem fields_ident {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen Φs) : (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ = Work.FTS.PhiStar.EH α (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = Work.FTS.PhiStar.EV (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = Work.FTS.PhiStar.EVz (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ = Work.FTS.PhiStar.EU α (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) = Work.FTS.PhiStar.EUz α (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) z θ = Work.FTS.PhiStar.EPU α (Work.FTS.VocabO2.Ycheck α Φs) z θ) := by
  obtain ⟨-, -, hY⟩ := smoothOpen_PhiTs hα hα1 hsm
  exact ⟨fun z θ hz h0 h1 => fi_EH hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EV hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EVz hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EU hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EUz hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EPU hY hz ⟨h0, h1⟩⟩

end

end Work.FTS.PhiStar.CoreAux
