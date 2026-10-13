/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsRLX/MuBlockBase` — the modulation block `-μ̄·AK + N_*` at a single profile

`EpsRLX/Defs.lean` fixes the block

  `muBlock α Φs E W = fun z θ => -μ̄(W)·AK α z θ + N_* μ(W) (lamfun μ(W)) W z θ`,

with the two modulation constants

  `μ(W)  = mufunS α (N₀ α (F_*+W) W) (N α (F_*+W) (Φ_s + E W)) W`,
  `μ̄(W)  = mubar (N₀ α (F_*+W) W) (N α (F_*+W) (Φ_s + E W))`.

This module names the two constants (`muOf`, `mubarOf`), records that they are the *definitional*
images of the family-level constants `muDyn`/`lamDyn` at the constant family `famOf (fun _ => W)`
(so that `MuLamOK`, which is stated for `muDyn`/`lamDyn`, applies verbatim), and proves the
**telescoping identity** along a difference `W₁ - W₂`:

  `muBlock α Φs E W₁ - muBlock α Φs E W₂
     = -Δμ̄·AK α + μ(W₁)·(D_z(W₁-W₂) - (W₁-W₂)) + Δμ·(D_z W₂ - W₂)`     on the open quadrant,

which is the pointwise form on which the `SmoothOpen`/`HkMem`/`Xn`-estimates of the block are
carried out (the two `N_*` collapses `N_* μ (lamfun μ) g = μ(D_z g - g)` require `μ ≠ -1`, which
on the class-`C` small ball is supplied by `MuLamOK`, i.e. by the sibling `MuLamOK_muOf`).

The helpers here are shared by `EpsRLX.MuBlockClassC` (the target) and by the two modules that
prove the closure and the `Xn`-bound of the difference (`MuBlockDiffSM`, `MuBlockXnBound`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.Defs
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.Apriori.ZeroMode
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.GalFields.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice famOf)

set_option autoImplicit false

/-! ## The two modulation constants of the block -/

/-- The modulation constant `μ` of the block at a single profile `W`:
`mufunS α (N₀ α (F_*+W) W) (N α (F_*+W) (Φ_s + E W)) W`. -/
noncomputable def muOf (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) : ℝ :=
  Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
    (Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + E W z θ)) W

/-- The modulation constant `μ̄` of the block at a single profile `W`:
`mubar (N₀ α (F_*+W) W) (N α (F_*+W) (Φ_s + E W))`. -/
noncomputable def mubarOf (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) : ℝ :=
  Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
    (Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + E W z θ))

/-! ## Identification with the family-level constants -/

/-- `muOf` at a profile `W` *is* `muDyn` at the constant family `famOf (fun _ => W)` and `τ = 0`
(definitionally: `Ftau`, `slice`, `Ftot` and `PsiCan` all reduce). -/
theorem muOf_eq_muDyn (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) :
    muOf α Φs E W = Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ : ℝ => W))) (famOf (fun _ => W)) 0 := rfl

/-- The companion of `muOf_eq_muDyn` for the second modulation constant `λ = lamfun μ`. -/
theorem lamfun_muOf_eq_lamDyn (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) :
    Work.Construction.lamfun (muOf α Φs E W) = Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ : ℝ => W))) (famOf (fun _ => W)) 0 := rfl

/-- The block, with its two constants named. -/
theorem muBlock_apply (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) (z θ : ℝ) :
    muBlock α Φs E W z θ = -(mubarOf α Φs E W) * Work.Construction.AK α z θ
      + Work.Construction.Nstar (muOf α Φs E W)
          (Work.Construction.lamfun (muOf α Φs E W)) W z θ := rfl

/-- The block, with its two constants named (function form). -/
theorem muBlock_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) :
    muBlock α Φs E W = fun z θ => -(mubarOf α Φs E W) * Work.Construction.AK α z θ
      + Work.Construction.Nstar (muOf α Φs E W)
          (Work.Construction.lamfun (muOf α Φs E W)) W z θ := rfl

/-- **`MuLamOK` bounds the block's modulation constants on the class-`C` small ball** (the
statement of `MuLamOK` is exactly about `muDyn`/`lamDyn` at the constant family). -/
theorem MuLamOK_muOf {α C₀ : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) {W : Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hXn : Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2) :
    |muOf α Φs E W| ≤ 1 / 2 ∧ |Work.Construction.lamfun (muOf α Φs E W)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := hml W hW hXn
  exact ⟨by rw [muOf_eq_muDyn]; exact h1, by rw [lamfun_muOf_eq_lamDyn]; exact h2⟩

/-! ## Two elementary tools -/

/-- `N_* μ (lamfun μ) g = μ·(D_z g - g)` pointwise, for `μ ≠ -1` (`Apriori.Nstar_lamfun`,
pointwise). -/
theorem Nstar_lamfun_eq {μ : ℝ} (hμ : μ ≠ -1) (g : Fn) (z θ : ℝ) :
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ
      = μ * (Work.Spaces.Dz g z θ - g z θ) := by
  have h := congrFun (congrFun (Work.FTS.Apriori.Nstar_lamfun hμ g) z) θ
  simpa using h

/-- **`D_z` is additive on the open quadrant for a pointwise decomposition `f = f' + k`.** -/
theorem Dz_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f') (hk : Work.FTS.EllipticEst.SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ + Work.Spaces.Dz k z θ := by
  intro z θ hz hθ0 hθ1
  have h1 := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := f)
    (G := fun z θ => f' z θ + k z θ) (fun z θ _ _ _ => h z θ) 1 z θ hz hθ0 hθ1
  have h2 := Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf' hk 1 z θ hz hθ0 hθ1
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1.trans h2

/-! ## The telescoping identity -/

/-- **The block telescopes along a difference.**  With `μᵢ = μ(Wᵢ)`, `μ̄ᵢ = μ̄(Wᵢ)` and
`μᵢ ≠ -1`, on the open quadrant

  `muBlock α Φs E W₁ - muBlock α Φs E W₂
     = -(μ̄₁-μ̄₂)·AK α + μ₁·(D_z(W₁-W₂) - (W₁-W₂)) + (μ₁-μ₂)·(D_z W₂ - W₂)`.

Proof: rewrite both `N_*`-blocks with the collapse `N_* μ (lamfun μ) g = μ(D_z g - g)`, rewrite
`D_z(W₁-W₂) = D_z W₁ - D_z W₂` with `Dz_add_of_smoothOpen`, `ring`. -/
theorem muBlock_sub_eq {α : ℝ} {Φs : Fn} {E : Fn → Fn} {W₁ W₂ : Fn}
    (hW₁ : Work.FTS.EllipticEst.SmoothOpen W₁) (hW₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hμ₁ : muOf α Φs E W₁ ≠ -1) (hμ₂ : muOf α Φs E W₂ ≠ -1) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      muBlock α Φs E W₁ z θ - muBlock α Φs E W₂ z θ
        = -(mubarOf α Φs E W₁ - mubarOf α Φs E W₂) * Work.Construction.AK α z θ
          + muOf α Φs E W₁ * (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
              - (W₁ z θ - W₂ z θ))
          + (muOf α Φs E W₁ - muOf α Φs E W₂) * (Work.Spaces.Dz W₂ z θ - W₂ z θ) := by
  intro z θ hz hθ0 hθ1
  have hDz : Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
      = Work.Spaces.Dz W₁ z θ - Work.Spaces.Dz W₂ z θ := by
    have h := Dz_add_of_smoothOpen (f := W₁) (f' := fun z θ => W₁ z θ - W₂ z θ) (k := W₂)
      (Work.FTS.NonlinRows.smoothOpen_sub hW₁ hW₂) hW₂ (fun z θ => by ring)
    have h' := h z θ hz hθ0 hθ1
    linarith
  rw [muBlock_apply, muBlock_apply, hDz, Nstar_lamfun_eq hμ₁ W₁ z θ,
    Nstar_lamfun_eq hμ₂ W₂ z θ]
  ring

end Work.FTS.StrongEps.EpsRLX
