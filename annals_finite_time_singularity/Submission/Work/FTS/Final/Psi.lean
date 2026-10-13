/-
# `Work.FTS.Final.Psi` — the `Law` additivity of the elliptic problem (audit item 1)

**Deliverable of this module**: `hPsi_of_pkgs`, the statement consumed by the dynamic chain
(`StrongGlobal`/`Open2`, and now the `ε`-route) as its hypothesis `hPsi`:

> `hPsi_of_pkgs (hS : StarPkgo2 α Cs Φs) (hE : ∀ g, ClassC α g → EllPkgGo α Ce g (E g)) :
>    ∀ G : Fam, (∀ τ ≥ 0, ClassC α (slice G τ)) → ∀ τ ≥ 0 →
>      IsBslSolPos α (Construction.Ftau α G τ) (slice (PsiCan Φs E G) τ)`

i.e. **additivity of the elliptic law `IsBslSolPos` along the canonical stream function**
`PsiCan Φs E G = Φs + E (slice G τ)`.  The audit's item 1 is this statement with `Law :=
IsBslSol` and the old class `GalClass`; the deliverable re-states it at the strong route's
interface, `Law := IsBslSolPos` and the linear class `ClassC` (design §A: `ClassC` is the linear
class of the elliptic layer, so the additivity proof goes through).

The mathematical content is exactly the linearity of the elliptic operator
`bslOp α = -α²z²∂_zz - α(5+α)z∂_z + Lzero` (`Work.Elliptic.bslOp_add`) together with the
additivity of the three remaining clauses (two Dirichlet values and the far-field decay).  The
source of the two summands is the *split* of the profile:

  `Construction.Ftau α G τ = Fstar α + slice G τ`,
  `slice (PsiCan Φs E G) τ = Φs + E (slice G τ)`,

where `Φs` solves the star problem (`StarPkgo2.sol`) and `E (slice G τ)` solves the perturbation
problem (`EllPkgGo.sol`).

Two intermediate lemmas are exported as well: `isBslSolPos_add` (the additivity of the law
itself, at the `StrongGlobal` reading) and `bslOp_add_of_contDiffOn` (the pointwise form on the
open quadrant).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Final.Defs
import Submission.Work.Elliptic.bslOp_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)

set_option autoImplicit false

/-! ## Additivity of the elliptic law -/

/-- The open quadrant is a neighbourhood of each of its points. -/
theorem qd_mem_nhds {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) :=
  (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ, hθ2⟩

/-- The pointwise additivity of `bslOp` on the open quadrant, from `C²`-regularity there. -/
theorem bslOp_add_of_contDiffOn {α : ℝ} {Ψ Φ : Fn}
    (hsΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd)
    (hsΦ : ContDiffOn ℝ 2 (Function.uncurry Φ) Work.Construction.Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Elliptic.bslOp α Ψ z θ + Work.Elliptic.bslOp α Φ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  exact Work.Elliptic.bslOp_add α Ψ Φ z θ hcos
    (hsΨ.contDiffAt (qd_mem_nhds hz hθ hθ2)) (hsΦ.contDiffAt (qd_mem_nhds hz hθ hθ2))

/-- **`IsBslSolPos` is additive** (at the `StrongGlobal` reading of the law): the sum of two
solutions of the (PolarBSL) problem solves the (PolarBSL) problem for the sum of the data.  This
is the engine of `hPsi_of_pkgs`. -/
theorem isBslSolPos_add {α : ℝ} {F₁ F₂ Ψ₁ Ψ₂ : Fn}
    (h₁ : IsBslSolPos α F₁ Ψ₁) (h₂ : IsBslSolPos α F₂ Ψ₂)
    (hs₁ : ContDiffOn ℝ 2 (Function.uncurry Ψ₁) Work.Construction.Qd)
    (hs₂ : ContDiffOn ℝ 2 (Function.uncurry Ψ₂) Work.Construction.Qd) :
    IsBslSolPos α (fun z θ => F₁ z θ + F₂ z θ) (fun z θ => Ψ₁ z θ + Ψ₂ z θ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ hθ2
    rw [bslOp_add_of_contDiffOn hs₁ hs₂ hz hθ hθ2, h₁.1 z hz θ hθ hθ2, h₂.1 z hz θ hθ hθ2]
  · intro z hz
    show Ψ₁ z 0 + Ψ₂ z 0 = 0
    rw [h₁.2.1 z hz, h₂.2.1 z hz, add_zero]
  · intro z hz
    show Ψ₁ z (π / 2) + Ψ₂ z (π / 2) = 0
    rw [h₁.2.2.1 z hz, h₂.2.2.1 z hz, add_zero]
  · intro θ hθ
    simpa using (h₁.2.2.2 θ hθ).add (h₂.2.2.2 θ hθ)

/-! ## The additivity along the canonical stream function -/

/-- A `SmoothOpen` function is `C²` on the open quadrant (`Q0 = Qd` definitionally). -/
theorem contDiffOn_two_of_smoothOpen {F : Fn} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContDiffOn ℝ 2 (Function.uncurry F) Work.Construction.Qd :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp h 2

/-- **`hPsi_of_pkgs` (audit §4 item 1, at `Law := IsBslSolPos` and the class `ClassC`).**

The canonical stream function `PsiCan Φs E G = Φs + E (slice G τ)` solves the elliptic problem for
the full profile `Ftau α G τ = Fstar α + slice G τ`, provided the star profile `Φs` solves the star
problem and the linear operator `E` solves the perturbation problem on the class `ClassC`.  This is
exactly the `hPsi` hypothesis of the dynamic chain: it is what makes the elliptic law hold at every
fake time `τ ≥ 0` for the solution of the modulated equation. -/
theorem hPsi_of_pkgs {α Cs Ce : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    (hS : StarPkgo2 α Cs Φs)
    (hE : ∀ g, ClassC α g → EllPkgGo α Ce g (E g)) :
    ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → ClassC α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
      IsBslSolPos α (Work.Construction.Ftau α G τ)
        (slice (PsiCan Φs (fun g => E g) G) τ) := by
  intro G hG τ hτ
  have h₁ : IsBslSolPos α (Work.Construction.Fstar α) Φs :=
    Work.FTS.StrongGlobal.IsBslSol.toPos hS.sol
  have h₂ : IsBslSolPos α (slice G τ) (E (slice G τ)) :=
    Work.FTS.StrongGlobal.IsBslSol.toPos (hE (slice G τ) (hG τ hτ)).sol
  have hs₁ : ContDiffOn ℝ 2 (Function.uncurry Φs) Work.Construction.Qd :=
    contDiffOn_two_of_smoothOpen hS.smooth
  have hs₂ : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => E (slice G τ) z θ))
      Work.Construction.Qd :=
    contDiffOn_two_of_smoothOpen (hE (slice G τ) (hG τ hτ)).smooth
  have hmain := isBslSolPos_add h₁ h₂ hs₁ hs₂
  convert hmain using 1
  · funext z θ
    rfl
  · funext z θ
    rfl

end Work.FTS.Final
