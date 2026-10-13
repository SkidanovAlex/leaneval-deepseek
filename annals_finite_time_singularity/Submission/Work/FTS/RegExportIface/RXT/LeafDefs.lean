import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.LeafDefs` — the definition block of `RXT/Leaves.lean`

Split out of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean` (same namespace, hence the same
fully-qualified names) so that leaf-proof modules can be written **without** importing `Leaves`:
`Leaves` imports this file, so every one of the ~130 consumers of `Leaves` is unaffected, while a
`LeafAux/<leaf>.lean` module (imported by `Leaves`) can import `LeafDefs` instead of `Leaves` and
the import cycle is broken.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS.RegExportIface.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG St1Class)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- The one-step backward inequality on compact boxes, with the coupling taken at the new time. -/
def ConeStep (n : ℕ) (φ : Fin n → ℝ → ℝ → ℝ → ℝ) (T A C F : ℝ) : Prop :=
  ∀ R ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ τ ∈ Ico (0:ℝ) T, ∀ h : ℝ, 0 < h → h < h₀ →
    τ + h ≤ T → ∀ s ψ : ℝ, |s| ≤ R → |ψ| ≤ R →
      ∃ s' ψ' : ℝ, |s' - s| ≤ A * h ∧ |ψ' - ψ| ≤ A * h ∧
        ∀ M B : ℝ, (∀ j, |φ j s' ψ' τ| ≤ M) → (∀ j, |φ j s ψ (τ + h)| ≤ B) →
          ∀ k, |φ k s ψ (τ + h)| ≤ M + h * (C * B + F) + ε * h

/-- The six components `(j,i) = (#D_z, #D_θ)` of the system. -/
def idx : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]

/-- the sanitised family, its stream function and its clock -/
abbrev GR (α : ℝ) (g : Fam) : Fam := gS α (tauExt g)
abbrev ΦR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : Fam := psiR α Φs E (tauExt g)
abbrev μR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ :=
  Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g
/-- the three transport coefficients (closed form, `b = Vθ7/sin 2θ`) -/
abbrev VR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  Vz7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g)
abbrev bR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ / Real.sin (2 * θ)
abbrev cR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  cs7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g)
/-- the `F_*`-forcing `Σ = Vz·D_zF_* + Vθ·∂_θF_* + cs·F_*` (slice at `τ`) -/
def SigR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  VR α Φs E g z θ τ * Work.Spaces.Dz (Work.Construction.Fstar (pExp α)) z θ
    + Vθ7 (pExp α) (ΦR α Φs E g) z θ τ * Work.Spaces.pth (Work.Construction.Fstar (pExp α)) z θ
    + cR α Φs E g z θ τ * Work.Construction.Fstar (pExp α) z θ

/-- The local regularity of `∂_τg` that S5a consumes (output of S5c). -/
def GdotLoc (S : ℝ) (g : Fam) : Prop :=
  (∀ σ ∈ Ioc (0:ℝ) S,
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.gdot g σ)) Work.FTS.EllipticEst.Q0) ∧
  ∀ a b c d : ℝ, 0 < a → a ≤ b → 0 < c → c ≤ d → d < π / 2 → ∃ C : ℝ,
    ∀ σ ∈ Ioc (0:ℝ) S, ∀ z ∈ Icc a b, ∀ θ ∈ Icc c d,
      (∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 1 →
        |Work.Spaces.pz (Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ)) z θ| ≤ C ∧
        |Work.Spaces.pth (Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ)) z θ| ≤ C)

end Work.FTS.RegExportIface.RXT
