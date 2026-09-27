import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4S.PushShellG

/-!
# `Work.Engulf.E4S.PushStep2` — `E4d` is the case `g := ND.g₁` of `E4S.pushShellG`

`Work.Engulf.E4Aux.pushStep2` (proved in `Submission/Work/Engulf/E4Aux/pushStep2.lean`) is
`Work.Engulf.E4S.pushShellG` with the moving map `g` specialised to the frozen map `ND.g₁` (and with
the two unused hypotheses `hcore`, `hG` of the old statement present).  This file records that
derivation in the universe-free form (`{M : Type*}`, `Work.Engulf.ToolsAllM M n`) so that a caller
may transport either direction.
-/

open Set Metric PL
open Work.Engulf.Alt

namespace Work.Engulf.E4S

/-- **`E4d`** (`Work.Engulf.E4Aux.pushStep2`): the push of one shelled simplex with the *frozen*
map `ND.g₁`; the case `g := ND.g₁` of `Work.Engulf.E4S.pushShellG`. -/
theorem pushStep2_of_pushShellG {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M}
    {Γ : PL.Cx N} {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)}
    {ψ : PL.CubeChart n M} {ε : ℝ}
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (T : Work.Engulf.ToolsAllM M n) (hV : IsOpen V) {i : ℕ} (hi : i < ND.ord.length)
    (hcore : f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    {A : PL.E N →ᵃ[ℝ] PL.E n}
    (hAeq : ∀ x ∈ PL.simp (ND.ord[i]), ND.g₁ x = ψ.toFun (A x))
    (hAopen : ∀ x ∈ PL.simp (ND.ord[i]), A x ∈ PL.openCube (1 : ℝ))
    {Φ : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q} {F : Set (PL.E q)} {γ₀ γ₁ : PL.E q → ℝ}
    (hFc : IsCompact F) (hFconv : Convex ℝ F) (hγ₀c : Continuous γ₀) (hγ₁c : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z) (hfr : ∀ z ∈ frontier F, γ₀ z = γ₁ z)
    (hprism : Φ '' (A '' PL.simp (ND.ord[i])) =
      {x : Work.Engulf.Pr (n - q - 1) q |
        x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1})
    {G : Set (PL.E N)}
    (hG : K ∪ (⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
        ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) ⊆ G)
    (hEc : IsClosed (X ∪ ND.g₁ '' G))
    {h : M ≃ₜ M} (hsupp : PL.CSupp h (Set.univ : Set M)) (heng : X ∪ ND.g₁ '' G ⊆ h '' V)
    (hbase : ∀ z ∈ F,
      ψ.toFun (Φ.symm ((0 : PL.E (n - q - 1)), z, γ₀ z)) ∈ X ∪ ND.g₁ '' G)
    {J : Set (PL.E q)} (hJF : J ⊆ F) (hJd : PL.DomDim J ((q : ℤ) - 2)) (hJc : IsClosed J)
    (hoverJ : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      ψ.toFun (Φ.symm ((0 : PL.E (n - q - 1)), z, t)) ∈ h '' V)
    (hAs : ∀ x ∈ PL.simp (ND.ord[i]), ψ.toFun (A x) ∈ X ∪ ND.g₁ '' G →
      ∃ z ∈ F, ∃ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        Φ (A x) = ((0 : PL.E (n - q - 1)), z, t) ∧ (t = γ₀ z ∨ z ∈ J)) :
    ∃ h' : M ≃ₜ M, PL.CSupp h' (Set.univ : Set M) ∧
      X ∪ ND.g₁ '' (G ∪ ⋃ w ∈ ND.ord[i], PL.simp (ND.ord[i].erase w)) ⊆ h' '' V :=
  pushShellG ND T hV hi hAeq hAopen hFc hFconv hγ₀c hγ₁c hle hfr hprism
    hEc hsupp heng hbase hJF hJd hJc hoverJ hAs

end Work.Engulf.E4S
