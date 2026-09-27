import Mathlib
import Submission.Work.Mostow.VolDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- `hjac` is invariant under the `Γ`-action when `F` is equivariant. Use `VolDefs.hjacComp`
(multiplicativity of `hjac` under composition) on `F ∘ (γ • ·)` and on `((f γ) • ·) ∘ F`, which are
equal as functions by `hFE`, together with the `HypIsometryProp` clauses `hjac (fun w => g • w) u = 1`
and `ContDiff ℝ 1 (fun w => g • w)`. -/
theorem hjacEquivariant (n : ℕ) (hI : HypIsometryProp n) {Γ Λ : Subgroup (PO n 1)} (f : Γ →* Λ)
    {F : E n → E n} (hF : ContDiff ℝ 1 F)
    (hFE : ∀ (γ : Γ) (u : E n), F (γ • u) = (f γ : PO n 1) • F u) :
    ∀ (γ : Γ) (u : E n), hjac F (γ • u) = hjac F u := by
  rcases hI with ⟨_,_,_,_,_,_,_,_, hsmulCD, _, hjacOne, _, _⟩
  intro γ u
  -- differentiability of the three maps involved
  have hFdiff : DifferentiableAt ℝ F (γ • u) := (hF.differentiable (by norm_num)).differentiableAt
  have hFdiffu : DifferentiableAt ℝ F u := (hF.differentiable (by norm_num)).differentiableAt
  have hGdiff : DifferentiableAt ℝ (fun w : E n => γ • w) u :=
    ((hsmulCD (γ : PO n 1)).differentiable (by norm_num)).differentiableAt
  have hHdiff : DifferentiableAt ℝ (fun w : E n => (f γ : PO n 1) • w) (F u) :=
    ((hsmulCD ((f γ : Λ) : PO n 1)).differentiable (by norm_num)).differentiableAt
  -- the two composite maps agree
  have hfun : (fun w : E n => (f γ : PO n 1) • w) ∘ F = F ∘ (fun w : E n => γ • w) := by
    funext w
    exact (hFE γ w).symm
  -- `hjac` of a hyperbolic isometry is identically one
  have hγ1 : hjac (fun w : E n => γ • w) u = 1 := hjacOne (γ : PO n 1) u
  have hH1 : hjac (fun w : E n => (f γ : PO n 1) • w) (F u) = 1 :=
    hjacOne ((f γ : Λ) : PO n 1) (F u)
  -- chain rule on `F ∘ (γ • ·)`
  have e1 : hjac (F ∘ (fun w : E n => γ • w)) u = hjac F (γ • u) := by
    have h := hjacComp (n := n) (F := F) (G := fun w : E n => γ • w) (u := u) hFdiff hGdiff
    rw [hγ1, mul_one] at h
    exact h
  -- chain rule on `((f γ) • ·) ∘ F`
  have e2 : hjac (F ∘ (fun w : E n => γ • w)) u = hjac F u := by
    have h := hjacComp (n := n) (F := fun w : E n => (f γ : PO n 1) • w) (G := F) (u := u)
      hHdiff hFdiffu
    rw [hfun] at h
    rw [hH1, one_mul] at h
    exact h
  rw [← e1, e2]

end Work.Mostow
