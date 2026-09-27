import Mathlib
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.E4Aux.affineIndependent_image_of_injOn

namespace Work.Engulf.E4alt

/-- **The frozen-independence fact the `E4alt` shelling step needs, derived from the extra
structural hypothesis `hfzv`.**  For a core face `σ` of `Γ₁` (one whose `f`-image lies in the
`5/8`-cube) whose simplex lies in `simp (τ₀ ∪ τ₁)`, the values `ND.vv` on the *unperturbed* vertices
`σ ∩ ND.Fzv` are affinely independent *provided* the convex hull of those vertices lies in `L`
(`hfzv`; see `NormData.Fzv_core`, which gives only that the frozen vertices themselves are in `L`).

Proof sketch (do not deviate): `ND.wit σ (hord-core) ` gives an affine `A` with `A v = ND.vv v` on
`σ` and `ND.g₁ = ψ ∘ A` on `simp σ`.  For `x y ∈ PL.simp (σ ∩ ND.Fzv)`, `A x = A y` implies
`ψ (A x) = ψ (A y)`, i.e. `ND.g₁ x = ND.g₁ y`; `hfzv` puts `x, y ∈ L`, so `ND.g₁frz` gives
`f x = f y`, and `H7.clean` (with `hσΔ` for the first argument's membership in `simp (τ₀ ∪ τ₁)`,
and `x, y ∈ simp (τ₀ ∪ τ₁) ∩ L ⊆ (K ∪ simp (τ₀ ∪ τ₁)) ∩ L` for the second) gives `x = y`.  Hence `A`
is injective on `simp (σ ∩ ND.Fzv)`; conclude with `Work.Engulf.E4Aux.affineIndependent_image_of_injOn`
applied to `ND.Γ₁.indep hσ` (restricted to the sub-finset `σ ∩ ND.Fzv`), rewriting `A v = ND.vv v`.
`ND.indep` must NOT be used (it consumes exactly this statement as a hypothesis). -/
theorem hndOfFzvHull {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (hfzv : ∀ s ∈ ND.Γ₁.faces, f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) →
      PL.simp (s ∩ ND.Fzv) ⊆ L)
    {σ : Finset (PL.E N)} (hσ : σ ∈ ND.Γ₁.faces)
    (hσΔ : PL.simp σ ⊆ PL.simp (τ₀ ∪ τ₁))
    (hcore : f '' PL.simp σ ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ)) :
    AffineIndependent ℝ (fun v : ↥(σ ∩ ND.Fzv) => ND.vv v) := by
  classical
  obtain ⟨A, hAeq, hArest⟩ := ND.wit σ hσ hcore
  have hAval : ∀ v ∈ σ, A v = ND.vv v := fun v hv => (hArest v (subset_simp hv)).2 v hv
  have hfzvσ : PL.simp (σ ∩ ND.Fzv) ⊆ L := hfzv σ hσ hcore
  have hσsub : σ ∩ ND.Fzv ⊆ σ := Finset.inter_subset_left
  have hinj : Set.InjOn A (PL.simp (σ ∩ ND.Fzv)) := by
    intro x hx y hy hxy
    have hxs : x ∈ PL.simp σ := simp_mono hσsub hx
    have hys : y ∈ PL.simp σ := simp_mono hσsub hy
    have hxL : x ∈ L := hfzvσ hx
    have hyL : y ∈ L := hfzvσ hy
    have hgx : ND.g₁ x = f x := ND.g₁frz hxL
    have hgy : ND.g₁ y = f y := ND.g₁frz hyL
    have hψ : ψ.toFun (A x) = ψ.toFun (A y) := by rw [hxy]
    have h1 : ND.g₁ x = ND.g₁ y := by rw [hAeq hxs, hAeq hys]; exact hψ
    have hfx : f x = f y := by rw [← hgx, ← hgy]; exact h1
    have hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁) := hσΔ hxs
    have hyΔ : y ∈ PL.simp (τ₀ ∪ τ₁) := hσΔ hys
    exact H7.clean x ⟨hxΔ, hxL⟩ y ⟨Or.inr hyΔ, hyL⟩ hfx
  have hind : AffineIndependent ℝ (fun v : ↥(σ ∩ ND.Fzv) => (v : PL.E N)) :=
    (ND.Γ₁.indep hσ).mono hσsub
  have hAA := Work.Engulf.E4Aux.affineIndependent_image_of_injOn hind hinj
  have hfun : (fun v : ↥(σ ∩ ND.Fzv) => A v) = (fun v : ↥(σ ∩ ND.Fzv) => ND.vv v) := by
    funext v
    exact hAval v.1 (Finset.mem_inter.mp v.2).1
  simpa only [hfun] using hAA

end Work.Engulf.E4alt
