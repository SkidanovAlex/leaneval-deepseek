import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Api

namespace Work.Engulf.E4alt

/-- **`hcol` for `NormData.pair`, derived from `L7Hyp.clean`.**

Let `σ₁`, `σ₂` be core faces of `Γ₁` (`f '' simp σᵢ ⊆ ψ '' closedCube (5/8)`), with
`simp σ₁ ⊆ simp (τ₀ ∪ τ₁)` and `simp σ₂ ⊆ K ∪ simp (τ₀ ∪ τ₁)`, and let `A₁`, `A₂` be the affine
witnesses of `ND.g₁` on them.  Then the images of the frozen hulls `simp (σᵢ ∩ ND.Fzv)` meet only
inside the image of the common frozen hull `simp (σ₁ ∩ σ₂ ∩ ND.Fzv)`.

The proof is the one of `E4Aux.image_simp_inter_subset`, with two twists forced by the stated
hypotheses: the `EqOn` facts are only available on the *frozen hulls* (`ND.wit`/`hwit` give `g₁`,
and `ND.g₁frz` + `ND.Fzv_hull` turn `g₁` into `f` on `L`), and the injectivity of `f` is
`L7Hyp.clean` restricted to the frozen hulls (which lie in `L`, and in `simp Δ` resp.
`K ∪ simp Δ`).  Concretely: if `z = A₁ x = A₂ y` with `x`, `y` frozen, then `f x = f y`, whence
`x = y`; now `x ∈ simp σ₁ ∩ simp σ₂ = simp (σ₁ ∩ σ₂)`, and affine independence of the vertices of
`σ₁` splits `simp (σ₁ ∩ ND.Fzv) ∩ simp (σ₁ ∩ σ₂)` as the hull of the intersection. -/
theorem hcolOfClean {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    {σ₁ σ₂ : Finset (PL.E N)} (hσ₁ : σ₁ ∈ ND.Γ₁.faces) (hσ₂ : σ₂ ∈ ND.Γ₁.faces)
    (hcore₁ : f '' PL.simp σ₁ ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    (hcore₂ : f '' PL.simp σ₂ ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    (hΔ₁ : PL.simp σ₁ ⊆ PL.simp (τ₀ ∪ τ₁))
    (h₂K : PL.simp σ₂ ⊆ K ∪ PL.simp (τ₀ ∪ τ₁))
    (A₁ A₂ : PL.E N →ᵃ[ℝ] PL.E n)
    (hwit₁ : ∀ x ∈ PL.simp σ₁, ND.g₁ x = ψ.toFun (A₁ x))
    (hwit₂ : ∀ x ∈ PL.simp σ₂, ND.g₁ x = ψ.toFun (A₂ x)) :
    ∀ z ∈ A₁ '' PL.simp (σ₁ ∩ ND.Fzv) ∩ A₂ '' PL.simp (σ₂ ∩ ND.Fzv),
      (∃ v ∈ σ₁ ∩ σ₂, v ∉ ND.Fzv) → z ∈ A₁ '' PL.simp (σ₁ ∩ σ₂ ∩ ND.Fzv) := by
  intro z hz _
  obtain ⟨⟨x, hx1, hxA₁⟩, ⟨y, hy1, hyA₂⟩⟩ := hz
  -- `x` lies in the frozen hull of `σ₁`, `y` in that of `σ₂`, and both map to `z`
  have hxσ₁ : x ∈ PL.simp σ₁ := Work.Engulf.simp_mono Finset.inter_subset_left hx1
  have hyσ₂ : y ∈ PL.simp σ₂ := Work.Engulf.simp_mono Finset.inter_subset_left hy1
  -- the frozen hulls lie in `L` (`NormData.Fzv_hull`), where `g₁` agrees with `f`
  have hxL : x ∈ L := ND.Fzv_hull σ₁ hσ₁ hcore₁ hx1
  have hyL : y ∈ L := ND.Fzv_hull σ₂ hσ₂ hcore₂ hy1
  -- and in `simp (τ₀ ∪ τ₁)` resp. `K ∪ simp (τ₀ ∪ τ₁)`, so `clean` applies
  have hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁) := hΔ₁ hxσ₁
  have hyΔ : y ∈ K ∪ PL.simp (τ₀ ∪ τ₁) := h₂K hyσ₂
  have hfx : f x = ψ.toFun (A₁ x) := by rw [← ND.g₁frz hxL, hwit₁ x hxσ₁]
  have hfy : f y = ψ.toFun (A₂ y) := by rw [← ND.g₁frz hyL, hwit₂ y hyσ₂]
  -- equal images in the chart give equal `f`-images, and `clean` makes the domain points agree
  have hxy : x = y :=
    H7.clean x ⟨hxΔ, hxL⟩ y ⟨hyΔ, hyL⟩ (by rw [hfx, hfy, hxA₁, hyA₂])
  have hxσ₂ : x ∈ PL.simp σ₂ := hxy ▸ hyσ₂
  have hx_σlm : x ∈ PL.simp (σ₁ ∩ σ₂) := by
    rw [← Work.Engulf.simp_inter hσ₁ hσ₂]; exact ⟨hxσ₁, hxσ₂⟩
  -- affine independence of the vertices of `σ₁` splits the two hulls
  have hkey : PL.simp (σ₁ ∩ ND.Fzv) ∩ PL.simp (σ₁ ∩ σ₂)
      = PL.simp ((σ₁ ∩ ND.Fzv) ∩ (σ₁ ∩ σ₂)) := by
    have hAI : AffineIndependent ℝ ((↑) : σ₁ → PL.E N) := ND.Γ₁.indep hσ₁
    simpa only [PL.simp, Finset.coe_inter] using (hAI.convexHull_inter
      (Finset.inter_subset_left : σ₁ ∩ ND.Fzv ⊆ σ₁)
      (Finset.inter_subset_left : σ₁ ∩ σ₂ ⊆ σ₁)).symm
  have hx_goal : x ∈ PL.simp (σ₁ ∩ σ₂ ∩ ND.Fzv) := by
    have hmem : x ∈ PL.simp ((σ₁ ∩ ND.Fzv) ∩ (σ₁ ∩ σ₂)) := by
      rw [← hkey]; exact ⟨hx1, hx_σlm⟩
    have hfin : (σ₁ ∩ ND.Fzv) ∩ (σ₁ ∩ σ₂) = σ₁ ∩ σ₂ ∩ ND.Fzv := by
      ext a; simp only [Finset.mem_inter]; tauto
    rwa [hfin] at hmem
  exact ⟨x, hx_goal, hxA₁⟩

end Work.Engulf.E4alt
