import Mathlib
import Submission.Work.SSSR.serreE1PieceDefs
import Submission.Work.SSSR.collapseDefs
import Submission.Work.SSSR.anodyneIota0
import Submission.Work.SSSR.collapseMapEndpoints
import Submission.Work.SSSR.collapseMapHorn
import Submission.Work.SSSR.homotopyMem
import Submission.Work.SSSR.hornSimpConst
import Submission.Work.SSSR.singularFibration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial
open scoped SSet.modelCategoryQuillen
noncomputable section

/-- The hom set out of `(⊥ : X.Subcomplex) ⊗ Δ[1]` is a subsingleton. -/
private theorem subsingleton_bot_prod {X : SSet.{0}} :
    Subsingleton (((⊥ : X.Subcomplex) : SSet.{0}) ⊗ (Δ[1] : SSet.{0}) ⟶ X) :=
  ⟨fun a b => by
    apply NatTrans.ext
    funext m
    ext z
    exact ((Set.notMem_empty z.1.1) z.1.2).elim⟩


/-- **The prism contraction of the pair `(T_σ, Λ)`.**  For a Serre fibration `p : E → B`, `1 ≤ s`, and a simplex `σ : Δ[s] ⟶ Sing B`, the pullback `T_σ = Δ[s] ×_{Sing B} Sing E` admits a combinatorial simplicial homotopy from the identity to a map `g` whose image lies in the horn subcomplex `Λ = pieceHorn (sSingP p) σ` (the part of `T_σ` lying over `⋃_{i<s} d_iΔ[s]`), and this homotopy preserves `Λ` levelwise.  This is the lifted straight-line contraction of `Δ[s]` to its last vertex `v_s`; `v_s` lies in the horn (for `s ≥ 1`), so the top of the contraction lands in `Λ`. -/
theorem pieceContraction {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) {s : ℕ} (hs : 1 ≤ s)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ∃ (g : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (H : CategoryTheory.SimplicialObject.Homotopy (𝟙 _) g),
      (∀ (n : ℕ)
        (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).obj (Opposite.op (SimplexCategory.mk n))),
        g.app _ x ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj _) ∧
      (∀ (n : ℕ) (i : Fin (n+1))
        (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).obj (Opposite.op (SimplexCategory.mk n))),
        x ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj _ →
        H.h i x ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj _) := by
  classical
  -- ===== the imported / delegated inputs =====
  have hSing : HomotopicalAlgebra.Fibration (Work.SSSR.sSingP p) :=
    Work.SSSR.singularFibration p hfib
  have hEndpoints := Work.SSSR.collapseMapEndpoints s
  have hHorn := Work.SSSR.collapseMapHorn s
  have hConst := Work.SSSR.hornSimpConst s hs
  have hMem := @Work.SSSR.homotopyMem
  -- ===== the pullback and its projections =====
  set X : SSet.{0} := pullback σ (Work.SSSR.sSingP p) with hX
  set pr : X ⟶ (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) :=
    pullback.fst σ (Work.SSSR.sSingP p) with hpr
  set q : X ⟶ Work.SSSR.sSing E := pullback.snd σ (Work.SSSR.sSingP p) with hq
  have hcond : pr ≫ σ = q ≫ Work.SSSR.sSingP p := pullback.condition
  set α : X ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶
      (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) :=
    MonoidalCategoryStruct.whiskerRight pr
      (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ≫ Work.SSSR.collapseMap s with hα
  have hαι₀ : SSet.ι₀ ≫ α = pr := by
    rw [hα, ← Category.assoc, SSet.ι₀_comp, Category.assoc, hEndpoints.1, Category.comp_id]
  -- ===== the resulting lifting problem =====
  have hsq : CommSq q (SSet.ι₀ (X := X)) (Work.SSSR.sSingP p) (α ≫ σ) := by
    refine ⟨?_⟩
    rw [hcond.symm, ← hαι₀, Category.assoc]
  haveI hlift : HasLiftingProperty (SSet.ι₀ (X := X)) (Work.SSSR.sSingP p) :=
    Work.SSSR.anodyneIota0 (Work.SSSR.sSingP p) hSing.mem
  set β : X ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶
      Work.SSSR.sSing E := hsq.lift with hβ
  have hβι₀ : SSet.ι₀ ≫ β = q := hsq.fac_left
  have hβσ : β ≫ Work.SSSR.sSingP p = α ≫ σ := hsq.fac_right
  -- ===== the homotopy map on the pullback =====
  set θ : X ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ X :=
    pullback.lift α β (by rw [hβσ]) with hθ
  have hθπ : θ ≫ pr = α := by
    rw [hθ, hpr]; exact pullback.lift_fst α β _
  have hθq : θ ≫ q = β := by
    rw [hθ, hq]; exact pullback.lift_snd α β _
  have hθι₀ : SSet.ι₀ ≫ θ = 𝟙 X := by
    rw [hθ]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hαι₀, hpr, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, hβι₀, hq, Category.id_comp]
  -- ===== assemble =====
  set g : X ⟶ X := SSet.ι₁ ≫ θ with hg
  haveI hsub : Subsingleton (((⊥ : X.Subcomplex) : SSet.{0}) ⊗
      (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ X) :=
    subsingleton_bot_prod
  set Hs : SSet.Homotopy (𝟙 X) g := { h := θ, h₀ := hθι₀, h₁ := rfl } with hHs
  -- pointwise forms of the two horn facts
  have hConstApp : ∀ (m : SimplexCategoryᵒᵖ)
      (a : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).obj m),
      ((SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}))
        ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))).app m) a
        ∈ (Work.SSSR.hornSimp s).obj m := by
    intro m a
    have h := hConst
    rw [Subfunctor.le_def] at h
    have h2 : a ∈ ((Work.SSSR.hornSimp s).preimage
        (SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}))
          ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s)))).obj m :=
      h m (trivial : a ∈ (⊤ : ((SSet.stdSimplex.obj (SimplexCategory.mk s) :
        SSet.{0})).Subcomplex).obj m)
    simpa only [SSet.Subcomplex.preimage_obj, Set.mem_preimage] using h2
  have hHornApp : ∀ (m : SimplexCategoryᵒᵖ)
      (z : (((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
        (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}))).obj m),
      z.1 ∈ (Work.SSSR.hornSimp s).obj m →
      ((Work.SSSR.collapseMap s).app m) z ∈ (Work.SSSR.hornSimp s).obj m := by
    intro m z hz
    have h := hHorn
    rw [Subfunctor.le_def] at h
    have hz' : z ∈ ((Work.SSSR.hornSimp s).prod
        (⊤ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}).Subcomplex)).obj m := by
      rw [SSet.Subcomplex.prod_obj]
      exact ⟨hz, trivial⟩
    have h2 : z ∈ ((Work.SSSR.hornSimp s).preimage (Work.SSSR.collapseMap s)).obj m := h m hz'
    simpa only [SSet.Subcomplex.preimage_obj, Set.mem_preimage] using h2
  -- the graph of `θ` over the horn lies in the horn
  have hA : (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).prod
        (⊤ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}).Subcomplex)
      ≤ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).preimage θ := by
    intro m z hz
    simp only [SSet.Subcomplex.prod_obj] at hz
    obtain ⟨hz1, -⟩ := hz
    have hz1' : pr.app m z.1 ∈ (Work.SSSR.hornSimp s).obj m := hz1
    show ((θ ≫ pr).app m) z ∈ (Work.SSSR.hornSimp s).obj m
    rw [hθπ, hα, SSet.comp_app]
    change ((Work.SSSR.collapseMap s).app m) ⟨pr.app m z.1, z.2⟩ ∈ (Work.SSSR.hornSimp s).obj m
    exact hHornApp m ⟨pr.app m z.1, z.2⟩ hz1'
  refine ⟨g, Hs.toSimplicialObjectHomotopy, ?_, ?_⟩
  · intro n x
    show ((g ≫ pr).app (Opposite.op (SimplexCategory.mk n))) x
      ∈ (Work.SSSR.hornSimp s).obj (Opposite.op (SimplexCategory.mk n))
    rw [hg, Category.assoc, hθπ, hα, ← Category.assoc, SSet.ι₁_comp, Category.assoc,
      hEndpoints.2, SSet.comp_app]
    change ((SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}))
        ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))).app
          (Opposite.op (SimplexCategory.mk n)))
        (pr.app (Opposite.op (SimplexCategory.mk n)) x)
      ∈ (Work.SSSR.hornSimp s).obj (Opposite.op (SimplexCategory.mk n))
    exact hConstApp _ _
  · intro n i x hx
    exact hMem (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ) Hs hA n i x hx

end

end Work.SSSR
