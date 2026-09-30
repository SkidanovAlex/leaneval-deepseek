import Mathlib
import Submission.Work.SSS.serreE1PieceDefs
import Submission.Work.SSS.collapseDefs
import Submission.Work.SSS.anodyneIota0
import Submission.Work.SSS.collapseMapEndpoints
import Submission.Work.SSS.collapseMapHorn
import Submission.Work.SSS.homotopyMem
import Submission.Work.SSS.hornSimpConst
import Submission.Work.SSS.singularFibration

namespace Work.SSS

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
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) {s : ℕ} (hs : 1 ≤ s)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    ∃ (g : Work.SSS.pullAlong (Work.SSS.sSingP p) σ ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
      (H : CategoryTheory.SimplicialObject.Homotopy (𝟙 _) g),
      (∀ (n : ℕ)
        (x : (Work.SSS.pullAlong (Work.SSS.sSingP p) σ).obj (Opposite.op (SimplexCategory.mk n))),
        g.app _ x ∈ (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).obj _) ∧
      (∀ (n : ℕ) (i : Fin (n+1))
        (x : (Work.SSS.pullAlong (Work.SSS.sSingP p) σ).obj (Opposite.op (SimplexCategory.mk n))),
        x ∈ (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).obj _ →
        H.h i x ∈ (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).obj _) := by
  classical
  -- ===== the imported / delegated inputs =====
  have hSing : HomotopicalAlgebra.Fibration (Work.SSS.sSingP p) :=
    Work.SSS.singularFibration p hfib
  have hEndpoints := Work.SSS.collapseMapEndpoints s
  have hHorn := Work.SSS.collapseMapHorn s
  have hConst := Work.SSS.hornSimpConst s hs
  have hMem := @Work.SSS.homotopyMem
  -- ===== the pullback and its projections =====
  set X : SSet.{0} := pullback σ (Work.SSS.sSingP p) with hX
  set pr : X ⟶ (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) :=
    pullback.fst σ (Work.SSS.sSingP p) with hpr
  set q : X ⟶ Work.SSS.sSing E := pullback.snd σ (Work.SSS.sSingP p) with hq
  have hcond : pr ≫ σ = q ≫ Work.SSS.sSingP p := pullback.condition
  set α : X ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶
      (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) :=
    MonoidalCategoryStruct.whiskerRight pr
      (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ≫ Work.SSS.collapseMap s with hα
  have hαι₀ : SSet.ι₀ ≫ α = pr := by
    rw [hα, ← Category.assoc, SSet.ι₀_comp, Category.assoc, hEndpoints.1, Category.comp_id]
  -- ===== the resulting lifting problem =====
  have hsq : CommSq q (SSet.ι₀ (X := X)) (Work.SSS.sSingP p) (α ≫ σ) := by
    refine ⟨?_⟩
    rw [hcond.symm, ← hαι₀, Category.assoc]
  haveI hlift : HasLiftingProperty (SSet.ι₀ (X := X)) (Work.SSS.sSingP p) :=
    Work.SSS.anodyneIota0 (Work.SSS.sSingP p) hSing.mem
  set β : X ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶
      Work.SSS.sSing E := hsq.lift with hβ
  have hβι₀ : SSet.ι₀ ≫ β = q := hsq.fac_left
  have hβσ : β ≫ Work.SSS.sSingP p = α ≫ σ := hsq.fac_right
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
        ∈ (Work.SSS.hornSimp s).obj m := by
    intro m a
    have h := hConst
    rw [Subfunctor.le_def] at h
    have h2 : a ∈ ((Work.SSS.hornSimp s).preimage
        (SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}))
          ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s)))).obj m :=
      h m (trivial : a ∈ (⊤ : ((SSet.stdSimplex.obj (SimplexCategory.mk s) :
        SSet.{0})).Subcomplex).obj m)
    simpa only [SSet.Subcomplex.preimage_obj, Set.mem_preimage] using h2
  have hHornApp : ∀ (m : SimplexCategoryᵒᵖ)
      (z : (((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
        (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}))).obj m),
      z.1 ∈ (Work.SSS.hornSimp s).obj m →
      ((Work.SSS.collapseMap s).app m) z ∈ (Work.SSS.hornSimp s).obj m := by
    intro m z hz
    have h := hHorn
    rw [Subfunctor.le_def] at h
    have hz' : z ∈ ((Work.SSS.hornSimp s).prod
        (⊤ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}).Subcomplex)).obj m := by
      rw [SSet.Subcomplex.prod_obj]
      exact ⟨hz, trivial⟩
    have h2 : z ∈ ((Work.SSS.hornSimp s).preimage (Work.SSS.collapseMap s)).obj m := h m hz'
    simpa only [SSet.Subcomplex.preimage_obj, Set.mem_preimage] using h2
  -- the graph of `θ` over the horn lies in the horn
  have hA : (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).prod
        (⊤ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}).Subcomplex)
      ≤ (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).preimage θ := by
    intro m z hz
    simp only [SSet.Subcomplex.prod_obj] at hz
    obtain ⟨hz1, -⟩ := hz
    have hz1' : pr.app m z.1 ∈ (Work.SSS.hornSimp s).obj m := hz1
    show ((θ ≫ pr).app m) z ∈ (Work.SSS.hornSimp s).obj m
    rw [hθπ, hα, SSet.comp_app]
    change ((Work.SSS.collapseMap s).app m) ⟨pr.app m z.1, z.2⟩ ∈ (Work.SSS.hornSimp s).obj m
    exact hHornApp m ⟨pr.app m z.1, z.2⟩ hz1'
  refine ⟨g, Hs.toSimplicialObjectHomotopy, ?_, ?_⟩
  · intro n x
    show ((g ≫ pr).app (Opposite.op (SimplexCategory.mk n))) x
      ∈ (Work.SSS.hornSimp s).obj (Opposite.op (SimplexCategory.mk n))
    rw [hg, Category.assoc, hθπ, hα, ← Category.assoc, SSet.ι₁_comp, Category.assoc,
      hEndpoints.2, SSet.comp_app]
    change ((SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}))
        ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))).app
          (Opposite.op (SimplexCategory.mk n)))
        (pr.app (Opposite.op (SimplexCategory.mk n)) x)
      ∈ (Work.SSS.hornSimp s).obj (Opposite.op (SimplexCategory.mk n))
    exact hConstApp _ _
  · intro n i x hx
    exact hMem (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ) Hs hA n i x hx

end

end Work.SSS
