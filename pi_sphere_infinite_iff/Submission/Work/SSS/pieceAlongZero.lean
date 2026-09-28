import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.serreE1PieceDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.SSS.toSSetObjEquiv_const_apply
import Submission.Work.SSS.sSingP_fibreIncl_comp
import Submission.Work.SSS.pieceAlongZeroCoker

/-!
# The base case `s = 0` of the σ-piece computation

The target statement `Work.SSS.pieceAlongZero` is proved here.  The mathematical content is the
identification of the *simplicial* pullback `T_σ = Δ[0] ×_{Sing B} Sing E` along a vertex
`σ : Δ[0] ⟶ Sing B` with the singular simplicial set of the fibre `F = p⁻¹(σ(v₀))` of `p` over the
point underlying `σ` (`Work.SSS.sigmaVert σ`).

The map `φ : Sing F ⟶ T_σ` is induced by the universal property of the pullback (the inclusion of
the fibre is a map over the constant vertex, `Work.SSS.sSingP_fibreIncl_comp`), and it is an
isomorphism: on `n`-simplices the inverse sends a simplex `τ` of `Sing E` satisfying
`Sing p ∘ τ = const (σ(v₀))` to the singular simplex of the fibre given by the map
`z ↦ ⟨τ z, _⟩`.  Here `σ` is the constant simplex at `sigmaVert σ`
(`Work.SSS.sigma_eq_const`), so that `Sing p ∘ τ` really is the constant `n`-simplex at
`sigmaVert σ` (`Work.SSS.toSSetObjEquiv_const_apply`), which is what makes `τ` land in the fibre;
surjectivity is exactly this recombination, and injectivity uses the description of the components
of `φ` and the fact that the inclusion of the fibre is injective.

Together with `Work.SSS.pieceAlongZeroCoker` (the boundary `∂T_σ` is empty for `s = 0`, so the
σ-piece is the whole complex `C(T_σ)`) and the definitional identity
`sCC (sSing F) = singularChains ℤ (TopCat.of F)`, this identifies the σ-piece with the singular
chain complex of the fibre.
-/

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {B : Type} [TopologicalSpace B]

/-- The `n`-simplex of `SSet.const σ₀` at the identity simplex is `SSet.yonedaEquiv (SSet.const σ₀)`. -/
lemma const_app_yoneda (σ₀ : (sSing B).obj (op (SimplexCategory.mk 0))) (n : SimplexCategory) :
    (SSet.const σ₀).app (op n) (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) =
      SSet.yonedaEquiv (SSet.const σ₀) := by
  conv_lhs => rw [← Equiv.symm_apply_apply (SSet.yonedaEquiv (n := n)) (SSet.const σ₀)]
  rw [SSet.yonedaEquiv_symm_app]
  have hid : SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) = 𝟙 n := by
    rw [← SSet.yonedaEquiv_symm_stdSimplex_id]
    exact Equiv.apply_symm_apply _ _
  rw [hid]
  simp

lemma sigma_eq_const
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B) :
    σ = SSet.const (TopCat.toSSetObj₀Equiv.symm (sigmaVert σ)) := by
  have h : σ = SSet.const (SSet.yonedaEquiv σ) := by
    conv_lhs => rw [← SSet.yonedaEquiv.symm_apply_apply σ]
    rw [SSet.yonedaEquiv_symm_zero]
  have h2 : SSet.yonedaEquiv σ = TopCat.toSSetObj₀Equiv.symm (sigmaVert σ) := by
    rw [show sigmaVert σ = TopCat.toSSetObj₀Equiv (SSet.yonedaEquiv σ) from by
      rw [sigmaVert, TopCat.toSSetObj₀Equiv_eq_T _ ⟨Pi.single (0 : Fin (0+1)) 1,
        single_mem_stdSimplex ℝ (0 : Fin (0+1))⟩], Equiv.symm_apply_apply]
  conv_lhs => rw [h]
  exact congrArg SSet.const h2

variable {E : Type} [TopologicalSpace E]
variable (p : C(E, B)) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)

/-- the constant map `sSing (fibre p b) ⟶ Δ[0]` -/
def phiAlongFst :
    sSing (Work.StemsB.fibre p (sigmaVert σ)) ⟶
      (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) :=
  SSet.const (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})))

def phiAlong : sSing (Work.StemsB.fibre p (sigmaVert σ)) ⟶ pullback σ (sSingP p) :=
  pullback.lift (phiAlongFst p σ) (sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))) (by
    have h1 : phiAlongFst p σ ≫ σ =
        phiAlongFst p σ ≫ SSet.const (TopCat.toSSetObj₀Equiv.symm (sigmaVert σ)) :=
      congrArg (fun s => phiAlongFst p σ ≫ s) (sigma_eq_const σ)
    rw [h1, SSet.comp_const]
    exact (sSingP_fibreIncl_comp p (sigmaVert σ)).symm)

lemma phiAlong_fst : phiAlong p σ ≫ pullback.fst σ (sSingP p) = phiAlongFst p σ :=
  pullback.lift_fst _ _ _

lemma phiAlong_snd : phiAlong p σ ≫ pullback.snd σ (sSingP p) =
    sSingP (Work.StemsB.fibreIncl p (sigmaVert σ)) :=
  pullback.lift_snd _ _ _

lemma phiAlong_app_surj (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((phiAlong p σ).app n) := by
  intro z
  obtain ⟨z', hz'⟩ := SSet.yonedaEquiv.surjective z
  let u : SSet.stdSimplex.obj n.unop ⟶ sSing E := z' ≫ pullback.snd σ (sSingP p)
  let y : (sSing E).obj n := SSet.yonedaEquiv u
  have hup : u ≫ sSingP p = SSet.const (TopCat.toSSetObj₀Equiv.symm (sigmaVert σ)) := by
    dsimp only [u]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    have h1 : (z' ≫ pullback.fst σ (sSingP p)) ≫ σ =
        (z' ≫ pullback.fst σ (sSingP p)) ≫
          SSet.const (TopCat.toSSetObj₀Equiv.symm (sigmaVert σ)) :=
      congrArg (fun s => (z' ≫ pullback.fst σ (sSingP p)) ≫ s) (sigma_eq_const σ)
    rw [h1, SSet.comp_const]
  have hu_app : u.app n (SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)) = y := by
    dsimp only [y]
    conv_lhs => rw [show u = SSet.yonedaEquiv.symm (SSet.yonedaEquiv u) from
      (Equiv.symm_apply_apply _ _).symm]
    rw [SSet.yonedaEquiv_symm_app]
    simp
  have hkey : (sSingP p).app n y =
      (SSet.const (TopCat.toSSetObj₀Equiv.symm (sigmaVert σ))).app n
        (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop))) := by
    have hcomp : SSet.yonedaEquiv (u ≫ sSingP p) = (sSingP p).app n y := by
      have h := SSet.yonedaEquiv_symm_comp (X := sSing E) (SSet.yonedaEquiv u) (sSingP p)
      rw [Equiv.symm_apply_apply] at h
      rw [h, Equiv.apply_symm_apply]
    have h := congrArg SSet.yonedaEquiv hup
    rw [hcomp, ← const_app_yoneda (TopCat.toSSetObj₀Equiv.symm (sigmaVert σ)) n.unop] at h
    exact h
  have hconst : p.comp (TopCat.toSSetObjEquivT (TopCat.of E) n y) =
      ContinuousMap.const (stdSimplex ℝ (Fin (n.unop.len+1))) (sigmaVert σ) := by
    have h := congrArg (TopCat.toSSetObjEquivT (TopCat.of B) n) hkey
    rw [show TopCat.toSSetObjEquivT (TopCat.of B) n ((sSingP p).app n y) =
        p.comp (TopCat.toSSetObjEquivT (TopCat.of E) n y) from rfl,
      toSSetObjEquiv_const_apply (TopCat.toSSetObj₀Equiv.symm (sigmaVert σ)) n.unop.len
        (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop)))] at h
    rw [Equiv.apply_symm_apply] at h
    exact h
  have hpt : ∀ z : stdSimplex ℝ (Fin (n.unop.len+1)),
      p (TopCat.toSSetObjEquivT (TopCat.of E) n y z) = sigmaVert σ := fun z => by
    have hz := congrArg (fun (f : C(stdSimplex ℝ (Fin (n.unop.len+1)), B)) => f z) hconst
    simpa only [ContinuousMap.comp_apply, ContinuousMap.const_apply] using hz
  let fy : C(stdSimplex ℝ (Fin (n.unop.len+1)), Work.StemsB.fibre p (sigmaVert σ)) :=
    { toFun := fun z => ⟨TopCat.toSSetObjEquivT (TopCat.of E) n y z, hpt z⟩
      continuous_toFun := (TopCat.toSSetObjEquivT (TopCat.of E) n y).continuous.subtype_mk hpt }
  let w : (sSing (Work.StemsB.fibre p (sigmaVert σ))).obj n :=
    (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n).symm fy
  refine ⟨w, ?_⟩
  have hw : TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n w = fy :=
    Equiv.apply_symm_apply _ _
  have hfi : (sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n w = y := by
    apply (TopCat.toSSetObjEquivT (TopCat.of E) n).injective
    rw [show TopCat.toSSetObjEquivT (TopCat.of E) n
          ((sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n w) =
        (Work.StemsB.fibreIncl p (sigmaVert σ)).comp
          (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n w) from rfl,
      hw]
    ext z
    rfl
  have hgoal : SSet.yonedaEquiv.symm w ≫ phiAlong p σ = z' := by
    apply pullback.hom_ext
    · calc (SSet.yonedaEquiv.symm w ≫ phiAlong p σ) ≫ pullback.fst σ (sSingP p)
          = SSet.yonedaEquiv.symm w ≫ (phiAlong p σ ≫ pullback.fst σ (sSingP p)) :=
            Category.assoc _ _ _
        _ = SSet.yonedaEquiv.symm w ≫ phiAlongFst p σ := by rw [phiAlong_fst]
        _ = z' ≫ pullback.fst σ (sSingP p) := SSet.stdSimplex.ext₀
    · calc (SSet.yonedaEquiv.symm w ≫ phiAlong p σ) ≫ pullback.snd σ (sSingP p)
          = SSet.yonedaEquiv.symm w ≫ (phiAlong p σ ≫ pullback.snd σ (sSingP p)) :=
            Category.assoc _ _ _
        _ = SSet.yonedaEquiv.symm w ≫ sSingP (Work.StemsB.fibreIncl p (sigmaVert σ)) := by
            rw [phiAlong_snd]
        _ = SSet.yonedaEquiv.symm
              ((sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n w) :=
            SSet.yonedaEquiv_symm_comp _ _
        _ = SSet.yonedaEquiv.symm y := by rw [hfi]
        _ = u := by
            show SSet.yonedaEquiv.symm (SSet.yonedaEquiv u) = u
            rw [Equiv.symm_apply_apply]
        _ = z' ≫ pullback.snd σ (sSingP p) := rfl
  have hz2 : SSet.yonedaEquiv.symm ((phiAlong p σ).app n w) = SSet.yonedaEquiv.symm z := by
    rw [← SSet.yonedaEquiv_symm_comp, hgoal, ← hz', Equiv.symm_apply_apply]
  exact SSet.yonedaEquiv.symm.injective hz2

lemma phiAlong_app_inj (n : SimplexCategoryᵒᵖ) : Function.Injective ((phiAlong p σ).app n) := by
  intro x y hxy
  have h1 : SSet.yonedaEquiv.symm x ≫ phiAlong p σ =
      SSet.yonedaEquiv.symm y ≫ phiAlong p σ := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hxy]
  have h2 : (sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n x =
      (sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n y := by
    have h := congrArg (fun (w : SSet.stdSimplex.obj n.unop ⟶ pullback σ (sSingP p)) =>
      w ≫ pullback.snd σ (sSingP p)) h1
    have key : ∀ w : SSet.stdSimplex.obj n.unop ⟶
        sSing (Work.StemsB.fibre p (sigmaVert σ)),
        (w ≫ phiAlong p σ) ≫ pullback.snd σ (sSingP p) =
          SSet.yonedaEquiv.symm ((sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n
            (SSet.yonedaEquiv w)) := by
      intro w
      rw [Category.assoc, phiAlong_snd p σ]
      conv_lhs => rw [← Equiv.symm_apply_apply (SSet.yonedaEquiv (n := n.unop)) w]
      rw [SSet.yonedaEquiv_symm_comp]
    rw [key (SSet.yonedaEquiv.symm x), key (SSet.yonedaEquiv.symm y)] at h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact SSet.yonedaEquiv.symm.injective h
  have h3 : (Work.StemsB.fibreIncl p (sigmaVert σ)).comp
      (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n x) =
      (Work.StemsB.fibreIncl p (sigmaVert σ)).comp
      (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n y) := by
    have h := congrArg (TopCat.toSSetObjEquivT (TopCat.of E) n) h2
    rw [show TopCat.toSSetObjEquivT (TopCat.of E) n
          ((sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n x) =
        (Work.StemsB.fibreIncl p (sigmaVert σ)).comp
          (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n x) from rfl,
      show TopCat.toSSetObjEquivT (TopCat.of E) n
          ((sSingP (Work.StemsB.fibreIncl p (sigmaVert σ))).app n y) =
        (Work.StemsB.fibreIncl p (sigmaVert σ)).comp
          (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n y) from rfl] at h
    exact h
  have h4 : TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n x =
      TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n y := by
    ext z
    exact Subtype.ext (by
      have hz := congrArg (fun (f : C(stdSimplex ℝ (Fin (n.unop.len+1)), E)) => f z) h3
      simpa only [ContinuousMap.comp_apply, Work.StemsB.fibreIncl_apply] using hz)
  exact (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) n).injective h4

lemma phiAlong_isIso : IsIso (phiAlong p σ) := by
  rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
  intro n
  rw [CategoryTheory.isIso_iff_bijective]
  exact ⟨phiAlong_app_inj p σ n, phiAlong_app_surj p σ n⟩

theorem pullAlong_vertex_iso :
    Nonempty (pullback σ (sSingP p) ≅ sSing (Work.StemsB.fibre p (sigmaVert σ))) := by
  haveI := phiAlong_isIso p σ
  exact ⟨(asIso (phiAlong p σ)).symm⟩


/-- **The base case `s = 0` of the σ-piece computation.**  For a continuous map `p : E → B` and a
vertex `σ : Δ[0] ⟶ Sing B`, the σ-piece `C(T_σ)/C(∂T_σ)` is, as a chain complex, the singular chain
complex of the fibre of `p` over the point `sigmaVert σ` underlying `σ`.

Indeed `∂Δ[0] = ⊥`, so `∂T_σ = ⊥` and `pieceAlong (sSingP p) σ ≅ C(T_σ)`; and the pullback
`T_σ = Δ[0] ×_{Sing B} Sing E` is (the singular simplicial set of) the fibre `p⁻¹(σ(v₀))`, because
the only map `[n] → [0]` is constant, so its `n`-simplices are exactly the singular `n`-simplices of
`E` lying over the point `sigmaVert σ`. -/
theorem pieceAlongZero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Nonempty (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ ≅
      Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))) := by
  obtain ⟨e1⟩ := pieceAlongZeroCoker p σ
  obtain ⟨e2⟩ := pullAlong_vertex_iso p σ
  exact ⟨e1 ≪≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso e2 ≪≫
    eqToIso (show sCC (sSing (Work.StemsB.fibre p (sigmaVert σ))) =
      Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (sigmaVert σ))) from rfl)⟩

end

end Work.SSS
