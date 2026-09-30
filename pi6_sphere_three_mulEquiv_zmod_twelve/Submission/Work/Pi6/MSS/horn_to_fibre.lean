import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
import Submission.Work.SSSR.serreE1PieceDefs
import Submission.Work.SSSR.range_eq_preimage_range_of_isPullback
import Submission.Work.SSS.pieceAlongZero

/-!
# The horn of the piece `T_σ` over a 1-simplex is the singular complex of the fibre

For a map `p : E → B` and a simplex `σ : Δ[1] ⟶ Sing B`, the *piece* over `σ` is the simplicial
pullback `T_σ = Δ[1] ×_{Sing B} Sing E`.  Its horn `Λ = pieceHorn (Sing p) σ` is the part of `T_σ`
lying over the *last* vertex `v₁ ∈ Δ[1]` (for `s = 1` the horn `⋃_{i<1} d_iΔ[1]` is exactly the
vertex `v₁ = range (δ 0)`).

The content of this file is the identification of that horn with the singular simplicial set of the
honest fibre `p⁻¹(σ(v₁))` of `p`:

* `vertMap` is the pasting map `T_{δ₀ ≫ σ} ⟶ T_σ`; its range is `pieceHorn (Sing p) σ`, and the
  square exhibiting it as the pullback of `pullback.fst σ (Sing p)` along `δ 0` is a pullback
  square (`vertMap_isPullback`), whence `range_vertMap`.
* `hornLift` is `vertMap` viewed as a map onto the horn; it is an isomorphism
  (`isIso_hornLift`) since it is injective (a mono, `hornLift_mono`) and surjective onto the horn
  (`range_vertMap`).
* `Work.SSS.phiAlong` identifies `T_{δ₀ ≫ σ} = Δ[0] ×_{Sing B} Sing E` with the singular complex of
  the fibre over the vertex `σ(v₁)` (`phiAlong_isIso`), compatibly with the inclusions of the fibre
  (`phiAlong_snd`).

Composing the inverse of the second isomorphism with the inverse of the first gives the required
map `ψ : Λ ⟶ Sing (p⁻¹(σ(v₁)))`, and `phiAlong_snd` together with `hornLift_ι`/`vertMap_snd`
identifies `ψ ≫ Sing (fibreIncl p _)` with `Λ.ι ≫ pullback.snd σ (Sing p)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

variable {X Y : SSet.{0}}

/-- The last vertex `δ 0 : Δ[0] ⟶ Δ[1]` (which is the constant map at the last vertex). -/
abbrev lastVertMap : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶
    SSet.stdSimplex.obj (SimplexCategory.mk 1) :=
  SSet.stdSimplex.δ (n := 0) (0 : Fin 2)

/-- For `s = 1` the horn `hornSimp 1 = ⋃_{i < 1} d_iΔ[1]` is the last vertex
`v₁ = range (δ 0) ⊆ Δ[1]`. -/
lemma hornSimp_one_eq_range_delta :
    Work.SSSR.hornSimp 1 = SSet.Subcomplex.range lastVertMap := by
  rw [show lastVertMap = SSet.stdSimplex.δ (n := 0) (0 : Fin 2) from rfl]
  rw [Work.SSSR.hornSimp, SSet.stdSimplex.range_δ (n := 0) (0 : Fin 2)]
  rw [show (⨆ (i : Fin 1), SSet.stdSimplex.face ({i.castSucc} : Finset (Fin 2))ᶜ)
      = SSet.stdSimplex.face ({((0 : Fin 1).castSucc : Fin 2)} : Finset (Fin 2))ᶜ from
    le_antisymm (iSup_le fun i => by rw [Subsingleton.elim i 0])
      (le_iSup (fun i : Fin 1 => SSet.stdSimplex.face ({i.castSucc} : Finset (Fin 2))ᶜ) 0)]
  exact congrArg _ (by decide)

/-- **The vertex pasting map**: the map `T_{δ₀ ≫ σ} = Δ[0] ×_{Sing B} X ⟶ Δ[1] ×_{Sing B} X = T_σ`
induced by `δ 0 : Δ[0] ⟶ Δ[1]`.  Its range is the horn of `T_σ`. -/
def vertMap (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    pullback (lastVertMap ≫ σ) f ⟶ pullback σ f :=
  pullback.lift
    (pullback.fst (lastVertMap ≫ σ) f ≫ lastVertMap)
    (pullback.snd (lastVertMap ≫ σ) f)
    (by rw [Category.assoc, pullback.condition])

lemma vertMap_fst (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    vertMap f σ ≫ pullback.fst σ f = pullback.fst (lastVertMap ≫ σ) f ≫ lastVertMap :=
  pullback.lift_fst _ _ _

lemma vertMap_snd (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    vertMap f σ ≫ pullback.snd σ f = pullback.snd (lastVertMap ≫ σ) f :=
  pullback.lift_snd _ _ _

/-- The square defining `vertMap` is a pullback square (pasting of the two pullback squares for
`T_σ` and `T_{δ₀ ≫ σ}`). -/
theorem vertMap_isPullback (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    IsPullback (vertMap f σ) (pullback.fst (lastVertMap ≫ σ) f)
      (pullback.fst σ f) lastVertMap := by
  exact IsPullback.of_right (X₁₃ := X) (X₂₃ := Y)
    (h₁₂ := pullback.snd σ f) (h₂₂ := σ) (v₁₃ := f)
    (by
      rw [vertMap_snd]
      exact IsPullback.flip (IsPullback.of_hasPullback (lastVertMap ≫ σ) f))
    (by rw [vertMap_fst])
    (IsPullback.flip (IsPullback.of_hasPullback σ f))

theorem vertMap_mono (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) : Mono (vertMap f σ) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (vertMap_isPullback f σ).isLimit

/-- The range of the vertex pasting map is the horn `pieceHorn f σ` of `T_σ`. -/
theorem range_vertMap (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    SSet.Subcomplex.range (vertMap f σ) = Work.SSSR.pieceHorn f σ := by
  rw [Work.SSSR.pieceHorn, hornSimp_one_eq_range_delta,
    Work.SSSR.range_eq_preimage_range_of_isPullback (vertMap_isPullback f σ)]
  rfl

/-- The vertex pasting map, viewed as a map onto the horn. -/
def hornLift (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    pullback (lastVertMap ≫ σ) f ⟶ (Work.SSSR.pieceHorn f σ).toSSet :=
  SSet.Subcomplex.lift (vertMap f σ) (le_of_eq (range_vertMap f σ))

theorem hornLift_ι (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    hornLift f σ ≫ (Work.SSSR.pieceHorn f σ).ι = vertMap f σ :=
  SSet.Subcomplex.lift_ι _ _

theorem hornLift_mono (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) :
    Mono (hornLift f σ) :=
  @mono_of_mono_fac _ _ _ _ _ _ _ _ (vertMap_mono f σ) (hornLift_ι f σ)

/-- **The horn of `T_σ` over a 1-simplex is the fibre piece `T_{δ₀ ≫ σ}`**: the vertex pasting
map is an isomorphism onto the horn. -/
theorem isIso_hornLift (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Y) : IsIso (hornLift f σ) := by
  haveI hmono : Mono (hornLift f σ) := hornLift_mono f σ
  rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · rw [← mono_iff_injective]
    infer_instance
  · intro x
    have hx : x.1 ∈ (SSet.Subcomplex.range (vertMap f σ)).obj n := by
      rw [range_vertMap]; exact x.2
    rw [Subfunctor.range_obj] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy

theorem horn_to_fibre {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    ∃ ψ : (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).toSSet ⟶
        Work.SSS.sSing (Work.StemsB.fibre p (Work.Pi6.MSS.E2cfk.lastVert σ)),
      CategoryTheory.IsIso ψ ∧
      CategoryTheory.CategoryStruct.comp ψ
          (Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.Pi6.MSS.E2cfk.lastVert σ)))
        = CategoryTheory.CategoryStruct.comp
            (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι
            (CategoryTheory.Limits.pullback.snd σ (Work.SSS.sSingP p)) := by
  haveI hκ : IsIso (hornLift (Work.SSS.sSingP p) σ) := isIso_hornLift (Work.SSS.sSingP p) σ
  haveI hφ : IsIso (Work.SSS.phiAlong p (lastVertMap ≫ σ)) :=
    Work.SSS.phiAlong_isIso p _
  refine ⟨CategoryTheory.inv (hornLift (Work.SSS.sSingP p) σ) ≫
      CategoryTheory.inv (Work.SSS.phiAlong p (lastVertMap ≫ σ)),
    inferInstance, ?_⟩
  have key : ((CategoryTheory.inv (hornLift (Work.SSS.sSingP p) σ) ≫
        CategoryTheory.inv (Work.SSS.phiAlong p (lastVertMap ≫ σ))) ≫
        Work.SSS.sSingP (Work.StemsB.fibreIncl p
          (Work.SSS.sigmaVert (lastVertMap ≫ σ))))
      = (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι ≫
        CategoryTheory.Limits.pullback.snd σ (Work.SSS.sSingP p) := by
    rw [Category.assoc]
    rw [show CategoryTheory.inv (Work.SSS.phiAlong p (lastVertMap ≫ σ)) ≫
          Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert (lastVertMap ≫ σ)))
        = CategoryTheory.Limits.pullback.snd (lastVertMap ≫ σ) (Work.SSS.sSingP p) from by
      rw [← Work.SSS.phiAlong_snd p]
      rw [IsIso.inv_hom_id_assoc]]
    rw [← vertMap_snd (Work.SSS.sSingP p) σ]
    rw [← Category.assoc]
    have h2 : CategoryTheory.inv (hornLift (Work.SSS.sSingP p) σ) ≫
        vertMap (Work.SSS.sSingP p) σ = (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι := by
      have h := IsIso.inv_hom_id_assoc (hornLift (Work.SSS.sSingP p) σ)
        (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι
      rwa [hornLift_ι (Work.SSS.sSingP p) σ] at h
    rw [h2]
    exact rfl
  show ((CategoryTheory.inv (hornLift (Work.SSS.sSingP p) σ) ≫
        CategoryTheory.inv (Work.SSS.phiAlong p (lastVertMap ≫ σ))) ≫
        Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert (lastVertMap ≫ σ))))
      = (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι ≫
        CategoryTheory.Limits.pullback.snd σ (Work.SSS.sSingP p)
  exact key

end

end Work.Pi6.MSS
