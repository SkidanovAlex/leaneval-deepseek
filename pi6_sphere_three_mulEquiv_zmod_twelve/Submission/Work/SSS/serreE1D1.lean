import Mathlib
import Submission.Work.SSS.serreE1Assembly
import Submission.Work.SSS.serreE1Psi
import Submission.Work.SSS.homology_sigmaExplicit
import Submission.Work.SSS.serreFiltration

/-!
# The comparison map of the first page, in the coordinates of the differential `d¹`

`Work.SSS.serreE1` requires a *chain* isomorphism `E1Complex ξ t ≅ N_*(B) ⊗ H_t(F)`.  The
degreewise isomorphism `Work.SSS.PsiIso` of `Submission/Work/SSS/serreE1Psi.lean` is built from
isomorphisms of chain complexes, but its degreewise components involve the "component decomposition"
`H(∐_σ piece_σ) ≅ ∐_σ H(piece_σ)` (`Work.SSS.homology_sigmaIso`), which is a `coproductComplex`
comparison and is therefore not transparent on the σ-summands.

This file introduces the *same* comparison map in the shape in which the differentials can be
computed: `PsiSig` is the coproduct, over the nondegenerate `s`-simplices `σ` of the base, of the
σ-components

  `M = H_t(F) ≅ H_{s+t}(piece_σ) ⟶ H_{s+t}(grF_s)`,

i.e. `Sigma.desc (fun σ => PsiCoef σ ≫ H(mapPhiY σ))`.  On the `σ`-summand this is *by definition*
`H(mapPhiY σ)`, so the value of `Psi` on the generator `[σ] ⊗ m` is the class of `mapPhiY σ` applied
to the image of `m` under the σ-piece isomorphism — exactly the input of the computation of the
first differential (`REFS/NOTES_LEAD_SSS_d1.md`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The σ-indexed comparison map of the first page.**  The coproduct, over the nondegenerate
`s`-simplices `σ` of the base, of the σ-components `H_t(F) ≅ H_{s+t}(piece_σ) ⟶ H_{s+t}(grF_s)`. -/
noncomputable def PsiSig (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t s : ℕ) :
    (∐ fun σ : nIndex (sSing B) s => coefM p e₀ t) ⟶
      (grF (Fc p) s).homology (s + t) :=
  Sigma.desc (fun σ : nIndex (sSing B) s =>
    (PsiCoef p e₀ hfib hc t s σ).hom ≫
      HomologicalComplex.homologyMap (mapPhiY (sSingP p) s σ) (s + t))

/-- **The comparison map of the first page, in the coordinates of `d¹`.**  This is the composite of
the inverse of the coefficient isomorphism `(N_*(B) ⊗ M)_s ≅ ∐_σ M` with `PsiSig`. -/
noncomputable def PsiG (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    (tensorComplex (Nn B) (coefM p e₀ t)).X s ⟶ (grF ξ.F s).homology (s + t) :=
  (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).inv ≫
    PsiSig p e₀ hfib hc t s ≫
    eqToHom (congrArg (fun F => (grF F s).homology (s + t)) hξ.symm)

/-- `PsiG` unfolds to `PsiSig` precomposed with the coefficent isomorphism. -/
theorem PsiG_eq (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    PsiG p e₀ hfib hc t ξ hξ s =
      (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).inv ≫ PsiSig p e₀ hfib hc t s ≫
        eqToHom (congrArg (fun F => (grF F s).homology (s + t)) hξ.symm) := rfl

/-- The `σ`-component of `PsiSig`. -/
theorem Sigma_ι_comp_PsiSig (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t s : ℕ) (σ : nIndex (sSing B) s) :
    Sigma.ι (fun _ : nIndex (sSing B) s => coefM p e₀ t) σ ≫ PsiSig p e₀ hfib hc t s
      = (PsiCoef p e₀ hfib hc t s σ).hom ≫
        HomologicalComplex.homologyMap (mapPhiY (sSingP p) s σ) (s + t) := by
  rw [PsiSig, Sigma.ι_desc]

/-- **The value of the comparison map on a generator.**  On the `σ`-summand `PsiSig` is the σ-piece
isomorphism followed by `H(mapPhiY σ)`. -/
theorem PsiSig_ι (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t s : ℕ) (σ : nIndex (sSing B) s)
    (m : coefM p e₀ t) :
    (eltHom m ≫ Sigma.ι (fun _ : nIndex (sSing B) s => coefM p e₀ t) σ) ≫
        PsiSig p e₀ hfib hc t s
      = eltHom ((PsiCoef p e₀ hfib hc t s σ).hom m) ≫
          HomologicalComplex.homologyMap (mapPhiY (sSingP p) s σ) (s + t) := by
  rw [Category.assoc, Sigma_ι_comp_PsiSig, ← Category.assoc, eltHom_comp]

/-- **The value of `PsiG` on the generator `[σ] ⊗ m`.**  With the identification
`(N_*(B) ⊗ M)_s ≅ ∐_{σ} M` of `Work.SSS.serreE1CoefIsoIso`, the generator corresponding to the
nondegenerate `s`-simplex `σ` and `m : M` is the image under the coefficient isomorphism of the
`σ`-component `eltHom m ≫ Sigma.ι σ`, and `PsiG` sends it to the class of `mapPhiY σ` applied to
the image of `m` under the σ-piece isomorphism `Work.SSS.PsiCoef`. -/
theorem PsiG_gen (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) (σ : nIndex (sSing B) s) (m : coefM p e₀ t) :
    (eltHom m ≫ Sigma.ι (fun _ : nIndex (sSing B) s => coefM p e₀ t) σ) ≫
        (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).hom ≫ PsiG p e₀ hfib hc t ξ hξ s
      = eltHom ((PsiCoef p e₀ hfib hc t s σ).hom m) ≫
          HomologicalComplex.homologyMap (mapPhiY (sSingP p) s σ) (s + t) ≫
          eqToHom (congrArg (fun F => (grF F s).homology (s + t)) hξ.symm) := by
  have h : (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).hom ≫ PsiG p e₀ hfib hc t ξ hξ s
      = PsiSig p e₀ hfib hc t s ≫
          eqToHom (congrArg (fun F => (grF F s).homology (s + t)) hξ.symm) := by
    simp only [PsiG, Iso.hom_inv_id_assoc]
  rw [h, ← Category.assoc, PsiSig_ι, Category.assoc]


/-! ## The `0`-face of the coherent lift

The `i = 0` face of the first differential is the only one whose base point moves
(`sigmaVert (d_0 sigma) = sigma (v_1)` instead of `sigma (v_0)`), so the comparison with the
coordinate `i_{d_0 sigma}` genuinely needs the fibre transport.  The chain-level input is the
`0`-face of the coherent lift `ezSimplex_sigma`, which factors through the pullback
`T_{d_0 sigma} = Δ[s] ×_{Sing B} Sing E` because the `0`-th coface of the fundamental simplex of
`Δ[s+1]` is a simplex whose first coordinate is `δ 0 ∘ pr₁`. -/

/-- **The `0`-face of the coherent lift.**  For `σ : Δ[P+1] → Sing B` and a coherent lift
`Φ = ezSimplex_σ`, the pairing `(pr₁, Φ(δ 0 ⊗ 𝟙))` factors through the pullback `T_{δ 0 ≫ σ}`, i.e.
it is the lift of `pr₁ ≫ (δ 0 ≫ σ)` given by restricting the lift of `σ` to its `0`-th face. -/
noncomputable def ezSimplexZero (p : C(E, B))
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ sSing (Work.StemsB.fibre p b)) ⟶
      pullAlong (sSingP p) (SSet.stdSimplex.δ (n := P) 0 ≫ σ) :=
  pullback.lift (SemiCartesianMonoidalCategory.fst _ _)
    (((SSet.stdSimplex.δ (n := P) 0 ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b))) ≫
        ezSimplex p Φ hproj (P+1) b σ h) ≫ pullback.snd σ (sSingP p))
    (by
      simp only [Category.assoc, ezSimplex_snd, hproj]
      rw [← Category.assoc (SSet.stdSimplex.δ (n := P) 0 ⊗ₘ 𝟙 _)
        (SemiCartesianMonoidalCategory.fst _ _) σ,
        CartesianMonoidalCategory.tensorHom_fst]
      rfl)

variable {p : C(E, B)}

@[simp] lemma ezSimplexZero_fst
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ezSimplexZero p Φ hproj P b σ h ≫ pullback.fst (SSet.stdSimplex.δ (n := P) 0 ≫ σ) (sSingP p)
      = SemiCartesianMonoidalCategory.fst _ _ :=
  pullback.lift_fst _ _ _

@[simp] lemma ezSimplexZero_snd
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ezSimplexZero p Φ hproj P b σ h ≫ pullback.snd (SSet.stdSimplex.δ (n := P) 0 ≫ σ) (sSingP p)
      = ((SSet.stdSimplex.δ (n := P) 0 ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b))) ≫
          ezSimplex p Φ hproj (P+1) b σ h) ≫ pullback.snd σ (sSingP p) :=
  pullback.lift_snd _ _ _

/-- The `0`-face of the lift, followed by the face inclusion `T_{d_0σ} ⟶ T_σ`, is the `0`-face of
the lift of `σ`. -/
lemma ezSimplexZero_comp_pullFaceIncl (p : C(E, B))
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ezSimplexZero p Φ hproj P b σ h ≫ pullFaceIncl (sSingP p) σ 0
      = (SSet.stdSimplex.δ (n := P) 0 ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b))) ≫
          ezSimplex p Φ hproj (P+1) b σ h := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullFaceIncl_fst, ← Category.assoc, ezSimplexZero_fst]
    rw [Category.assoc, ezSimplex_fst, CartesianMonoidalCategory.tensorHom_fst]
  · rw [Category.assoc, pullFaceIncl_snd, ezSimplexZero_snd]

end

end Work.SSS
