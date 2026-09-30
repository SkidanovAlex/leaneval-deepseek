import Mathlib
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.SSSR.serreE1Psi
import Submission.Work.SSSR.homology_sigmaExplicit
import Submission.Work.SSSR.serreFiltration
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The σ-indexed comparison map of the first page.**  The coproduct, over the nondegenerate
`s`-simplices `σ` of the base, of the σ-components `H_t(F) ≅ H_{s+t}(piece_σ) ⟶ H_{s+t}(grF_s)`. -/
noncomputable def PsiSig (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t s : ℕ) :
    (∐ fun σ : nIndex (sSing B) s => coefM p e₀ t) ⟶
      (grF (Fc (R := R) p) s).homology (s + t) :=
  Sigma.desc (fun σ : nIndex (sSing B) s =>
    (PsiCoef p e₀ hfib hc t s σ).hom ≫
      HomologicalComplex.homologyMap (mapPhiY R (sSingP p) s σ) (s + t))

/-- **The comparison map of the first page, in the coordinates of `d¹`.**  This is the composite of
the inverse of the coefficient isomorphism `(N_*(B) ⊗ M)_s ≅ ∐_σ M` with `PsiSig`. -/
noncomputable def PsiG (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    (tensorComplex R (Nn B) (coefM p e₀ t)).X s ⟶ (grF ξ.F s).homology (s + t) :=
  (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).inv ≫
    PsiSig p e₀ hfib hc t s ≫
    eqToHom (congrArg (fun F => (grF F s).homology (s + t)) hξ.symm)

/-- `PsiG` unfolds to `PsiSig` precomposed with the coefficent isomorphism. -/
theorem PsiG_eq (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    PsiG p e₀ hfib hc t ξ hξ s =
      (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).inv ≫ PsiSig p e₀ hfib hc t s ≫
        eqToHom (congrArg (fun F => (grF F s).homology (s + t)) hξ.symm) := rfl

/-- The `σ`-component of `PsiSig`. -/
theorem Sigma_ι_comp_PsiSig (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t s : ℕ) (σ : nIndex (sSing B) s) :
    Sigma.ι (fun _ : nIndex (sSing B) s => coefM p e₀ t) σ ≫ PsiSig p e₀ hfib hc t s
      = (PsiCoef p e₀ hfib hc t s σ).hom ≫
        HomologicalComplex.homologyMap (mapPhiY R (sSingP p) s σ) (s + t) := by
  rw [PsiSig, Sigma.ι_desc]

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
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ sSing (Work.SSSR.StemsB.fibre p b)) ⟶
      pullAlong (sSingP p) (SSet.stdSimplex.δ (n := P) 0 ≫ σ) :=
  pullback.lift (SemiCartesianMonoidalCategory.fst _ _)
    (((SSet.stdSimplex.δ (n := P) 0 ⊗ₘ 𝟙 (sSing (Work.SSSR.StemsB.fibre p b))) ≫
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
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
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
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ezSimplexZero p Φ hproj P b σ h ≫ pullback.snd (SSet.stdSimplex.δ (n := P) 0 ≫ σ) (sSingP p)
      = ((SSet.stdSimplex.δ (n := P) 0 ⊗ₘ 𝟙 (sSing (Work.SSSR.StemsB.fibre p b))) ≫
          ezSimplex p Φ hproj (P+1) b σ h) ≫ pullback.snd σ (sSingP p) :=
  pullback.lift_snd _ _ _

end

end Work.SSSR
