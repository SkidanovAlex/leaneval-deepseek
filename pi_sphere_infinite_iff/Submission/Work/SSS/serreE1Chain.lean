import Mathlib
import Submission.Work.SSS.serreE1D1
import Submission.Work.SSS.sigma_iota_homology_sigmaIso_inv

/-!
# The comparison map of the first page: the coproduct decomposition and its invertibility

`Work.SSS.PsiSig` (in `Submission/Work/SSS/serreE1D1.lean`) is the comparison map of the first page
of the Serre spectral sequence written in the coordinates in which the differential `d¹` is
computed: it is the coproduct, over the nondegenerate `s`-simplices `σ` of `Sing B`, of the
σ-components `H_t(F) ≅ H_{s+t}(piece_σ) → H_{s+t}(grF_s)`.

This file records that `PsiSig` is *exactly* the composite
`(∐_σ ΨCoef_σ) ≫ H(∐_σ piece_σ) ≅ ∐_σ H(piece_σ) ≫ H(mapPhi)`, i.e. a composite of three
isomorphisms, whence `IsIso (PsiSig …)`.  Consequently the degreewise comparison map `PsiG` of the
E¹ row complex with `N_*(B) ⊗ H_t(F)` is an isomorphism (`isIso_PsiG`) — the "easy half" of
`Work.SSS.serreE1`.  No use of `Classical.choice`d `Nonempty`-valued statements is made: all the
factors are the explicit isomorphisms `PsiCoef`, `homology_sigmaIso`, `mapPhiIso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **`PsiSig` is the coproduct of its σ-components.**  Composing it with the three isomorphisms
`∐_σ ΨCoef_σ`, `H(∐_σ piece_σ) ≅ ∐_σ H(piece_σ)` and `H(mapPhi)` recovers the coproduct
description `Σ.desc (fun σ => ΨCoef_σ ≫ H(mapPhiY_σ))` that defines it. -/
theorem PsiSig_eq_map (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t s : ℕ) :
    PsiSig p e₀ hfib hc t s =
      (Sigma.mapIso (fun σ : nIndex (sSing B) s => PsiCoef p e₀ hfib hc t s σ)).hom ≫
        (homology_sigmaIso (fun σ : nIndex (sSing B) s =>
          pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)) (s + t)).inv ≫
        HomologicalComplex.homologyMap (mapPhi (sSingP p) s) (s + t) := by
  apply Sigma.hom_ext
  intro σ
  rw [PsiSig]
  rw [Sigma.ι_desc]
  rw [show Sigma.ι (fun _ : nIndex (sSing B) s => coefM p e₀ t) σ ≫
        ((Sigma.mapIso (fun σ : nIndex (sSing B) s => PsiCoef p e₀ hfib hc t s σ)).hom ≫
          ((homology_sigmaIso (fun σ : nIndex (sSing B) s =>
            pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)) (s + t)).inv ≫
            HomologicalComplex.homologyMap (mapPhi (sSingP p) s) (s + t)))
      = (PsiCoef p e₀ hfib hc t s σ).hom ≫
          ((Sigma.ι (fun σ : nIndex (sSing B) s =>
              (pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)).homology (s + t)) σ ≫
            (homology_sigmaIso (fun σ : nIndex (sSing B) s =>
              pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)) (s + t)).inv) ≫
            HomologicalComplex.homologyMap (mapPhi (sSingP p) s) (s + t)) from by
      rw [← Category.assoc, Sigma.ι_mapIso_hom]
      simp only [Category.assoc]]
  rw [sigma_iota_homology_sigmaIso_inv, ← HomologicalComplex.homologyMap_comp]
  rw [show Sigma.ι (fun σ : nIndex (sSing B) s =>
        pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)) σ
        ≫ mapPhi (sSingP p) s = mapPhiY (sSingP p) s σ from by
      rw [mapPhi]; exact Sigma.ι_desc _ σ]

/-- **The σ-indexed comparison map of the first page is an isomorphism.** -/
theorem isIso_PsiSig (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t s : ℕ) :
    IsIso (PsiSig p e₀ hfib hc t s) := by
  rw [PsiSig_eq_map p e₀ hfib hc t s]
  haveI h1 : IsIso (Sigma.mapIso (fun σ : nIndex (sSing B) s => PsiCoef p e₀ hfib hc t s σ)).hom :=
    (Sigma.mapIso (fun σ : nIndex (sSing B) s => PsiCoef p e₀ hfib hc t s σ)).isIso_hom
  haveI h2 : IsIso (homology_sigmaIso (fun σ : nIndex (sSing B) s =>
      pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)) (s + t)).inv :=
    (homology_sigmaIso (fun σ : nIndex (sSing B) s =>
      pieceAlong (sSingP p) (nIndexSigma (sSing B) s σ)) (s + t)).isIso_inv
  haveI h3 : IsIso (HomologicalComplex.homologyMap (mapPhi (sSingP p) s) (s + t)) :=
    (HomologicalComplex.homologyMapIso (mapPhiIso (sSingP p) s) (s + t)).isIso_hom
  infer_instance

/-- **The degreewise comparison map `PsiG` of the first page is an isomorphism.** -/
theorem isIso_PsiG (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (s : ℕ) :
    IsIso (PsiG p e₀ hfib hc t ξ hξ s) := by
  haveI := isIso_PsiSig p e₀ hfib hc t s
  rw [PsiG]
  infer_instance

/-! ## Sign corrections

The chain condition for the comparison map holds only up to a dimension-dependent sign `±1`; the
correction multiplies the `s`-th component by such a sign.  These lemmas record that this keeps the
component an isomorphism. -/

lemma isIso_neg_id (M : ModuleCat ℤ) : IsIso (-(𝟙 M)) := by
  have h : (-(𝟙 M)) ≫ (-(𝟙 M)) = 𝟙 M := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, neg_neg]
  exact ⟨-(𝟙 M), h, h⟩

lemma isIso_zsmul_id (M : ModuleCat ℤ) (k : ℤ) (h : k = 1 ∨ k = -1) : IsIso (k • 𝟙 M) := by
  rcases h with rfl | rfl
  · simpa [one_zsmul] using (inferInstance : IsIso (𝟙 M))
  · simpa [neg_one_zsmul] using isIso_neg_id M

lemma isIso_zsmul_of_isIso {X Y : ModuleCat ℤ} (f : X ⟶ Y) [IsIso f] (k : ℤ)
    (h : k = 1 ∨ k = -1) : IsIso (k • f) := by
  rw [show k • f = (k • 𝟙 X) ≫ f from by rw [Preadditive.zsmul_comp, Category.id_comp]]
  haveI := isIso_zsmul_id X k h
  infer_instance


/-! ## The sign correction and the reduction of `serreE1` to the chain condition

The chain condition for the comparison map holds only up to a dimension-dependent sign `eps s = ±1`
(see `REFS/NOTES_SESSION5.md`).  Multiplying the `s`-th component of the comparison map by the
partial product `signCorr eps s = eps 0 * … * eps (s-1)` (a sign again) makes it an honest chain
map: this is the content of the next theorem, whose hypothesis is exactly the remaining
obligation. -/

/-- The sign correction: `signCorr eps 0 = 1` and `signCorr eps (s+1) = signCorr eps s * eps s`. -/
def signCorr (eps : ℕ → ℤ) : ℕ → ℤ :=
  fun s => Nat.rec 1 (fun s ih => ih * eps s) s

lemma signCorr_zero (eps : ℕ → ℤ) : signCorr eps 0 = 1 := rfl

lemma signCorr_succ (eps : ℕ → ℤ) (s : ℕ) : signCorr eps (s+1) = signCorr eps s * eps s := rfl

lemma signCorr_eq_one_or_neg (eps : ℕ → ℤ) (heps : ∀ s : ℕ, eps s = 1 ∨ eps s = -1) (s : ℕ) :
    signCorr eps s = 1 ∨ signCorr eps s = -1 := by
  induction s with
  | zero => exact Or.inl rfl
  | succ s ih =>
    rw [signCorr_succ]
    rcases ih with h | h <;> rcases heps s with h' | h' <;> rw [h, h'] <;> norm_num

lemma signCorr_mul_eps (eps : ℕ → ℤ) (heps : ∀ s : ℕ, eps s = 1 ∨ eps s = -1) (s : ℕ) :
    signCorr eps (s+1) * eps s = signCorr eps s := by
  rw [signCorr_succ]
  rcases heps s with h | h <;> rw [h] <;> ring

/-- **Reduction of `Work.SSS.serreE1` to the chain condition.**  If the degreewise comparison map
`PsiG` satisfies the chain condition up to a dimension-dependent sign, then the E¹ row complex is
isomorphic to the normalised chains of the base tensored with the homology of the fibre. -/
theorem serreE1_of_chainCondition (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (hcrux : ∃ eps : ℕ → ℤ, (∀ s : ℕ, eps s = 1 ∨ eps s = -1) ∧
      ∀ (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E))) (hξ : ξ.F = Fc p)
        (s : ℕ),
        PsiG p e₀ hfib hc t ξ hξ (s+1) ≫ d1 ξ s t
          = eps s • ((tensorComplex (Nn B) (coefM p e₀ t)).d (s+1) s
                       ≫ PsiG p e₀ hfib hc t ξ hξ s)) :
    ∀ (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E))) (hξ : ξ.F = Fc p),
      Nonempty (E1Complex ξ t ≅ tensorComplex (Nn B) (coefM p e₀ t)) := by
  obtain ⟨eps, heps, hcomm⟩ := hcrux
  intro ξ hξ
  let w : ∀ s, (tensorComplex (Nn B) (coefM p e₀ t)).X s ⟶ (E1Complex ξ t).X s :=
    fun s => signCorr eps s • PsiG p e₀ hfib hc t ξ hξ s
  haveI hw : ∀ s, IsIso (w s) := fun s => by
    haveI hpsi : IsIso (PsiG p e₀ hfib hc t ξ hξ s) := isIso_PsiG p e₀ hfib hc t ξ hξ s
    exact isIso_zsmul_of_isIso (PsiG p e₀ hfib hc t ξ hξ s) (signCorr eps s)
      (signCorr_eq_one_or_neg eps heps s)
  refine ⟨(HomologicalComplex.Hom.isoOfComponents (fun s => asIso (w s)) ?_).symm⟩
  intro i j hij
  have hji : j + 1 = i := hij
  subst hji
  have hd : (E1Complex ξ t).d (j+1) j = d1 ξ j t :=
    ChainComplex.of_d (fun s => E1 ξ s t) (fun s => d1 ξ s t) j
  show w (j+1) ≫ (E1Complex ξ t).d (j+1) j
    = (tensorComplex (Nn B) (coefM p e₀ t)).d (j+1) j ≫ w j
  rw [show w (j+1) = signCorr eps (j+1) • PsiG p e₀ hfib hc t ξ hξ (j+1) from rfl,
    show w j = signCorr eps j • PsiG p e₀ hfib hc t ξ hξ j from rfl,
    hd, Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomm ξ hξ j,
    smul_smul, signCorr_mul_eps eps heps j]

end

end Work.SSS
