import Mathlib
import Submission.Work.Pi6.MSS.e2PsiPairDefs
import Submission.Work.SSSR.serreE1Chain
import Submission.Work.Pi6.MSS.kunneth_exists
import Submission.Work.Pi6.MSS.normKron_exists
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Vocabulary for the final assembly of `Work.Pi6.MSS.e2Psi_bij`

This file fixes the objects used by the last step of the proof of `e2Psi_bij`:

* `hannSerre` — the hypothesis `hann` of `evS_bij`;
* `e2Hb` — the (explicit) identification `H_n(C) ≅ Z_n ⧸ B_n` of a chain complex of vector spaces;
* `e1elt`, `d1elt` — the `E¹`-class of a cycle of `Kg s` and its `d¹`-image;
* `e1SerreIso` — the **explicit** isomorphism `N_*(B) ⊗ H_q(F) ≅ E¹_{*,q}` (the `hom` of
  `serreE1_of_chainCondition`, with the `Nonempty` removed so that its value becomes computable);
* `psiE2` — its homology map, i.e. the explicit isomorphism `H_s(N_*(B) ⊗ H_q(F)) ≅ E²_{s,q}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The hypothesis `hann` of `evS_bij`, available unconditionally. -/
theorem hannSerre (𝕜 : Type) [Field 𝕜] (p : C(E, B)) :
    ∀ s n : ℕ, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n :=
  fun s n => Work.Pi6.MSS.coFiltAnn 𝕜 (sF p) s n

/-- **The identification `H_n(C) ≅ Z_n ⧸ B_n`** for a chain complex of vector spaces, made explicit
(the proof of `Work.StemsB.homology_iso_H_field`). -/
noncomputable def e2Hb (𝕜 : Type) [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    K.homology n ≅ ModuleCat.of 𝕜 (↥(Work.StemsB.fdZ 𝕜 K n) ⧸ Work.StemsB.fdH 𝕜 K n) :=
  (K.homologyIsoSc' (n + 1) n (n - 1) (Work.Cohomology.down_prev n)
      (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (K.sc' (n + 1) n (n - 1))

/-- The `E¹`-class of a cycle `w` of the graded piece `Kg s`, transported to the term `X s` of the
`E¹`-complex of the filtration `e1cFilt 𝕜 p`. -/
noncomputable def e1elt (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (w : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) (s + q))) :
    (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s :=
  (e2Hb 𝕜 (Kg 𝕜 p s) (s + q)).inv.hom
    ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (s + q)).mkQ w)

/-- The `d¹`-image of a cycle of the graded piece `Kg (s+1)`, as an element of the `E¹`-classes of
the graded piece `Kg s`. -/
noncomputable def d1elt (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (w : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q))) :
    (↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) (s + q))) ⧸ Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (s + q) :=
  (e2Hb 𝕜 (Kg 𝕜 p s) (s + q)).hom.hom
    ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (s + 1) s
      (e1elt 𝕜 p (s + 1) q w))

/-- **The explicit first-page comparison isomorphism** `N_*(B) ⊗ H_q(F) ≅ E¹_{*,q}`, obtained by
removing the `Nonempty` from `Work.SSSR.serreE1_of_chainCondition` (whose proof is explicit). -/
noncomputable def e1SerreIso (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ) :
    Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM p e₀ q) ≅
      Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q := by
  let P := Work.SSSR.serreE1_chainCondition (R := 𝕜) p e₀ hfib hconn q
  let eps : ℕ → ℤ := Classical.choose P
  have heps : ∀ s : ℕ, eps s = 1 ∨ eps s = -1 := (Classical.choose_spec P).1
  have hcomm := (Classical.choose_spec P).2
  let w : ∀ s : ℕ, (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM p e₀ q)).X s ⟶ (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s :=
    fun s => Work.SSSR.signCorr eps s •
      Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl s
  haveI hw : ∀ s : ℕ, IsIso (w s) := fun s => by
    haveI hpsi : IsIso (Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl s) :=
      Work.SSSR.isIso_PsiG (R := 𝕜) p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl s
    exact Work.SSSR.isIso_zsmul_of_isIso
      (Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl s)
      (Work.SSSR.signCorr eps s) (Work.SSSR.signCorr_eq_one_or_neg eps heps s)
  exact HomologicalComplex.Hom.isoOfComponents (fun s => asIso (w s)) (fun i j hij => by
    have hji : j + 1 = i := hij
    subst hji
    have hd : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (j+1) j
        = Work.SSSR.d1 (e1cFilt 𝕜 p) j q :=
      ChainComplex.of_d (fun s => Work.SSSR.E1 (e1cFilt 𝕜 p) s q)
        (fun s => Work.SSSR.d1 (e1cFilt 𝕜 p) s q) j
    show w (j+1) ≫ (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (j+1) j
      = (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM p e₀ q)).d (j+1) j ≫ w j
    rw [show w (j+1) = Work.SSSR.signCorr eps (j+1) •
          Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl (j+1) from rfl,
      show w j = Work.SSSR.signCorr eps j •
          Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl j from rfl,
      hd, Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomm (e1cFilt 𝕜 p) rfl j,
      smul_smul, Work.SSSR.signCorr_mul_eps eps heps j])

/-- The explicit isomorphism `H_s(N_*(B) ⊗ H_q(F)) ≅ E²_{s,q}`. -/
noncomputable def psiE2 (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ) (s : ℕ) :
    (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM p e₀ q)).homology s ⟶
      (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homology s :=
  HomologicalComplex.homologyMap (e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom s

/-- The **generator** of `N_s(B) ⊗ H_q(F)`: the sum `∑_j λ_j ι_{σ_j}(triv_{σ_j}[z_j])`, in the
presentation `∐_σ H_q(F)` of the tensor complex. -/
noncomputable def genElem (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (s q n : ℕ) (lam : Fin n → 𝕜)
    (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q ((ComplexShape.down ℕ).next q) (z j) = 0) :
    (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM p e₀ q)).X (s + 1) :=
  (Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ q) (s + 1)).hom.hom
    (∑ j : Fin n, lam j •
      (CategoryTheory.Limits.Sigma.ι
        (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1) => Work.SSSR.coefM p e₀ q)
        (σ j))
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
              ((ComplexShape.down ℕ).next q) rfl (hz j)))))

/-- The corresponding sum of the generator cycles `pairW` in the graded piece `Kg (s+1)`. -/
noncomputable def pairWsum (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (s q n : ℕ) (lam : Fin n → 𝕜)
    (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q ((ComplexShape.down ℕ).next q) (z j) = 0) :
    ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q)) :=
  ∑ j : Fin n, lam j • pairW 𝕜 p hfib s q (σ j) (z j) (hz j)

/-- The homology class of the generator `genElem`, given that it is a cycle. -/
noncomputable def genCyc (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (s q n : ℕ) (lam : Fin n → 𝕜)
    (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q ((ComplexShape.down ℕ).next q) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d (s + 1) ((ComplexShape.down ℕ).next (s + 1))
        (genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz) = 0) :
    (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)).homology (s + 1) :=
  ModuleCat.Hom.hom (HomologicalComplex.homologyπ
    (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)) (s + 1))
    (HomologicalComplex.cyclesMk
      (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q))
      (genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz)
      ((ComplexShape.down ℕ).next (s + 1)) rfl hcyc)

end

end Work.Pi6.MSS

