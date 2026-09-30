import Mathlib
import Submission.Work.MbarHomology.CellAtlas.Core
import Submission.Work.MbarHomology.CellAtlas.InsertSetup
import Submission.Work.MbarHomology.CellAtlas.insert_cPieceCoeffF_bijective
import Submission.Work.MbarHomology.CellAtlas.insert_kPsi_chain
import Submission.Work.MbarHomology.CellAtlas.insert_kSup_le_sup_map
import Submission.Work.MbarHomology.CellAtlas.insert_kPsi_mem_kSup_imp_ltSub
import Submission.Work.HomologyIso.quasiIso_iff_of_conj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

namespace CellAtlas

namespace Insert

open HomologicalComplex (singleObjXSelf)

attribute [local instance 2000] Pi.Function.module Finsupp.module
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

set_option allowUnsafeReducibility true
attribute [local reducible] Work.Subdivision.PolyCW.leSub Work.Subdivision.PolyCW.ltSub
  Work.Subdivision.PolyCW.locRel Work.Subdivision.PolyCW.locMod Work.Subdivision.PolyCW.locCx
  Work.Subdivision.SubData.quot Work.Subdivision.SubData.quotOf
  Work.Subdivision.SubData.quotCptMap Work.Subdivision.SubData.quotDcpt
  Work.Subdivision.SubData.chain Work.Subdivision.SubData.quotD
  Work.Subdivision.SubData.dL Work.Subdivision.SubData.dLcpt
  Work.MbarHomology.CellAtlas.KSD Work.MbarHomology.CellAtlas.CSD
  Work.MbarHomology.CellAtlas.KPiece Work.MbarHomology.CellAtlas.CPiece

universe u

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW.{u}}
  {C : Work.Certificates.FinChainCx}


theorem kIso_hom_inv (k : ℕ) (y : kMod K k) :
    (kIso K k).hom ((kIso K k).inv y) = y := by
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]

theorem kIso_inv_hom (k : ℕ) (y : K.chainX k) :
    (kIso K k).inv ((kIso K k).hom y) = y := by
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]

theorem kAlpha (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (y : Work.Subdivision.chainMod P.Cell k) :
    (kIso K k).hom (kPsiK A n f₀ k y) = kPsi A n f₀ k y :=
  kIso_hom_inv k _

theorem kPsiK_mem_kMod_insert (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (z : Work.Subdivision.chainMod P.Cell k) :
    kPsiK A n f₀ k z ∈ KMod A n (insert f₀ E) k := by
  rw [mem_KMod, kPsiK_apply]
  rw [show (kIso K k).hom ((kIso K k).inv (kPsi A n f₀ k z)) = kPsi A n f₀ k z
    from kIso_hom_inv k _]
  exact kPsi_mem_kSup_insert A n E f₀ k z

theorem kPsiK_mem_kMod_E_iff (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (z : Work.Subdivision.chainMod P.Cell k) :
    kPsiK A n f₀ k z ∈ KMod A n E k ↔ kPsi A n f₀ k z ∈ kSup A n E k := by
  rw [mem_KMod, kPsiK_apply]
  rw [show (kIso K k).hom ((kIso K k).inv (kPsi A n f₀ k z)) = kPsi A n f₀ k z
    from kIso_hom_inv k _]

theorem kPsiK_ltSub_eq_zero (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) {z : Work.Subdivision.chainMod P.Cell k}
    (hz : z ∈ Work.Subdivision.PolyCW.ltSub P (A.root (n + 1) f₀) k) :
    kPsiK A n f₀ k z = 0 := by
  rw [kPsiK_apply, kPsi_ltSub_eq_zero A n f₀ k hz]
  show (kIso K k).inv 0 = 0
  exact map_zero _

/-- The restricted comparison map, into the new level of `K`. -/
noncomputable def kInc (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) :
    ↥(Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) k) →ₗ[ℤ]
      ↥(KMod A n (insert f₀ E) k) :=
  LinearMap.codRestrict (KMod A n (insert f₀ E) k)
    ((kPsiK A n f₀ k).comp
      (Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) k).subtype)
    fun x => kPsiK_mem_kMod_insert A n E f₀ k x.1

/-- The element of the new level obtained by transporting `u` back along `kIso`. -/
noncomputable def kInvElem (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (u : kMod K k) (hu : u ∈ kSup A n (insert f₀ E) k) :
    ↥(KMod A n (insert f₀ E) k) :=
  ⟨(kIso K k).inv u, by
    have h1 : (kIso K k).hom ((kIso K k).inv u) ∈ kSup A n (insert f₀ E) k := by
      rw [kIso_hom_inv]
      exact hu
    exact (mem_KMod (K := K)).mpr h1⟩

theorem kInvElem_apply (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (u : kMod K k) (hu : u ∈ kSup A n (insert f₀ E) k) :
    ((kInvElem A n E f₀ k u hu : ↥(KMod A n (insert f₀ E) k)) : K.chainX k)
      = (kIso K k).inv u := rfl

theorem kInc_mem_kPiece (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (x : ↥(Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) k))
    (hx : x.1 ∈ Work.Subdivision.PolyCW.ltSub P (A.root (n + 1) f₀) k) :
    kInc A n E f₀ k x ∈ (KPiece A n E f₀).sub k := by
  change kPsiK A n f₀ k x.1 ∈ (KSD A n E).sub k
  rw [kPsiK_ltSub_eq_zero A n f₀ k hx]
  exact Submodule.zero_mem _

theorem kInc_le_comap (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) :
    Work.Subdivision.PolyCW.locRel P (A.root (n + 1) f₀) k ≤
      ((KPiece A n E f₀).sub k).comap (kInc A n E f₀ k) := by
  intro x hx
  have hx' : x.1 ∈ Work.Subdivision.PolyCW.ltSub P (A.root (n + 1) f₀) k := hx
  exact kInc_mem_kPiece A n E f₀ k x hx'

theorem kInc_comap_le (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ) :
    ((KPiece A n E f₀).sub k).comap (kInc A n E f₀ k) ≤
      Work.Subdivision.PolyCW.locRel P (A.root (n + 1) f₀) k := by
  intro x hx
  change kPsiK A n f₀ k x.1 ∈ (KSD A n E).sub k at hx
  change x.1 ∈ Work.Subdivision.PolyCW.ltSub P (A.root (n + 1) f₀) k
  exact insert_kPsi_mem_kSup_imp_ltSub A n E f₀ hf k x.1 x.2
    ((kPsiK_mem_kMod_E_iff A n E f₀ k x.1).mp hx)

theorem kInvElem_mem_kPiece (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (u : kMod K k) (hu : u ∈ kSup A n E k) :
    kInvElem A n E f₀ k u (kSup_le_insert A n E f₀ k hu) ∈ (KPiece A n E f₀).sub k := by
  change (kIso K k).inv u ∈ (KSD A n E).sub k
  have h1 : (kIso K k).hom ((kIso K k).inv u) ∈ kSup A n E k := by
    rw [kIso_hom_inv]
    exact hu
  exact (mem_KMod (K := K)).mpr h1

theorem kInc_sup (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) :
    (kInc A n E f₀ k).range ⊔ (KPiece A n E f₀).sub k = ⊤ := by
  refine eq_top_iff.mpr fun w _ => ?_
  have hw : (kIso K k).hom (w : K.chainX k) ∈ kSup A n (insert f₀ E) k :=
    mem_KMod.mp (show (w : K.chainX k) ∈ KMod A n (insert f₀ E) k from w.2)
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Submodule.mem_sup.mp (insert_kSup_le_sup_map A n E f₀ k hw)
  obtain ⟨z, hz, hzv⟩ := hv
  have hdecomp : w = kInc A n E f₀ k ⟨z, hz⟩
      + kInvElem A n E f₀ k u (kSup_le_insert A n E f₀ k hu) := by
    refine Subtype.ext ?_
    show (w : K.chainX k) = (kPsiK A n f₀ k z + (kIso K k).inv u)
    have h1 : (kIso K k).inv (u + v) = (w : K.chainX k) := by
      rw [huv, kIso_inv_hom]
    calc (w : K.chainX k) = (kIso K k).inv (u + v) := h1.symm
      _ = (kIso K k).inv u + (kIso K k).inv v := map_add _ _ _
      _ = (kIso K k).inv u + kPsiK A n f₀ k z := by rw [← hzv]; rfl
      _ = kPsiK A n f₀ k z + (kIso K k).inv u := add_comm _ _
  rw [hdecomp]
  refine Submodule.add_mem_sup (LinearMap.mem_range_self (kInc A n E f₀ k) ⟨z, hz⟩) ?_
  exact kInvElem_mem_kPiece A n E f₀ k u hu

/-- The comparison map on the piece quotients, as a linear map. -/
noncomputable def kPieceMapLin (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) :
    Work.Subdivision.PolyCW.locMod P (A.root (n + 1) f₀) k →ₗ[ℤ]
      (KPiece A n E f₀).quot.X k :=
  Submodule.mapQ (Work.Subdivision.PolyCW.locRel P (A.root (n + 1) f₀) k)
    ((KPiece A n E f₀).sub k) (kInc A n E f₀ k) (kInc_le_comap A n E f₀ k)

theorem kPieceMapLin_apply (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (x : ↥(Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) k)) :
    kPieceMapLin A n E f₀ k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (kInc A n E f₀ k x) :=
  Submodule.mapQ_apply _ _ _ x

theorem kPieceMapLin_bijective (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ) :
    Function.Bijective (kPieceMapLin A n E f₀ k) :=
  Work.Subdivision.sdPieceMapLinMapQ_bijective_aux (kInc A n E f₀ k)
    (kInc_le_comap A n E f₀ k) (kInc_comap_le A n E f₀ hf k) (kInc_sup A n E f₀ k)

theorem kIso_chainD (k : ℕ) (y : K.chainX (k + 1)) :
    kδCpt K k ((kIso K (k + 1)).hom y) = (kIso K k).hom ((K.chainD k) y) := by
  rw [kδCpt, ModuleCat.comp_apply, ModuleCat.comp_apply, kIso_inv_hom]

/-! ## The `C`-side piece -/

/-- In degrees other than `n+1` the `C`-piece quotient vanishes. -/
theorem CPiece_subsingleton (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) {k : ℕ} (hk : k ≠ n + 1) :
    Subsingleton ((CPiece (C := C) n E f₀).quot.X k) := by
  have hsub : (CPiece (C := C) n E f₀).sub k = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [CPiece_sub, Submodule.mem_comap]
    have hx : ((CSD (C := C) n (insert f₀ E)).sub k).subtype x
        ∈ CMod C n (insert f₀ E) k := x.2
    rwa [CMod_insert_eq_of_ne (C := C) hk] at hx
  exact ⟨fun x y => (Work.Subdivision.subsingleton_quotient_of_eq_top hsub).elim x y⟩

/-- The `C`-piece, as the one-dimensional model complex generated by the class of
the new cell. -/
noncomputable def cPieceMap (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    Work.Subdivision.unitCx (n + 1) ⟶ (CPiece (C := C) n E f₀).quot :=
  HomologicalComplex.mkHomFromSingle
    (K := (CPiece (C := C) n E f₀).quot) (j := n + 1)
    (A := Work.Subdivision.unitMod)
    (cPieceCoeffF A n E f₀)
    (fun k hk => by
      haveI : Subsingleton ((CPiece (C := C) n E f₀).quot.X k) :=
        CPiece_subsingleton A n E f₀ (by
          have h2 : k + 1 = n + 1 := hk
          omega)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)

theorem cPieceMap_f_succ (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    (cPieceMap A n E f₀).f (n + 1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod).hom ≫ cPieceCoeffF A n E f₀ :=
  HomologicalComplex.mkHomFromSingle_f _ _

theorem cPieceMap_isIso (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) :
    IsIso (cPieceMap A n E f₀) := by
  have coeff : IsIso (cPieceCoeffF A n E f₀) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact insert_cPieceCoeffF_bijective A n E f₀ hf
  haveI hf' : ∀ k, IsIso ((cPieceMap A n E f₀).f k) := fun k => by
    by_cases hk : k = n + 1
    · rw [hk, cPieceMap_f_succ]
      infer_instance
    · rw [ConcreteCategory.isIso_iff_bijective]
      haveI : Subsingleton ((Work.Subdivision.unitCx (n + 1)).X k) :=
        Work.Subdivision.unitCx_subsingleton hk
      haveI : Subsingleton ((CPiece (C := C) n E f₀).quot.X k) :=
        CPiece_subsingleton A n E f₀ hk
      refine ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components (cPieceMap A n E f₀)

/-- **The `C`-piece quotient is the one-dimensional model complex.** -/
noncomputable def cPieceIso (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) :
    (CPiece (C := C) n E f₀).quot ≅ Work.Subdivision.unitCx (n + 1) := by
  haveI := cPieceMap_isIso A n E f₀ hf
  exact (asIso (cPieceMap A n E f₀)).symm

@[simp] theorem cPieceIso_inv (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) :
    (cPieceIso A n E f₀ hf).inv = cPieceMap A n E f₀ := rfl

/-- The restricted differential of a level of `K`, in the `KMod` encoding. -/
noncomputable def kModD (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) :
    ↥(KMod A n E (k + 1)) →ₗ[ℤ] ↥(KMod A n E k) :=
  (K.chainD k).hom.restrict fun x hx => KMod_d_apply A n E k hx

theorem chainD_apply (k : ℕ) (y : K.chainX (k + 1)) :
    (K.chain.d (k + 1) k).hom y = (K.chainD k) y := by
  rw [Work.DeltaHomology.DeltaCx.chain_d]
  rfl

theorem kModD_apply (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) (x : ↥(KMod A n E (k + 1))) :
    ((kModD A n E k x : ↥(KMod A n E k)) : K.chainX k)
      = (K.chainD k) (x : K.chainX (k + 1)) := rfl

/-- The differential of the level, in the shape produced by the quotient API. -/
theorem chainHd_eq_kModD (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) (x : ↥(KMod A n E (k + 1))) :
    ((ModuleCat.Hom.hom (((KSD A n E).chain).d (k + 1) k)) x : ↥((KSD A n E).chain.X k))
      = (kModD A n E k x : ↥(KMod A n E k)) := by
  rw [Work.Subdivision.SubData.chain_d]
  refine Subtype.ext ?_
  exact (Work.Subdivision.SubData.dL_apply (S := KSD A n E) k x).trans
    (chainD_apply k (x : K.chainX (k + 1)))

theorem kIso_chain_d (k : ℕ) (y : K.chainX (k + 1)) :
    kδCpt K k ((kIso K (k + 1)).hom y)
      = (kIso K k).hom ((K.chain.d (k + 1) k) y) := by
  rw [chainD_apply]
  exact kIso_chainD k y

/-- The representative-level form of the chain-map condition. -/
theorem kPieceMapLin_diff_mem (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (y : ↥(Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) (k + 1))) :
    (kModD A n (insert f₀ E) k (kInc A n E f₀ (k + 1) y)
        - kInc A n E f₀ k (Work.Subdivision.PolyCW.leSubD P (A.root (n + 1) f₀) k y))
      ∈ (KPiece A n E f₀).sub k := by
  change ((((K.chainD k) (kPsiK A n f₀ (k + 1) y.1) : K.chainX k)
      - kPsiK A n f₀ k (Work.Subdivision.D (α := P.Cell) k y.1)) : K.chainX k)
      ∈ (KSD A n E).sub k
  have hkey : (kIso K k).hom ((((K.chainD k) (kPsiK A n f₀ (k + 1) y.1) : K.chainX k)
        - kPsiK A n f₀ k (Work.Subdivision.D (α := P.Cell) k y.1)) : K.chainX k)
      = kδCpt K k (kPsi A n f₀ (k + 1) y.1)
        - kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k y.1) := by
    rw [map_sub, ← kIso_chainD k (kPsiK A n f₀ (k + 1) y.1), kAlpha, kAlpha]
  have hmem : kδCpt K k (kPsi A n f₀ (k + 1) y.1)
      - kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k y.1) ∈ kSup A n E k :=
    insert_kPsi_chain A n E f₀ k y.1 y.2
  have hmem' : ((((K.chainD k) (kPsiK A n f₀ (k + 1) y.1) : K.chainX k)
      - kPsiK A n f₀ k (Work.Subdivision.D (α := P.Cell) k y.1)) : K.chainX k)
      ∈ KMod A n E k := by
    rw [mem_KMod, hkey]
    exact hmem
  exact hmem'


/-- The comparison map on the piece quotients commutes with the differentials, as
linear maps (the cross-universe form of the chain-map condition). -/
theorem kPieceMapLin_comm_lin (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (x : Work.Subdivision.PolyCW.locMod P (A.root (n + 1) f₀) (k + 1)) :
    kPieceMapLin A n E f₀ k
        (Work.Subdivision.PolyCW.locD P (A.root (n + 1) f₀) k x)
      = ((KPiece A n E f₀).quotD k) (kPieceMapLin A n E f₀ (k + 1) x) := by
  refine Submodule.Quotient.induction_on
    (p := Work.Subdivision.PolyCW.locRel P (A.root (n + 1) f₀) (k + 1)) x ?_
  intro y
  rw [Work.Subdivision.PolyCW.locD_mk]
  rw [kPieceMapLin_apply A n E f₀ k
    (Work.Subdivision.PolyCW.leSubD P (A.root (n + 1) f₀) k y)]
  rw [kPieceMapLin_apply A n E f₀ (k + 1) y]
  have hbr : ((ModuleCat.Hom.hom (((KSD A n (insert f₀ E)).chain).d (k + 1) k))
        ((kInc A n E f₀ (k + 1)) y))
      = (kModD A n (insert f₀ E) k ((kInc A n E f₀ (k + 1)) y) :
          ↥(KMod A n (insert f₀ E) k)) :=
    chainHd_eq_kModD A n (insert f₀ E) k ((kInc A n E f₀ (k + 1)) y)
  have h1 : (Submodule.Quotient.mk
        (kInc A n E f₀ k (Work.Subdivision.PolyCW.leSubD P (A.root (n + 1) f₀) k y)) :
          ↥(KMod A n (insert f₀ E) k) ⧸ (KPiece A n E f₀).sub k)
      = Submodule.Quotient.mk
          ((kModD A n (insert f₀ E) k ((kInc A n E f₀ (k + 1)) y) :
            ↥(KMod A n (insert f₀ E) k))) := by
    refine (Submodule.Quotient.eq _).mpr ?_
    have h := kPieceMapLin_diff_mem A n E f₀ k y
    have h2 := Submodule.neg_mem _ h
    rwa [neg_sub] at h2
  have h2 : (Submodule.Quotient.mk
        ((kModD A n (insert f₀ E) k ((kInc A n E f₀ (k + 1)) y) :
          ↥(KMod A n (insert f₀ E) k))) :
          ↥((KSD A n (insert f₀ E)).chain.X k) ⧸ (KPiece A n E f₀).sub k)
      = ((KPiece A n E f₀).quotD k) (Submodule.Quotient.mk (kInc A n E f₀ (k + 1) y)) :=
    (congrArg Submodule.Quotient.mk hbr.symm).trans
      ((KPiece A n E f₀).quotD_apply k ((kInc A n E f₀ (k + 1)) y)).symm
  exact h1.trans h2


theorem kPsiK_subdivCell (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1))) :
    kPsiK A n f₀ (n + 1)
        (Work.Subdivision.PolyCW.subdivCell P (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩)
      = A.z (n + 1) f₀ := by
  rw [kPsiK_apply, kPsi_subdivCell, kz]
  exact kIso_inv_hom (n + 1) (A.z (n + 1) f₀)

/-- The linear equivalence underlying an isomorphism of `ℤ`-modules. -/
noncomputable def moduleCatIsoLinEquiv {M N : ModuleCat ℤ} (e : M ≅ N) : ↥M ≃ₗ[ℤ] ↥N where
  toFun := fun x => e.hom.hom x
  invFun := fun x => e.inv.hom x
  left_inv x := by
    show e.inv.hom (e.hom.hom x) = x
    rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
  right_inv x := by
    show e.hom.hom (e.inv.hom x) = x
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  map_add' x y := (e.hom.hom).map_add x y
  map_smul' c x := (e.hom.hom).map_smul c x

/-- The canonical linear equivalence between two universe instantiations of `ℤ`. -/
noncomputable def uliftZEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ULift.{0} ℤ where
  toFun x := ULift.up x.down
  invFun x := ULift.up x.down
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_add' x y := by cases x; cases y; rfl
  map_smul' c x := by cases x; rfl

/-- The degreewise linear equivalence between the two model complexes `unitCx (n+1)`,
one in each universe. -/
noncomputable def kUnitEquivTop (n : ℕ) :
    ↥((Work.Subdivision.unitCx.{u} (n + 1)).X (n + 1)) ≃ₗ[ℤ]
      ↥((Work.Subdivision.unitCx.{0} (n + 1)).X (n + 1)) :=
  (moduleCatIsoLinEquiv (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
      Work.Subdivision.unitMod.{u})).trans
    (uliftZEquiv.trans
      ((moduleCatIsoLinEquiv (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod.{0})).symm))

theorem kUnitEquivTop_apply (n : ℕ) (x : ↥((Work.Subdivision.unitCx.{u} (n + 1)).X (n + 1))) :
    kUnitEquivTop n x = (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
      Work.Subdivision.unitMod.{0}).inv.hom
      (uliftZEquiv ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod.{u}).hom.hom x)) := rfl

theorem kUnitEquivTop_gen (n : ℕ) (c : ℤ) :
    kUnitEquivTop n
        ((singleObjXSelf (ComplexShape.down ℕ) (n + 1) Work.Subdivision.unitMod.{u}).inv.hom
          (ULift.up c : ULift.{u} ℤ))
      = (singleObjXSelf (ComplexShape.down ℕ) (n + 1) Work.Subdivision.unitMod.{0}).inv.hom
          (ULift.up c : ULift.{0} ℤ) := by
  rw [kUnitEquivTop_apply]
  congr 1
  show uliftZEquiv ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
      Work.Subdivision.unitMod.{u}).hom.hom
      ((singleObjXSelf (ComplexShape.down ℕ) (n + 1) Work.Subdivision.unitMod.{u}).inv.hom
        (ULift.up c : ULift.{u} ℤ))) = uliftZEquiv (ULift.up c : ULift.{u} ℤ)
  rw [show (singleObjXSelf (ComplexShape.down ℕ) (n + 1) Work.Subdivision.unitMod.{u}).hom.hom
      ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod.{u}).inv.hom (ULift.up c : ULift.{u} ℤ))
      = (ULift.up c : ULift.{u} ℤ) from by
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]]

/-- The value of `spanMap` on a multiple of the generator of `ULift ℤ`. -/
theorem spanMap_up {M : ModuleCat ℤ} (x : M) (c : ℤ) :
    Work.Subdivision.PolyCW.spanMap x (ULift.up c) = c • x := by
  have hc : (ULift.up c : ULift ℤ) = c • (ULift.up (1 : ℤ) : ULift ℤ) := by
    apply ULift.ext
    rw [ULift.smul_down, ULift.down_up, ULift.down_up]
    simp
  rw [hc, map_smul, Work.Subdivision.spanMap_one]

/-- The degreewise linear equivalence between the two model complexes, in both
universes: the `singleObjXSelf`-isomorphism, the canonical `ULift`-equivalence of
`ℤ`, and the `singleObjXSelf`-isomorphism again. -/
noncomputable def kUnitEquiv (n : ℕ) : ∀ k : ℕ,
    ↥((Work.Subdivision.unitCx.{u} (n + 1)).X k) ≃ₗ[ℤ]
      ↥((Work.Subdivision.unitCx.{0} (n + 1)).X k) := fun k => by
  by_cases hk : k = n + 1
  · subst hk
    exact kUnitEquivTop n
  · refine LinearEquiv.ofBijective (0 : ↥((Work.Subdivision.unitCx.{u} (n + 1)).X k) →ₗ[ℤ]
      ↥((Work.Subdivision.unitCx.{0} (n + 1)).X k)) ⟨?_, ?_⟩
    · intro a b _
      haveI : Subsingleton ↥((Work.Subdivision.unitCx.{u} (n + 1)).X k) :=
        Work.Subdivision.unitCx_subsingleton hk
      exact Subsingleton.elim a b
    · intro b
      refine ⟨0, ?_⟩
      haveI : Subsingleton ↥((Work.Subdivision.unitCx.{0} (n + 1)).X k) :=
        Work.Subdivision.unitCx_subsingleton hk
      exact Subsingleton.elim _ _

theorem kUnitEquiv_self (n : ℕ) : kUnitEquiv n (n + 1) = kUnitEquivTop n := by
  rw [kUnitEquiv]
  rw [dif_pos rfl]

/-- The model complexes have only trivial differentials, so the comparison of the
two universes commutes with them. -/
theorem kUnitEquiv_comm (n : ℕ) (k : ℕ)
    (x : ↥((Work.Subdivision.unitCx.{u} (n + 1)).X (k + 1))) :
    kUnitEquiv n k ((Work.Subdivision.unitCx.{u} (n + 1)).d (k + 1) k x)
      = (Work.Subdivision.unitCx.{0} (n + 1)).d (k + 1) k (kUnitEquiv n (k + 1) x) := by
  by_cases hk : k = n + 1
  · haveI : Subsingleton ↥((Work.Subdivision.unitCx.{u} (n + 1)).X (k + 1)) :=
      Work.Subdivision.unitCx_subsingleton (by omega)
    rw [Subsingleton.elim x 0]
    simp only [map_zero]
  · haveI : Subsingleton ↥((Work.Subdivision.unitCx.{0} (n + 1)).X k) :=
      Work.Subdivision.unitCx_subsingleton hk
    exact Subsingleton.elim _ _

/-! ## The comparison map on the piece quotients -/

/-- The membership of the image of the generator of `C` in the new level of `K`. -/
theorem kz_mem_kMod_insert (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    A.z (n + 1) f₀ ∈ KMod A n (insert f₀ E) (n + 1) := by
  rw [← kPsiK_subdivCell A n f₀]
  exact kPsiK_mem_kMod_insert A n E f₀ (n + 1) _

/-- The value of the quotient map on the generator of the `C`-piece. -/
theorem quotMap_cPieceGen (A : CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    (((CPiece (C := C) n E f₀).quotMap (KPiece A n E f₀)
        (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀)).f (n + 1)) (cPieceGen A n E f₀)
      = Submodule.Quotient.mk
          (⟨A.z (n + 1) f₀, kz_mem_kMod_insert A n E f₀⟩ :
            ↥(KMod A n (insert f₀ E) (n + 1))) := by
  rw [cPieceGen, Work.Subdivision.quotMap_apply_mk]
  congr 1
  refine Subtype.ext ?_
  show (A.zMap h).f (n + 1) (cGen C (n + 1) f₀) = A.z (n + 1) f₀
  rw [zMap_f]
  show A.zMapFun (n + 1) (Pi.single f₀ (1 : ℤ)) = A.z (n + 1) f₀
  exact zMapFun_piSingle A (n + 1) f₀

/-- The class of `A.z (n+1) f₀` is the image of the local class of the subdivision
chain under the comparison map. -/
theorem kPieceMapLin_locClsAux (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    kPieceMapLin A n E f₀ (n + 1)
        (Work.Subdivision.PolyCW.locClsAux P (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩)
      = Submodule.Quotient.mk
          (⟨A.z (n + 1) f₀, kz_mem_kMod_insert A n E f₀⟩ :
            ↥(KMod A n (insert f₀ E) (n + 1))) := by
  rw [Work.Subdivision.PolyCW.locClsAux_eq,
    kPieceMapLin_apply A n E f₀ (n + 1)
      ⟨Work.Subdivision.PolyCW.subdivCell P (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩,
        Work.Subdivision.PolyCW.subdivCell_mem_leSub P (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩⟩]
  congr 1
  exact Subtype.ext (kPsiK_subdivCell A n f₀)

/-- The degreewise linear equivalence between the local complex of the new cell and
the piece quotient of the `K`-side filtration. -/
noncomputable def kPieceEquiv (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ) :
    ↥((Work.Subdivision.PolyCW.locCx P (A.root (n + 1) f₀)).X k) ≃ₗ[ℤ]
      ↥((KPiece A n E f₀).quot.X k) :=
  LinearEquiv.ofBijective (kPieceMapLin A n E f₀ k) (kPieceMapLin_bijective A n E f₀ hf k)

theorem kPieceEquiv_apply (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ)
    (x : ↥((Work.Subdivision.PolyCW.locCx P (A.root (n + 1) f₀)).X k)) :
    (kPieceEquiv A n E f₀ hf k) x = kPieceMapLin A n E f₀ k x := rfl

/-- The comparison map commutes with the differentials, as linear maps. -/
theorem kPieceEquiv_comm (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ)
    (x : ↥((Work.Subdivision.PolyCW.locCx P (A.root (n + 1) f₀)).X (k + 1))) :
    (kPieceEquiv A n E f₀ hf k)
        ((Work.Subdivision.PolyCW.locCx P (A.root (n + 1) f₀)).d (k + 1) k x)
      = ((KPiece A n E f₀).quot).d (k + 1) k (kPieceEquiv A n E f₀ hf (k + 1) x) := by
  rw [kPieceEquiv_apply, kPieceEquiv_apply]
  rw [Work.Subdivision.PolyCW.locCx_d, Work.Subdivision.SubData.quot_d]
  simp only [ModuleCat.hom_ofHom]
  exact kPieceMapLin_comm_lin A n E f₀ k x

/-- The value of the local map of the new cell on a multiple of the generator of
the model complex. -/
theorem locMapAux_apply_gen (A : CellAtlas K P C) (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (n : ℕ) (f₀ : Fin (C.dim (n + 1))) (c : ℤ) :
    (Work.Subdivision.PolyCW.locMapAux P hdd haug (n + 1)
        ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩).f (n + 1)
        ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
          Work.Subdivision.unitMod.{u}).inv (ULift.up c : ULift.{u} ℤ))
      = c • Work.Subdivision.PolyCW.locClsAux P (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩ := by
  rw [Work.Subdivision.PolyCW.locMapAux_f_eq, ModuleCat.comp_apply]
  rw [show (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod.{u}).hom
        ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
          Work.Subdivision.unitMod.{u}).inv (ULift.up c : ULift.{u} ℤ))
      = (ULift.up c : ULift.{u} ℤ) from by
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]]
  exact spanMap_up _ c

/-- The value of the `C`-piece map on a multiple of the generator of the model
complex. -/
theorem cPieceMap_apply_gen (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (c : ℤ) :
    (cPieceMap A n E f₀).f (n + 1)
        ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
          Work.Subdivision.unitMod.{0}).inv (ULift.up c : ULift.{0} ℤ))
      = c • cPieceGen A n E f₀ := by
  rw [cPieceMap_f_succ, ModuleCat.comp_apply]
  rw [show (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod.{0}).hom
        ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
          Work.Subdivision.unitMod.{0}).inv (ULift.up c : ULift.{0} ℤ))
      = (ULift.up c : ULift.{0} ℤ) from by
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]]
  rw [cPieceCoeffF]
  exact spanMap_up _ c

/-- The comparison map carries the local generator to the class of `A.z (n+1) f₀`. -/
theorem kPieceEquiv_locClsAux (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) :
    kPieceEquiv A n E f₀ hf (n + 1)
        (Work.Subdivision.PolyCW.locClsAux P (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩)
      = Submodule.Quotient.mk
          (⟨A.z (n + 1) f₀, kz_mem_kMod_insert A n E f₀⟩ :
            ↥(KMod A n (insert f₀ E) (n + 1))) := by
  rw [kPieceEquiv_apply]
  exact kPieceMapLin_locClsAux A n E f₀

/-- **The compatibility of the two comparison maps on the generators.** -/
theorem kPiece_compat (A : CellAtlas K P C) (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (h : A.BoundaryCompat) (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ)
    (x : ↥((Work.Subdivision.unitCx.{u} (n + 1)).X k)) :
    (kPieceEquiv A n E f₀ hf k)
        ((Work.Subdivision.PolyCW.locMapAux P hdd haug (n + 1)
          ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩).f k x)
      = (((cPieceMap A n E f₀) ≫ ((CPiece (C := C) n E f₀).quotMap (KPiece A n E f₀)
          (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀))).f k) (kUnitEquiv n k x) := by
  by_cases hk : k = n + 1
  · subst hk
    obtain ⟨c, hc⟩ : ∃ c : ℤ, (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod.{u}).hom.hom x = (ULift.up c : ULift.{u} ℤ) :=
      ⟨((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
          Work.Subdivision.unitMod.{u}).hom.hom x).down, by
        cases (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
          Work.Subdivision.unitMod.{u}).hom.hom x
        rfl⟩
    have hx : x = (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
        Work.Subdivision.unitMod.{u}).inv (ULift.up c : ULift.{u} ℤ) := by
      rw [← hc]
      rw [show (singleObjXSelf (ComplexShape.down ℕ) (n + 1)
          Work.Subdivision.unitMod.{u}).inv
          ((singleObjXSelf (ComplexShape.down ℕ) (n + 1)
            Work.Subdivision.unitMod.{u}).hom.hom x) = x from by
        rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]]
    rw [hx, kUnitEquiv_self, kUnitEquivTop_gen]
    rw [locMapAux_apply_gen, HomologicalComplex.comp_f, ModuleCat.comp_apply,
      cPieceMap_apply_gen]
    rw [map_smul, map_smul, kPieceEquiv_locClsAux, quotMap_cPieceGen]
  · haveI : Subsingleton ↥((Work.Subdivision.unitCx.{u} (n + 1)).X k) :=
      Work.Subdivision.unitCx_subsingleton hk
    rw [Subsingleton.elim x 0]
    simp only [map_zero]


theorem quasiIso_levelMap_insert_aux (A : CellAtlas K P C) (hdd : P.HasDdZero)
    (haug : P.HasAugZero) (hsp : P.LocallySpherical hdd haug) (h : A.BoundaryCompat) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E)
    (ih : QuasiIso (levelMap A h n E)) :
    QuasiIso (levelMap A h n (insert f₀ E)) := by
  have hlevel : QuasiIso ((CSD (C := C) n E).restrictMap (KSD A n E) (A.zMap h)
      (levelHf A h n E)) := ih
  have hpiece : QuasiIso ((CPiece (C := C) n E f₀).restrictMap (KPiece A n E f₀)
      (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀)) :=
    Work.Subdivision.quasiIso_of_iso_square
      (Work.Subdivision.SubData.comapChainIso (CSD (C := C) n (insert f₀ E)) (CMod C n E)
        (fun k => CMod_mono (Finset.subset_insert f₀ E) k) (CSD (C := C) n E).d_mem)
      (Work.Subdivision.SubData.comapChainIso (KSD A n (insert f₀ E)) (KMod A n E)
        (fun k => KMod_mono (Finset.subset_insert f₀ E) k) (KSD A n E).d_mem)
      ((Work.Subdivision.SubData.mk (CMod C n E) (CSD (C := C) n E).d_mem).restrictMap
        (Work.Subdivision.SubData.mk (KMod A n E) (KSD A n E).d_mem) (A.zMap h)
        (levelHf A h n E))
      ((CPiece (C := C) n E f₀).restrictMap (KPiece A n E f₀)
        (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀))
      (Work.Subdivision.comapChainIso_restrictMap_comm (CSD (C := C) n (insert f₀ E))
        (CMod C n E) (fun k => CMod_mono (Finset.subset_insert f₀ E) k)
        (CSD (C := C) n E).d_mem
        (KSD A n (insert f₀ E)) (KMod A n E)
        (fun k => KMod_mono (Finset.subset_insert f₀ E) k) (KSD A n E).d_mem
        (A.zMap h) (levelHf A h n (insert f₀ E)) (levelHf A h n E))
      hlevel
  let g : Work.Subdivision.unitCx.{0} (n + 1) ⟶ (KPiece A n E f₀).quot :=
    (cPieceMap A n E f₀) ≫ ((CPiece (C := C) n E f₀).quotMap (KPiece A n E f₀)
      (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀))
  have hq : QuasiIso g :=
    (Work.HomologyIso.quasiIso_iff_of_conj (Universe := (PUnit : Type))
      (u := (PUnit.unit : PUnit)) (kPieceEquiv A n E f₀ hf)
      (kPieceEquiv_comm A n E f₀ hf) (kUnitEquiv n) (kUnitEquiv_comm n)
      (Work.Subdivision.PolyCW.locMapAux P hdd haug (n + 1)
        ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩)
      g (kPiece_compat A hdd haug h n E f₀ hf)).mp
      (Work.Subdivision.PolyCW.locMapAux_quasiIso P hdd haug hsp (n + 1)
        ⟨A.root (n + 1) f₀, A.dim_root (n + 1) f₀⟩)
  have h₃ : QuasiIso (((CPiece (C := C) n E f₀).quotMap (KPiece A n E f₀)
      (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀))) := by
    haveI : IsIso (cPieceMap A n E f₀) := cPieceMap_isIso A n E f₀ hf
    refine Work.Subdivision.quasiIso_of_iso_square (e := (asIso (cPieceMap A n E f₀)).symm)
      (e' := Iso.refl ((KPiece A n E f₀).quot)) (f := g)
      (f' := ((CPiece (C := C) n E f₀).quotMap (KPiece A n E f₀)
        (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀))) ?_ hq
    rw [show (Iso.refl ((KPiece A n E f₀).quot)).hom = 𝟙 ((KPiece A n E f₀).quot) from rfl,
      Category.comp_id]
    exact Iso.inv_hom_id_assoc _ _
  exact Work.Subdivision.quasiIso_of_sub_quot (CPiece (C := C) n E f₀) (KPiece A n E f₀)
    (levelMap A h n (insert f₀ E)) (pieceHf A h n E f₀) (Work.Subdivision.incl_proj _)
    (Work.Subdivision.incl_proj _) hpiece h₃


end Insert

/-- **The induction step of the cell-by-cell refinement of the atlas filtration.** -/
theorem quasiIso_levelMap_insert {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx} (A : Work.MbarHomology.CellAtlas K P C) (hdd : P.HasDdZero) (haug : P.HasAugZero) (hsp : P.LocallySpherical hdd haug) (h : A.BoundaryCompat) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (ih : QuasiIso (Work.MbarHomology.CellAtlas.levelMap A h n E)) : QuasiIso (Work.MbarHomology.CellAtlas.levelMap A h n (insert f₀ E)) :=
  Work.MbarHomology.CellAtlas.Insert.quasiIso_levelMap_insert_aux A hdd haug hsp h n E f₀ hf ih

end CellAtlas

end

end Work.MbarHomology
