import Mathlib
import Submission.Work.Pi6.MSS.e2Canon
import Submission.Work.Pi6.MSS.e1SerreIso_gen
import Submission.Work.Pi6.MSS.serreE1CoefIsoIso_iota_single
import Submission.Work.Pi6.MSS.cochain_apply_fromNorm_iota

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Simplicial

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Elementary bookkeeping -/

private lemma iso_inv_hom_apply {𝕜 : Type} [Ring 𝕜] {M N : ModuleCat 𝕜} (e : M ≅ N) (y : ↥M) :
    (ModuleCat.Hom.hom e.inv) ((ModuleCat.Hom.hom e.hom) y) = y := by
  have h := congrArg (fun (f : M ⟶ M) => (ModuleCat.Hom.hom f) y) (Iso.hom_inv_id e)
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h

private lemma dualMap_symm_apply {𝕜 : Type} [CommSemiring 𝕜] {U W : Type*}
    [AddCommMonoid U] [Module 𝕜 U] [AddCommMonoid W] [Module 𝕜 W]
    (e : U ≃ₗ[𝕜] W) (Y : U →ₗ[𝕜] 𝕜) (x : U) :
    (LinearEquiv.dualMap e).symm Y (e x) = Y x := by
  have h : (LinearEquiv.dualMap e) ((LinearEquiv.dualMap e).symm Y) = Y :=
    LinearEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun (f : U →ₗ[𝕜] 𝕜) => f x) h
  simpa only [LinearEquiv.dualMap_apply] using h2

/-- `e2CanonH` is the transpose of the inverse of `psiE2`, hence it cancels `psiE2`. -/
theorem e2CanonH_psiE2 (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    (X : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).homology s →ₗ[𝕜] 𝕜)
    (y : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).homology s) :
    e2CanonH 𝕜 E B p e₀ hfib hconn s q X
      (psiE2 𝕜 E B p e₀ hfib hconn q s y) = X y := by
  simp only [e2CanonH, psiE2, LinearEquiv.dualMap_apply, CategoryTheory.Iso.toLinearEquiv_apply,
    CategoryTheory.Iso.symm_hom]
  congr 1
  exact iso_inv_hom_apply _ _

/-- `e2CanonG` is the transpose of the inverse of `kunnethCompIso`, hence it cancels
`kunnethCompIso`. -/
theorem e2CanonG_kunnethCompIso (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B]
    (M : ModuleCat 𝕜) (s : ℕ)
    (Y : (TensorProduct 𝕜 (↥((normC 𝕜 B).homology s)) (↥M)) →ₗ[𝕜] 𝕜)
    (x : TensorProduct 𝕜 (↥((normC 𝕜 B).homology s)) (↥M)) :
    e2CanonG 𝕜 B M s Y (kunnethCompIso 𝕜 B M s x) = Y x :=
  dualMap_symm_apply _ _ _

/-- `e2CanonStep` on a pure tensor of arguments. -/
theorem e2CanonStep_tmul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    [FiniteDimensional 𝕜 (Work.SSSR.coefM (R := 𝕜) p e₀ q)]
    (a : Work.Pi6.Coh 𝕜 B s) (b : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (x : ↥((normC 𝕜 B).homology s)) (y : ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) :
    e2CanonStep 𝕜 E B p e₀ hfib hconn s q (TensorProduct.tmul 𝕜 a b)
      (TensorProduct.tmul 𝕜 x y)
      = kappaB 𝕜 B s a x * kappaFe 𝕜 E B p e₀ hfib hconn q b y := by
  simp only [e2CanonStep, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    Work.Pi6.MSS.phiLin_tmul]

/-- The value of `kappaB` on the class of a cycle, for a skeletal cocycle. -/
theorem kappaB_clsB_cycle (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ)
    (β : ↥(ZB 𝕜 B s)) (z : (normC 𝕜 B).cycles s) :
    kappaB 𝕜 B s (clsB 𝕜 B s β) ((normC 𝕜 B).homologyπ s z)
      = β.1 (((SSet.fromNormalizedChainComplex (SSS.sSing B) (ModuleCat.of 𝕜 𝕜)).f s).hom
              ((ModuleCat.Hom.hom ((normC 𝕜 B).iCycles s)) z)) := by
  rw [clsB_apply]
  exact kappaB_apply 𝕜 B s β.1 β.2.1 z

/-- The computation rule of `kunnethIso` on a pure tensor. -/
lemma kunnethIso_tmul (𝕜 : Type) [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ)
    (M : ModuleCat 𝕜) (s : ℕ) (m : ↥M) (z : ↥(C.homology s)) :
    kunnethIso 𝕜 C M s (TensorProduct.tmul 𝕜 z m)
      = (HomologicalComplex.homologyMap (tensUnit C M m) s).hom z := by
  have h := congrArg
    (fun (g : ↥(C.homology s) →ₗ[𝕜] ↥((Work.Pi6.MSS.expTens 𝕜 C M).homology s)) => g z)
    (Work.Pi6.MSS.kunnethIso_apply 𝕜 C M s m)
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearEquiv.coe_toLinearMap] using h

/-! ## The chain-level functional `Λ` and its descent to homology -/

/-- The abbreviation for the tensor complex `N_*(B) ⊗ H_q(F)`. -/
abbrev Ktc (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (q : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)

/-- The coefficient extension `N_*(B;𝕜) ⊗ H_q(F)`. -/
abbrev Kte (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (q : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.Pi6.MSS.expTens 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)

/-- `β` as a functional on the normalized chains of `B`. -/
noncomputable def betaChainF (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ)
    (β : ↥(ZB 𝕜 B s)) : ↥((normC 𝕜 B).X s) →ₗ[𝕜] 𝕜 :=
  β.1.comp ((SSet.fromNormalizedChainComplex (SSS.sSing B) (ModuleCat.of 𝕜 𝕜)).f s).hom

/-- The elementwise computation rule of the coefficient-unit chain map. -/
lemma tensUnit_f_apply (𝕜 : Type) [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (M : ModuleCat 𝕜)
    (m : ↥M) (n : ℕ) (x : ↥(C.X n)) :
    (ModuleCat.Hom.hom ((tensUnit C M m).f n)) x = TensorProduct.tmul 𝕜 x m := by
  simp only [tensUnit, ModuleCat.hom_ofHom, LinearMap.flip_apply, TensorProduct.mk_apply]

/-- The pairing of `β` with the `N_*(B)`-factor and of `f` with the coefficient factor. -/
noncomputable def pairingLin (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (↥((normC 𝕜 B).X (s+1)) ⊗[𝕜] ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) →ₗ[𝕜] 𝕜 :=
  (TensorProduct.lid 𝕜 𝕜).toLinearMap.comp
    (TensorProduct.map (betaChainF 𝕜 B (s+1) β) (kappaF 𝕜 E B p e₀ hfib hconn q f))

lemma pairingLin_tmul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (a : ↥((normC 𝕜 B).X (s+1))) (m : ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) :
    pairingLin 𝕜 E B p e₀ hfib hconn s q β f (TensorProduct.tmul 𝕜 a m)
      = betaChainF 𝕜 B (s+1) β a * kappaF 𝕜 E B p e₀ hfib hconn q f m := by
  simp only [pairingLin, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]

private lemma cocycle_apply_d (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ)
    (β : ↥(ZB 𝕜 B (s+1))) :
    ∀ z : ↥(((SSS.sSing B).chainComplex (ModuleCat.of 𝕜 𝕜)).X (s+2)),
      β.1 ((((SSS.sSing B).chainComplex (ModuleCat.of 𝕜 𝕜)).d (s+2) (s+1)).hom z) = 0 := by
  have hβ : Work.Cohomology.cochainDiff 𝕜 (SSS.sSing B) β.1 = 0 := by
    have h2 : (Work.Cohomology.cochainDiffLM 𝕜 (SSS.sSing B) (s+1)) β.1 = 0 := β.2.1
    rw [Work.Cohomology.cochainDiffLM_apply] at h2
    exact h2
  intro z
  have h : β.1.comp ((((SSS.sSing B).chainComplex (ModuleCat.of 𝕜 𝕜)).d (s+2) (s+1)).hom) = 0 := by
    rw [← hβ]
    rfl
  exact congrArg (fun f => f z) h

lemma betaChainF_boundary (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ)
    (β : ↥(ZB 𝕜 B (s+1))) (a : ↥((normC 𝕜 B).X (s+2))) :
    betaChainF 𝕜 B (s+1) β ((ModuleCat.Hom.hom ((normC 𝕜 B).d (s+2) (s+1))) a) = 0 := by
  show β.1 (((SSet.fromNormalizedChainComplex (SSS.sSing B) (ModuleCat.of 𝕜 𝕜)).f (s+1)).hom
    (((normC 𝕜 B).d (s+2) (s+1)).hom a)) = 0
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.Hom.comm, ModuleCat.comp_apply]
  exact cocycle_apply_d 𝕜 B s β _

/-- The pairing `β ⊗ κF` kills boundaries of the coefficient extension. -/
lemma pairingLin_boundary (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (u : ↥((Kte 𝕜 B p e₀ q).X (s+2))) :
    pairingLin 𝕜 E B p e₀ hfib hconn s q β f ((Kte 𝕜 B p e₀ q).d (s+2) (s+1) u) = 0 := by
  rw [Work.Pi6.MSS.expTens_d_eq 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+2) (s+1)]
  simp only [ModuleCat.hom_whiskerRight]
  change pairingLin 𝕜 E B p e₀ hfib hconn s q β f
    ((LinearMap.rTensor ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)
      ((normC 𝕜 B).d (s+2) (s+1)).hom) u) = 0
  induction u using TensorProduct.inductionOn with
  | tmul a m => rw [LinearMap.rTensor_tmul, pairingLin_tmul, betaChainF_boundary, zero_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- The chain-level functional `Λ_chain = (β ⊗ κFf) ∘ collapseX` on the tensor complex. -/
noncomputable def LambdaChain (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (Ktc 𝕜 B p e₀ q).X (s+1) →ₗ[𝕜] 𝕜 :=
  (pairingLin 𝕜 E B p e₀ hfib hconn s q β f).comp
    (Work.SSSR.collapseX (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1)).hom

lemma lambdaChain_splitX (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (v : ↥((normC 𝕜 B).X (s+1)) ⊗[𝕜] ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) :
    LambdaChain 𝕜 E B p e₀ hfib hconn s q β f
        ((ModuleCat.Hom.hom (Work.SSSR.splitX (normC 𝕜 B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1))) v)
      = pairingLin 𝕜 E B p e₀ hfib hconn s q β f v := by
  change (pairingLin 𝕜 E B p e₀ hfib hconn s q β f)
      ((ModuleCat.Hom.hom (Work.SSSR.collapseX (normC 𝕜 B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1)))
        ((ModuleCat.Hom.hom (Work.SSSR.splitX (normC 𝕜 B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1))) v))
    = (pairingLin 𝕜 E B p e₀ hfib hconn s q β f) v
  congr 1
  have h2 := congrArg (fun (f : MonoidalCategoryStruct.tensorObj ((normC 𝕜 B).X (s+1))
      (Work.SSSR.coefM (R := 𝕜) p e₀ q) ⟶ MonoidalCategoryStruct.tensorObj ((normC 𝕜 B).X (s+1))
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)) => f.hom v)
    (Work.SSSR.splitX_collapseX (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1))
  rw [ModuleCat.comp_apply, ModuleCat.id_apply] at h2
  exact h2

/-- The degreewise components of `tensorComplexIsoExpTensIso` are `collapseX`. -/
lemma tensorComplexIsoExpTensIso_hom_f (𝕜 : Type) [Field 𝕜] {K : ChainComplex (ModuleCat 𝕜) ℕ}
    (M : ModuleCat 𝕜) (n : ℕ) :
    (Work.SSSR.tensorComplexIsoExpTensIso K M).hom.f n = Work.SSSR.collapseX K M n := by
  haveI hi : IsIso (Work.SSSR.splitX K M n) :=
    ⟨Work.SSSR.collapseX K M n, Work.SSSR.splitX_collapseX K M n, Work.SSSR.collapseX_splitX K M n⟩
  have hcomp := congrArg (fun (f : Work.SSSR.expTens K M ⟶ Work.SSSR.expTens K M) => f.f n)
      (Iso.inv_hom_id (Work.SSSR.tensorComplexIsoExpTensIso K M))
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hcomp
  rw [show (Work.SSSR.tensorComplexIsoExpTensIso K M).inv.f n = Work.SSSR.splitX K M n from rfl] at hcomp
  refine (cancel_epi (Work.SSSR.splitX K M n)).mp ?_
  exact hcomp.trans (Work.SSSR.splitX_collapseX K M n).symm

/-- A cycle of the coefficient extension is a cycle for the differential in the `next` direction. -/
lemma d_iCycles_Kte (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (q s : ℕ) (c : ↥((Kte 𝕜 B p e₀ q).cycles (s+1))) :
    ((Kte 𝕜 B p e₀ q).d (s+1) ((ComplexShape.down ℕ).next (s+1))).hom
      (((Kte 𝕜 B p e₀ q).iCycles (s+1)).hom c) = 0 := by
  have h : (((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).hom c) :
      ↥((Kte 𝕜 B p e₀ q).X (s+1))) = ((Kte 𝕜 B p e₀ q).iCycles (s+1)).hom c :=
    Work.Pi6.MSS.cycZIso_hom_val (Kte 𝕜 B p e₀ q) (s+1) c
  rw [← h, Work.Cohomology.down_next]
  exact ((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).hom c).2

/-- A cycle of the normalized chain complex is a cycle for the differential in the `next`
direction. -/
lemma d_iCycles_normC (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (n : ℕ)
    (c : ↥((normC 𝕜 B).cycles n)) :
    ((normC 𝕜 B).d n ((ComplexShape.down ℕ).next n)).hom (((normC 𝕜 B).iCycles n).hom c) = 0 := by
  have h : (((Work.Pi6.MSS.cycZIso 𝕜 (normC 𝕜 B) n).hom c) :
      ↥((normC 𝕜 B).X n)) = ((normC 𝕜 B).iCycles n).hom c :=
    Work.Pi6.MSS.cycZIso_hom_val (normC 𝕜 B) n c
  rw [← h, Work.Cohomology.down_next]
  exact ((Work.Pi6.MSS.cycZIso 𝕜 (normC 𝕜 B) n).hom c).2

/-- The pairing restricted to the cycles of the coefficient extension. -/
noncomputable def LambdaZB (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    ↥(Work.StemsB.fdZ 𝕜 (Kte 𝕜 B p e₀ q) (s+1)) →ₗ[𝕜] 𝕜 :=
  (pairingLin 𝕜 E B p e₀ hfib hconn s q β f).comp
    (Work.StemsB.fdZ 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).subtype

/-- `LambdaZB` vanishes on the boundaries inside the cycles. -/
lemma LambdaZB_ker (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) (s+1)
      ≤ LinearMap.ker (LambdaZB 𝕜 E B p e₀ hfib hconn s q β f) := by
  intro x hx
  show (LambdaZB 𝕜 E B p e₀ hfib hconn s q β f) x = 0
  change pairingLin 𝕜 E B p e₀ hfib hconn s q β f
    (x : ↥((Kte 𝕜 B p e₀ q).X (s+1))) = 0
  have hx' : (x : ↥((Kte 𝕜 B p e₀ q).X (s+1))) ∈ Work.StemsB.fdB 𝕜 (Kte 𝕜 B p e₀ q) (s+1) :=
    (Work.StemsB.mem_fdH 𝕜 (Kte 𝕜 B p e₀ q) (s+1) x).mp hx
  obtain ⟨u, hu⟩ := (LinearMap.mem_range).mp hx'
  rw [← hu]
  exact pairingLin_boundary 𝕜 E B p e₀ hfib hconn s q β f u

/-- **The descent of the chain-level pairing to the homology of the coefficient extension.** -/
noncomputable def LambdaBar (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (Kte 𝕜 B p e₀ q).homology (s+1) →ₗ[𝕜] 𝕜 :=
  (Submodule.liftQ (Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) (s+1))
      (LambdaZB 𝕜 E B p e₀ hfib hconn s q β f)
      (LambdaZB_ker 𝕜 E B p e₀ hfib hconn s q β f)).comp
    (Work.Pi6.MSS.homZBIso 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).hom.hom

lemma LambdaBar_cyclesMk (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (y : ↥((Kte 𝕜 B p e₀ q).X (s+1)))
    (hy : (Kte 𝕜 B p e₀ q).d (s+1) ((ComplexShape.down ℕ).next (s+1)) y = 0) :
    LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
      ((Kte 𝕜 B p e₀ q).homologyπ (s+1) ((Kte 𝕜 B p e₀ q).cyclesMk y ((ComplexShape.down ℕ).next (s+1)) rfl hy))
      = pairingLin 𝕜 E B p e₀ hfib hconn s q β f y := by
  rw [LambdaBar, LinearMap.comp_apply, Work.Pi6.MSS.homZBIso_apply]
  show ((Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).liftQ
      (LambdaZB 𝕜 E B p e₀ hfib hconn s q β f)
      (LambdaZB_ker 𝕜 E B p e₀ hfib hconn s q β f))
      ((Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).mkQ
        ((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).hom
          ((Kte 𝕜 B p e₀ q).cyclesMk y ((ComplexShape.down ℕ).next (s+1)) rfl hy)))
    = pairingLin 𝕜 E B p e₀ hfib hconn s q β f y
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  change pairingLin 𝕜 E B p e₀ hfib hconn s q β f
      (((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) (s+1)).hom
        ((Kte 𝕜 B p e₀ q).cyclesMk y ((ComplexShape.down ℕ).next (s+1)) rfl hy)) :
          ↥((Kte 𝕜 B p e₀ q).X (s+1))) = pairingLin 𝕜 E B p e₀ hfib hconn s q β f y
  rw [Work.Pi6.MSS.cycZIso_hom_val, Work.SSSR.hmcm_iCycles_cyclesMk]

/-- The value of `Λ_bar` on the class of a cycle. -/
lemma LambdaBar_cycle (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (c : ↥((Kte 𝕜 B p e₀ q).cycles (s+1))) :
    LambdaBar 𝕜 E B p e₀ hfib hconn s q β f ((Kte 𝕜 B p e₀ q).homologyπ (s+1) c)
      = pairingLin 𝕜 E B p e₀ hfib hconn s q β f
          (((Kte 𝕜 B p e₀ q).iCycles (s+1)).hom c) := by
  rw [show (Kte 𝕜 B p e₀ q).homologyπ (s+1) c
      = (Kte 𝕜 B p e₀ q).homologyπ (s+1)
          ((Kte 𝕜 B p e₀ q).cyclesMk (((Kte 𝕜 B p e₀ q).iCycles (s+1)).hom c)
            ((ComplexShape.down ℕ).next (s+1)) rfl (d_iCycles_Kte 𝕜 E B p e₀ q s c))
      from congrArg _ (Work.Pi6.MSS.cyclesMk_iCycles _ c _ rfl
        (d_iCycles_Kte 𝕜 E B p e₀ q s c)).symm]
  rw [LambdaBar_cyclesMk]

/-- The value of `Λ_bar` on the `collapseX`-image of a cycle class. -/
lemma LambdaBar_collapseX (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (c : ↥((Ktc 𝕜 B p e₀ q).cycles (s+1))) :
    LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
        ((HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q)).hom (s+1)).hom
          ((Ktc 𝕜 B p e₀ q).homologyπ (s+1) c))
      = LambdaChain 𝕜 E B p e₀ hfib hconn s q β f (((Ktc 𝕜 B p e₀ q).iCycles (s+1)).hom c) := by
  rw [Work.Pi6.MSS.homologyMap_homologyπ]
  rw [LambdaBar_cycle]
  rw [Work.Pi6.MSS.iCycles_cyclesMap]
  rw [tensorComplexIsoExpTensIso_hom_f]
  rfl

/-! ## The identity `Λ = Λ_bar ∘ Künneth` -/

/-- **The main identity**: the `E²`-pairing is the descent of the chain-level pairing composed
with the Künneth isomorphism. -/
lemma e2CanonStep_eq_LambdaBar (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    [FiniteDimensional 𝕜 (Work.SSSR.coefM (R := 𝕜) p e₀ q)]
    (β : ↥(ZB 𝕜 B (s+1))) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (x : TensorProduct 𝕜 (↥((normC 𝕜 B).homology (s+1)))
      (↥(Work.SSSR.coefM (R := 𝕜) p e₀ q))) :
    e2CanonStep 𝕜 E B p e₀ hfib hconn (s+1) q
        (TensorProduct.tmul 𝕜 (clsB 𝕜 B (s+1) β) f) x
      = LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
          (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z m =>
      obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective _).mp
        (inferInstance : Epi (HomologicalComplex.homologyπ (normC 𝕜 B) (s+1))) z
      rw [e2CanonStep_tmul, kappaB_clsB_cycle]
      change betaChainF 𝕜 B (s+1) β ((ModuleCat.Hom.hom ((normC 𝕜 B).iCycles (s+1))) c)
          * kappaF 𝕜 E B p e₀ hfib hconn q f m
        = LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
            (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1)
              (TensorProduct.tmul 𝕜
                ((HomologicalComplex.homologyπ (normC 𝕜 B) (s+1)) c) m))
      rw [kunnethIso_tmul]
      rw [show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (tensUnit (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) m) (s+1)))
            ((HomologicalComplex.homologyπ (normC 𝕜 B) (s+1)) c)
          = (Kte 𝕜 B p e₀ q).homologyπ (s+1)
              ((HomologicalComplex.cyclesMap (tensUnit (normC 𝕜 B)
                (Work.SSSR.coefM (R := 𝕜) p e₀ q) m) (s+1)) c)
          from Work.Pi6.MSS.homologyMap_homologyπ _ _ _]
      rw [LambdaBar_cycle]
      rw [Work.Pi6.MSS.iCycles_cyclesMap, tensUnit_f_apply, pairingLin_tmul]
  | add x y hx hy =>
      calc e2CanonStep 𝕜 E B p e₀ hfib hconn (s+1) q
            (TensorProduct.tmul 𝕜 (clsB 𝕜 B (s+1) β) f) (x + y)
          = e2CanonStep 𝕜 E B p e₀ hfib hconn (s+1) q
              (TensorProduct.tmul 𝕜 (clsB 𝕜 B (s+1) β) f) x
            + e2CanonStep 𝕜 E B p e₀ hfib hconn (s+1) q
              (TensorProduct.tmul 𝕜 (clsB 𝕜 B (s+1) β) f) y := map_add _ x y
        _ = LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
              (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1) x)
            + LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
              (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1) y) := by
            rw [hx, hy]
        _ = LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
              (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1) (x + y)) := by
            rw [map_add, map_add]

/-- The simplex underlying a nondegenerate simplex `σ`, read off at the top simplex of `Δ[s+1]`. -/
lemma sigHat_app_topS (B : Type) [TopologicalSpace B] (s : ℕ)
    (σ : Work.SSSR.nIndex (SSS.sSing B) (s+1)) :
    (Work.SSSR.sigHat σ).app (Opposite.op (SimplexCategory.mk (s+1)))
        (Work.Pi6.MSSK.topS (s+1))
      = Work.SSSR.nIndexBase (SSS.sSing B) σ := by
  rw [Work.SSSR.sigHat, Work.Pi6.MSSK.topS, Work.SSSR.nIndexSigma_app]
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A skeletal cocycle vanishes on every degenerate simplex. -/
lemma ZB_kills_degenerate (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (n : ℕ)
    (β : ↥(ZB 𝕜 B n)) (x : (SSS.sSing B) _⦋n⦌) (hx : x ∈ (SSS.sSing B).degenerate n) :
    Work.Cohomology.genEval 𝕜 (SSS.sSing B) β.1 x = 0 :=
  ((Work.Pi6.MSS.mem_ZB 𝕜 (B := B) (s := n) (c := β.1)).mp β.2).2 x
    (ess_lt_of_mem_degenerate hx)

/-! ## The generator computation -/

/-- The chain functional `Λ_chain` is a linear map, so it commutes with finite sums. -/
private lemma LambdaChain_sum (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) {ι : Type} (t : Finset ι)
    (a : ι → 𝕜) (w : ι → ↥((Ktc 𝕜 B p e₀ q).X (s+1))) :
    LambdaChain 𝕜 E B p e₀ hfib hconn s q β f (∑ i ∈ t, a i • w i)
      = ∑ i ∈ t, a i • LambdaChain 𝕜 E B p e₀ hfib hconn s q β f (w i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])

/-- The value of `β` on a normalized generator is the evaluation of the cocycle on the simplex. -/
lemma betaChainF_iota (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (n : ℕ)
    (β : ↥(ZB 𝕜 B n)) (x : (SSS.sSing B) _⦋n⦌) :
    betaChainF 𝕜 B n β (((SSS.sSing B).ιNormalizedChainComplex
        (R := ModuleCat.of 𝕜 𝕜) x).hom 1)
      = Work.Cohomology.genEval 𝕜 (SSS.sSing B) β.1 x := by
  show β.1 (((SSet.fromNormalizedChainComplex (SSS.sSing B)
      (ModuleCat.of 𝕜 𝕜)).f n).hom (((SSS.sSing B).ιNormalizedChainComplex
        (R := ModuleCat.of 𝕜 𝕜) x).hom 1))
    = Work.Cohomology.genEval 𝕜 (SSS.sSing B) β.1 x
  exact Work.Pi6.MSS.cochain_apply_fromNorm_iota 𝕜 (SSS.sSing B) n x β.1
    (fun y hy => ZB_kills_degenerate 𝕜 B n β y hy)

/-- **The value of `Λ_chain` on the canonical generator**: the sum of the products of the
`β`-values on the base simplices and the `κFf`-values on the fibre classes. -/
lemma LambdaChain_genElem (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) (β : ↥(ZB 𝕜 B (s+1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (n : ℕ) (lam : Fin n → 𝕜) (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0) :
    LambdaChain 𝕜 E B p e₀ hfib hconn s q β f (genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz)
      = ∑ j : Fin n, lam j *
          (betaChainF 𝕜 B (s+1) β
            (((SSS.sSing B).ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜)
              (Work.SSSR.nIndexBase (SSS.sSing B) (σ j))).hom 1)
          * kappaF 𝕜 E B p e₀ hfib hconn q f
              ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
                ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                  ((Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                    ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
  have hgen : ∀ j : Fin n,
      (Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1)).hom.hom
        ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1)
            => Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j)).hom
          ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                ((ComplexShape.down ℕ).next q) rfl (hz j)))))
      = Work.SSSR.splitX (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1)
          (TensorProduct.tmul 𝕜
            (((SSS.sSing B).ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜)
              (Work.SSSR.nIndexBase (SSS.sSing B) (σ j))).hom 1)
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j))))) := fun j =>
    Work.Pi6.MSS.serreE1CoefIsoIso_iota_single 𝕜 (Work.SSSR.sSing B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s+1) (σ j) _
  rw [genElem, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearMap.map_smul, LinearMap.map_smul, hgen j, lambdaChain_splitX, pairingLin_tmul,
    smul_eq_mul]

/-- The `inv`-componentwise form of the `hom_inv_id` of an isomorphism of `𝕜`-modules. -/
private lemma hom_iso_inv_apply {𝕜 : Type} [Ring 𝕜] {M N : ModuleCat 𝕜} (e : M ≅ N) (y : ↥N) :
    (ModuleCat.Hom.hom e.hom) ((ModuleCat.Hom.hom e.inv) y) = y := by
  have h := congrArg (fun (f : N ⟶ N) => (ModuleCat.Hom.hom f) y) (Iso.inv_hom_id e)
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h

/-- `kunnethIso` is the `homologyMap` of `tensorComplexIsoExpTensIso` composed with
`kunnethCompIso`. -/
lemma kunnethIso_eq_homologyMap_kunnethCompIso (𝕜 : Type) [Field 𝕜] (B : Type)
    [TopologicalSpace B] (M : ModuleCat 𝕜) (s : ℕ)
    (x : TensorProduct 𝕜 (↥((normC 𝕜 B).homology s)) (↥M)) :
    kunnethIso 𝕜 (normC 𝕜 B) M s x
      = (HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B) M).hom s).hom
          (kunnethCompIso 𝕜 B M s x) := by
  have hsplit : kunnethCompIso 𝕜 B M s x
      = (HomologicalComplex.homologyMapIso
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B) M) s).inv.hom
          (kunnethIso 𝕜 (normC 𝕜 B) M s x) := by
    rw [kunnethCompIso, LinearEquiv.trans_apply, CategoryTheory.Iso.toLinearEquiv_apply,
      CategoryTheory.Iso.symm_hom]
  rw [hsplit, ← HomologicalComplex.homologyMapIso_hom]
  exact (hom_iso_inv_apply _ _).symm

/-- The value of `kunnethIso` on the inverse image under `kunnethCompIso`. -/
lemma kunnethIso_symm_kunnethCompIso (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B]
    (M : ModuleCat 𝕜) (s : ℕ)
    (g : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) M).homology s) :
    kunnethIso 𝕜 (normC 𝕜 B) M s ((kunnethCompIso 𝕜 B M s).symm g)
      = (HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B) M).hom s).hom g := by
  rw [kunnethIso_eq_homologyMap_kunnethCompIso, LinearEquiv.apply_symm_apply]

theorem e2Canon_gen (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N) (β : ↥(Work.Pi6.MSS.ZB 𝕜 B (s + 1)))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (n : ℕ) (lam : Fin n → 𝕜)
    (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d (s + 1) ((ComplexShape.down ℕ).next (s + 1))
        (Work.Pi6.MSS.genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz) = 0) :
    (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin (s + 1) q hq
        (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B (s + 1) β) f))
      (Work.Pi6.MSS.psiE2 𝕜 E B p e₀ hfib hconn q (s + 1)
        (Work.Pi6.MSS.genCyc 𝕜 p e₀ hfib hconn s q n lam σ z hz hcyc))
    = ∑ j : Fin n, lam j *
        (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
          ((Work.SSSR.sigHat (σ j)).app (Opposite.op (SimplexCategory.mk (s + 1)))
            (Work.Pi6.MSSK.topS (s + 1)))) *
        (Work.Pi6.MSS.kappaF 𝕜 E B p e₀ hfib hconn q f
          (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom
            (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
                (Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))) q)
              (HomologicalComplex.cyclesMk
                (Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))) (z j)
                ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
  haveI hHq : FiniteDimensional 𝕜 (Work.SSSR.coefM (R := 𝕜) p e₀ q) := by
    haveI hCohF : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :=
      hfin q hq
    obtain ⟨eFib0⟩ := Work.StemsB.fieldDualUCT (F := 𝕜)
      (Work.Cohomology.singularChains 𝕜 (TopCat.of (Work.StemsB.fibre p (p e₀)))) q
    haveI hd : FiniteDimensional 𝕜 ((Work.Cohomology.dualComplex 𝕜
        (Work.Cohomology.singularChains 𝕜
          (TopCat.of (Work.StemsB.fibre p (p e₀))))).homology q) := hCohF
    haveI hdual : FiniteDimensional 𝕜 ((Work.SSSR.coefM (R := 𝕜) p e₀ q) →ₗ[𝕜] 𝕜) :=
      LinearEquiv.finiteDimensional (Iso.toLinearEquiv eFib0)
    exact finiteDimensional_of_finiteDimensional_dual 𝕜 _
  set g := Work.Pi6.MSS.genCyc 𝕜 p e₀ hfib hconn s q n lam σ z hz hcyc with hg
  have hL : Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin (s + 1) q hq
      (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B (s + 1) β) f)
      (Work.Pi6.MSS.psiE2 𝕜 E B p e₀ hfib hconn q (s + 1) g)
    = LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
        ((HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q)).hom (s + 1)).hom g) := by
    rw [show Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin (s + 1) q hq
        = (e2CanonStep 𝕜 E B p e₀ hfib hconn (s + 1) q).trans
            ((e2CanonG 𝕜 B (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s + 1)).trans
              (e2CanonH 𝕜 E B p e₀ hfib hconn (s + 1) q)) from rfl]
    simp only [LinearEquiv.trans_apply]
    rw [e2CanonH_psiE2]
    conv_lhs => rw [← LinearEquiv.apply_symm_apply
      (kunnethCompIso 𝕜 B (Work.SSSR.coefM (R := 𝕜) p e₀ q) (s + 1)) g]
    rw [e2CanonG_kunnethCompIso]
    rw [e2CanonStep_eq_LambdaBar 𝕜 E B p e₀ hfib hconn s q β f]
    rw [kunnethIso_symm_kunnethCompIso]
  have hR : LambdaBar 𝕜 E B p e₀ hfib hconn s q β f
        ((HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q)).hom (s + 1)).hom g)
      = ∑ j : Fin n, lam j *
          (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
            ((Work.SSSR.sigHat (σ j)).app (Opposite.op (SimplexCategory.mk (s + 1)))
              (Work.Pi6.MSSK.topS (s + 1)))) *
          (Work.Pi6.MSS.kappaF 𝕜 E B p e₀ hfib hconn q f
            (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom
              (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
                  (Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))) q)
                (HomologicalComplex.cyclesMk
                  (Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))) (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
    rw [show g = (Ktc 𝕜 B p e₀ q).homologyπ (s + 1)
        ((Ktc 𝕜 B p e₀ q).cyclesMk
          (Work.Pi6.MSS.genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz)
          ((ComplexShape.down ℕ).next (s + 1)) rfl hcyc) from rfl]
    rw [LambdaBar_collapseX 𝕜 E B p e₀ hfib hconn s q β f
      ((Ktc 𝕜 B p e₀ q).cyclesMk
        (Work.Pi6.MSS.genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz)
        ((ComplexShape.down ℕ).next (s + 1)) rfl hcyc)]
    rw [Work.SSSR.hmcm_iCycles_cyclesMk]
    rw [LambdaChain_genElem 𝕜 E B p e₀ hfib hconn s q β f n lam σ z hz]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [betaChainF_iota, ← sigHat_app_topS B s (σ j)]
    ring
  rw [hL, hR]

end

end Work.Pi6.MSS
