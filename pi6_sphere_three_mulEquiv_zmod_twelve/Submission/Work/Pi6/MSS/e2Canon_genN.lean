import Mathlib
import Submission.Work.Pi6.MSS.e2PsiCanonN
import Submission.Work.Pi6.MSS.e2Canon_gen
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The generator computation in arbitrary filtration degree

`Work.Pi6.MSS.e2Canon_gen` computes the canonical pairing on the generator `genElem` of
`N_{s+1}(B) ⊗ H_q(F)`, i.e. only in filtration degrees `≥ 1` (its first parameter `s` is the
Serre filtration index and the total degree is `s+1`).  This file reproduces the whole
development with the total degree `n` as the parameter, so that it also covers `n = 0`, and
proves the degree general generator computation `Work.Pi6.MSS.e2Canon_genN`.

Nothing here is mathematically new: every definition and every proof is the degree-`n` version of
the corresponding item of `Submission/Work/Pi6/MSS/e2Canon_gen.lean`, obtained by replacing the
degree `s + 1` by `n` (and `sigHat` by `nIndexSigma`, of which `sigHat` is an abbreviation, and
`genElem`/`genCyc` by their degree general twins `genElemN`/`genCycN`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Simplicial

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The chain-level functional in degree `n` -/

/-- The pairing of `β` with the `N_n(B)`-factor and of `f` with the coefficient factor, in degree
`n`. -/
noncomputable def pairingLinN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (↥((normC 𝕜 B).X n) ⊗[𝕜] ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) →ₗ[𝕜] 𝕜 :=
  (TensorProduct.lid 𝕜 𝕜).toLinearMap.comp
    (TensorProduct.map (betaChainF 𝕜 B n β) (kappaF 𝕜 E B p e₀ hfib hconn q f))

lemma pairingLinN_tmul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (a : ↥((normC 𝕜 B).X n)) (m : ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) :
    pairingLinN 𝕜 E B p e₀ hfib hconn n q β f (TensorProduct.tmul 𝕜 a m)
      = betaChainF 𝕜 B n β a * kappaF 𝕜 E B p e₀ hfib hconn q f m := by
  simp only [pairingLinN, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]

private lemma cocycle_apply_dN (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (n : ℕ)
    (β : ↥(ZB 𝕜 B n)) :
    ∀ z : ↥(((SSS.sSing B).chainComplex (ModuleCat.of 𝕜 𝕜)).X (n+1)),
      β.1 ((((SSS.sSing B).chainComplex (ModuleCat.of 𝕜 𝕜)).d (n+1) n).hom z) = 0 := by
  have hβ : Work.Cohomology.cochainDiff 𝕜 (SSS.sSing B) β.1 = 0 := by
    have h2 : (Work.Cohomology.cochainDiffLM 𝕜 (SSS.sSing B) n) β.1 = 0 := β.2.1
    rw [Work.Cohomology.cochainDiffLM_apply] at h2
    exact h2
  intro z
  have h : β.1.comp ((((SSS.sSing B).chainComplex (ModuleCat.of 𝕜 𝕜)).d (n+1) n).hom) = 0 := by
    rw [← hβ]
    rfl
  exact congrArg (fun f => f z) h

lemma betaChainFN_boundary (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (n : ℕ)
    (β : ↥(ZB 𝕜 B n)) (a : ↥((normC 𝕜 B).X (n+1))) :
    betaChainF 𝕜 B n β ((ModuleCat.Hom.hom ((normC 𝕜 B).d (n+1) n)) a) = 0 := by
  show β.1 (((SSet.fromNormalizedChainComplex (SSS.sSing B) (ModuleCat.of 𝕜 𝕜)).f n).hom
    (((normC 𝕜 B).d (n+1) n).hom a)) = 0
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.Hom.comm, ModuleCat.comp_apply]
  exact cocycle_apply_dN 𝕜 B n β _

/-- The pairing `β ⊗ κF` kills boundaries of the coefficient extension, in degree `n`. -/
lemma pairingLinN_boundary (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (u : ↥((Kte 𝕜 B p e₀ q).X (n+1))) :
    pairingLinN 𝕜 E B p e₀ hfib hconn n q β f ((Kte 𝕜 B p e₀ q).d (n+1) n u) = 0 := by
  rw [Work.Pi6.MSS.expTens_d_eq 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) (n+1) n]
  simp only [ModuleCat.hom_whiskerRight]
  change pairingLinN 𝕜 E B p e₀ hfib hconn n q β f
    ((LinearMap.rTensor ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)
      ((normC 𝕜 B).d (n+1) n).hom) u) = 0
  induction u using TensorProduct.inductionOn with
  | tmul a m => rw [LinearMap.rTensor_tmul, pairingLinN_tmul, betaChainFN_boundary, zero_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- The chain-level functional `Λ_chain = (β ⊗ κFf) ∘ collapseX` on the tensor complex, in
degree `n`. -/
noncomputable def LambdaChainN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (Ktc 𝕜 B p e₀ q).X n →ₗ[𝕜] 𝕜 :=
  (pairingLinN 𝕜 E B p e₀ hfib hconn n q β f).comp
    (Work.SSSR.collapseX (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n).hom

lemma lambdaChainN_splitX (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (v : ↥((normC 𝕜 B).X n) ⊗[𝕜] ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) :
    LambdaChainN 𝕜 E B p e₀ hfib hconn n q β f
        ((ModuleCat.Hom.hom (Work.SSSR.splitX (normC 𝕜 B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) n)) v)
      = pairingLinN 𝕜 E B p e₀ hfib hconn n q β f v := by
  change (pairingLinN 𝕜 E B p e₀ hfib hconn n q β f)
      ((ModuleCat.Hom.hom (Work.SSSR.collapseX (normC 𝕜 B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q) n))
        ((ModuleCat.Hom.hom (Work.SSSR.splitX (normC 𝕜 B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) n)) v))
    = (pairingLinN 𝕜 E B p e₀ hfib hconn n q β f) v
  congr 1
  have h2 := congrArg (fun (f : MonoidalCategoryStruct.tensorObj ((normC 𝕜 B).X n)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q) ⟶ MonoidalCategoryStruct.tensorObj ((normC 𝕜 B).X n)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)) => f.hom v)
    (Work.SSSR.splitX_collapseX (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n)
  rw [ModuleCat.comp_apply, ModuleCat.id_apply] at h2
  exact h2

/-- A cycle of the coefficient extension is a cycle for the differential in the `next` direction,
in degree `n`. -/
lemma d_iCycles_KteN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (q n : ℕ) (c : ↥((Kte 𝕜 B p e₀ q).cycles n)) :
    ((Kte 𝕜 B p e₀ q).d n ((ComplexShape.down ℕ).next n)).hom
      (((Kte 𝕜 B p e₀ q).iCycles n).hom c) = 0 := by
  have h : (((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) n).hom c) :
      ↥((Kte 𝕜 B p e₀ q).X n)) = ((Kte 𝕜 B p e₀ q).iCycles n).hom c :=
    Work.Pi6.MSS.cycZIso_hom_val (Kte 𝕜 B p e₀ q) n c
  rw [← h, Work.Cohomology.down_next]
  exact ((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) n).hom c).2

/-- The pairing restricted to the cycles of the coefficient extension, in degree `n`. -/
noncomputable def LambdaZBN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    ↥(Work.StemsB.fdZ 𝕜 (Kte 𝕜 B p e₀ q) n) →ₗ[𝕜] 𝕜 :=
  (pairingLinN 𝕜 E B p e₀ hfib hconn n q β f).comp
    (Work.StemsB.fdZ 𝕜 (Kte 𝕜 B p e₀ q) n).subtype

/-- `LambdaZBN` vanishes on the boundaries inside the cycles. -/
lemma LambdaZBN_ker (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) n
      ≤ LinearMap.ker (LambdaZBN 𝕜 E B p e₀ hfib hconn n q β f) := by
  intro x hx
  show (LambdaZBN 𝕜 E B p e₀ hfib hconn n q β f) x = 0
  change pairingLinN 𝕜 E B p e₀ hfib hconn n q β f
    (x : ↥((Kte 𝕜 B p e₀ q).X n)) = 0
  have hx' : (x : ↥((Kte 𝕜 B p e₀ q).X n)) ∈ Work.StemsB.fdB 𝕜 (Kte 𝕜 B p e₀ q) n :=
    (Work.StemsB.mem_fdH 𝕜 (Kte 𝕜 B p e₀ q) n x).mp hx
  obtain ⟨u, hu⟩ := (LinearMap.mem_range).mp hx'
  rw [← hu]
  exact pairingLinN_boundary 𝕜 E B p e₀ hfib hconn n q β f u

/-- **The descent of the chain-level pairing to the homology of the coefficient extension**, in
degree `n`. -/
noncomputable def LambdaBarN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (Kte 𝕜 B p e₀ q).homology n →ₗ[𝕜] 𝕜 :=
  (Submodule.liftQ (Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) n)
      (LambdaZBN 𝕜 E B p e₀ hfib hconn n q β f)
      (LambdaZBN_ker 𝕜 E B p e₀ hfib hconn n q β f)).comp
    (Work.Pi6.MSS.homZBIso 𝕜 (Kte 𝕜 B p e₀ q) n).hom.hom

lemma LambdaBarN_cyclesMk (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (y : ↥((Kte 𝕜 B p e₀ q).X n))
    (hy : (Kte 𝕜 B p e₀ q).d n ((ComplexShape.down ℕ).next n) y = 0) :
    LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
      ((Kte 𝕜 B p e₀ q).homologyπ n
        ((Kte 𝕜 B p e₀ q).cyclesMk y ((ComplexShape.down ℕ).next n) rfl hy))
      = pairingLinN 𝕜 E B p e₀ hfib hconn n q β f y := by
  rw [LambdaBarN, LinearMap.comp_apply, Work.Pi6.MSS.homZBIso_apply]
  show ((Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) n).liftQ
      (LambdaZBN 𝕜 E B p e₀ hfib hconn n q β f)
      (LambdaZBN_ker 𝕜 E B p e₀ hfib hconn n q β f))
      ((Work.StemsB.fdH 𝕜 (Kte 𝕜 B p e₀ q) n).mkQ
        ((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) n).hom
          ((Kte 𝕜 B p e₀ q).cyclesMk y ((ComplexShape.down ℕ).next n) rfl hy)))
    = pairingLinN 𝕜 E B p e₀ hfib hconn n q β f y
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  change pairingLinN 𝕜 E B p e₀ hfib hconn n q β f
      (((Work.Pi6.MSS.cycZIso 𝕜 (Kte 𝕜 B p e₀ q) n).hom
        ((Kte 𝕜 B p e₀ q).cyclesMk y ((ComplexShape.down ℕ).next n) rfl hy)) :
          ↥((Kte 𝕜 B p e₀ q).X n)) = pairingLinN 𝕜 E B p e₀ hfib hconn n q β f y
  rw [Work.Pi6.MSS.cycZIso_hom_val, Work.SSSR.hmcm_iCycles_cyclesMk]

/-- The value of `Λ_bar` on the class of a cycle, in degree `n`. -/
lemma LambdaBarN_cycle (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (c : ↥((Kte 𝕜 B p e₀ q).cycles n)) :
    LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f ((Kte 𝕜 B p e₀ q).homologyπ n c)
      = pairingLinN 𝕜 E B p e₀ hfib hconn n q β f
          (((Kte 𝕜 B p e₀ q).iCycles n).hom c) := by
  rw [show (Kte 𝕜 B p e₀ q).homologyπ n c
      = (Kte 𝕜 B p e₀ q).homologyπ n
          ((Kte 𝕜 B p e₀ q).cyclesMk (((Kte 𝕜 B p e₀ q).iCycles n).hom c)
            ((ComplexShape.down ℕ).next n) rfl (d_iCycles_KteN 𝕜 E B p e₀ q n c))
      from congrArg _ (Work.Pi6.MSS.cyclesMk_iCycles _ c _ rfl
        (d_iCycles_KteN 𝕜 E B p e₀ q n c)).symm]
  rw [LambdaBarN_cyclesMk]

/-- The value of `Λ_bar` on the `collapseX`-image of a cycle class, in degree `n`. -/
lemma LambdaBarN_collapseX (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (c : ↥((Ktc 𝕜 B p e₀ q).cycles n)) :
    LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
        ((HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q)).hom n).hom
          ((Ktc 𝕜 B p e₀ q).homologyπ n c))
      = LambdaChainN 𝕜 E B p e₀ hfib hconn n q β f (((Ktc 𝕜 B p e₀ q).iCycles n).hom c) := by
  rw [Work.Pi6.MSS.homologyMap_homologyπ]
  rw [LambdaBarN_cycle]
  rw [Work.Pi6.MSS.iCycles_cyclesMap]
  rw [tensorComplexIsoExpTensIso_hom_f]
  rfl

/-! ## The identity `Λ = Λ_bar ∘ Künneth` in degree `n` -/

/-- **The main identity in degree `n`**: the `E²`-pairing is the descent of the chain-level pairing
composed with the Künneth isomorphism. -/
lemma e2CanonStep_eq_LambdaBarN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ)
    [FiniteDimensional 𝕜 (Work.SSSR.coefM (R := 𝕜) p e₀ q)]
    (β : ↥(ZB 𝕜 B n)) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (x : TensorProduct 𝕜 (↥((normC 𝕜 B).homology n))
      (↥(Work.SSSR.coefM (R := 𝕜) p e₀ q))) :
    e2CanonStep 𝕜 E B p e₀ hfib hconn n q
        (TensorProduct.tmul 𝕜 (clsB 𝕜 B n β) f) x
      = LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
          (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z m =>
      obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective _).mp
        (inferInstance : Epi (HomologicalComplex.homologyπ (normC 𝕜 B) n)) z
      rw [e2CanonStep_tmul, kappaB_clsB_cycle]
      change betaChainF 𝕜 B n β ((ModuleCat.Hom.hom ((normC 𝕜 B).iCycles n)) c)
          * kappaF 𝕜 E B p e₀ hfib hconn q f m
        = LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
            (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n
              (TensorProduct.tmul 𝕜
                ((HomologicalComplex.homologyπ (normC 𝕜 B) n) c) m))
      rw [kunnethIso_tmul]
      rw [show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (tensUnit (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) m) n))
            ((HomologicalComplex.homologyπ (normC 𝕜 B) n) c)
          = (Kte 𝕜 B p e₀ q).homologyπ n
              ((HomologicalComplex.cyclesMap (tensUnit (normC 𝕜 B)
                (Work.SSSR.coefM (R := 𝕜) p e₀ q) m) n) c)
          from Work.Pi6.MSS.homologyMap_homologyπ _ _ _]
      rw [LambdaBarN_cycle]
      rw [Work.Pi6.MSS.iCycles_cyclesMap, tensUnit_f_apply, pairingLinN_tmul]
  | add x y hx hy =>
      calc e2CanonStep 𝕜 E B p e₀ hfib hconn n q
            (TensorProduct.tmul 𝕜 (clsB 𝕜 B n β) f) (x + y)
          = e2CanonStep 𝕜 E B p e₀ hfib hconn n q
              (TensorProduct.tmul 𝕜 (clsB 𝕜 B n β) f) x
            + e2CanonStep 𝕜 E B p e₀ hfib hconn n q
              (TensorProduct.tmul 𝕜 (clsB 𝕜 B n β) f) y := map_add _ x y
        _ = LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
              (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n x)
            + LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
              (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n y) := by
            rw [hx, hy]
        _ = LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
              (kunnethIso 𝕜 (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n (x + y)) := by
            rw [map_add, map_add]

/-- The simplex underlying a nondegenerate simplex `σ`, read off at the top simplex of `Δ[n]`. -/
lemma nIndexSigma_app_topS (B : Type) [TopologicalSpace B] (n : ℕ)
    (σ : Work.SSSR.nIndex (SSS.sSing B) n) :
    (Work.SSSR.nIndexSigma (SSS.sSing B) n σ).app (Opposite.op (SimplexCategory.mk n))
        (Work.Pi6.MSSK.topS n)
      = Work.SSSR.nIndexBase (SSS.sSing B) σ := by
  rw [Work.Pi6.MSSK.topS, Work.SSSR.nIndexSigma_app]
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-! ## The generator computation in degree `n` -/

/-- **The value of `Λ_chain` on the degree-`n` canonical generator**. -/
lemma LambdaChainN_genElemN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
    (hz : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0) :
    LambdaChainN 𝕜 E B p e₀ hfib hconn n q β f
        (genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz)
      = ∑ j : Fin k, lam j *
          (betaChainF 𝕜 B n β
            (((SSS.sSing B).ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜)
              (Work.SSSR.nIndexBase (SSS.sSing B) (σ j))).hom 1)
          * kappaF 𝕜 E B p e₀ hfib hconn q f
              ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom)
                ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).homologyπ q))
                  ((Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).cyclesMk (z j)
                    ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
  have hgen : ∀ j : Fin k,
      (Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) n).hom.hom
        ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) n
            => Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j)).hom
          ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).cyclesMk (z j)
                ((ComplexShape.down ℕ).next q) rfl (hz j)))))
      = Work.SSSR.splitX (normC 𝕜 B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n
          (TensorProduct.tmul 𝕜
            (((SSS.sSing B).ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜)
              (Work.SSSR.nIndexBase (SSS.sSing B) (σ j))).hom 1)
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j))))) := fun j =>
    Work.Pi6.MSS.serreE1CoefIsoIso_iota_single 𝕜 (Work.SSSR.sSing B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q) n (σ j) _
  rw [genElemN, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearMap.map_smul, LinearMap.map_smul, hgen j, lambdaChainN_splitX, pairingLinN_tmul,
    smul_eq_mul]

theorem e2Canon_genN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (n q : ℕ) (hq : q ≤ N) (β : ↥(Work.Pi6.MSS.ZB 𝕜 B n))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
    (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
      ((ComplexShape.down ℕ).next q))) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d n ((ComplexShape.down ℕ).next n)
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz) = 0) :
    (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin n q hq
        (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B n β) f))
      (Work.Pi6.MSS.psiE2 𝕜 E B p e₀ hfib hconn q n
        (Work.Pi6.MSS.genCycN 𝕜 p e₀ hfib hconn n q k lam σ z hz hcyc))
    = ∑ j : Fin k, lam j *
        (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
          ((Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)).app
            (Opposite.op (SimplexCategory.mk n)) (Work.Pi6.MSSK.topS n))) *
        (Work.Pi6.MSS.kappaF 𝕜 E B p e₀ hfib hconn q f
          (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom
            (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
                (Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))) q)
              (HomologicalComplex.cyclesMk
                (Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j))))
                (z j) ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
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
  set g := Work.Pi6.MSS.genCycN 𝕜 p e₀ hfib hconn n q k lam σ z hz hcyc with hg
  have hL : Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin n q hq
      (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B n β) f)
      (Work.Pi6.MSS.psiE2 𝕜 E B p e₀ hfib hconn q n g)
    = LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
        ((HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q)).hom n).hom g) := by
    rw [show Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin n q hq
        = (e2CanonStep 𝕜 E B p e₀ hfib hconn n q).trans
            ((e2CanonG 𝕜 B (Work.SSSR.coefM (R := 𝕜) p e₀ q) n).trans
              (e2CanonH 𝕜 E B p e₀ hfib hconn n q)) from rfl]
    simp only [LinearEquiv.trans_apply]
    rw [e2CanonH_psiE2]
    conv_lhs => rw [← LinearEquiv.apply_symm_apply
      (kunnethCompIso 𝕜 B (Work.SSSR.coefM (R := 𝕜) p e₀ q) n) g]
    rw [e2CanonG_kunnethCompIso]
    rw [e2CanonStep_eq_LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f]
    rw [kunnethIso_symm_kunnethCompIso]
  have hR : LambdaBarN 𝕜 E B p e₀ hfib hconn n q β f
        ((HomologicalComplex.homologyMap
          (Work.SSSR.tensorComplexIsoExpTensIso (normC 𝕜 B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q)).hom n).hom g)
      = ∑ j : Fin k, lam j *
          (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
            ((Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)).app
              (Opposite.op (SimplexCategory.mk n)) (Work.Pi6.MSSK.topS n))) *
          (Work.Pi6.MSS.kappaF 𝕜 E B p e₀ hfib hconn q f
            (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom
              (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
                  (Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))) q)
                (HomologicalComplex.cyclesMk
                  (Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j))))
                  (z j) ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
    rw [show g = (Ktc 𝕜 B p e₀ q).homologyπ n
        ((Ktc 𝕜 B p e₀ q).cyclesMk
          (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz)
          ((ComplexShape.down ℕ).next n) rfl hcyc) from rfl]
    rw [LambdaBarN_collapseX 𝕜 E B p e₀ hfib hconn n q β f
      ((Ktc 𝕜 B p e₀ q).cyclesMk
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz)
        ((ComplexShape.down ℕ).next n) rfl hcyc)]
    rw [Work.SSSR.hmcm_iCycles_cyclesMk]
    rw [LambdaChainN_genElemN 𝕜 E B p e₀ hfib hconn n q β f k lam σ z hz]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [betaChainF_iota, ← nIndexSigma_app_topS B n (σ j)]
    ring
  rw [hL, hR]

end

end Work.Pi6.MSS
