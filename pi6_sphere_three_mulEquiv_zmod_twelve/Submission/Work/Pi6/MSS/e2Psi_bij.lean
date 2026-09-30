import Mathlib
import Submission.Work.Pi6.MSS.e2Asm
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSS.e2Row_exists
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.e2Add
import Submission.Work.Pi6.MSS.pageTwo
import Submission.Work.Pi6.MSS.e1CohDual
import Submission.Work.Pi6.MSS.normCoh
import Submission.Work.Pi6.MSS.tensorDual
import Submission.Work.SSSR.serreE1R
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.Pi6.MSS.mixedEvaluation
import Submission.Work.Pi6.MSS.cruxChain_mem_A
import Submission.Work.Pi6.MSS.cruxFibre_surjective
import Submission.Work.Pi6.MSS.evZ_d_transpose_vanishing
import Submission.Work.Pi6.MSS.e2Pairing_descent
import Submission.Work.Pi6.MSS.e2Psi_repr_ZB
import Submission.Work.SSSR.chainCondition_gen
import Submission.Work.SSSR.serreE1Main
import Submission.Work.Pi6.MSS.psiSig_generator
import Submission.Work.Pi6.MSS.big1_faceSum
import Submission.Work.Pi6.MSS.e2PsiPairDefs
import Submission.Work.Pi6.MSS.e2Psi_pairing
import Submission.Work.Pi6.MSS.kunnethDefs
import Submission.Work.Pi6.MSS.fieldDualUCT_explicit
import Submission.Work.Pi6.MSS.e2Bar
import Submission.Work.Pi6.MSS.e2Lbar
import Submission.Work.Pi6.MSS.e2L0_imd
import Submission.Work.Pi6.MSS.e2Lbar_injective
import Submission.Work.Pi6.MSS.e2Canon
import Submission.Work.Pi6.MSS.e1SerreIso_gen
import Submission.Work.Pi6.MSS.e2Canon_gen
import Submission.Work.Pi6.MSS.e2Psi_canon
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `e2mkQ` is surjective: every class of the `E²`-page has a `d¹`-cycle representative. -/
theorem e2mkQ_surjective (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ) :
    Function.Surjective (e2mkQ 𝕜 E B p s q) := by
  intro w
  obtain ⟨v, hv⟩ := Submodule.mkQ_surjective
    (Work.StemsB.fdH 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s)
    ((e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).hom.hom w)
  refine ⟨v, ?_⟩
  show (e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).inv.hom
    ((Work.StemsB.fdH 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).mkQ v) = w
  rw [hv]
  exact (e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).hom_inv_id_apply w

/-- The pairing `e2Lbar y` vanishes on the boundaries `fdH` of the `E¹`-complex: the image of
`d¹` pairs trivially (`e2L0_imd`). -/
theorem e2Lbar_fdH_eq_zero (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ)
    (y : mssE 𝕜 (Wc 𝕜 p) 2 ((s : ℤ), (q : ℤ)))
    (v : ↥(Work.StemsB.fdZ 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s))
    (hv : v ∈ Work.StemsB.fdH 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s) :
    e2Lbar 𝕜 E B p s q y v = 0 := by
  obtain ⟨u, hu⟩ := (Work.StemsB.mem_fdH 𝕜
    (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s v).mp hv
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 (Wc 𝕜 p) 2 s (s + q)).comap
      (pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)).subtype) y
  rw [e2Lbar_mkQ]
  have hv2 : v = e2dIm 𝕜 E B p s q u := by
    apply Subtype.ext
    show (v : ↥((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s))
      = ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (s + 1) s).hom u
    exact hu.symm
  rw [hv2]
  exact e2L0_imd 𝕜 E B p s q x u

theorem e2Psi_bij (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    ∀ s q : ℕ, s ≤ N → q ≤ N → Function.Bijective
      (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
        (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q) := by
  intro s q hs hq
  obtain ⟨T, hT, hcanon⟩ :=
    Work.Pi6.MSS.e2Psi_canon 𝕜 E B p e₀ N hfib hconn hfin s q hs hq
  let T' : (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) ≃ₗ[𝕜]
      (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) := LinearEquiv.ofBijective T hT
  have hT' : ∀ ξ, T' ξ = T ξ := fun ξ => rfl
  have hmkQ := e2mkQ_surjective 𝕜 E B p s q
  refine ⟨?_, ?_⟩
  · intro ξ η hξη
    have hv : ∀ v : ↥(e2KerD 𝕜 p s q),
        (e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq (T ξ)) (e2mkQ 𝕜 E B p s q v)
          = (e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq (T η)) (e2mkQ 𝕜 E B p s q v) := by
      intro v
      rw [← hcanon ξ v, ← hcanon η v, hξη]
    have hcanon_ext : e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq (T ξ)
        = e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq (T η) := by
      ext w
      obtain ⟨v, rfl⟩ := hmkQ w
      exact hv v
    have hTηξ : T ξ = T η :=
      (e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq).injective hcanon_ext
    exact hT.1 hTηξ
  · intro y
    have him : Work.StemsB.fdH 𝕜
        (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s
        ≤ LinearMap.ker (e2Lbar 𝕜 E B p s q y) := by
      intro v hv
      rw [LinearMap.mem_ker]
      exact e2Lbar_fdH_eq_zero 𝕜 E B p s q y v hv
    let ψ : (↥(Work.StemsB.fdZ 𝕜
        (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s) ⧸
        Work.StemsB.fdH 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s) →ₗ[𝕜] 𝕜 :=
      Submodule.liftQ (Work.StemsB.fdH 𝕜
        (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s)
        (e2Lbar 𝕜 E B p s q y) him
    have hψ : ∀ v : ↥(Work.StemsB.fdZ 𝕜
        (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s),
        ψ ((Work.StemsB.fdH 𝕜
          (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).mkQ v)
          = e2Lbar 𝕜 E B p s q y v := by
      intro v
      show (Work.StemsB.fdH 𝕜
          (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).liftQ
          (e2Lbar 𝕜 E B p s q y) him (Submodule.Quotient.mk v)
        = e2Lbar 𝕜 E B p s q y v
      rfl
    let ρ : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homology s →ₗ[𝕜] 𝕜 :=
      ψ.comp (e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).hom.hom
    have hρ : ∀ v : ↥(Work.StemsB.fdZ 𝕜
        (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s),
        ρ (e2mkQ 𝕜 E B p s q v) = e2Lbar 𝕜 E B p s q y v := by
      intro v
      show ψ ((e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).hom.hom
        ((e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).inv.hom
          ((Work.StemsB.fdH 𝕜
            (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).mkQ v))) = _
      rw [Iso.inv_hom_id_apply]
      exact hψ v
    obtain ⟨ξ, hξ⟩ :=
      (e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq).surjective ρ
    refine ⟨T'.symm ξ, ?_⟩
    apply e2Lbar_injective 𝕜 E B p s q
    ext v
    rw [hcanon (T'.symm ξ) v,
      show T (T'.symm ξ) = T' (T'.symm ξ) from (hT' _).symm, T'.apply_symm_apply,
      hξ, hρ v]

end

end Work.Pi6.MSS
