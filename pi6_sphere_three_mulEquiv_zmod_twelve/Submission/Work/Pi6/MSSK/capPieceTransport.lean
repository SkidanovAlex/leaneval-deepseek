import Mathlib
import Submission.Work.Pi6.MSSK.CapAux
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.VertexBridges
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.CapThetaLift
import Submission.Work.Pi6.MSSK.TransportAux
import Submission.Work.Pi6.MSSK.capEdgeIdentity
import Submission.Work.Pi6.MSSK.capLastFaceTop_edgeIncl
import Submission.Work.Pi6.MSSK.edgePieceToPullback
import Submission.Work.Pi6.MSSK.edgeTransportChain
import Submission.Work.Pi6.MSSK.mono_edgeIncl
import Submission.Work.Pi6.MSSK.mono_fibreInc
import Submission.Work.Pi6.MSSK.fibreIncCapThetaLift
import Submission.Work.Pi6.MSSK.capThetaLift_isCycle
import Submission.Work.Pi6.MSSK.cap_theta_bdry_zero
import Submission.Work.Pi6.MSSK.thetaTop_cocycle
import Submission.Work.Pi6.MSSK.exists_bdry_lift_of_pieceAlong_cycle
import Submission.Work.Pi6.MSSK.lastPathExists
import Submission.Work.Pi6.MSSK.lastEdgeVertexBridges
import Submission.Work.Pi6.MSSK.peel_aux
import Submission.Work.Pi6.MSSK.edgePieceTransport
import Submission.Work.Pi6.MSSK.peelData
import Submission.Work.Pi6.MSSK.capAuxZero
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.pieceIso_peel
import Submission.Work.SSSR.transportIsoPathChain
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.SSSR.pieceAlongZero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-! Guidance from the project lead (the requester):

AREA MSSK (lead-dispatched 2026-09-29; unblocks MSS e2AddKoszul, the crux). Read REFS/NOTES_LEAD_MSSK.md §1 (the complete proof).
Contract vocabulary: Submission/Work/Pi6/MSSK/Defs.lean (lastV, fibreInc, thetaTop). Library: Work.SSSR.* (the ring-generic E¹ port:
pieceAlong, bdryAlong, pullAlong, serreE1PieceIso (serreE1PieceExplicit.lean), pieceConnectingIsoIso, pieceAlongZeroIso,
pullAlongVertexIsoIso, lastFaceMap/pieceLastFace (lastFaceDefs.lean), triv/transportIsoPath/edgeTransport), Work.Cohomology.cap,
cap_apply, cap_d (cap boundary formula), kronecker_cap_cup.
Statement: θ ⌢ c for a representative c of (serreE1PieceIso σ)⁻¹ x lifts to a cycle over the last vertex whose class is ε·(transport of x),
compared through triv. Induct on s exactly along the definition of serreE1PieceIso (it peels the LAST face). Decompose immediately:
(a) capThetaOverLast — θ⌢c lies in the image of fibreInc (front/back face combinatorics via cap_apply);
(b) capThetaCycle — δθ = 0 and θ vanishes over ∂Δ[s], so θ⌢c is a cycle when c is a relative cycle;
(c) capEdgeStep — on T_σ, δ(θ of the last face) = ±θ, so θ⌢c and θ_{dσ}⌢(∂c) are homologous in the part of T_σ over the last edge,
    and the two fibre inclusions into it are related by the edge transport;
(d) assembly by induction on s with triv's path-compatibility.
-/

namespace Work.Pi6.MSSK

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

variable {R : Type} [CommRing R] [Nontrivial R]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

lemma zsmul_neg_one_pow (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M]
    (n : ℕ) (x : M) : ((-1 : ℤ)^n : ℤ) • x = ((-1 : R)^n) • x := by
  rw [← Int.cast_smul_eq_zsmul (R := R) (M := M)]
  simp

lemma triv_eqToIso_hom_apply (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) (k : ℕ) {b b' : B} (h : b = b')
    (y : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) k) :
    (Work.SSSR.triv p e₀ hfib hsconn k b').hom.hom
        ((CategoryTheory.eqToIso (congrArg (fun x : B =>
          Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p x) k) h)).hom.hom y)
      = (Work.SSSR.triv p e₀ hfib hsconn k b).hom.hom y := by
  have hh := triv_eqToIso (R := R) p e₀ hfib hsconn k h
  exact congrArg (fun (g : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) k ⟶
    Work.SSSR.coefM p e₀ k) => (ModuleCat.Hom.hom g) y) hh

theorem capAux_all (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) :
    ∀ (s k : ℕ) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B),
      Aux R p e₀ hfib hsconn s k σ := by
  intro s
  induction s with
  | zero =>
    intro k σ
    exact capAuxZero R p e₀ hfib hsconn k σ
  | succ t ih =>
    intro k σ c hcrel
    have hrel2 : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d
        ((t+1) + k) ((t+1) + k - 1)))
        ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f ((t+1) + k))) c) = 0 := by
      rw [← nextDownEq ((t+1) + k)]
      exact hcrel
    obtain ⟨W, hWcyc, hWpeel⟩ := Work.Pi6.MSSK.Peel.peelData R p σ c hrel2
    have hcast : t + k = (t+1) + k - 1 := by omega
    let w' : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).X (t+k) :=
      Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))
        hcast.symm W
    have hw'cast : ∀ h : t + k = (t+1) + k - 1,
        Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))) h w' = W := by
      intro h
      rw [Work.SSSR.StepAux.castElem_irrel (K := Work.SSSR.sCC R (Work.SSSR.pullAlong
          (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))
        (h := h) (h' := hcast) w']
      exact Peel.castElem_cancel' hcast W
    have hpeel : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f
        ((t+1)+k-1)))
        (((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d ((t+1)+k) ((t+1)+k-1)).hom c)
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f ((t+1)+k-1)))
            (((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f ((t+1)+k-1))
              ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ).f ((t+1)+k-1)
                (Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))
                  (by omega : t + k = (t+1) + k - 1) w'))) := by
      rw [hw'cast]
      exact hWpeel
    have hw'rel2 : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).d
        (t + k) ((ComplexShape.down ℕ).next (t + k))))
        ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R
          (Work.SSSR.bdryAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f
            (t + k))) w') = 0 := by
      rw [nextDownEq (t + k)]
      rw [← Work.SSSR.StepAux.castElem_map (CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R
        (Work.SSSR.bdryAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι))
        hcast.symm W]
      exact Peel.castElem_d_eq_zero hcast.symm _ hWcyc
    obtain ⟨z'', hz''1, hz''2⟩ := ih k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ) w' hw'rel2
    obtain ⟨z', hz'1, hz'2⟩ := Work.Pi6.MSSK.edgePieceTransport R p e₀ hfib hsconn σ c hrel2
      w' hpeel z'' hz''1



    refine ⟨z', hz'1, ?_⟩
    have hpeel' := Work.SSSR.pieceIso_peel p hfib t k (Work.SSSR.sigmaVert σ) σ c hcrel
      w' hw'rel2 hpeel
    have h1a : (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom (((Work.SSSR.serreE1PieceIso p hfib (t+1) k σ).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ ((t+1)+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f ((t+1)+k))) c) ((ComplexShape.down ℕ).next ((t+1)+k)) rfl hcrel)))) = (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom (((-1 : ℤ)^(t+1)) • ((CategoryTheory.eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology k) (Work.SSSR.sigmaVert_face (Fin.last (t+1)) (by intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))))) := by
      have h := congrArg (fun y => (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom y) hpeel'
      exact h
    have key : (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom ((CategoryTheory.eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology k) (Work.SSSR.sigmaVert_face (Fin.last (t+1)) (by intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2))))) = (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))) :=
      triv_eqToIso_hom_apply (R := R) (b := Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
        (b' := Work.SSSR.sigmaVert σ) p e₀ hfib hsconn k (Work.SSSR.sigmaVert_face (Fin.last (t+1)) (by intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ) ((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))
    have hmapz : (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom (((-1 : ℤ)^(t+1)) • ((CategoryTheory.eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology k) (Work.SSSR.sigmaVert_face (Fin.last (t+1)) (by intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2))))))
        = ((-1 : ℤ)^(t+1)) • (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom ((CategoryTheory.eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology k) (Work.SSSR.sigmaVert_face (Fin.last (t+1)) (by intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2))))) :=
      map_zsmul ((Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom) ((-1 : ℤ)^(t+1)) ((CategoryTheory.eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology k) (Work.SSSR.sigmaVert_face (Fin.last (t+1)) (by intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))))
    have hzs2 : ((-1 : ℤ)^(t+1)) • (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))) = ((-1 : R)^(t+1)) • (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))) :=
      zsmul_neg_one_pow R (Work.SSSR.coefM p e₀ k) (t+1) ((Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))))
    have hC : (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom (((Work.SSSR.serreE1PieceIso p hfib (t+1) k σ).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ ((t+1)+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f ((t+1)+k))) c) ((ComplexShape.down ℕ).next ((t+1)+k)) rfl hcrel)))) = ((-1 : R)^(t+1)) • (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))) := by
      rw [h1a, hmapz, key, hzs2]
    have hD : (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).hom.hom (((Work.SSSR.serreE1PieceIso p hfib t k (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).homologyπ (t+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).ι)).f (t+k))) w') ((ComplexShape.down ℕ).next (t+k)) rfl hw'rel2)))) = ((-1 : R)^(t+1)) • (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom (((Work.SSSR.serreE1PieceIso p hfib (t+1) k σ).hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ ((t+1)+k))) ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f ((t+1)+k))) c) ((ComplexShape.down ℕ).next ((t+1)+k)) rfl hcrel)))) := by
      rw [hC, smul_smul]
      rcases neg_one_pow_eq_one_or_neg_one R (t+1) with h | h <;> rw [h] <;> simp
    rw [hz'2, hz''2, hD, smul_smul, capSign_succ]
    congr 1
    ring

lemma iso_inv_hom_apply' {R : Type} [CommRing R] {A B : ModuleCat R} (e : A ≅ B) (x : B) :
    e.hom.hom (e.inv.hom x) = x := by
  have h := congrArg (fun (g : B ⟶ B) => (ModuleCat.Hom.hom g) x) (Iso.inv_hom_id e)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

theorem capPieceTransport (R : Type) [CommRing R] [Nontrivial R]
    (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (s k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ∃ ε : R, (ε = 1 ∨ ε = -1) ∧
      ∀ (x : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)) k)
        (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + k))
        (z : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cycles (s + k)),
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).iCycles (s + k)).hom z =
            (((CategoryTheory.Limits.cokernel.π
              (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s + k)).hom c) →
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ (s + k)).hom z =
            (Work.SSSR.serreE1PieceIso p hfib s k σ).inv.hom x →
        ∃ z' : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (Work.Pi6.MSSK.lastV s ≫ σ))).cycles k,
          ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f k).hom
              (((Work.SSSR.sCC R _).iCycles k).hom z') =
            Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
              (Work.Pi6.MSSK.thetaTop R p σ) k c ∧
          (Work.SSSR.triv p e₀ hfib hc k (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV s ≫ σ))).hom.hom
              ((HomologicalComplex.homologyMap
                (Work.SSSR.sCCMap R (Work.SSSR.pullAlongVertexIsoIso p (Work.Pi6.MSSK.lastV s ≫ σ)).hom) k).hom
                (((Work.SSSR.sCC R _).homologyπ k).hom z')) =
            ε • (Work.SSSR.triv p e₀ hfib hc k (Work.SSSR.sigmaVert σ)).hom.hom x := by
  refine ⟨capSign R s, capSign_eq_one_or_neg_one (R := R) s, ?_⟩
  intro x c z hz1 hz2
  have hcyc : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (s+k)
      ((ComplexShape.down ℕ).next (s+k))))
      ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).iCycles (s+k))) z) = 0 := by
    have h := congrArg (fun (g : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cycles (s+k) ⟶
        (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).X ((ComplexShape.down ℕ).next (s+k))) =>
        (ModuleCat.Hom.hom g) z)
      (HomologicalComplex.iCycles_d (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (s+k)
        ((ComplexShape.down ℕ).next (s+k)))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hcrel : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (s+k)
      ((ComplexShape.down ℕ).next (s+k))))
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s+k))) c) = 0 := by
    rw [← hz1]
    exact hcyc
  obtain ⟨z', hz'1, hz'2⟩ := capAux_all p e₀ hfib hc s k σ c hcrel
  refine ⟨z', hz'1, ?_⟩
  have hz_eq : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R
        (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s+k))) c)
      ((ComplexShape.down ℕ).next (s+k)) rfl hcrel = z := by
    apply (Preadditive.mono_iff_injective ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).iCycles (s+k))).mp inferInstance
    simp only [Work.SSSR.StepAux.forget2_Ab_hom_apply]
    rw [Work.SSSR.StepAux.iCycles_cyclesMk, hz1]
  have hx : x = (Work.SSSR.serreE1PieceIso p hfib s k σ).hom.hom
      ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ (s+k)))
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
          ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R
            (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s+k))) c)
          ((ComplexShape.down ℕ).next (s+k)) rfl hcrel)) := by
    have h1 : (Work.SSSR.serreE1PieceIso p hfib s k σ).hom.hom
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ (s+k)))
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R
              (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s+k))) c)
            ((ComplexShape.down ℕ).next (s+k)) rfl hcrel)) = x := by
      rw [hz_eq, hz2]
      exact iso_inv_hom_apply' (Work.SSSR.serreE1PieceIso p hfib s k σ) x
    exact h1.symm
  rw [hx]
  exact hz'2

end

end Work.Pi6.MSSK
