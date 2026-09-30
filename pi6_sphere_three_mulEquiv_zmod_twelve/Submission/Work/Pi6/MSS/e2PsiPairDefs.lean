import Mathlib
import Submission.Work.Pi6.MSS.mixedEvaluation
import Submission.Work.Pi6.MSS.e2Psi_repr_ZB
import Submission.Work.SSSR.sndToSerre_range
import Submission.Work.Pi6.MSS.Kgpi_d_cruxIota_sndToR
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Vocabulary for the computation of `Ψ` on the generators of `E²`

This file fixes the objects appearing in the key computation `Work.Pi6.MSS.e2Psi_pairing`:
the `pZ 2`-representative `pairElem` of `Ψ (clsB β ⊗ f)` attached to a skeletal base cocycle `β`
and a column cycle `y`, its image `pairElemOne` in the level `E_1` cycles, the graded-piece cycle
`pairW` lifting the generator `[Kgπ (sCCMap (sndToR σ) (cruxIota σ z))]`, and the scalar
`pairRHS` of the Eilenberg–Zilber/mixed-product computation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `Z_2^s ⊆ Z_1^s`. -/
theorem pZ_two_le_one (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    pZ 𝕜 (Wc 𝕜 p) 2 s n ≤ pZ 𝕜 (Wc 𝕜 p) 1 s n := by
  intro x hx
  exact ⟨hx.1, pd_F_mono_of_le (W := Wc 𝕜 p) (show s + 1 ≤ s + 2 by omega) hx.2⟩

/-- The pullback of a skeletal cocycle is a `2`-cycle of the Serre filtration in bidegree
`(s, s)`. -/
theorem pbC_mem_pZ_two (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s : ℕ) (β : ↥(ZB 𝕜 B s)) :
    pbC 𝕜 p s β.1 ∈ pZ 𝕜 (Wc 𝕜 p) 2 s s := by
  have hzero : (serreCF 𝕜 E B p).d s (pbC 𝕜 p s β.1) = 0 := by
    simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
    exact cochainDiff_pbC 𝕜 p β.2.1
  refine ⟨pbC_mem_skel 𝕜 p β.2.2, ?_⟩
  show (serreCF 𝕜 E B p).d s (pbC 𝕜 p s β.1) ∈ (serreCF 𝕜 E B p).F (s + 2) (s + 1)
  rw [hzero, show s + 2 = (s + 1) + 1 from rfl, (serreCF 𝕜 E B p).F_top (s + 1)]
  exact Submodule.zero_mem _

/-- The `pZ 2`-representative of `Ψ (clsB β ⊗ f)`: the concrete page product of the pullback of
`β` with the column cycle `y`. -/
abbrev pairElem (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (β : ↥(ZB 𝕜 B s)) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q)) :
    ↥(pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)) :=
  pd_mulZ 2 s (s + 0) 0 q ⟨pbC 𝕜 p s β.1, pbC_mem_pZ_two 𝕜 p s β⟩ y

/-- The image of `pairElem` in the level `E_1` cycles `Z_1^s`. -/
noncomputable def pairElemOne (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (β : ↥(ZB 𝕜 B s)) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q)) :
    ↥(pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)) :=
  ⟨(pairElem 𝕜 p s q β y).1, pZ_two_le_one 𝕜 p s (s + q) (pairElem 𝕜 p s q β y).2⟩

/-- The graded-piece cycle `[Kgπ (sCCMap (sndToR σ) (cruxIota σ z))]` of the generator attached
to a nondegenerate `(k+1)`-simplex `σ` and a fibre cycle `z`. -/
noncomputable def pairW (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (k q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p (k + 1)) ((k + 1) + q)) :=
  ⟨(ModuleCat.Hom.hom ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
        (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k + 1) + q)))
        (cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z)),
    show (ModuleCat.Hom.hom ((Kg 𝕜 p (k + 1)).d (((k + 1) + q))
        ((((k + 1) + q)) - 1)))
      ((ModuleCat.Hom.hom ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
          (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k + 1) + q)))
          (cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z))) = 0 from by
      rw [show (((k + 1) + q)) - 1 = (ComplexShape.down ℕ).next ((k + 1) + q) from by
        rw [Work.SSSR.down_next_eq]]
      exact Kgpi_d_cruxIota_sndToR 𝕜 E B p hfib k q σ z hz⟩

/-- The scalar of the mixed-product computation `⟨Ψ(β ⊗ f), [W_γ]⟩`. -/
noncomputable def pairRHS (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (k q : ℕ)
    (β : ↥(ZB 𝕜 B (k + 1))) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q))
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    𝕜 :=
  cruxEps 𝕜 (k + 1) * Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
      ((Work.SSSR.sigHat σ).app (op (SimplexCategory.mk (k + 1))) (Work.Pi6.MSSK.topS (k + 1))) *
    Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
      (rho 𝕜 E B p e₀ q
        (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype) y))
      (cruxFibre 𝕜 p e₀ hfib hconn (k + 1) q (Work.SSSR.sigHat σ) z hz)

/-- The statement of the key computation `e2Psi_pairing`. -/
def PairingStatement (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B] :
    Prop :=
  ∀ (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (k q : ℕ)
    (β : ↥(ZB 𝕜 B (k + 1))) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q))
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).d q ((ComplexShape.down ℕ).next q))) z = 0),
    evZ 𝕜 p (k + 1) ((k + 1) + q) (coFiltAnn 𝕜 (sF p))
        (pairElemOne 𝕜 p (k + 1) q β y)
        ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (k + 1)) ((k + 1) + q)).mkQ
          (pairW 𝕜 p hfib k q σ z hz)) = pairRHS 𝕜 p e₀ hfib hconn k q β y σ z hz

end

end Work.Pi6.MSS
