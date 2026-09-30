import Mathlib
import Submission.Work.Pi6.MSS.e2FinalDefs
import Submission.Work.Pi6.MSS.normKron_exists
import Submission.Work.Pi6.MSS.tensorDual
import Submission.Work.Pi6.MSS.kunneth_exists
import Submission.Work.SSSR.serreE1CoefExplicit
import Submission.Work.Cohomology.kronH_bijective_field
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The canonical pairing `H^s(B;𝕜) ⊗ H^q(F;𝕜) ⟶ (E²_{s,q})^*`

This file defines, explicitly, the composite

`H^s(B) ⊗ H^q(F) ⟶ H_s(B)^* ⊗ H_q(F)^* ⟶ (H_s(B) ⊗ H_q(F))^* ⟶ H_s(N_*(B) ⊗ H_q(F))^*
  ⟶ (E²_{s,q})^*`,

where the last arrow is the transpose of the explicit isomorphism
`Work.Pi6.MSS.psiE2 : H_s(N_*(B) ⊗ H_q(F)) ≅ E²_{s,q}` of `e2FinalDefs.lean`.  It is the map that
`Work.Pi6.MSS.e2Psi` is compared with; the comparison is checked on the generators
`Work.Pi6.MSS.genElem` and uses `Work.Pi6.MSS.e2Psi_pairing`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The base-point factor of the canonical pairing: `H^s(B;𝕜) ≅ (H_s(N_*(B;𝕜)))^*`, the explicit
form of `Work.Pi6.MSS.normKron_exists`. -/
noncomputable def kappaB (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ) :
    Work.Pi6.Coh 𝕜 B s ≃ₗ[𝕜]
      (↥((Work.Pi6.MSS.normC 𝕜 B).homology s) →ₗ[𝕜] 𝕜) :=
  Classical.choose (Work.Pi6.MSS.normKron_exists 𝕜 B s)

/-- The computation rule of `kappaB` on the class of a skeletal cocycle. -/
theorem kappaB_apply (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s)
    (hα : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) α = 0)
    (z : (Work.Pi6.MSS.normC 𝕜 B).cycles s) :
    kappaB 𝕜 B s (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) α hα)
        (((Work.Pi6.MSS.normC 𝕜 B).homologyπ s) z)
      = α (((SSet.fromNormalizedChainComplex (Work.SSS.sSing B)
            (ModuleCat.of 𝕜 𝕜)).f s).hom
            ((ModuleCat.Hom.hom ((Work.Pi6.MSS.normC 𝕜 B).iCycles s)) z)) :=
  Classical.choose_spec (Work.Pi6.MSS.normKron_exists 𝕜 B s) α hα z

/-- The fibre factor of the canonical pairing, with the canonical transport to the base point
folded in: `f ↦ (m ↦ ⟨f, triv_{p e₀}⁻¹ m⟩)`. -/
noncomputable def kappaFe (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ) :
    Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q ≃ₗ[𝕜]
      (Work.SSSR.coefM (R := 𝕜) p e₀ q →ₗ[𝕜] 𝕜) :=
  (LinearEquiv.ofBijective
      (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q)
      (Work.Cohomology.kronH_bijective_field 𝕜
        (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q)).trans
    (LinearEquiv.dualMap (Iso.toLinearEquiv
      (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).symm)).symm

/-- The underlying linear map of `kappaFe`. -/
noncomputable def kappaF (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ) :
    Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
      (Work.SSSR.coefM (R := 𝕜) p e₀ q →ₗ[𝕜] 𝕜) :=
  (kappaFe 𝕜 E B p e₀ hfib hconn q).toLinearMap

/-- The canonical Künneth isomorphism `H_s(C) ⊗ M ≅ H_s(C ⊗ M)` over a field, as a linear
equivalence (from `Work.Pi6.MSS.kunneth_exists`). -/
noncomputable def kunnethIso (𝕜 : Type) [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ)
    (M : ModuleCat 𝕜) (s : ℕ) :
    TensorProduct 𝕜 (↥(C.homology s)) (↥M) ≃ₗ[𝕜]
      ↥((Work.Pi6.MSS.expTens 𝕜 C M).homology s) :=
  LinearEquiv.ofBijective (Classical.choose (Work.Pi6.MSS.kunneth_exists 𝕜 C M s))
    (Classical.choose_spec (Work.Pi6.MSS.kunneth_exists 𝕜 C M s)).2

/-- The computation rule of `kunnethIso`: `[z] ⊗ m ↦ [z ⊗ m]`. -/
theorem kunnethIso_apply (𝕜 : Type) [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ)
    (M : ModuleCat 𝕜) (s : ℕ) (m : M) :
    (kunnethIso 𝕜 C M s).toLinearMap ∘ₗ
        (TensorProduct.mk 𝕜 ↥(C.homology s) ↥M).flip m
      = (HomologicalComplex.homologyMap (Work.Pi6.MSS.tensUnit C M m) s).hom :=
  (Classical.choose_spec (Work.Pi6.MSS.kunneth_exists 𝕜 C M s)).1 m

/-- The first half of the canonical pairing: `V ⟶ (H_s(N_*(B)) ⊗ H_q(F))^*` (Kronecker on both
factors). -/
noncomputable def e2CanonStep (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    [FiniteDimensional 𝕜 (Work.SSSR.coefM (R := 𝕜) p e₀ q)] :
    (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) ≃ₗ[𝕜]
      ((TensorProduct 𝕜 (↥((Work.Pi6.MSS.normC 𝕜 B).homology s))
        (↥(Work.SSSR.coefM (R := 𝕜) p e₀ q))) →ₗ[𝕜] 𝕜) :=
  (TensorProduct.congr (kappaB 𝕜 B s) (kappaFe 𝕜 E B p e₀ hfib hconn q)).trans
    (phiLin (ModuleCat.of 𝕜 ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q))
      ↥((Work.Pi6.MSS.normC 𝕜 B).homology s))

/-- The Künneth isomorphism `H_s(N_*(B)) ⊗ H_q(F) ≅ H_s(N_*(B) ⊗ H_q(F))`. -/
noncomputable def kunnethCompIso (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B]
    (M : ModuleCat 𝕜) (s : ℕ) :
    TensorProduct 𝕜 (↥((Work.Pi6.MSS.normC 𝕜 B).homology s)) (↥M) ≃ₗ[𝕜]
      (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) M).homology s :=
  (kunnethIso 𝕜 (Work.Pi6.MSS.normC 𝕜 B) M s).trans
    (Iso.toLinearEquiv (HomologicalComplex.homologyMapIso
      (Work.SSSR.tensorComplexIsoExpTensIso (Work.Pi6.MSS.normC 𝕜 B) M) s).symm)

/-- The Künneth step of the canonical pairing: dualise `H_s(N_*(B)) ⊗ H_q(F) ≅ H_s(N_*(B) ⊗ H_q(F))`. -/
noncomputable def e2CanonG (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B]
    (M : ModuleCat 𝕜) (s : ℕ) :
    ((TensorProduct 𝕜 (↥((Work.Pi6.MSS.normC 𝕜 B).homology s)) (↥M)) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
      ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) M).homology s →ₗ[𝕜] 𝕜) :=
  (LinearEquiv.dualMap (kunnethCompIso 𝕜 B M s)).symm

/-- The final step of the canonical pairing: dualise the explicit identification
`psiE2 : H_s(N_*(B) ⊗ H_q(F)) ≅ E²_{s,q}`. -/
noncomputable def e2CanonH (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ) :
    ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).homology s →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
      ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homology s →ₗ[𝕜] 𝕜) :=
  LinearEquiv.dualMap (Iso.toLinearEquiv (HomologicalComplex.homologyMapIso
    (e1SerreIso 𝕜 E B p e₀ hfib hconn q) s).symm)

/-- **The canonical pairing** `H^s(B;𝕜) ⊗ H^q(F;𝕜) ≅ (E²_{s,q})^*`. -/
noncomputable def e2Canon (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N) :
    (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) ≃ₗ[𝕜]
      ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homology s →ₗ[𝕜] 𝕜) := by
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
  exact (e2CanonStep 𝕜 E B p e₀ hfib hconn s q).trans
    ((e2CanonG 𝕜 B (Work.SSSR.coefM (R := 𝕜) p e₀ q) s).trans
      (e2CanonH 𝕜 E B p e₀ hfib hconn s q))

end

end Work.Pi6.MSS
