import Mathlib
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.pageTwo
import Submission.Work.Pi6.MSS.TensorDefs
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.MSS.normCoh
import Submission.Work.Pi6.MSS.tensorDual
import Submission.Work.Pi6.MSS.e1CohDual
import Submission.Work.SSSR.serreE1R
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The additive `E_2` identification of the cohomological Serre spectral sequence

For a Serre fibration `p : E → B` over a simply connected base, with fibre `F = p⁻¹(p e₀)` and
coefficients in a field `𝕜`, the `E_2` page of the Serre cochain filtration `serreCF 𝕜 E B p` in
bidegree `(s,q)` is `H^s(B;𝕜) ⊗ H^q(F;𝕜)`:

`Work.Pi6.MSS.e2Add`.

The proof is the composite of five identifications, all of them already available in the tree:

* `E_2^{s,q} ≅ H^s(E_1^{•,q})` — `Work.Pi6.MSS.pageTwo` (`E_2 = H(E_1)`);
* `E_1^{•,q} ≅ Hof(N_*(B;𝕜) ⊗ H_q(F;𝕜))` — `Work.Pi6.MSS.e1DualGlue` below (the `𝕜`-dual of the
  chain level `E_1` row: `Work.Pi6.MSS.e1CohDual` + the coefficient-ring-generic
  `Work.SSSR.serreE1R`, glued along the existence of the Serre filtration
  `Work.SSSR.serreFiltrationR`);
* `H^s(Hom(N_*(B) ⊗ H_q(F),𝕜)) ≅ H^s(Hom(N_*(B),𝕜)) ⊗ (H_q(F) →ₗ 𝕜)` —
  `Work.Pi6.MSS.tensorDual` (needs `H_q(F;𝕜)` finite dimensional, supplied by the hypotheses and
  the field duality `Work.StemsB.fieldDualUCT`);
* `H^s(Hom(N_*(B),𝕜)) ≅ H^s(B;𝕜)` — `Work.Pi6.MSS.normCoh` (normalised = unnormalised chains);
* `(H_q(F) →ₗ 𝕜) ≅ H^q(F;𝕜)` — `Work.StemsB.fieldDualUCT` again (universal coefficients over a
  field).
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The `E_1` row as the dual of the chain level `E_1` row

The two inputs are `Work.Pi6.MSS.e1CohDual` (the cohomological `E_1` row is the `𝕜`-dual of the
chain level `E_1` complex of the Serre filtration) and `Work.SSSR.serreE1R` (the chain level `E_1`
complex is `N_*(B;𝕜) ⊗ H_q(F;𝕜)`), together with the existence of the Serre filtration
`Work.SSSR.serreFiltrationR`. -/

/-- **The dual of an isomorphism of chain complexes.**  The `𝕜`-dual cochain complex is a
contravariant functor, so an isomorphism `C ≅ D` of chain complexes induces an isomorphism
`dualComplex 𝕜 C ≅ dualComplex 𝕜 D` of the dual cochain complexes. -/
def dualIsoMap {𝕜 : Type} [CommRing 𝕜] {C D : ChainComplex (ModuleCat 𝕜) ℕ} (e : C ≅ D) :
    Work.Cohomology.dualComplex 𝕜 C ≅ Work.Cohomology.dualComplex 𝕜 D where
  hom := Work.Cohomology.dualComplexMap 𝕜 D C e.inv
  inv := Work.Cohomology.dualComplexMap 𝕜 C D e.hom
  hom_inv_id := by
    rw [← Work.Cohomology.dualComplexMap_comp 𝕜 e.hom e.inv, Iso.hom_inv_id,
      Work.Cohomology.dualComplexMap_id 𝕜 C]
  inv_hom_id := by
    rw [← Work.Cohomology.dualComplexMap_comp 𝕜 e.inv e.hom, Iso.inv_hom_id,
      Work.Cohomology.dualComplexMap_id 𝕜 D]

/-- **The `E_1` row of the cohomological Serre spectral sequence of a Serre fibration over a simply
connected base, over any field `𝕜`, is the `𝕜`-dual of the chain level `E_1` row
`N_*(B;𝕜) ⊗ H_q(F;𝕜)`.** -/
theorem e1DualGlue (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ) :
    Nonempty (E1Row 𝕜 (serreCF 𝕜 E B p) q ≅
      Work.Cohomology.dualComplex 𝕜
        (tensorC 𝕜 (normC 𝕜 B)
          ((Work.Cohomology.singularChains 𝕜
            (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology q))) := by
  obtain ⟨ξ, hξ⟩ := Work.SSSR.serreFiltrationR 𝕜 E B p
  have hξ' : ξ.F = Work.SSSR.serF 𝕜 (Work.SSS.sSingP p) := by
    rw [hξ]
    rfl
  obtain ⟨e1⟩ := e1CohDual 𝕜 E B p q ξ hξ'
  obtain ⟨e2⟩ := Work.SSSR.serreE1R 𝕜 E B p e₀ hfib hconn ξ hξ q
  exact ⟨e1 ≪≫ dualIsoMap e2⟩

/-! ## Over a field, a space whose dual is finite dimensional is finite dimensional -/

theorem finiteDimensional_of_finiteDimensional_dual (𝕜 : Type) [Field 𝕜] (V : Type)
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 (V →ₗ[𝕜] 𝕜)] :
    FiniteDimensional 𝕜 V := by
  classical
  exact FiniteDimensional.of_injective (Module.Dual.eval 𝕜 V)
    ((Module.Free.chooseBasis 𝕜 V).eval_injective)

theorem e2Add (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N) :
    Nonempty (Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 s (s + q) ≅
      ModuleCat.of 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))) := by
  classical
  -- the fibre and its homology
  haveI hCohF : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := hfin q hq
  obtain ⟨eFib0⟩ := Work.StemsB.fieldDualUCT (F := 𝕜)
    (Work.Cohomology.singularChains 𝕜 (TopCat.of (Work.StemsB.fibre p (p e₀)))) q
  haveI hHq : FiniteDimensional 𝕜 ((Work.Cohomology.singularChains 𝕜
      (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology q) := by
    haveI hd : FiniteDimensional 𝕜 ((Work.Cohomology.dualComplex 𝕜
        (Work.Cohomology.singularChains 𝕜
          (TopCat.of (Work.StemsB.fibre p (p e₀))))).homology q) := hCohF
    haveI hdual : FiniteDimensional 𝕜 (((Work.Cohomology.singularChains 𝕜
        (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology q) →ₗ[𝕜] 𝕜) :=
      LinearEquiv.finiteDimensional (Iso.toLinearEquiv eFib0)
    exact finiteDimensional_of_finiteDimensional_dual 𝕜 _
  -- the four comparison isomorphisms
  obtain ⟨ePage⟩ := pageTwo 𝕜 (serreCF 𝕜 E B p) q s
  obtain ⟨eE1⟩ := e1DualGlue 𝕜 E B p e₀ hfib hconn q
  obtain ⟨eTD⟩ := tensorDual 𝕜 (normC 𝕜 B)
    ((Work.Cohomology.singularChains 𝕜 (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology q) s
  obtain ⟨eN⟩ := normCoh 𝕜 B s
  -- the tensor factor identifications
  have eFib : (((Work.Cohomology.singularChains 𝕜
      (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology q) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
      Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q :=
    (Iso.toLinearEquiv eFib0).symm
  have eNorm : ((Work.Cohomology.dualComplex 𝕜 (normC 𝕜 B)).homology s) ≃ₗ[𝕜]
      Work.Pi6.Coh 𝕜 B s := Iso.toLinearEquiv eN
  have eTen : TensorProduct 𝕜 ((Work.Cohomology.dualComplex 𝕜 (normC 𝕜 B)).homology s)
      (((Work.Cohomology.singularChains 𝕜
        (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology q) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
      TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s) (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :=
    TensorProduct.congr eNorm eFib
  refine ⟨pEcastN 𝕜 (serreCF 𝕜 E B p) 2 s (by omega) ≪≫ ePage ≪≫
    HomologicalComplex.homologyMapIso eE1 s ≪≫ eTD ≪≫ LinearEquiv.toModuleIso eTen⟩

end

end Work.Pi6.MSS
