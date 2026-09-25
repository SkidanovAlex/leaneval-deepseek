import Mathlib
import Submission.Work.CFTLib.RelShafReps
import Submission.Work.CFTLib.NKIdeles
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.subsingleton_tateCohomology_neg_one_localUnitIdeles
import Submission.Work.CFTLib.subsingleton_tateCohomology_localUnitIdeles_zero
import Submission.Work.CFTLib.finite_tateCohomology_clRep_neg_one
import Submission.Work.CFTLib.RelShafSESData
import Submission.Work.CFTLib.exists_relShafSESData
import Submission.Work.CFTLib.rankP_tate_middle_le
import Submission.Work.CFTLib.moduleFinite_tensor_h0_oUnitsRep
import Submission.Work.CFTLib.rankP_le_rankP_of_injective
import Submission.Work.CFTLib.rankP_h0_oUnits_le
import Submission.Work.CFT.ClassFormation.rankP_eq_of_addEquiv

/-!
# The `p`-rank of `Ĥ⁻¹(G, C_K)` is bounded by the units plus the class group

For `K/F` a finite Galois extension of number fields, unramified at all finite places with the real
places staying real, the four-term exact sequence `1 → 𝒪_Kˣ → J_K → C_K → Cl(𝓞 K) → 1` of
`ℤ[Gal(K/F)]`-modules gives, in low Tate cohomology, the bound

`rank_p Ĥ⁻¹(G, C_K) ≤ rank_p Ĥ⁰(G, 𝒪_Kˣ) + rank_p Ĥ⁻¹(G, Cl(𝓞 K))`,

the finite-level form of Roquette's idèle computation.  The two connecting maps of the long exact
sequences of the two short exact sequences cut out of the four-term sequence are combined with the
vanishing `Ĥ⁰(J_K) = Ĥ⁻¹(J_K) = 0` for unramified `K/F`.
-/

open scoped TensorProduct
open NumberField CategoryTheory

namespace Work.CFTLib

open NK.GlobalCFT

theorem rankP_hm1_ideleClass_le {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime]
    (hUnr : CFTLib.IsUnramified F K) :
    Work.CFT.ClassFormation.rankP p
        ↑(tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1))
      ≤ Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.oUnitsRep F K) 0)
        + Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.clRep F K) (-1)) := by
  classical
  obtain ⟨d⟩ := exists_relShafSESData (F := F) (K := K)
  -- vanishing of Ĥ⁻¹ and Ĥ⁰ of the unit idèles
  have hJ1 : Subsingleton ↥(tateCohomology d.ses1.X₂ (-1)) :=
    d.ses1X2.symm ▸ subsingleton_tateCohomology_neg_one_localUnitIdeles (F := F) (K := K) hUnr
  have hJ0 : Subsingleton ↥(tateCohomology d.ses1.X₂ 0) :=
    d.ses1X2.symm ▸ subsingleton_tateCohomology_localUnitIdeles_zero (F := F) (K := K) hUnr
  -- the connecting map is an isomorphism
  have hex3 : LinearMap.range ((tateCohomologyFunctor (-1)).map d.ses1.g).hom
      = LinearMap.ker (TateCohomology.δ d.ses1Exact (-1)).hom :=
    (TateCohomology.exact₃ d.ses1Exact (-1)).moduleCat_range_eq_ker
  have hex1 : LinearMap.range (TateCohomology.δ d.ses1Exact (-1)).hom
      = LinearMap.ker ((tateCohomologyFunctor (0 : ℤ)).map d.ses1.f).hom :=
    (TateCohomology.exact₁ d.ses1Exact (-1)).moduleCat_range_eq_ker
  have hkerδ : LinearMap.ker (TateCohomology.δ d.ses1Exact (-1)).hom = ⊥ := by
    rw [← hex3]
    refine (Submodule.eq_bot_iff _).mpr ?_
    rintro x ⟨y, rfl⟩
    rw [Subsingleton.elim y 0, map_zero]
  have hinjδ : Function.Injective (TateCohomology.δ d.ses1Exact (-1)).hom :=
    LinearMap.ker_eq_bot.mp hkerδ
  have htop : LinearMap.ker ((tateCohomologyFunctor (0 : ℤ)).map d.ses1.f).hom = ⊤ := by
    rw [LinearMap.ker_eq_top, LinearMap.ext_iff]
    intro x
    exact Subsingleton.elim _ _
  have hsurjδ : Function.Surjective (TateCohomology.δ d.ses1Exact (-1)).hom := by
    rw [← LinearMap.range_eq_top, hex1, htop]
  have hiso : ↥(tateCohomology d.ses1.X₃ (-1)) ≃ₗ[ℤ] ↥(tateCohomology d.ses1.X₁ 0) :=
    LinearEquiv.ofBijective _ ⟨hinjδ, hsurjδ⟩
  have hstep2 :
      Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses1.X₃ (-1))
        = Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses1.X₁ 0) :=
    Work.CFT.ClassFormation.rankP_eq_of_addEquiv p hiso.toAddEquiv
  -- finiteness inputs
  have hfin₀ : Module.Finite (ZMod p)
      (ZMod p ⊗[ℤ] ↑(tateCohomology (Work.CFTLib.oUnitsRep F K) 0)) :=
    moduleFinite_tensor_h0_oUnitsRep (F := F) (K := K) p
  have hfinA : Module.Finite (ZMod p)
      (ZMod p ⊗[ℤ] ↑(tateCohomology d.ses1.X₁ 0)) := by
    have hL : ↥(tateCohomology d.ses1.X₁ 0)
        ≃ₗ[ℤ] ↥(tateCohomology (Work.CFTLib.oUnitsRep F K) 0) :=
      (eqToIso (congrArg (fun M => tateCohomology M 0) d.ses1X1)).toLinearEquiv
    have hsurj : Function.Surjective (AddMonoidHom.toZModLinearMap p
        (((TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) hL).symm).toLinearMap).toAddMonoidHom) :=
      (TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) hL).symm.surjective
    exact Module.Finite.of_surjective (hM := hfin₀) _ hsurj
  have hfinB : Module.Finite (ZMod p)
      (ZMod p ⊗[ℤ] ↑(tateCohomology d.ses1.X₃ (-1))) := by
    have hsurj : Function.Surjective (AddMonoidHom.toZModLinearMap p
        (((TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) hiso).symm).toLinearMap).toAddMonoidHom) :=
      (TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) hiso).symm.surjective
    exact Module.Finite.of_surjective (hM := hfinA) _ hsurj
  have hfinC : Module.Finite (ZMod p)
      (ZMod p ⊗[ℤ] ↑(tateCohomology d.ses2.X₁ (-1))) := by
    have hL : ↥(tateCohomology d.ses2.X₁ (-1))
        ≃ₗ[ℤ] ↥(tateCohomology d.ses1.X₃ (-1)) :=
      (eqToIso (congrArg (fun M => tateCohomology M (-1))
        (d.ses2X1.trans d.ses1X3.symm))).toLinearEquiv
    have hsurj : Function.Surjective (AddMonoidHom.toZModLinearMap p
        (((TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) hL).symm).toLinearMap).toAddMonoidHom) :=
      (TensorProduct.congr (LinearEquiv.refl ℤ (ZMod p)) hL).symm.surjective
    exact Module.Finite.of_surjective (hM := hfinB) _ hsurj
  have hZfin : Finite ↥(tateCohomology d.ses2.X₃ (-1)) := by
    have h := (finite_tateCohomology_clRep_neg_one (F := F) (K := K)).1
    rw [d.ses2X3]; exact h
  have hstep1 : Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses2.X₂ (-1))
      ≤ Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses2.X₁ (-1))
        + Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses2.X₃ (-1)) :=
    rankP_tate_middle_le p d.ses2 d.ses2Exact (-1) hfinC hZfin
  calc Work.CFT.ClassFormation.rankP p
        ↑(tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1))
      = Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses2.X₂ (-1)) := by rw [d.ses2X2]
    _ ≤ Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses2.X₁ (-1))
          + Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses2.X₃ (-1)) := hstep1
    _ = Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses1.X₃ (-1))
          + Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.clRep F K) (-1)) := by
        rw [d.ses2X1, d.ses1X3.symm, d.ses2X3]
    _ = Work.CFT.ClassFormation.rankP p ↑(tateCohomology d.ses1.X₁ 0)
          + Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.clRep F K) (-1)) := by
        rw [hstep2]
    _ = Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.oUnitsRep F K) 0)
          + Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.clRep F K) (-1)) := by
        rw [d.ses1X1]

end Work.CFTLib
