import Mathlib
import Submission.NK.GlobalCFTdeep.CoCore.Cyclic
import Submission.NK.GlobalCFTdeep.CoCore.H1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Herbrand-quotient computation from the cohomological field axiom

For a finite Galois extension `L / K` of number fields with **cyclic** Galois group `G`, the
cohomological field axiom (`H¹(H, C_L) = 0` and `|H²(H, C_L)| = |H|` for every subgroup `H ≤ G`,
plus a fundamental class of order `[L : K]`) already determines the Herbrand quotient of the
idèle class group:

  `h(G, C_L) = |Ĥ⁰(G, C_L)| / |Ĥ¹(G, C_L)| = [L : K]`.

The three inputs are

* `Ĥ¹(G, C_L) ≅ H¹(G, C_L) = 0` (Tate cohomology agrees with group cohomology in positive
  degrees, `TateCohomology.isoGroupCohomology`, together with `h.h1_trivial` at the top subgroup),
  so that `|Ĥ¹(G, C_L)| = 1`;
* `Ĥ⁰(G, C_L) ≅ H²(G, C_L)` by the two-periodicity of the cohomology of a cyclic group
  (`NK.GlobalCFTdeep.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero`), together with
  `h.h2_card` at the top subgroup, which gives `|Ĥ⁰(G, C_L)| = |G| = [L : K]`
  (`IsGalois.card_aut_eq_finrank`);
* the cross-multiplied form of the Herbrand quotient, `|Ĥ⁰| = [L : K] · |Ĥ¹|`.

No reciprocity is used: this is the direction "cohomological field axiom ⟹ Herbrand quotient",
i.e. the abstract part of Milne, *Class Field Theory*, Theorem 4.3 for the cyclic case (Milne's own
proof of `h(G, C_L) = [L : K]` proceeds instead through the `S`-idèles and `S`-units, see
`Herbrand/Reduction.lean`).
-/

namespace NK.GlobalCFTdeep.Herbrand

/-- **Milne, *CFT*, Theorem 4.3, from the cohomological field axiom.**  For a cyclic Galois
extension of number fields, the cohomological field axiom computes the Herbrand quotient of the
idèle class group: `|Ĥ⁰(G, C_L)| = [L : K] · |Ĥ¹(G, C_L)|` with `Ĥ¹(G, C_L)` finite.

Indeed `Ĥ¹(G, C_L) ≅ H¹(G, C_L) = 0` and `Ĥ⁰(G, C_L) ≅ H²(G, C_L)` has order `|G| = [L : K]`. -/
theorem herbrandQuotient_of_cohomologicalFieldAxiom {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (h : NK.GlobalCFT.CohomologicalFieldAxiom K L) :
    NK.GlobalCFT.HerbrandQuotient K L := by
  -- `Ĥ¹(G, C_L) ≅ H¹(G, C_L) = 0`, so `|Ĥ¹(G, C_L)| = 1`.
  have hcard1 : Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 1) = 1 := by
    have hsub : Subsingleton (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 1) :=
      Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_of_subsingleton_groupCohomology
        _ 1 (Commons.RepresentationTheory.TateCohomology.subsingleton_groupCohomology_top _
          1 (h.h1_trivial ⊤))
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
  -- `|H²(G, C_L)| = |G| = [L : K]` from the field axiom at the top subgroup.
  have hcard2_res : Nat.card (groupCohomology
      (Rep.res (⊤ : Subgroup (L ≃ₐ[K] L)).subtype (NK.GlobalCFT.IdeleClassGroup.rep K L)) 2)
      = Nat.card (L ≃ₐ[K] L) := by
    rw [h.h2_card ⊤]
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have hcard2 : Nat.card (groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 2)
      = Nat.card (L ≃ₐ[K] L) := by
    obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.groupCohomology_top_iso
      (NK.GlobalCFT.IdeleClassGroup.rep K L) 2
    exact (Nat.card_congr e.toLinearEquiv.toEquiv).symm.trans hcard2_res
  -- Two-periodicity of the cohomology of the cyclic group `G`: `Ĥ⁰(G, C_L) ≅ H²(G, C_L)`.
  have h0 : Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 0)
      = Module.finrank K L := by
    rw [← NK.GlobalCFTdeep.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero
        (K := K) (L := L),
      hcard2, IsGalois.card_aut_eq_finrank K L]
  refine ⟨?_, ?_⟩
  · rw [hcard1]; norm_num
  · rw [h0, hcard1, mul_one]

end NK.GlobalCFTdeep.Herbrand
