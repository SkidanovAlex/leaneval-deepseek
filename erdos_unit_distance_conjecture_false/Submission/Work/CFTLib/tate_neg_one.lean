import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.TateH2
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
import Submission.Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_neg_of_pos

/-! Guidance from the project lead (the requester):

# Tate's theorem in degree −1 (Tate–Nakayama; Serre, Local Fields IX §8 Thm 13; Milne CFT II.3.11)

Abstract group cohomology, no number theory. For a finite p-group G and a ℤ[G]-module C with H¹(H,C)=0 and
|H²(H,C)| = |H| for every subgroup H, and a fundamental class α ∈ H²(G,C) of order |G|, prove
H₂(G,ℤ) ≅ Ĥ⁻¹(G,C). (Ĥ⁻³(G,ℤ) = H₂(G,ℤ).)

## Route

`NU.exists_normalized_cocycle` normalises `α` to a `2`-cocycle `z` with `z (g,1) = 0`, and
`NU.subsingleton_tateCohomology_Sprint` (the Nakayama–Rim criterion, via the splitting module
`A(α) : 0 → C → C(α) → I_G → 0`, which is cohomologically trivial for a `p`-group) makes the
middle term of that sequence acyclic in every degree.  Hence the connecting homomorphism of

* `0 → C → C(α) → I_G → 0`, read in degree `-2`, gives `Ĥ⁻²(G, I_G) ≅ Ĥ⁻¹(G, C)`;
* `0 → I_G → ℤ[G] → ℤ → 0`, read in degree `-3`, gives `Ĥ⁻³(G, ℤ) ≅ Ĥ⁻²(G, I_G)`.

Composing with `H_2(G, ℤ) ≅ Ĥ⁻³(G, ℤ)` (`Schur.HnZ_two_addEquiv_tate`) yields the claim.
-/

namespace Work.CFTLib

open Work.CFT.ClassFormation

/-- **Tate's theorem in degree `-1`.**  For a finite `p`-group `G` and a `ℤ[G]`-module `C` with
`H¹(H, C) = 0` and `|H²(H, C)| = |H|` for every subgroup `H`, a fundamental class
`α ∈ H²(G, C)` of additive order `|G|` yields an isomorphism `H₂(G, ℤ) ≅ Ĥ⁻¹(G, C)`. -/
theorem tate_neg_one {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (C : Rep ℤ G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (α : groupCohomology C 2) (hα : addOrderOf α = Nat.card G) :
    Nonempty (Work.CFT.ClassFormation.HnZ G 2 ≃+ tateCohomology C (-1)) := by
  -- a finite `p`-group is nilpotent, hence solvable: this is the hypothesis of the
  -- Nakayama–Rim criterion used below.
  haveI : Group.IsSolvable G := by
    haveI : Group.IsNilpotent G := IsPGroup.isNilpotent hG
    infer_instance
  -- normalise the fundamental class to a 2-cocycle `z` with `z (g, 1) = 0`
  obtain ⟨z, hzα, hz⟩ := NU.exists_normalized_cocycle C α
  -- the splitting module `C(α)` is cohomologically trivial (acyclic in every degree)
  have hacyc := NU.subsingleton_tateCohomology_Sprint C z hz α hzα hα h1 h2
  -- `0 → I_G → ℤ[G] → ℤ → 0` in degree `-3`: `Ĥ⁻³(G, ℤ) ≅ Ĥ⁻²(G, I_G)`
  have hL1 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ (-3)) :=
    NU.subsingleton_tateCohomology_leftRegular G (-3)
  have hL2 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ ((-3 : ℤ) + 1)) :=
    NU.subsingleton_tateCohomology_leftRegular G ((-3 : ℤ) + 1)
  obtain ⟨e1⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.IShort (G := G)) (NU.IShort_shortExact (G := G)) (-3) hL1 hL2
  -- `0 → C → C(α) → I_G → 0` in degree `-2`: `Ĥ⁻²(G, I_G) ≅ Ĥ⁻¹(G, C)`
  have hA1 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ (-2)) := hacyc (-2)
  have hA2 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ ((-2 : ℤ) + 1)) :=
    hacyc ((-2 : ℤ) + 1)
  obtain ⟨e2⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.AShortZ C z hz) (NU.AShortZ_shortExact C z hz) (-2) hA1 hA2
  -- compose with `H_2(G, ℤ) ≅ Ĥ⁻³(G, ℤ)`
  exact ⟨(Schur.HnZ_two_addEquiv_tate G).trans (e1.trans e2).toAddEquiv⟩

end Work.CFTLib
