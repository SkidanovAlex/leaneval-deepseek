import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.map_eq_zero_of_mono_valuation
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero

set_option maxHeartbeats 2000000

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory

/-- **A `map` on group cohomology factors through the `map` for the identity group homomorphism.**
For a group homomorphism `f : G →* H`, a representation morphism `φ : Res(f)(A) ⟶ B` and a degree
`n`, the induced map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` factors as the restriction along `f`, followed by the
map on `Hⁿ(G, Res(f)(A))` induced by `φ` (with the identity group homomorphism). -/
lemma map_eq_map_id_comp_map
    {k G H : Type} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ) :
    groupCohomology.map f φ n
      = groupCohomology.map f (𝟙 (Rep.res f A)) n ≫
        groupCohomology.map (MonoidHom.id G) φ n := by
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr (MonoidHom.comp_id f).symm ?_ n
  ext x
  simp

theorem res_comp_inf_eq_zero_of_ord
    {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep.{0,0,0} ℤ G)
    (ord₁ : Rep.res ((QuotientGroup.mk' M).comp N.subtype) (A.quotientToInvariants M)
      ⟶ Rep.trivial ℤ N ℤ)
    (ord₂ : Rep.res (MonoidHom.id N) (Rep.res N.subtype A)
      ⟶ Rep.trivial ℤ N ℤ)
    (ι : Rep.res ((QuotientGroup.mk' M).comp N.subtype) (A.quotientToInvariants M)
      ⟶ Rep.res N.subtype A)
    [Fintype N]
    (hmono : CategoryTheory.Mono (groupCohomology.map (MonoidHom.id N) ord₂ 2))
    (e : ℕ) (hι : CategoryTheory.CategoryStruct.comp ι ord₂ = e • ord₁)
    (he : Nat.card N ∣ e)
    (hfac : CategoryTheory.CategoryStruct.comp ((groupCohomology.infNatTrans ℤ M 2).app A)
        ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A)
      = groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype) ι 2) :
    CategoryTheory.CategoryStruct.comp ((groupCohomology.infNatTrans ℤ M 2).app A)
        ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A) = 0 := by
  -- The map on `H²` induced by `ι` with the identity group homomorphism vanishes.
  have h1 : (groupCohomology.map (MonoidHom.id N) ι 2
      : groupCohomology (Rep.res ((QuotientGroup.mk' M).comp N.subtype) (A.quotientToInvariants M)) 2
        ⟶ groupCohomology (Rep.res N.subtype A) 2) = 0 :=
    map_eq_zero_of_mono_valuation (G := N)
      (B₁ := Rep.res ((QuotientGroup.mk' M).comp N.subtype) (A.quotientToInvariants M))
      (B₂ := Rep.res N.subtype A)
      ord₁ (show Rep.res N.subtype A ⟶ Rep.trivial ℤ N ℤ from ord₂) hmono ι e hι he
  -- Hence the map induced by `ι` with the group homomorphism `N → G ⧸ M` vanishes as well.
  have h2 : (groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype) ι 2
      : groupCohomology (A.quotientToInvariants M) 2 ⟶ groupCohomology (Rep.res N.subtype A) 2)
      = 0 := by
    rw [map_eq_map_id_comp_map]
    rw [h1]
    simp
  rw [hfac]
  exact h2

end Commons.RepresentationTheory.GroupCohomology
