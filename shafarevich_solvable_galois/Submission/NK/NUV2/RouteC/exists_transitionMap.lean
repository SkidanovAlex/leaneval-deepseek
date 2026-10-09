import Mathlib
import Submission.NK.NUV2.RouteC.inf_injective_range_eq
import Submission.NK.NUV2.RouteC.h2_card_eq_card_of_abelian_local

/-!
# The transition map on local fundamental classes (Route C, step L3, existence part)

For a finite Galois extension `L₃/L₂` of number fields, places `q₃ | q₂` and a pair of *normal*
subgroups `N₂ ≤ N₁` of the local Galois group `G = Gal((L₃)_{q₃} / (L₂)_{q₂})`, let

`Inf_M : H²(G ⧸ M, Eᴹˣ) ⟶ H²(G, Eˣ)`

be the inflation along `G → G ⧸ M`.  Step L2 (`NK.NUV2.RouteC.inf_injective_range_eq`) says that
`Inf_M` is injective with image the `|G ⧸ M|`-torsion subgroup of `H²(G, Eˣ)`.

This file draws the consequence that the *transition map* is well defined: every class `u` at the
level `N₂` has a (necessarily unique) preimage `u'` at the level `N₁` under `Inf_{N₁}`, provided one
twists `u` by the index ratio `|G ⧸ N₂| / |G ⧸ N₁|`.  Concretely

`Inf_{N₁}(u') = (|G ⧸ N₂| / |G ⧸ N₁|) • Inf_{N₂}(u)`,

which is the compatibility relation for a compatible system of fundamental classes: with
`L = E^{N₁} ⊆ E' = E^{N₂}` the ratio is `[E' : L]`, so this is exactly `Inf_{L→E'}(u_L) =
[E' : L] · Inf_{E'}(u_{E'})` of the plan.

*Uniqueness* is injectivity of `Inf_{N₁}` (L2).  *Existence* is the computation
`|G ⧸ N₁| • ((|G ⧸ N₂| / |G ⧸ N₁|) • Inf_{N₂}(u)) = |G ⧸ N₂| • Inf_{N₂}(u) = 0`, where the last
vanishing is the range description of L2 at the level `N₂` (equivalently:
`Nat.card (G ⧸ N₂) • u = 0`, `Nat.card_nsmul_H2_eq_zero`), so the twist lies in the `|G ⧸ N₁|`-torsion
`= range Inf_{N₁}`.  The divisibility `|G ⧸ N₁| ∣ |G ⧸ N₂|` is `Subgroup.index_dvd_of_le h`
together with `Subgroup.index_eq_card`.

Note that no hypothesis on the *order* of `u` is needed: the statement holds for every class `u`.
-/

set_option linter.style.haveILetI false

open IsDedekindDomain CategoryTheory

namespace NK.NUV2.RouteC

theorem exists_transitionMap {L₂ L₃ : Type} [Field L₂] [NumberField L₂] [Field L₃]
    [NumberField L₃] [Algebra L₂ L₃] [FiniteDimensional L₂ L₃] [IsGalois L₂ L₃]
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (q₃ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₃))
    (hq₃₂ : q₃.asIdeal.LiesOver q₂.asIdeal)
    (N₁ N₂ : Subgroup (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂)) [N₁.Normal]
    [N₂.Normal] (h : N₂ ≤ N₁)
    (u : groupCohomology ((NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂).quotientToInvariants N₂) 2)
    (hu : addOrderOf u = Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂)) :
    ∃! u' : groupCohomology ((NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂).quotientToInvariants N₁) 2,
      (groupCohomology.infNatTrans ℤ N₁ 2).app (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂) u'
        = (Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) /
            Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₁) : ℤ)
          • (groupCohomology.infNatTrans ℤ N₂ 2).app (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂) u := by
  -- step L2 at the two levels: injectivity of `Inf` and its range as the torsion subgroup
  obtain ⟨hinj, hrange⟩ := inf_injective_range_eq q₂ q₃ hq₃₂ N₁
  obtain ⟨_, hrange₂⟩ := inf_injective_range_eq q₂ q₃ hq₃₂ N₂
  -- the index ratio, on the level of integer scalars
  have hcard : Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₁)
      ∣ Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) := by
    have h1 : Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₁) = N₁.index :=
      (Subgroup.index_eq_card N₁).symm
    have h2 : Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) = N₂.index :=
      (Subgroup.index_eq_card N₂).symm
    rw [h1, h2]
    exact Subgroup.index_dvd_of_le h
  have hk : (Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₁) : ℤ)
      * ((Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) : ℤ)
          / (Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₁) : ℤ))
      = (Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) : ℤ) := by
    rw [← Int.natCast_ediv, ← Nat.cast_mul, Nat.mul_div_cancel' hcard]
  -- the class `Inf_{N₂} u` is killed by `|G ⧸ N₂|` (L2 at the level `N₂`)
  have hnat : (Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) : ℤ) •
      (groupCohomology.infNatTrans ℤ N₂ 2).app (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂) u = 0 := by
    have hmem : ((groupCohomology.infNatTrans ℤ N₂ 2).app
        (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom u ∈
        LinearMap.range ((groupCohomology.infNatTrans ℤ N₂ 2).app
          (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom :=
      LinearMap.mem_range_self _ u
    rw [hrange₂] at hmem
    have hh := LinearMap.mem_ker.mp hmem
    simpa using hh
  -- the twist lies in the `|G ⧸ N₁|`-torsion, i.e. in the range of `Inf_{N₁}`
  have hmem : ((Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) : ℤ)
        / (Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₁) : ℤ)) •
        ((groupCohomology.infNatTrans ℤ N₂ 2).app
          (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom u
      ∈ LinearMap.range ((groupCohomology.infNatTrans ℤ N₁ 2).app
          (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom := by
    have hsmul_id : ∀ {M : Type} [AddCommGroup M] [Module ℤ M] (c : ℤ) (w : M),
        ((c • (LinearMap.id : M →ₗ[ℤ] M)) w) = c • w := by
      intro M _ _ c w
      simp
    rw [hrange, LinearMap.mem_ker, hsmul_id, ← mul_zsmul, hk]
    exact hnat
  -- existence (from the range description) and uniqueness (from injectivity)
  obtain ⟨u', hu'⟩ := LinearMap.mem_range.mp hmem
  exact ⟨u', hu', fun v hv => hinj (hv.trans hu'.symm)⟩

end NK.NUV2.RouteC
