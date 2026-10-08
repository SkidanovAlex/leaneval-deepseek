import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.eq_top_of_isConjInvariant
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-! ## Z4: the unipotent group `U` is abelian

Auxiliary facts for `Work.ZASS.isMulCommutative_of_zass`, kept in the namespace
`Work.ZASS.Z4` so as not to collide with the parallel work of the other agents of the area. -/
namespace Z4

open Work.Zassenhaus

variable {G X : Type} [Group G] [MulAction G X]

/-- **Z4, auxiliary.** `H = G_{∞0}` lies in the normalizer of `U`, because `U ⊴ B` and
`H ≤ B = G_∞`: both `h` and `h⁻¹` conjugate `U` into itself. -/
theorem pairStab_le_normalizer {inf zero : X} {U : Subgroup G}
    (hUB : U ≤ borel G inf) (hN : (U.subgroupOf (borel G inf)).Normal) :
    pairStab G inf zero ≤ Subgroup.normalizer (U : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact mem_conjBy_of_subgroupOf_normal hUB hN (pairStab_le_borel inf zero hh) hx
  · intro hx
    have hh' : h⁻¹ ∈ pairStab G inf zero := inv_mem hh
    have hx' := mem_conjBy_of_subgroupOf_normal hUB hN (pairStab_le_borel inf zero hh') hx
    have hval : conjBy h⁻¹ (h * x * h⁻¹) = x := by simp only [conjBy]; group
    rwa [hval] at hx'

/-- **Z4, auxiliary.** The center of `U`, viewed as a subgroup of the ambient group `G`, is
invariant under conjugation by any subgroup `H` of `N_G(U)`: conjugation by `h ∈ N_G(U)`
permutes `U`, hence permutes the elements of `U` that commute with all of `U`. -/
theorem isConjInvariant_map_center {U H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (U : Set G)) :
    IsConjInvariant H (Subgroup.map U.subtype (Subgroup.center U)) := by
  intro h hh w hw
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
  have hmem : conjBy h (x : G) ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hH hh) (x : G)).mp x.2
  refine Subgroup.mem_map.mpr ⟨⟨conjBy h (x : G), hmem⟩, ?_, rfl⟩
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  show (g : G) * conjBy h (x : G) = conjBy h (x : G) * (g : G)
  -- `conjBy h` maps `U` bijectively onto itself, so `g = conjBy h y` with `y ∈ U`
  have hg' : h⁻¹ ∈ H := inv_mem hh
  have hy : conjBy h⁻¹ (g : G) ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hH hg') (g : G)).mp g.2
  have hcomm : conjBy h⁻¹ (g : G) * (x : G) = (x : G) * conjBy h⁻¹ (g : G) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨conjBy h⁻¹ (g : G), hy⟩)
  have hconj : conjBy h (conjBy h⁻¹ (g : G)) = (g : G) := by simp only [conjBy]; group
  calc (g : G) * conjBy h (x : G)
      = conjBy h (conjBy h⁻¹ (g : G)) * conjBy h (x : G) := by rw [hconj]
    _ = conjBy h (conjBy h⁻¹ (g : G) * (x : G)) := by simp only [conjBy]; group
    _ = conjBy h ((x : G) * conjBy h⁻¹ (g : G)) := by rw [hcomm]
    _ = conjBy h (x : G) * conjBy h (conjBy h⁻¹ (g : G)) := by simp only [conjBy]; group
    _ = conjBy h (x : G) * (g : G) := by rw [hconj]

end Z4

/-- **Z4 (blueprint §ZASS).** The unipotent group `U` is abelian.  The center `Z(U)` is
nontrivial (`IsPGroup.center_nontrivial`), `H = G_{∞0}` normalizes `U` (as `U ⊴ B` and
`H ≤ B`), hence preserves `Z(U)`, and `Z(U)` is a nontrivial `H`-invariant subgroup of `U`;
`ZASS/eq_top_of_isConjInvariant` (applied to `W = Z(U)`) gives `Z(U) = U`, i.e. `U` is
abelian. -/
theorem isMulCommutative_of_zass {G X : Type} [Group G] [Finite G] [MulAction G X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 1 ≤ k) {q : ℕ} (hq : q = p ^ k)
    {inf zero : X} {U : Subgroup G} (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hcardU : Nat.card U = p ^ k)
    (hcardH : Nat.card (Work.Zassenhaus.pairStab G inf zero) = (q - 1) / 2)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hfix : Work.ZASS.FixedPointFreeConj U (Work.Zassenhaus.pairStab G inf zero)) :
    IsMulCommutative U := by
  subst hq
  set W : Subgroup G := Subgroup.map U.subtype (Subgroup.center U) with hWdef
  -- `H = G_{∞0}` lies in `N_G(U)`
  have hHle : Work.Zassenhaus.pairStab G inf zero ≤ Subgroup.normalizer (U : Set G) :=
    Z4.pairStab_le_normalizer hUB hN
  -- `W = Z(U) ≤ U`, and `U` is a `p`-group of order `p^k`
  have hWU : W ≤ U := Subgroup.map_subtype_le (Subgroup.center U)
  have hUP : IsPGroup p U := IsPGroup.of_card hcardU
  -- `W` is nontrivial: the center of the nontrivial `p`-group `U` is nontrivial
  have hWne : W ≠ ⊥ := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hU1 : 1 < Nat.card U := by rw [hcardU]; omega
    have hntU : Nontrivial ↥U := Finite.one_lt_card_iff_nontrivial.mp hU1
    have hntZ : Nontrivial ↥(Subgroup.center U) := IsPGroup.center_nontrivial hUP
    have hZ1 : 1 < Nat.card ↥(Subgroup.center U) :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hW1 : 1 < Nat.card W := by rw [hWdef, Subgroup.card_subtype]; exact hZ1
    exact (Subgroup.one_lt_card_iff_ne_bot W).mp hW1
  -- `H` preserves `Z(U)`
  have hWinv : IsConjInvariant (Work.Zassenhaus.pairStab G inf zero) W := by
    rw [hWdef]
    exact Z4.isConjInvariant_map_center hHle
  -- the master counting lemma Z4/Z5, applied to `W = Z(U)`, gives `Z(U) = U`
  have hW : W = U :=
    eq_top_of_isConjInvariant hp hk hWU hUP hcardU hHle hfix hcardH hWne hWinv
  -- hence every element of `U` commutes with every other element of `U`
  have hcenter : U ≤ Subgroup.centralizer (U : Set G) := by
    intro u hu
    have huW : u ∈ W := hW ▸ hu
    rw [hWdef] at huW
    obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp huW
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hcv : v * (x : G) = (x : G) * v :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx (⟨v, hv⟩ : U))
    have hxu' : (x : G) = u := hxu
    rw [hxu'] at hcv
    exact hcv
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp hcenter

end Work.ZASS
