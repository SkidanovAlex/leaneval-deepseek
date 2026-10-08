import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.L27_api

/-!
# CORE2B — Bender 2.7 (a), the `2'`-part: odd subgroups of `F(M)` lie in `F_{2'}(M)`

The lemma proved here is the elementary group-theoretic input of Bender's proof of
Lemma 2.7 (a) which says that the commutator `⁅M,t⁆` lies in `F_{π'}(M)`:

> if `K ≤ F(M)` has **odd order**, then `K ≤ F_{2'}(M) = O_{2'}(F(M))`.

The mathematics: every prime `q` dividing `|K|` is odd; `F(M)` is nilpotent (Isaacs
Corollary 1.28(a)), so every `q`-subgroup of it is contained in the *normal* Sylow
`q`-subgroup, hence in `O_q(F(M))`, and each `O_q(F(M))` with `q ∈ {2}ᶜ` is a normal
`{2}ᶜ`-subgroup of `F(M)`, so it lies in `O_{2'}(F(M))`.  Summing over the primes of `|K|`
gives the claim.

The only structural input is nilpotency of the Fitting subgroup, imported (together with the
maximality of `F`) from the odd-order library.  The `Work.GW2` vocabulary is replicated
verbatim in every area, so the GLUE bridges to the library cannot be imported into this
module (the import would clash on the re-declared names); the two bridges needed here are
therefore reproved below, in this area's own copy of the vocabulary.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false

/-! ## 1. Two bridges to the odd-order library -/

-- Note: `fitting_eq_isaacsFitting` is declared in `Submission.Work.CORE2B.L27_api` (imported
-- above) and is deliberately not repeated here, to avoid a duplicate declaration.

/-- **Isaacs Corollary 1.28(a)** in the contract vocabulary: `F(G)` is nilpotent. -/
instance fitting_isNilpotent {G : Type} [Group G] [Finite G] :
    Group.IsNilpotent ↥(Work.GW2.fitting G) := by
  rw [fitting_eq_isaacsFitting]
  infer_instance

/-- **Universal property of `O_π(H)`.**  Every normal `π`-subgroup of `H` lies in `O_π(H)`:
`O_π(H)` is the normal core of the join of the normal `π`-subgroups, and a normal subgroup
contained in a join lies in its normal core. -/
theorem le_piCore_of_normal_isPiGroup {H : Type} [Group H] {π : Set ℕ} {N : Subgroup H}
    [N.Normal] (hN : Subgroup.IsPiSubgroup π N) : N ≤ Work.GW2.piCore π H :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-! ## 2. A `π`-subgroup of a finite nilpotent group lies in `O_π` -/

/-- **A `π`-subgroup of a finite nilpotent group lies in `O_π`.**

`N` is nilpotent (a subgroup of the nilpotent `H`), hence the join of its own Sylow subgroups
(`iSup_default_sylow_eq_top_of_nilpotent`).  The image in `H` of the Sylow `q`-subgroup of `N`,
`q ∈ π`, is a `q`-subgroup of `H`; it is contained in some Sylow `q`-subgroup `Q` of `H`, which
is normal because `H` is nilpotent, and `Q` is a (normal) `π`-subgroup since `q ∈ π`.  Hence
the image lies in `O_π(H)` by the universal property of the `π`-core. -/
theorem le_piCore_of_isPiSubgroup_of_isNilpotent {H : Type} [Group H] [Finite H]
    [Group.IsNilpotent H] (π : Set ℕ) (N : Subgroup H) (hN : Subgroup.IsPiSubgroup π N) :
    N ≤ Work.GW2.piCore π H := by
  have htop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop, ← OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N,
    Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpπ : p ∈ π := hN p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  -- the image of the Sylow `p`-subgroup of `N` is a `p`-subgroup of `H`
  have hpg : IsPGroup p (((default : Sylow p ↥N) : Subgroup ↥N).map N.subtype) :=
    IsPGroup.map (default : Sylow p ↥N).isPGroup' N.subtype
  -- so it lies in a Sylow `p`-subgroup of `H`, which is normal, hence lies in `O_p(H) ≤ O_π(H)`
  obtain ⟨Q, hleQ⟩ := hpg.exists_le_sylow
  haveI : (Q : Subgroup H).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent Q
  exact hleQ.trans (le_piCore_of_normal_isPiGroup (H := H) (π := π)
    (Subgroup.isPiSubgroup_of_isPGroup_of_mem Q.isPGroup' hpπ))

/-! ## 3. The same statement for a nilpotent subgroup of an ambient group -/

/-- **A `π`-subgroup of a nilpotent subgroup `F ≤ G` lies in `O_π(F)`.**

The subgroup `N` corresponds to `N.subgroupOf F ≤ F` (same cardinality, because `N ≤ F`), a
`π`-subgroup of the group `↥F`, and section 2 applies inside `↥F`. -/
theorem le_map_piCore_of_isPiSubgroup {G : Type} [Group G] [Finite G] (F : Subgroup G)
    [hF : Group.IsNilpotent ↥F] (π : Set ℕ) {N : Subgroup G} (hNF : N ≤ F)
    (hN : Subgroup.IsPiSubgroup π N) :
    N ≤ (Work.GW2.piCore π F).map F.subtype := by
  have hmap : (N.subgroupOf F).map F.subtype = N :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hNF)
  have hcard : Nat.card ↥(N.subgroupOf F) = Nat.card ↥N := by
    rw [← Subgroup.card_map_of_injective F.subtype_injective, hmap]
  have hNpi : Subgroup.IsPiSubgroup π (N.subgroupOf F) := fun p hp => hN p (hcard ▸ hp)
  intro x hx
  have hxF : (⟨x, hNF hx⟩ : ↥F) ∈ N.subgroupOf F := Subgroup.mem_subgroupOf.mpr hx
  have hxpi : (⟨x, hNF hx⟩ : ↥F) ∈ Work.GW2.piCore π F :=
    le_piCore_of_isPiSubgroup_of_isNilpotent (H := ↥F) π (N.subgroupOf F) hNpi hxF
  exact ⟨⟨x, hNF hx⟩, hxpi, rfl⟩

/-! ## 4. The requested lemma -/

/-- **Bender 1981, Lemma 2.7 (a), `2'`-part.**  Every odd-order subgroup `K` of a finite group
`G` contained in the Fitting subgroup of a subgroup `M ≤ G` lies in `F_{2'}(M) = O_{2'}(F(M))`.

The subgroup of `↥M` corresponding to `K` is an odd-order (i.e. `{2}ᶜ`-)subgroup of the
nilpotent group `F(M)`, so it lies in `O_{2'}(F(M))` by section 3, which is what the claim
says after unfolding the two `…In` subgroups. -/
theorem L27_fittingPi_compl_of_odd :
    ∀ (G : Type) [Group G] [Finite G] (M K : Subgroup G),
      K ≤ Work.GW2.fittingIn M → Odd (Nat.card K) →
        K ≤ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M := by
  intro G _ _ M K hK hodd
  -- `K ⊆ F(M) ⊆ M` as subsets of `G`
  have hKM : K ≤ M := hK.trans (Subgroup.map_subtype_le _)
  -- the same subgroup, viewed inside `↥M`
  have hNF : K.subgroupOf M ≤ Work.GW2.fitting ↥M := by
    intro x hx
    have hx' : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hK hx')
    exact Subtype.ext hyx ▸ hy
  -- it has the same cardinality as `K`
  have hcard : Nat.card ↥(K.subgroupOf M) = Nat.card K := by
    have hmap : (K.subgroupOf M).map M.subtype = K :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hKM)
    rw [← Subgroup.card_map_of_injective M.subtype_injective, hmap]
  -- so it is an odd-order, i.e. `{2}ᶜ`-, subgroup of `F(M)`
  have hpi : Subgroup.IsPiSubgroup ({2}ᶜ : Set ℕ) (K.subgroupOf M) :=
    (odd_iff_isPiSubgroup_ne_two (K.subgroupOf M)).mp (hcard ▸ hodd)
  have hstep : K.subgroupOf M ≤ Work.GW2.fittingPi ({2}ᶜ : Set ℕ) M :=
    le_map_piCore_of_isPiSubgroup (Work.GW2.fitting ↥M) ({2}ᶜ : Set ℕ) hNF hpi
  -- transport back into `G`
  intro x hx
  have hxM : x ∈ M := hKM hx
  have hxN : (⟨x, hxM⟩ : ↥M) ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
  obtain ⟨z, hz, hzF⟩ := Subgroup.mem_map.mp (hstep hxN)
  refine Subgroup.mem_map.mpr ⟨(Work.GW2.fitting ↥M).subtype z, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  · exact congrArg Subtype.val hzF

end Work.CORE2B
