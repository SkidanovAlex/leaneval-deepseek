import Mathlib
import Submission.Work.DSTR.Defs
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.GLUE.Bridge

/-!
# `O_{2'}` facts for the vocabulary of `Submission.Work.ASM.Defs`

Port of the elementary `O(G)`-API of `Submission/Work/RED/OddCoreFacts.lean` to the
`Work.GW2` vocabulary that this area imports (the two vocabularies are separate copies, so the
statements have to be re-proved here), together with the consequence used by DS10a:

* `Work.GW2.piCore_odd` : `O_π(G)` has `π`-order (here: odd order for `π = {2}ᶜ`);
* `Work.DSTR.M110.oddOrderOf_mem_fittingPiIn` : every element of `F_{2'}(K) ≤ G` has odd order.
-/

namespace Work.GW2

open Subgroup

/-- A subgroup of a finite group has odd order iff every prime dividing its order is odd. -/
theorem odd_iff_isPiSubgroup_ne_two {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N := by
  unfold Subgroup.IsPiSubgroup
  have hne : Nat.card ↥N ≠ 0 := (Nat.card_pos (α := ↥N)).ne'
  constructor
  · intro hodd q hq hq2
    rw [hq2] at hq
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hq).2.1)
  · intro h
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact h 2 (Nat.mem_primeFactors.mpr
      ⟨by norm_num, even_iff_two_dvd.mp heven, hne⟩) rfl

/-- The supremum of the normal `π`-subgroups is the odd-order library's `O_π(G)`. -/
theorem sSup_normal_isPiSubgroup_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    sSup {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup π N}
      = OddOrder.Isaacs.Ch03.oPiCore π G := by
  rw [OddOrder.Isaacs.Ch03.oPiCore]
  refine le_antisymm (sSup_le ?_) (iSup_le ?_)
  · rintro N ⟨hN, hpN⟩
    exact le_iSup_of_le ⟨N, hN, hpN⟩ le_rfl
  · rintro ⟨N, hN1, hN2⟩
    exact le_sSup ⟨hN1, hN2⟩

/-- `O_π(G)` is normal, so taking `normalCore` of it changes nothing. -/
theorem normalCore_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    (OddOrder.Isaacs.Ch03.oPiCore π G).normalCore = OddOrder.Isaacs.Ch03.oPiCore π G :=
  Subgroup.normalCore_eq_self _


/-- **`O_{2'}(G)` has odd order.** -/
theorem piCore_odd (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (piCore ({2}ᶜ : Set ℕ) G)) := by
  rw [piCore_eq_oPiCore (G := G)]
  exact (odd_iff_isPiSubgroup_ne_two
      (OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G)).mpr
    (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G) ({q : ℕ | q ≠ 2}))

/-- Maximality of `O_{2'}`: every normal odd-order subgroup lies in it. -/
theorem le_piCore_of_odd_normal {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hNn : N.Normal) (hN : Odd (Nat.card N)) : N ≤ piCore ({2}ᶜ : Set ℕ) G := by
  refine Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hNn, ?_⟩)
  exact (odd_iff_isPiSubgroup_ne_two N).mp hN

end Work.GW2

namespace Work.DSTR.M110

open Subgroup

/-- If `k ∣ n` and `n` is odd then `k` is odd. -/
private lemma odd_of_dvd_of_odd {k n : ℕ} (h : k ∣ n) (hn : Odd n) : Odd k := by
  obtain ⟨c, rfl⟩ := h
  refine Nat.not_even_iff_odd.mp fun hk => ?_
  exact hn.not_two_dvd_nat ((even_iff_two_dvd.mp hk).trans (dvd_mul_right k c))

/-- Every element of the `2'`-part `F_{2'}(K)` of the Fitting subgroup of `K ≤ G` has odd
order. -/
theorem oddOrderOf_mem_fittingPiIn {G : Type*} [Group G] [Finite G] (K : Subgroup G) (x : G)
    (hx : x ∈ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) K) : Odd (orderOf x) := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  -- `z : ↥(fitting ↥K)`, `hz : z ∈ O_{2'}(fitting ↥K)`, `hzy : (z : ↥K) = y`
  have hcard : Odd (Nat.card ↥(Work.GW2.piCore ({2}ᶜ : Set ℕ) ↥(Work.GW2.fitting ↥K))) :=
    Work.GW2.piCore_odd _
  have hdiv : orderOf z ∣ Nat.card ↥(Work.GW2.piCore ({2}ᶜ : Set ℕ) ↥(Work.GW2.fitting ↥K)) :=
    Subgroup.orderOf_dvd_natCard _ hz
  have hzodd : Odd (orderOf z) := odd_of_dvd_of_odd hdiv hcard
  have hxz : x = (((z : ↥(Work.GW2.fitting ↥K)) : ↥K) : G) := by
    rw [← hyx, ← hzy]
    rfl
  rw [hxz]
  simpa using hzodd

/-- `F_{2'}(K) ≤ K`. -/
theorem fittingPiIn_le {G : Type*} [Group G] (K : Subgroup G) :
    Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) K ≤ K := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  rw [← hyx, ← hzy]
  exact Subtype.coe_prop (z : ↥K)

/-- The Fitting subgroup of a finite group is nilpotent. -/
theorem fitting_isNilpotent (N : Type) [Group N] [Finite N] :
    Group.IsNilpotent ↥(Work.GW2.fitting N) :=
  (Work.CORE2A.fitting_eq_isaacsFitting (G := N)) ▸
    (inferInstance : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting N))

/-- **`F_{2'}(K)` is nilpotent.** -/
theorem fittingPiIn_isNilpotent {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Group.IsNilpotent ↥(Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) K) := by
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := fitting_isNilpotent ↥K
  have h1 : Group.IsNilpotent ↥(Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥K) := by
    rw [Work.GW2.fittingPi]
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.subtype_injective _))).mp (Subgroup.isNilpotent _)
  rw [Work.GW2.fittingPiIn]
  exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ _
    (Subgroup.subtype_injective _))).mp h1

/-- `F_π(K) = O_π(F(K))` is normal in `↥K`: it is characteristic in the normal subgroup
`F(K)`.  (Port of `Work.CORE2B.fittingPi_normal_local`, whose module cannot be imported here
because it carries its own copy of the `Work.GW2` vocabulary.) -/
theorem fittingPi_normal (G : Type) [Group G] (π : Set ℕ) (K : Subgroup G) :
    (Work.GW2.fittingPi π K).Normal := by
  haveI hFK : (Work.GW2.fitting K).Normal := Subgroup.normalCore_normal _
  haveI hchar : (Work.GW2.piCore π ↥(Work.GW2.fitting K)).Characteristic := by
    rw [Work.GW2.piCore_eq_oPiCore]
    exact OddOrder.Isaacs.Ch03.oPiCore.characteristic π ↥(Work.GW2.fitting K)
  exact ConjAct.normal_of_characteristic_of_normal

/-- `K` normalizes `F_π(K) = O_π(F(K))` (viewed inside `G`). -/
theorem le_normalizer_fittingPiIn (G : Type) [Group G] (π : Set ℕ) (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.fittingPiIn π K : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
      (fittingPi_normal G π K).conj_mem y hy ⟨k, hk⟩, ?_⟩
    have hyx' : (y : G) = x := hyx
    show k * (y : G) * k⁻¹ = k * x * k⁻¹
    rw [hyx']
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩,
      (by simpa using (fittingPi_normal G π K).conj_mem y hy ⟨k, hk⟩⁻¹), ?_⟩
    have hyx' : (y : G) = k * x * k⁻¹ := hyx
    show k⁻¹ * (y : G) * k = x
    rw [hyx']
    group

end Work.DSTR.M110
