import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.ThreePoints.p3cd_strongEmbedded_gen
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.involutions_commute_of_below
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- The centre of a finite group lies in every strongly embedded subgroup: a central element
`z ∉ H` would give `H ⊓ H^z = H` of odd order, contradicting the evenness of `|H|`. -/
private lemma center_le_of_stronglyEmbedded {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) : Subgroup.center G ≤ H := by
  intro z hz
  by_contra hzH
  have hodd := hH.2.2 z hzH
  have hle : H ≤ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H := by
    intro x hx
    refine ⟨z⁻¹ * x * z, ?_, ?_⟩
    · have hcomm : x * z = z * x := (Subgroup.mem_center_iff.mp hz) x
      have hzx : z⁻¹ * x * z = x := by
        rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hzx]; exact hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hconj : H ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H = H :=
    inf_eq_left.mpr hle
  rw [hconj] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hH.2.1

/-- If `a` and `b` are involutions whose commutator `c = a b a⁻¹ b⁻¹` is central of odd order,
then `a` and `b` commute.  (The commutator is then both equal to its inverse -- `a c a⁻¹ = c⁻¹`
because `a² = 1`, and `a c a⁻¹ = c` because `c` is central -- and of odd order, so it is `1`.) -/
private lemma commute_of_commutator_mem_center_of_odd {K : Type*} [Group K] {a b c : K}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c = a * b * a⁻¹ * b⁻¹)
    (hcen : c ∈ Subgroup.center K) (hodd : Odd (orderOf c)) :
    a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  -- `a c a⁻¹ = b a⁻¹ b⁻¹ a⁻¹ = c⁻¹`
  have h1 : a * c * a⁻¹ = b * a⁻¹ * b⁻¹ * a⁻¹ := by
    rw [hc]
    rw [show a * (a * b * a⁻¹ * b⁻¹) * a⁻¹ = (a * a) * (b * a⁻¹ * b⁻¹ * a⁻¹) from by group,
      ha, one_mul]
  have h2 : c⁻¹ = b * a⁻¹ * b⁻¹ * a⁻¹ := by
    rw [hc]
    rw [show (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ from by group, ha', hb']
  have hconj : a * c * a⁻¹ = c⁻¹ := by rw [h1, ← h2]
  have hcenta : a * c * a⁻¹ = c := by
    have h := (Subgroup.mem_center_iff.mp hcen) a
    rw [h]; group
  have hceq : c = c⁻¹ := by rw [← hconj, hcenta]
  have hcc : c * c = 1 := mul_eq_one_iff_eq_inv.mpr hceq
  have h2' : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hcc)
  have h1' : orderOf c = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h | h
    · exact h
    · exfalso
      have hev : Even (orderOf c) := h.symm ▸ (⟨1, rfl⟩ : Even 2)
      exact (Nat.not_even_iff_odd.mpr hodd) hev
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1'
  have hx : a * b * a⁻¹ * b⁻¹ = 1 := hc ▸ hc1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = 1 * (b * a) := by rw [hx]
    _ = b * a := one_mul _

/-- **Peterfalvi I Ch. III §1 Lemma 3, commutativity of the involutions of `N_H(X)`** (p.175).
For `1 ≠ X ≤ V = C_D(t)` with `N_K(X) ≠ 1`, the involutions of `H ⊓ N_G(X)` commute pairwise.
Route: `ChIIFourProp` P1(b) makes `N_H(X) = H ⊓ N_G(X)` strongly embedded in `N_G(X)`; P3 gives
`N_G(X) = F ⊔ N_V(X)` with `F = O^{2'}(C_G(X))` and `H ⊓ N_G(X) = S ⋊ (D ⊓ N_G(X))` (`S` a
`2`-group, `D ⊓ N_G(X)` of odd order), so every involution of `N_H(X)` lies in `F ⊓ H`; modulo the
odd centre `Z(F) = O_{2'}(F)` the involutions of `F ⊓ H` commute (`ModelFactsProp` applied to the
simple Bender group `F/Z(F)`, in which the image of `F ⊓ H` is strongly embedded), so their
commutator is central of odd order and therefore trivial. -/
theorem sec1_lemma3_struct_commute (hC4 : Submission.Blueprint.ChIIFourProp)
    (hMod : Submission.Blueprint.ModelFactsProp)
    {G : Type} [Group G] [Finite G] (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hNK : ∃ k ∈ Work.NormalComplement.Design.NK H t X, k ≠ 1) :
    ∀ u ∈ Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G),
      ∀ v ∈ Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G), u * v = v * u := by
  classical
  intro u hu v hv
  -- ## 0. The hypothesis `N_K(X) ≠ 1` in the form used by `ChIIFourProp` P3
  obtain ⟨k, hkNK, hk1⟩ := hNK
  have hkK : k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t := hkNK.1
  have hkN : k ∈ Subgroup.normalizer (X : Set G) := hkNK.2
  have hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G) := ⟨k, hkK, hk1, hkN⟩
  -- ## 1. Basic abbreviations
  set M : Subgroup G := H ⊓ Subgroup.normalizer (X : Set G) with hMdef
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hDdef
  have hDodd : Odd (Nat.card ↥D) :=
    Work.ThreePoints.IsStronglyEmbedded.odd_card_inf_conj hH htH
  -- ## 2. Ch. II §4 P1(b): `F ⊓ H` is strongly embedded in `F = O^{2'}(C_G(X))`
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht htH hXV
  have hInv_sub : Submission.Blueprint.involutions
      (Subgroup.centralizer (X : Set G) : Set G) ⊆ Work.ThreePoints.p3F X :=
    Work.ThreePoints.involutions_subset_p3F X
  have hFN : Work.ThreePoints.p3F X ≤ Subgroup.normalizer (X : Set G) :=
    (Work.ThreePoints.p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hXH : X ≤ Submission.Blueprint.conj (1 : G) H := by
    rw [Work.DoubleTransitivity.conj_one]
    exact hXV.trans (le_trans inf_le_left inf_le_left)
  have hSE0 := (hC4 G hS H hH t ht htH).1 X (Work.ThreePoints.p3F X) hX3 hInv_sub hFN 1 hXH
  rw [Work.DoubleTransitivity.conj_one] at hSE0
  -- `hSE0 : IsStronglyEmbedded ((p3F X ⊓ H).subgroupOf (p3F X))`
  -- ## 3. Ch. II §4 P3 for `X`
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  have hP3 := (hC4 G hS H hH t ht htH).2.2.2.1
  have hP3c := hP3 X hX hXV hNX
  dsimp only at hP3c
  rw [← hCdef] at hP3c
  set F : Subgroup G := (Submission.Blueprint.oddResidual C).map C.subtype with hFdef
  obtain ⟨hNGX, ⟨S, hSp, hSFH, hSidx, hMS, hSD, hSsup⟩, ⟨hZc, hYZc⟩, _hNdata⟩ := hP3c
  obtain ⟨Y, hYgrp, φ, hφsurj, hφker, hYbender⟩ := hYZc
  letI : Group Y := hYgrp
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  have hSE : IsStronglyEmbedded ((F ⊓ H).subgroupOf F) := hSE0
  -- ## 4. Every involution of `H ⊓ N_G(X)` lies in `F ⊓ H`
  set K : Subgroup G := Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)
    with hKdef
  have hKM : K ≤ M := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx1).1, hx2⟩
  have hSM : S ≤ M := by
    intro x hx
    obtain ⟨hxF, hxH⟩ := Subgroup.mem_inf.mp (hSFH hx)
    exact Subgroup.mem_inf.mpr ⟨hxH, hFN hxF⟩
  have hKS : K ≤ Subgroup.normalizer (S : Set G) := hKM.trans hMS
  have hcardM : Nat.card ↥M = Nat.card ↥S * Nat.card ↥K := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := S) (K := K) hKS
    have h2 : S ⊓ K = ⊥ := by
      rw [hKdef, ← inf_assoc, hSD]
      simp
    rw [hSsup, h2, Subgroup.card_bot, mul_one] at h
    exact h
  have hSindex : (S.subgroupOf M).index = Nat.card ↥K := by
    have h1 := Subgroup.card_mul_index (S.subgroupOf M)
    have h2 : Nat.card ↥(S.subgroupOf M) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
    rw [h2, hcardM] at h1
    exact Nat.mul_left_cancel Nat.card_pos h1
  haveI : (S.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hMS
  have hSindexOdd : Odd (S.subgroupOf M).index := by
    rw [hSindex]
    exact Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le (inf_le_left : K ≤ D))
  have hmem_S : ∀ {x : G}, x ∈ M → orderOf x = 2 → x ∈ S := by
    intro x hxM hx2
    have h : (⟨x, hxM⟩ : ↥M) ∈ S.subgroupOf M :=
      Work.ThreePoints.mem_of_orderOf_eq_two_of_odd_index
        (x := (⟨x, hxM⟩ : ↥M)) hSindexOdd (by rw [Subgroup.orderOf_mk]; exact hx2)
    exact Subgroup.mem_subgroupOf.mp h
  have huFH : u ∈ F ⊓ H := hSFH (hmem_S hu.1 hu.2)
  have hvFH : v ∈ F ⊓ H := hSFH (hmem_S hv.1 hv.2)
  have huF : u ∈ F := (Subgroup.mem_inf.mp huFH).1
  have huH : u ∈ H := (Subgroup.mem_inf.mp huFH).2
  have hvF : v ∈ F := (Subgroup.mem_inf.mp hvFH).1
  have hvH : v ∈ H := (Subgroup.mem_inf.mp hvFH).2
  -- ## 5. The image of `F ⊓ H` is strongly embedded in the simple Bender group `Y = F/Z(F)`
  have hkerH : φ.ker ≤ (F ⊓ H).subgroupOf F := by
    rw [hφker]
    exact center_le_of_stronglyEmbedded hSE
  have hoddKer : Odd (Nat.card φ.ker) := by
    rw [hφker, ← hZc]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have himgSemb : IsStronglyEmbedded (((F ⊓ H).subgroupOf F).map φ) :=
    Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd φ hφsurj hoddKer hkerH hSE
  -- ## 6. The images of `u` and `v` are involutions of that strongly embedded subgroup
  have huIm_mem : φ (⟨u, huF⟩ : ↥F) ∈ (((F ⊓ H).subgroupOf F).map φ : Subgroup Y) :=
    Subgroup.mem_map.mpr ⟨⟨u, huF⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨huF, huH⟩), rfl⟩
  have hvIm_mem : φ (⟨v, hvF⟩ : ↥F) ∈ (((F ⊓ H).subgroupOf F).map φ : Subgroup Y) :=
    Subgroup.mem_map.mpr ⟨⟨v, hvF⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hvF, hvH⟩), rfl⟩
  have huF2 : orderOf (⟨u, huF⟩ : ↥F) = 2 := by rw [Subgroup.orderOf_mk]; exact hu.2
  have hvF2 : orderOf (⟨v, hvF⟩ : ↥F) = 2 := by rw [Subgroup.orderOf_mk]; exact hv.2
  have hnotmem : ∀ {x : G} (hxF : x ∈ F) (hx2 : orderOf x = 2), φ (⟨x, hxF⟩ : ↥F) ≠ 1 := by
    intro x hxF hx2 h
    have hmem : (⟨x, hxF⟩ : ↥F) ∈ φ.ker := h
    rw [hφker] at hmem
    have hmemO : (⟨x, hxF⟩ : ↥F) ∈ Submission.Blueprint.oddCore ↥F := by
      rw [hZc]; exact hmem
    have h2dvd : 2 ∣ Nat.card ↥(Submission.Blueprint.oddCore ↥F) := by
      have h1 := orderOf_dvd_natCard
        (⟨(⟨x, hxF⟩ : ↥F), hmemO⟩ : ↥(Submission.Blueprint.oddCore ↥F))
      rw [Subgroup.orderOf_mk] at h1
      rwa [show orderOf (⟨x, hxF⟩ : ↥F) = 2 from by rw [Subgroup.orderOf_mk]; exact hx2] at h1
    exact (Nat.not_even_iff_odd.mpr Work.BrauerSuzuki.OddCore.oddCard_oddCore)
      (even_iff_two_dvd.mpr h2dvd)
  have huIm2 : orderOf (φ (⟨u, huF⟩ : ↥F)) = 2 := by
    have hdvd : orderOf (φ (⟨u, huF⟩ : ↥F)) ∣ 2 := by
      have h := orderOf_map_dvd φ (⟨u, huF⟩ : ↥F)
      rwa [huF2] at h
    exact (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left
      (fun h => hnotmem huF hu.2 (orderOf_eq_one_iff.mp h))
  have hvIm2 : orderOf (φ (⟨v, hvF⟩ : ↥F)) = 2 := by
    have hdvd : orderOf (φ (⟨v, hvF⟩ : ↥F)) ∣ 2 := by
      have h := orderOf_map_dvd φ (⟨v, hvF⟩ : ↥F)
      rwa [hvF2] at h
    exact (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left
      (fun h => hnotmem hvF hv.2 (orderOf_eq_one_iff.mp h))
  have hcommY : φ (⟨u, huF⟩ : ↥F) * φ (⟨v, hvF⟩ : ↥F)
      = φ (⟨v, hvF⟩ : ↥F) * φ (⟨u, huF⟩ : ↥F) :=
    ((hMod Y hYbender).2.2.2 (((F ⊓ H).subgroupOf F).map φ) himgSemb).1
      (φ ⟨u, huF⟩) ⟨huIm_mem, huIm2⟩ (φ ⟨v, hvF⟩) ⟨hvIm_mem, hvIm2⟩
  -- ## 7. The commutator of `u` and `v` in `F` is central of odd order, hence trivial
  have hcMem : (⟨u, huF⟩ : ↥F) * (⟨v, hvF⟩ : ↥F) * (⟨u, huF⟩ : ↥F)⁻¹ * (⟨v, hvF⟩ : ↥F)⁻¹
      ∈ Subgroup.center ↥F := by
    rw [← hφker, MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommY]
    group
  have hcOdd : Odd (orderOf ((⟨u, huF⟩ : ↥F) * (⟨v, hvF⟩ : ↥F)
      * (⟨u, huF⟩ : ↥F)⁻¹ * (⟨v, hvF⟩ : ↥F)⁻¹)) := by
    have hmemO : (⟨u, huF⟩ : ↥F) * (⟨v, hvF⟩ : ↥F) * (⟨u, huF⟩ : ↥F)⁻¹
        * (⟨v, hvF⟩ : ↥F)⁻¹ ∈ Submission.Blueprint.oddCore ↥F := by
      rw [hZc]; exact hcMem
    have h1 := orderOf_dvd_natCard
      (⟨_, hmemO⟩ : ↥(Submission.Blueprint.oddCore ↥F))
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat Work.BrauerSuzuki.OddCore.oddCard_oddCore h1
  have hcommF : (⟨u, huF⟩ : ↥F) * (⟨v, hvF⟩ : ↥F)
      = (⟨v, hvF⟩ : ↥F) * (⟨u, huF⟩ : ↥F) :=
    commute_of_commutator_mem_center_of_odd
      (Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two huF2)
      (Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hvF2) rfl hcMem hcOdd
  -- ## 8. Descend to `G`
  have hfin := congrArg (fun z : ↥F => (z : G)) hcommF
  simpa using hfin

end Work.NormalComplement
