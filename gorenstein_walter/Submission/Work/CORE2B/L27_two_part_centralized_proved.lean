import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.L27_two_part
import Submission.Work.CORE2B.sylow_central_of_large_inter
import Submission.Work.CORE2B.L27cf_twoResidual
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315
import Submission.Work.Dihedral.Defs
import Submission.Work.RED.Basic
import Submission.Work.RED.DihedralSubgroup

/-!
# `Work.CORE2B.L27_two_part_centralized` (Bender 1981, Lemma 2.7, step 3, first half)

Under `L27Hyp B M`, the involution `t` centralizes `F₂(M) = fittingPiIn {2} M`.

Route (Bender p. 221, "`t` centralizes `O₂(M)`").

* `F₂(M) = O₂(F(M)) ≤ O₂(M)`: the `2`-part of `F(M)`, viewed in `M`, is a characteristic
  subgroup of `F(M) ◁ M`, hence a normal `2`-subgroup of `M`, so it lies in the largest one.
* It is therefore enough that `O₂(M)` is centralized by `t`.  A normal `2`-subgroup of `M` lies
  in every Sylow `2`-subgroup of `M`, so this in turn follows from **`t` is `2`-central in `M`**:
  some Sylow `2`-subgroup `P` of `M` satisfies `P ≤ C_G(t)`.
* `t` is `2`-central in `M` in each of the three alternatives of `L27Hyp.size`:
  * `8 ≤ |S ⊓ M|`: Bender's "large intersection" case; `S ⊓ M ≤ C(t)` has order `≥ 8`, and in a
    dihedral `2`-group the centralizer of a non-central involution is a Klein four-group.
  * `|S| = 4`: then every `2`-subgroup of `G` has order at most `4`, hence is commutative.
  * `t ∈ O₂(M)`: the residual case, handled by the transfer argument of the localisation area.

The file also records the elementary bridges (`Work.GW2.piCore = O_π`, characteristicity of the
`π`-core, `F₂(M) ≤ O₂(M)`) and the dihedral-group centralizer computations used by the first case.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-! ## 1. Bridges to the ported odd-order library -/

/-- `O_π(G)` of the contract vocabulary is Isaacs' `oPiCore`. -/
theorem L27c_piCore_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    Work.GW2.piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G := by
  apply le_antisymm
  · refine (Subgroup.normalCore_le _).trans ?_
    refine sSup_le ?_
    rintro N ⟨hN, hpi⟩
    exact le_iSup (fun H : {H : Subgroup G // H.Normal ∧ Subgroup.IsPiSubgroup π H} =>
      (H.val : Subgroup G)) ⟨N, hN, hpi⟩
  · refine Subgroup.normal_le_normalCore.mpr ?_
    exact iSup_le fun H => le_sSup H.property

/-- `O_π(G)` is characteristic. -/
theorem L27c_piCore_characteristic {G : Type*} [Group G] (π : Set ℕ) :
    (Work.GW2.piCore π G).Characteristic := by
  rw [L27c_piCore_eq_oPiCore π]
  infer_instance

/-- `O_π(G)` is a `π`-subgroup. -/
theorem L27c_isPiSubgroup_piCore {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    Subgroup.IsPiSubgroup π (Work.GW2.piCore π G) := by
  rw [L27c_piCore_eq_oPiCore π]
  exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π

/-- A `{2}`-subgroup is a `2`-group. -/
theorem L27c_isPGroup_of_isPiSubgroup_two {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (h : Subgroup.IsPiSubgroup ({n : ℕ | n = 2}) N) : IsPGroup 2 N := by
  rcases eq_or_ne N ⊥ with hN | hN
  · rw [hN]
    exact IsPGroup.of_card (p := 2) (G := ↥(⊥ : Subgroup G)) (n := 0) (by simp)
  · have hcard : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
    have hk : Nat.card ↥N = 2 ^ (Nat.card ↥N).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hcard
        (fun {d} hd hdvd => h d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, hcard⟩))
    exact IsPGroup.of_card (p := 2) (G := ↥N) hk

/-! ## 2. `F₂(M) ≤ O₂(M)` -/

/-- Every normal `p`-subgroup lies in `O_p` (universal property of the `p`-core). -/
theorem L27c_le_pCore_of_normal_isPGroup {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    [N.Normal] (hN : IsPGroup p N) : N ≤ Work.GW2.pCore p G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- `F₂(M) ≤ O₂(M)`: the `2`-part of `F(M)`, viewed in `M`, is a normal `2`-subgroup. -/
theorem L27c_fittingPi_two_le_pCore_two {M : Type*} [Group M] [Finite M] :
    Work.GW2.fittingPi {n : ℕ | n = 2} M ≤ Work.GW2.pCore 2 M := by
  classical
  set F := Work.GW2.fitting M with hF
  set K : Subgroup ↥F := Work.GW2.piCore ({n : ℕ | n = 2}) ↥F with hK
  haveI hcharK : K.Characteristic := L27c_piCore_characteristic ({n : ℕ | n = 2})
  haveI hnormF : F.Normal := Subgroup.normalCore_normal _
  haveI hNnorm : (K.map F.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hpi : Subgroup.IsPiSubgroup ({n : ℕ | n = 2}) (K.map F.subtype) :=
    fun p hp => L27c_isPiSubgroup_piCore ({n : ℕ | n = 2})
      p (Nat.primeFactors_mono (Subgroup.card_map_dvd _ _) Nat.card_pos.ne' hp)
  have hle := L27c_le_pCore_of_normal_isPGroup (p := 2) (N := K.map F.subtype)
    (L27c_isPGroup_of_isPiSubgroup_two hpi)
  simpa [Work.GW2.fittingPi, hK, hF] using hle

/-! ## 3. Reduction: a Sylow `2`-subgroup of `M` centralizing `t` suffices -/

/-- `O₂(G)` of the contract vocabulary is a `2`-group. -/
theorem L27c_pCore_isPGroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p ↥(Work.GW2.pCore p G) := by
  rw [Work.GW2.pCore]
  have hsup : IsPGroup p ↥(sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}) :=
    Sylow.sSup_of_normal {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  exact hsup.to_le (Subgroup.normalCore_le _)

/-- A normal `2`-subgroup of `M` lies in every Sylow `2`-subgroup of `M`; hence `O₂(M)` is
centralized by `t` as soon as some Sylow `2`-subgroup of `M` is. -/
theorem L27c_pCoreIn_two_le_centralizer_of_sylow {G : Type} [Group G] [Finite G]
    (M : Subgroup G) (t : G) (P : Sylow 2 M)
    (hP : ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G)) :
    Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({t} : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Work.GW2.pCore 2 ↥M ≤ (P : Subgroup M) :=
    IsPGroup.le_sylow_of_normal (L27c_pCore_isPGroup (G := ↥M) (p := 2)) P
  intro x hx
  rw [Work.GW2.pCoreIn] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact (hP y (hle hy)).symm

/-! ## 4. Centralizers in dihedral groups (used by the case `8 ≤ |S ⊓ M|`) -/

/-- In `ZMod m`, the solutions of `2 * a = 0` are `0` and `m / 2`. -/
theorem L27c_zmod_two_mul_eq_zero {m : ℕ} [NeZero m] (a : ZMod m) (ha : 2 * a = 0) :
    a = 0 ∨ a = ((m / 2 : ℕ) : ZMod m) := by
  have hneg : -a = a := by
    have h : a + a = 0 := by simpa [two_mul] using ha
    exact neg_eq_iff_add_eq_zero.mpr h
  rcases (ZMod.neg_eq_self_iff a).mp hneg with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hval : a.val = m / 2 := by
      have hlt := ZMod.val_lt a
      omega
    rw [← ZMod.natCast_zmod_val a, hval]

/-- In `ZMod m` with `2 ∣ m`, doubling `m / 2` gives `0`. -/
theorem L27c_zmod_two_mul_div_two {m : ℕ} [NeZero m] (heven : 2 ∣ m) :
    (2 : ZMod m) * ((m / 2 : ℕ) : ZMod m) = 0 := by
  rw [← Nat.cast_two, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact ⟨1, by rw [mul_one, Nat.mul_div_cancel' heven]⟩

/-- In `DihedralGroup m` with `2 ∣ m`, the rotation `r (m/2)` is central. -/
theorem L27c_dihedral_r_half_central {m : ℕ} [NeZero m] (heven : 2 ∣ m) :
    ∀ x : DihedralGroup m, x * DihedralGroup.r ((m / 2 : ℕ) : ZMod m)
      = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) * x := by
  have h2 : (2 : ZMod m) * ((m / 2 : ℕ) : ZMod m) = 0 := L27c_zmod_two_mul_div_two heven
  have hneg : -((m / 2 : ℕ) : ZMod m) = ((m / 2 : ℕ) : ZMod m) := by
    rw [neg_eq_iff_add_eq_zero]
    simpa [two_mul] using h2
  intro x
  rcases Work.Dihedral.eq_r_or_sr x with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 1
    rw [sub_eq_add_neg, hneg]

/-- In `DihedralGroup m` with `2 ∣ m`, anything commuting with the reflection `sr i` is one of
`1`, `r (m/2)`, `sr i`, `sr (i + m/2)`. -/
theorem L27c_dihedral_commute_sr {m : ℕ} [NeZero m] (heven : 2 ∣ m) (i : ZMod m)
    (x : DihedralGroup m) (hx : x * DihedralGroup.sr i = DihedralGroup.sr i * x) :
    x = 1 ∨ x = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) ∨ x = DihedralGroup.sr i ∨
      x = DihedralGroup.sr (i + ((m / 2 : ℕ) : ZMod m)) := by
  rcases Work.Dihedral.eq_r_or_sr x with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at hx
    have hij : i - j = i + j := DihedralGroup.sr.inj hx
    have hneg : -j = j := by
      have h : i - j = i + j := hij
      have h2 : -j = j := by
        have h3 := congrArg (fun y : ZMod m => y - i) h
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, add_right_comm] using h3
      exact h2
    have h2j : 2 * j = 0 := by
      rw [two_mul]
      exact add_eq_zero_iff_eq_neg.mpr hneg.symm
    rcases L27c_zmod_two_mul_eq_zero j h2j with h | h
    · subst h
      exact Or.inl (by rw [DihedralGroup.r_zero])
    · exact Or.inr (Or.inl (by rw [h]))
  · rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr] at hx
    have hji : i - j = j - i := DihedralGroup.r.inj hx
    have hneg : -(j - i) = j - i := by
      rw [neg_sub]
      exact hji
    have h2 : 2 * (j - i) = 0 := by
      rw [two_mul]
      exact add_eq_zero_iff_eq_neg.mpr hneg.symm
    rcases L27c_zmod_two_mul_eq_zero (j - i) h2 with h | h
    · have hji' : j = i := sub_eq_zero.mp h
      subst hji'
      exact Or.inr (Or.inr (Or.inl rfl))
    · have hji' : j = ((m / 2 : ℕ) : ZMod m) + i := sub_eq_iff_eq_add.mp h
      rw [add_comm] at hji'
      subst hji'
      exact Or.inr (Or.inr (Or.inr rfl))

/-! ## 5. The target -/

/-- Bender 1981, Lemma 2.7, step 3, first half: `t` centralizes `F₂(M) = O₂(F(M))`.

`F₂(M) ≤ O₂(M)`, and `t` is 2-central in `M`: the size condition `L27Hyp.size` provides a
Sylow `2`-subgroup `P` of `M` with `P ≤ C(t)` in each of its three alternatives
(`8 ≤ |S ⊓ M|`, `|S| = 4`, `t ∈ O₂(M)').  Then `O₂(M) ≤ P ≤ C(t)`. -/
theorem L27_two_part_centralized_proved : Work.CORE2B.L27_two_part_centralized := by
  intro T h23 h26 G _ _ hFT hCtx B M hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (↥(B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | h
    · exact absurd h hncS
    · exact h
  have htc : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := t_central_in_S B
  have key : ∀ P : Sylow 2 M, (∀ x ∈ (P : Subgroup M), (x : G) * B.t = B.t * (x : G)) →
      Work.GW2.fittingPiIn {2} M ≤ Subgroup.centralizer ({B.t} : Set G) :=
    fun P hP => (L27two.fitting_two_le_two_core M).trans
      (L27c_pCoreIn_two_le_centralizer_of_sylow M B.t P hP)
  rcases hM.size with h8 | h4 | hres
  · obtain ⟨P, hP⟩ := sylow_central_of_large_inter B.S n hn B.t B.t_order htc M hM.t_mem
      hM.sylow_nc h8
    exact key P hP
  · obtain ⟨P, hP⟩ := L27two.sylow_central_of_card_four B.S B.t B.t_order h4 M hM.t_mem
      hM.sylow_nc
    exact key P hP
  · obtain ⟨P, hP⟩ := L27cf_twoResidual B.S n hn B.t B.t_order htc M hM.t_mem
      hM.sylow_nc hres
    exact key P hP

end Work.CORE2B
