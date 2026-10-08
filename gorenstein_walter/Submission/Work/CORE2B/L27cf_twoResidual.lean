import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.API
import Submission.Work.FUS.Dihedral
import Submission.Work.FUS.thompson_transfer
import Submission.Work.FUS.DihedralFacts.rot_involutions
import Submission.Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral

/-!
# CORE2B — `t` is 2-central in `M` when `t ∈ O²(M)`

This is the third and last case of Bender's Lemma 2.7, step 1 ("`t` is 2-central in `M`"),
namely the case `t ∈ O²(M)`: if `t` is an involution of `M` lying in the 2-residual `O²(M)`,
and the Sylow `2`-subgroups of `M` are non-cyclic (so, `M` being a subgroup of a group with
dihedral Sylow `2`-subgroups, they are dihedral), then some Sylow `2`-subgroup `P` of `M` is
centralised by `t`.

The proof is the classical "transfer" argument:

* pick a Sylow `2`-subgroup `P ≤ M` containing `t`, and put `σ : P →* ZMod 2` the reflection
  sign of the dihedral group `P ≅ DihedralGroup m`;
* if `t` is a "rotation" involution of `P`, then `t` is the central involution of `P` and there
  is nothing to prove;
* otherwise Thompson's transfer lemma (`Work.FUS.thompson_transfer`) together with the
  hypothesis `t ∈ O²(M)` (every normal subgroup of `2`-power index contains `O²(M)`) forces `t`
  to be conjugate to a "rotation" involution of `P`, i.e. to the central involution of a Sylow
  `2`-subgroup of `M`.
-/

open scoped Pointwise

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem L27cf_twoResidual {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (t : G) (ht : orderOf t = 2)
    (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x) (M : Subgroup G) (htM : t ∈ M)
    (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P) (hres : t ∈ Work.GW2.twoResidualIn M) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex S
  -- `t` as an element of `M`, and the Sylow 2-subgroups of `G`
  let tM : M := ⟨t, htM⟩
  have ht2M : orderOf tM = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have htM1 : tM ≠ 1 := by
    intro h
    have h1 : orderOf tM = 1 := by rw [h, orderOf_one]
    rw [ht2M] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨eS⟩ := hS
  -- a Sylow 2-subgroup `P` of `M` containing `t`
  obtain ⟨P, htP⟩ : ∃ P : Sylow 2 M, tM ∈ (P : Subgroup M) := by
    have hgen : IsPGroup 2 ↥(Subgroup.zpowers tM) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, ht2M]; norm_num
    obtain ⟨P, hP⟩ := hgen.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers tM)⟩
  have htP2 : orderOf (⟨tM, htP⟩ : ↥(P : Subgroup M)) = 2 := by
    rw [Subgroup.orderOf_mk, ht2M]
  -- `2 ≤ n`: the Sylow of `M` is non-cyclic, hence of order `≥ 4`, and lies in a conjugate of `S`
  have hn : 2 ≤ n := by
    have hcardS : Nat.card ↥(S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
    have hP4 : 4 ≤ Nat.card ↥(P : Subgroup M) := by
      obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
      have hk2 : 2 ≤ k := by
        by_contra hcon
        rw [not_le] at hcon
        interval_cases k
        · have h1 : Nat.card ↥(P : Subgroup M) = 1 := by rw [hk]; norm_num
          haveI : Subsingleton ↥(P : Subgroup M) := (Nat.card_eq_one_iff_unique.mp h1).1
          exact hnc P isCyclic_of_subsingleton
        · have h1 : Nat.card ↥(P : Subgroup M) = 2 := by rw [hk]; norm_num
          exact hnc P (isCyclic_of_prime_card (p := 2) h1)
      rw [hk]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hPS : Nat.card ↥(P : Subgroup M) ≤ Nat.card ↥(S : Subgroup G) := by
      have hQ : IsPGroup 2 ↥(((P : Subgroup M)).map M.subtype) := P.isPGroup'.map M.subtype
      obtain ⟨S', hQS'⟩ := hQ.exists_le_sylow
      calc Nat.card ↥(P : Subgroup M)
          = Nat.card ↥(((P : Subgroup M)).map M.subtype) :=
            (Subgroup.card_map_of_injective M.subtype_injective).symm
        _ ≤ Nat.card ↥(S' : Subgroup G) := Subgroup.card_le_of_le hQS'
        _ = Nat.card ↥(S : Subgroup G) := Nat.card_congr (Sylow.equiv S' S).toEquiv
    omega
  -- `P ≅ DihedralGroup m` with `m ≥ 2`
  obtain ⟨m, hm2, ⟨e⟩⟩ :
      ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(P : Subgroup M) ≃* DihedralGroup m) := by
    have hQ : IsPGroup 2 ↥(((P : Subgroup M)).map M.subtype) := P.isPGroup'.map M.subtype
    have hmap := Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective
    rcases Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral S n hn ⟨eS⟩ _ hQ with
        hcyc | ⟨m, hm2, ⟨em⟩⟩
    · exact absurd ((MulEquiv.isCyclic hmap).mpr hcyc) (hnc P)
    · exact ⟨m, hm2, ⟨hmap.trans em⟩⟩
  haveI : NeZero m := ⟨by omega⟩
  -- `m` is even
  have hmeven : Even m := by
    have hcardP : Nat.card ↥(P : Subgroup M) = 2 * m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    exact Work.FUS.even_of_two_mul_eq_two_pow hm2 (hcardP ▸ hk)
  -- the central involution of `P`, in the `DihedralGroup m` picture
  let zM : ↥(P : Subgroup M) := e.symm (DihedralGroup.r ((m / 2 : ℕ) : ZMod m))
  have hz_central : ∀ y : ↥(P : Subgroup M), y * zM = zM * y := by
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    have h2k : (((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m)) = 0 := by
      obtain ⟨c, hc⟩ := hmeven
      rw [← Nat.cast_add, show m / 2 + m / 2 = m from by omega, ZMod.natCast_self]
    rcases Work.Dihedral.eq_r_or_sr (e y) with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [hi, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
      congr 1
      ring
    · rw [hi, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      congr 1
      have hk_neg : ((m / 2 : ℕ) : ZMod m) = -(((m / 2 : ℕ) : ZMod m)) :=
        eq_neg_of_add_eq_zero_left h2k
      rw [sub_eq_add_neg, ← hk_neg]
  -- the reflection sign on `P`
  let σ : ↥(P : Subgroup M) →* Multiplicative (ZMod 2) := (Work.FUS.reflSign m).comp e.toMonoidHom
  have hσker : σ.ker = (Work.Dihedral.rot m).comap e.toMonoidHom := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, σ, MonoidHom.comp_apply]
    rw [← Work.FUS.ker_reflSign m, MonoidHom.mem_ker]
  have hzapp : e zM = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) :=
    MulEquiv.apply_symm_apply e _
  by_cases hσ : σ ⟨tM, htP⟩ = 1
  · -- `t` is a rotation involution of `P`: it is the central involution
    have ht_eq : (⟨tM, htP⟩ : ↥(P : Subgroup M)) = zM := by
      have hx2 : (⟨tM, htP⟩ : ↥(P : Subgroup M)) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one (⟨tM, htP⟩ : ↥(P : Subgroup M))
        rwa [htP2] at h
      have hsq : (e ⟨tM, htP⟩) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
      have hmem : e ⟨tM, htP⟩ ∈ Work.Dihedral.rot m := by
        have h1 : (⟨tM, htP⟩ : ↥(P : Subgroup M)) ∈ σ.ker := hσ
        rwa [hσker, Subgroup.mem_comap] at h1
      rcases Work.FUS.DihedralFacts.rot_involutions m hmeven (e ⟨tM, htP⟩) hmem hsq with
          h1 | h1
      · exfalso
        have : (⟨tM, htP⟩ : ↥(P : Subgroup M)) = 1 := e.injective (by rw [h1, map_one])
        exact htM1 (congrArg Subtype.val this)
      · exact e.injective (by rw [h1, hzapp])
    refine ⟨P, fun x hx => ?_⟩
    have hcomm : (⟨x, hx⟩ : ↥(P : Subgroup M)) * (⟨tM, htP⟩ : ↥(P : Subgroup M))
        = (⟨tM, htP⟩ : ↥(P : Subgroup M)) * ⟨x, hx⟩ := by
      rw [ht_eq]; exact hz_central ⟨x, hx⟩
    have hcomm' := congrArg (fun y : ↥(P : Subgroup M) => ((y : M) : G)) hcomm
    simpa [tM] using hcomm'
  · -- `t` is a reflection: Thompson's transfer lemma
    have hodd : Odd (P : Subgroup M).index := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact P.not_dvd_index
    have hfus : ¬ (∀ g : M, ∀ (hh : g * (⟨tM, htP⟩ : ↥(P : Subgroup M)) * g⁻¹ ∈ (P : Subgroup M)),
        σ ⟨g * (⟨tM, htP⟩ : ↥(P : Subgroup M)) * g⁻¹, hh⟩ ≠ 1) := by
      intro hfus'
      obtain ⟨N, hN, hidx, htN⟩ :=
        Work.FUS.thompson_transfer (P : Subgroup M) hodd σ ⟨tM, htP⟩ htP2 hσ hfus'
      haveI : N.Normal := hN
      -- `O²(M) ≤ N` because `N` has 2-power index
      have hO2le : Work.GW2.twoResidual ↥M ≤ N := by
        rw [Work.CORE2B.twoResidual_le_iff]
        intro g hg
        have hQcard : Nat.card (M ⧸ N) = 2 := by
          rw [← Subgroup.index_eq_card, hidx]
        have hg2 : g ^ 2 ∈ N := by
          have hdvd : orderOf (QuotientGroup.mk' N g) ∣ 2 := by
            have := orderOf_dvd_natCard (QuotientGroup.mk' N g)
            rwa [hQcard] at this
          have h1 : (QuotientGroup.mk' N g) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
          have h2 : QuotientGroup.mk' N (g ^ 2) = 1 := by rw [map_pow, h1]
          exact (QuotientGroup.eq_one_iff (N := N) (g ^ 2)).mp h2
        obtain ⟨c, hc⟩ := hg
        have hg1 : g⁻¹ ∈ N := by
          have h3 : g ^ (2 * c) = g⁻¹ := by
            have h4 : g ^ (2 * c + 1) = 1 := by rw [← hc]; exact pow_orderOf_eq_one g
            have h5 : g ^ (2 * c) * g = 1 := by rw [pow_succ] at h4; exact h4
            exact eq_inv_of_mul_eq_one_left h5
          rw [← h3]
          have h6 : g ^ (2 * c) = (g ^ 2) ^ c := by rw [pow_mul]
          rw [h6]; exact Subgroup.pow_mem N hg2 c
        simpa using Subgroup.inv_mem N hg1
      have htMN : tM ∈ N := by
        obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hres
        have hkt : k = tM := Subtype.ext hkeq
        rw [← hkt]
        exact hO2le hk
      exact htN htMN
    simp only [not_forall, not_not] at hfus
    obtain ⟨g, hh, hgσ⟩ := hfus
    -- the conjugate of `t` lies in the rotation part, hence equals the central involution
    have hu_eq : (⟨g * tM * g⁻¹, hh⟩ : ↥(P : Subgroup M)) = zM := by
      have hmem : e ⟨g * tM * g⁻¹, hh⟩ ∈ Work.Dihedral.rot m := by
        have h1 : (⟨g * tM * g⁻¹, hh⟩ : ↥(P : Subgroup M)) ∈ σ.ker := hgσ
        rwa [hσker, Subgroup.mem_comap] at h1
      have hord : orderOf (⟨g * tM * g⁻¹, hh⟩ : ↥(P : Subgroup M)) = 2 := by
        rw [Subgroup.orderOf_mk]
        have h1 : orderOf (g * tM * g⁻¹) = orderOf tM := by
          simpa using MulEquiv.orderOf_eq (MulAut.conj g) tM
        rw [h1, ht2M]
      have hsq : (e ⟨g * tM * g⁻¹, hh⟩) ^ 2 = 1 := by
        have hx2 : (⟨g * tM * g⁻¹, hh⟩ : ↥(P : Subgroup M)) ^ 2 = 1 := by
          have h := pow_orderOf_eq_one (⟨g * tM * g⁻¹, hh⟩ : ↥(P : Subgroup M))
          rwa [hord] at h
        rw [← map_pow, hx2, map_one]
      rcases Work.FUS.DihedralFacts.rot_involutions m hmeven (e _) hmem hsq with h1 | h1
      · exfalso
        have h2 : (⟨g * tM * g⁻¹, hh⟩ : ↥(P : Subgroup M)) = 1 :=
          e.injective (by rw [h1, map_one])
        have h3 : g * tM * g⁻¹ = 1 := congrArg Subtype.val h2
        have h4 : tM = 1 := by
          have h5 : tM = g⁻¹ * (g * tM * g⁻¹) * g := by group
          rw [h3, mul_one, inv_mul_cancel] at h5
          exact h5
        exact htM1 h4
      · exact e.injective (by rw [h1, hzapp])
    -- `t` centralises the Sylow `g⁻¹ • P`
    have hzval : (zM : M) = MulAut.conj g tM := by
      rw [← hu_eq, MulAut.conj_apply]
    refine ⟨g⁻¹ • P, fun x hx => ?_⟩
    have hxP : MulAut.conj g x ∈ (P : Subgroup M) := by
      have h1 : x ∈ (MulAut.conj g⁻¹) • ((P : Subgroup M)) := by
        rw [← Sylow.coe_subgroup_smul]; exact hx
      have h2 := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g⁻¹)
        (S := (P : Subgroup M)) (x := x)).mp h1
      simpa [MulAut.smul_def, MulAut.conj_apply] using h2
    have hcomm : (⟨MulAut.conj g x, hxP⟩ : ↥(P : Subgroup M)) * zM
        = zM * ⟨MulAut.conj g x, hxP⟩ := hz_central _
    have hcommM : MulAut.conj g x * (zM : M) = (zM : M) * MulAut.conj g x :=
      congrArg (fun y : ↥(P : Subgroup M) => (y : M)) hcomm
    have h1 : x * tM = tM * x := by
      rw [hzval, ← map_mul, ← map_mul] at hcommM
      exact (MulAut.conj g).injective hcommM
    have h2 := congrArg (fun y : M => (y : G)) h1
    simpa [tM] using h2

end Work.CORE2B
