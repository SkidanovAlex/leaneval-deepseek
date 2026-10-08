import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.cyclic_index_two_center_mem
import Submission.Work.CORE2B.L27_aux
import Submission.Work.CORE2B.L27_aux2
import Submission.Work.CORE2B.twoResidual_involution_conj
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.Dihedral.Defs

/-!
# AREA CORE2B — Bender 1981, Lemma 2.7, step 1 (`Work.CORE2B.L27_normal_contains_t`)

Bender's Lemma 2.7 (p. 221): if `Ĥ ⇝ M ≠ Ĥ`, `t ∉ E(M)`, the Sylow 2-subgroups of `M` are
non-cyclic, and `|S ∩ M| ≥ 8` or `|S| = 4` or `t ∈ O²(M)`, then *every normal subgroup of `M`
of order divisible by `4` contains `t`*.

The auxiliary group-theoretic lemmas used here live in
`Submission/Work/CORE2B/L27_aux.lean` and `.../L27_aux2.lean`; the fusion input
`Work.CORE2B.twoResidual_involution_conj` is proved in `.../twoResidual_involution_conj.lean`.

## Route

Write `S` for the Sylow 2-subgroup of `G`, `t` for its central involution, and `S₀` for the cyclic
index-two subgroup of `S` (whose unique involution is `t`).  Let `N ≤ M` be normal in `M` with
`4 ∣ |N|`, and let `Qt` be a Sylow 2-subgroup of `M` containing `t`.

* Every Sylow `2`-subgroup `Q` of `M` meets `N` in a subgroup of order divisible by `4`
  (`sylow_inf_dvd`).
* If `|Qt| = 4`, then `Qt ⊓ N = Qt`, so `t ∈ N`.
* Otherwise `|Qt| ≥ 8`.  If `t ∈ O²(M)`, the fusion lemma conjugates `t` to the central involution
  of `Qt`, which lies in `N`.  If `|S ⊓ M| ≥ 8`, take `Q` a Sylow of `M` containing `S ⊓ M`; the
  central involution of `Q` lies both in `S ⊓ M` and in `N`, and `t` is equal to it because `t`
  and it are both central involutions of the subgroup `S ⊓ M` of the dihedral group `S` and
  `|S ⊓ M| ≥ 8` (`center_unique_of_dihedral_subgroup`).
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-- If `m` is odd and `2^k ∣ a * m` then `2^k ∣ a`. -/
theorem dvd_of_mul_odd {k a m : ℕ} (hm : Odd m) (h : 2 ^ k ∣ a * m) : 2 ^ k ∣ a :=
  ((Nat.coprime_two_right.mpr hm).pow_right k).symm.dvd_of_dvd_mul_right h

/-- Every Sylow `2`-subgroup of a finite group `M` meets a normal subgroup `N ≤ M` of order
divisible by `4` in a subgroup of order divisible by `4`. -/
theorem sylow_inf_dvd {M : Type*} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (h4 : 4 ∣ Nat.card N) (Q : Sylow 2 M) : 4 ∣ Nat.card ↥((Q : Subgroup M) ⊓ N) := by
  have hrel : ((Q : Subgroup M) ⊓ N).relIndex N = (Q : Subgroup M).relIndex ((Q : Subgroup M) ⊔ N) := by
    have hA : ((Q : Subgroup M) ⊓ N).relIndex (Q : Subgroup M) = N.relIndex (Q : Subgroup M) :=
      Subgroup.inf_relIndex_left (H := (Q : Subgroup M)) (K := N)
    have hB : N.relIndex (N ⊔ (Q : Subgroup M)) = N.relIndex (Q : Subgroup M) :=
      Subgroup.relIndex_sup_left (Q : Subgroup M) N
    have hsup : N.relIndex ((Q : Subgroup M) ⊔ N) = N.relIndex (Q : Subgroup M) := by
      rw [sup_comm]; exact hB
    have h1 := Subgroup.relIndex_mul_relIndex (H := (Q : Subgroup M) ⊓ N) (K := (Q : Subgroup M))
      (L := (Q : Subgroup M) ⊔ N) inf_le_left le_sup_left
    have h2 := Subgroup.relIndex_mul_relIndex (H := (Q : Subgroup M) ⊓ N) (K := N)
      (L := (Q : Subgroup M) ⊔ N) inf_le_right le_sup_right
    rw [hA, ← h2, hsup] at h1
    have h1' : (Q : Subgroup M).relIndex ((Q : Subgroup M) ⊔ N) * N.relIndex (Q : Subgroup M)
        = ((Q : Subgroup M) ⊓ N).relIndex N * N.relIndex (Q : Subgroup M) := by
      rw [Nat.mul_comm ((Q : Subgroup M).relIndex ((Q : Subgroup M) ⊔ N))]; exact h1
    have hQpos : 0 < Nat.card ↥(Q : Subgroup M) := Nat.card_pos
    have hpos : 0 < N.relIndex (Q : Subgroup M) := by
      rcases Nat.eq_zero_or_pos (N.relIndex (Q : Subgroup M)) with h0 | h
      · exfalso
        have hd := Subgroup.relIndex_dvd_card N (Q : Subgroup M)
        rw [h0] at hd
        rw [Nat.eq_zero_of_zero_dvd hd] at hQpos
        exact absurd hQpos (by omega)
      · exact h
    exact (Nat.mul_right_cancel hpos h1').symm
  have hmul : ((Q : Subgroup M) ⊓ N).relIndex N * Nat.card ↥((Q : Subgroup M) ⊓ N)
      = Nat.card ↥N := by
    have h := Subgroup.relIndex_mul_card ((Q : Subgroup M) ⊓ N) N
    rwa [inf_eq_left.mpr inf_le_right] at h
  have hodd : Odd (((Q : Subgroup M) ⊓ N).relIndex N) := by
    rw [hrel]
    have hQodd : Odd (Q : Subgroup M).index :=
      Nat.not_even_iff_odd.mp fun h => Q.not_dvd_index (even_iff_two_dvd.mp h)
    have hdvd : (Q : Subgroup M).relIndex ((Q : Subgroup M) ⊔ N) ∣ (Q : Subgroup M).index :=
      ⟨((Q : Subgroup M) ⊔ N).index, (Subgroup.relIndex_mul_index le_sup_left).symm⟩
    exact Odd.of_dvd_nat hQodd hdvd
  have hd : 2 ^ 2 ∣ Nat.card ↥((Q : Subgroup M) ⊓ N) * ((Q : Subgroup M) ⊓ N).relIndex N := by
    rw [Nat.mul_comm, hmul]
    simpa using h4
  simpa using dvd_of_mul_odd hodd hd



/-- The `hyper`... main theorem (scratch). -/
theorem L27_step1 : Work.CORE2B.L27_normal_contains_t := by
  intro T h23 h26 G _ _ hFT hCtx B M hM N hNM hNnorm h4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## setup
  have hSnc : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  have huniqS0 : ∀ x ∈ B.S0, orderOf x = 2 → x = B.t := by
    intro x hx hx2
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have h := unique_involution_of_cyclic (H := ↥B.S0)
      (a := (⟨x, hx⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
      (by rw [Subgroup.orderOf_mk x hx]; exact hx2)
      (by rw [Subgroup.orderOf_mk B.t B.t_mem]; exact B.t_order)
    exact congrArg Subtype.val h
  have hSmul : Nat.card (B.S : Subgroup G) = 2 * Nat.card B.S0 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [B.S0_index, inf_eq_left.mpr B.S0_le] at h
    exact h.symm
  have h2S0 : 2 ≤ Nat.card B.S0 := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr B.t_mem)
    rw [Nat.card_zpowers, B.t_order] at h
    exact Nat.le_of_dvd Nat.card_pos h
  have hSdih : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | ⟨n, hn⟩
    · exact absurd h hSnc
    · refine ⟨n, ?_, hn⟩
      have hcard : Nat.card (B.S : Subgroup G) = 2 * n := by
        rw [Nat.card_congr hn.some.toEquiv, DihedralGroup.nat_card]
      have h2n : 2 * n = 2 * Nat.card B.S0 := by rw [← hcard, hSmul]
      have : n = Nat.card B.S0 := Nat.mul_left_cancel (by norm_num) h2n
      omega
  have hcS : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := t_central_in_S B
  have htS : B.t ∈ (B.S : Subgroup G) := B.S0_le B.t_mem
  have htM : B.t ∈ M := hM.t_mem
  haveI hN'norm : (N.subgroupOf M).Normal := hNnorm
  have h4' : 4 ∣ Nat.card ↥(N.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]; exact h4
  -- ## a Sylow of M containing t
  have ht'ord : orderOf (⟨B.t, htM⟩ : ↥M) = 2 := by
    rw [Subgroup.orderOf_mk B.t htM]; exact B.t_order
  have ht'pg : IsPGroup 2 ↥(Subgroup.zpowers (⟨B.t, htM⟩ : ↥M)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ht'ord, pow_one]
  obtain ⟨Qt, htQt⟩ := IsPGroup.exists_le_sylow (p := 2)
    (P := Subgroup.zpowers (⟨B.t, htM⟩ : ↥M)) ht'pg
  have ht'Qt : (⟨B.t, htM⟩ : ↥M) ∈ (Qt : Subgroup ↥M) := htQt (Subgroup.mem_zpowers _)
  rcases lt_or_ge (Nat.card ↥(Qt : Subgroup ↥M)) 8 with hsmall | hbig
  · -- ## Branch 1: |Qt| = 4
    obtain ⟨k, hk⟩ := Qt.isPGroup'.exists_card_eq
    have hkge : 2 ≤ k := by
      by_contra hcon
      have hklt : k < 2 := by omega
      have hcyc : IsCyclic ↥(Qt : Subgroup ↥M) := by
        apply isCyclic_of_card_dvd_prime (p := 2)
        rw [hk]
        interval_cases k <;> simp
      exact hM.sylow_nc Qt hcyc
    have hQt4 : Nat.card ↥(Qt : Subgroup ↥M) = 4 := by
      rw [hk]
      rcases lt_or_ge k 3 with h | h
      · interval_cases k <;> simp_all
      · exfalso
        have h3 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ k)
        omega
    have hinf4 : Nat.card ↥((Qt : Subgroup ↥M) ⊓ N.subgroupOf M) = 4 := by
      have hd := sylow_inf_dvd (N.subgroupOf M) h4' Qt
      have hle := Subgroup.card_dvd_of_le
        (inf_le_left : (Qt : Subgroup ↥M) ⊓ N.subgroupOf M ≤ (Qt : Subgroup ↥M))
      rw [hQt4] at hle
      exact Nat.dvd_antisymm hle hd
    have hQtle : (Qt : Subgroup ↥M) ≤ N.subgroupOf M := by
      have h := Subgroup.eq_of_le_of_card_ge
        (inf_le_left : (Qt : Subgroup ↥M) ⊓ N.subgroupOf M ≤ (Qt : Subgroup ↥M))
        (K := (Qt : Subgroup ↥M)) (by rw [hinf4, hQt4])
      exact h ▸ inf_le_right
    exact Subgroup.mem_subgroupOf.mp (hQtle ht'Qt)
  · -- ## Branch 2: |Qt| ≥ 8
    have hQt8 : 8 ≤ Nat.card ↥(Qt : Subgroup ↥M) := hbig
    -- get the dihedral structure of any Sylow of M
    have dih_of : ∀ Q : Sylow 2 ↥M, ∃ k : ℕ, 4 ≤ k ∧
        Nonempty (↥(Q : Subgroup ↥M) ≃* DihedralGroup k) := by
      intro Q
      have hQ8 : 8 ≤ Nat.card ↥(Q : Subgroup ↥M) := by
        rw [Nat.card_congr (Sylow.equiv Q Qt).toEquiv]
        exact hbig
      rcases Work.RED.DihOrCycSubgroup Work.RED.DihedralSubgroup (K := M) hCtx.sylow Q with h | ⟨k, hk⟩
      · exact absurd h (hM.sylow_nc Q)
      · refine ⟨k, ?_, hk⟩
        have hc : Nat.card ↥(Q : Subgroup ↥M) = 2 * k := by
          rw [Nat.card_congr hk.some.toEquiv, DihedralGroup.nat_card]
        omega
    -- the fusion hypothesis
    have hfus : ∀ (X : Type) [Group X] [Finite X] (P : Sylow 2 X) (k : ℕ), 2 ≤ k →
        Nonempty ((P : Subgroup X) ≃* DihedralGroup k) →
        (∀ N : Subgroup X, N.Normal → N.index ≠ 2) →
        (∀ x y : X, orderOf x = 2 → orderOf y = 2 → ∃ c : X, c * x * c⁻¹ = y) := by
      intro X _ _ P k hk2 hP hno2
      have h1 := (T.fus X P k hk2 hP hno2).1
      intro x y hx hy
      exact isConj_iff.mp (h1 x y hx hy)
    rcases hM.size with hsize | hsize | htO
    · -- ## case (ii): |S ⊓ M| ≥ 8
      have hQ'pg : IsPGroup 2 ↥(((B.S : Subgroup G) ⊓ M).subgroupOf M) := by
        have h1 := (B.S.isPGroup').to_le (inf_le_left : (B.S : Subgroup G) ⊓ M ≤ (B.S : Subgroup G))
        exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : (B.S : Subgroup G) ⊓ M ≤ M)).symm
      obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow (p := 2)
        (P := ((B.S : Subgroup G) ⊓ M).subgroupOf M) hQ'pg
      obtain ⟨k, hk4, ⟨e⟩⟩ := dih_of Q
      obtain ⟨T0, τ, hT0le, hT0cyc, hT0idx, hτT0, hτ2, hτuniq⟩ := dih_helper hk4 e
      have hτc : ∀ y ∈ (Q : Subgroup ↥M), y * τ = τ * y :=
        center_of_cyclic_index_two _ _ hT0le hT0idx hτT0 hτ2 hτuniq
      -- τ ∈ N
      have hτN : τ ∈ N.subgroupOf M := by
        have hd := sylow_inf_dvd (N.subgroupOf M) h4' Q
        have hge : 4 ≤ Nat.card ↥((Q : Subgroup ↥M) ⊓ N.subgroupOf M) := Nat.le_of_dvd Nat.card_pos hd
        have := cyclic_index_two_center_mem (S := (Q : Subgroup ↥M)) (S0 := T0)
          Q.isPGroup' hT0le hT0cyc hT0idx hτT0 hτ2 hτuniq
          ((Q : Subgroup ↥M) ⊓ N.subgroupOf M) inf_le_left hge
        exact this.2
      -- τ ∈ (S ⊓ M).subgroupOf M
      have hτQ' : τ ∈ ((B.S : Subgroup G) ⊓ M).subgroupOf M := by
        have hge : 4 ≤ Nat.card ↥(((B.S : Subgroup G) ⊓ M).subgroupOf M) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : (B.S : Subgroup G) ⊓ M ≤ M)).toEquiv]
          omega
        exact cyclic_index_two_center_mem (S := (Q : Subgroup ↥M)) (S0 := T0)
          Q.isPGroup' hT0le hT0cyc hT0idx hτT0 hτ2 hτuniq
          (((B.S : Subgroup G) ⊓ M).subgroupOf M) hQle hge
      have hτSM : ((τ : ↥M) : G) ∈ (B.S : Subgroup G) ⊓ M := Subgroup.mem_subgroupOf.mp hτQ'
      -- t = τ via the uniqueness statement for `B.S ⊓ M`
      have htSM : B.t ∈ (B.S : Subgroup G) ⊓ M := ⟨htS, htM⟩
      have hcen_t : ∀ y ∈ (B.S : Subgroup G) ⊓ M, y * B.t = B.t * y := fun y hy => hcS y hy.1
      have hcen_τ : ∀ y ∈ (B.S : Subgroup G) ⊓ M, y * (τ : G) = (τ : G) * y := by
        intro y hy
        have hyQ : (⟨y, hy.2⟩ : ↥M) ∈ (Q : Subgroup ↥M) := hQle (Subgroup.mem_subgroupOf.mpr hy)
        have h := hτc (⟨y, hy.2⟩ : ↥M) hyQ
        exact congrArg Subtype.val h
      obtain ⟨n, hn2, hn⟩ := hSdih
      have htτ : B.t = ((τ : ↥M) : G) :=
        center_unique_of_dihedral_subgroup hn hn2
          (inf_le_left : (B.S : Subgroup G) ⊓ M ≤ (B.S : Subgroup G)) hsize
          htSM hτSM hcen_t hcen_τ B.t_order (by rw [Subgroup.orderOf_coe]; exact hτ2)
      rw [htτ]
      exact Subgroup.mem_subgroupOf.mp hτN
    · -- ## case |S| = 4 : impossible
      exfalso
      obtain ⟨j, hj⟩ := Qt.isPGroup'.exists_card_eq
      have hj3 : 3 ≤ j := by
        by_contra hcon
        push_neg at hcon
        have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h8Q : 8 ∣ Nat.card ↥(Qt : Subgroup ↥M) := by
        rw [hj]
        exact ⟨2 ^ (j - 3), by
          show 2 ^ j = 2 ^ 3 * 2 ^ (j - 3)
          rw [← pow_add]; congr 1; omega⟩
      have h8G : 8 ∣ Nat.card G :=
        h8Q.trans ((Subgroup.card_subgroup_dvd_card (Qt : Subgroup ↥M)).trans
          (Subgroup.card_subgroup_dvd_card M))
      have hoddidx : Odd (B.S : Subgroup G).index :=
        Nat.not_even_iff_odd.mp fun h => B.S.not_dvd_index (even_iff_two_dvd.mp h)
      have hmul := Subgroup.card_mul_index (B.S : Subgroup G)
      rw [hsize] at hmul
      have h2 : (4 : ℕ) * 2 ∣ (4 : ℕ) * (B.S : Subgroup G).index := by
        rw [hmul]
        exact h8G
      exact absurd (even_iff_two_dvd.mpr
        ((Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 4)).mp h2))
        (Nat.not_even_iff_odd.mpr hoddidx)
    · -- ## case (i): t ∈ O²(M)
      obtain ⟨k, hk4, ⟨e⟩⟩ := dih_of Qt
      obtain ⟨T0, τ, hT0le, hT0cyc, hT0idx, hτT0, hτ2, hτuniq⟩ := dih_helper hk4 e
      have hτc : ∀ y ∈ (Qt : Subgroup ↥M), y * τ = τ * y :=
        center_of_cyclic_index_two _ _ hT0le hT0idx hτT0 hτ2 hτuniq
      have hτN : τ ∈ N.subgroupOf M := by
        have hd := sylow_inf_dvd (N.subgroupOf M) h4' Qt
        have hge : 4 ≤ Nat.card ↥((Qt : Subgroup ↥M) ⊓ N.subgroupOf M) := Nat.le_of_dvd Nat.card_pos hd
        have := cyclic_index_two_center_mem (S := (Qt : Subgroup ↥M)) (S0 := T0)
          Qt.isPGroup' hT0le hT0cyc hT0idx hτT0 hτ2 hτuniq
          ((Qt : Subgroup ↥M) ⊓ N.subgroupOf M) inf_le_left hge
        exact this.2
      have htO' : (⟨B.t, htM⟩ : ↥M) ∈ Work.GW2.twoResidual ↥M := by
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp htO
        rwa [show (⟨B.t, htM⟩ : ↥M) = x from Subtype.ext hxeq.symm]
      obtain ⟨c, hc⟩ := twoResidual_involution_conj hfus Qt k hk4 ⟨e⟩ ht'ord htO' hτ2 (hT0le hτT0) hτc
      have : (⟨B.t, htM⟩ : ↥M) ∈ N.subgroupOf M := by
        have h2 : (⟨B.t, htM⟩ : ↥M) = c⁻¹ * τ * c := by
          rw [← hc]; group
        rw [h2]
        simpa using hN'norm.conj_mem τ hτN c⁻¹
      exact Subgroup.mem_subgroupOf.mp this

end Work.CORE2B
