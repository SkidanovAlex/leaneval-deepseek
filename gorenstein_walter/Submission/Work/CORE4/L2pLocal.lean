import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.L2F.Bridge
import Submission.Work.L2F.BridgeAddOn
import Submission.Work.CORE4.L2PAux.normal_complement_of_normalizer_le_centralizer
import Submission.Work.CORE4.L2PAux.exists_conjSub_of_isComplement
import Submission.Work.CORE4.L2PAux.exists_invariant_sylow
import Submission.Work.CORE4.L2PAux.le_centralizer_of_normalized_isPGroup_odd
import Submission.Work.CORE4.L2PAux.twoSubgroup_le_centralizer_or_four_v2
import Submission.Work.CORE4.L2PAux.factorization_card_psl2
import Submission.Work.CORE4.L2PAux.sylow_prime_inter_eq_bot_or_eq
import Submission.Work.CORE4.L2PAux.arith_aux

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-!
# §4 (12) input `L2pLocalProp`: the single-copy `L₂(q)` fact for the amalgam count

Proof structure (`Submission/Work/NOTES_LEAD_gw_design27.md` §2, route (Bender/Dickson-free)):

* `l2p_psl_main` proves the statement inside the model `PSL(2, GaloisField r e)`, using
  Burnside's normal `p`-complement theorem (`MonoidHom.transferSylow`, imported via
  `L2PAux.normal_complement_of_normalizer_le_centralizer`), the fixed point
  argument for `T`-invariant Sylow subgroups, the `L2F` torus facts
  (`l2TorusNormalizerProp`), the Dickson-type inputs
  `le_centralizer_of_normalized_isPGroup_odd` / `twoSubgroup_le_centralizer_or_four_v2`,
  the Sylow `r`-subgroup data (`factorization_card_psl2`,
  `sylow_prime_inter_eq_bot_or_eq`), and the arithmetic `arith_aux`.
* `l2p_l2pLocal_of_model` transports that statement along the isomorphism
  `↥E ≃* PSL(2, GaloisField r e)` (normalizers, centralizers and conjugation all transport).
* `L2pLocal` is the `Work.GW2.C27.L2pLocalProp` statement of `CORE4/Defs27.lean`.
-/

open Subgroup

/-- `MulAut.conj` applied as a monoid homomorphism is explicit conjugation. -/
lemma l2p_conj_toMonoidHom_apply {G : Type*} [Group G] (g x : G) :
    (MulEquiv.toMonoidHom (MulAut.conj g)) x = g * x * g⁻¹ := by
  simp [MulAut.conj_apply]

/-- Conjugation fixes a normal subgroup. -/
lemma l2p_conjSub_eq_self_of_normal {G : Type*} [Group G] (N : Subgroup G) (hN : N.Normal) (g : G) :
    Work.GW2.conjSub g N = N := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    rw [← hxy, l2p_conj_toMonoidHom_apply]
    exact hN.conj_mem x hx g
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * y * g, hN.conj_mem' y hy g, ?_⟩
    rw [l2p_conj_toMonoidHom_apply]
    group

/-- Conjugating a subgroup of `↥H` and then pushing into `L` is conjugation in `L`. -/
lemma l2p_map_conj_map_subtype {L : Type} [Group L] (H : Subgroup L) (K : Subgroup ↥H) (h : ↥H) :
    (K.map H.subtype).map (MulAut.conj (h : L)).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).map H.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- Conjugation by an element of the centralizer of `T` fixes `T`. -/
lemma l2p_conjSub_eq_self_of_mem_centralizer {G : Type*} [Group G] {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (T : Set G)) : Work.GW2.conjSub g T = T := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have hx' : x * g = g * x := Subgroup.mem_centralizer_iff.mp hg x hx
    have h1 : (MulEquiv.toMonoidHom (MulAut.conj g)) x = x := by
      rw [l2p_conj_toMonoidHom_apply]
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hx']
        _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [h1] at hxy
    rwa [← hxy]
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    have hy' : y * g = g * y := Subgroup.mem_centralizer_iff.mp hg y hy
    rw [l2p_conj_toMonoidHom_apply]
    calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [hy']
      _ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-- `conjSub` is multiplicative: it is a left action by conjugation. -/
lemma l2p_conjSub_mul {G : Type*} [Group G] (a b : G) (T : Subgroup G) :
    Work.GW2.conjSub (a * b) T = Work.GW2.conjSub a (Work.GW2.conjSub b T) := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- A subgroup of the normalizer of `T` inside `H` corresponds to a subgroup of `N_L(T)`. -/
lemma l2p_map_normalizer_subgroupOf_le {L : Type} [Group L] {T H : Subgroup L} (hTH : T ≤ H) :
    Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) ≤
      (Subgroup.normalizer (T : Set L)).subgroupOf H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have hzH : z ∈ H := hTH hz
    have h2 := (Subgroup.mem_normalizer_iff.mp hx ⟨z, hzH⟩).mp
      (show (⟨z, hzH⟩ : ↥H) ∈ T.subgroupOf H from hz)
    simpa using (Subgroup.mem_subgroupOf.mp h2)
  · intro hz
    have hzH : z ∈ H := by
      have hxH : (x : L) ∈ H := x.2
      have hz' : (x : L)⁻¹ * ((x : L) * z * (x : L)⁻¹) * (x : L) ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem hxH) (hTH hz)) hxH
      rwa [show (x : L)⁻¹ * ((x : L) * z * (x : L)⁻¹) * (x : L) = z from by group] at hz'
    have hxinv : x⁻¹ ∈ Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      Subgroup.inv_mem _ hx
    have h2 := (Subgroup.mem_normalizer_iff.mp hxinv (⟨(x : L) * z * (x : L)⁻¹, hTH hz⟩ : ↥H)).mp
      (show (⟨(x : L) * z * (x : L)⁻¹, hTH hz⟩ : ↥H) ∈ T.subgroupOf H from hz)
    have hval : (x⁻¹ * (⟨(x : L) * z * (x : L)⁻¹, hTH hz⟩ : ↥H) * (x⁻¹)⁻¹ : ↥H) =
        (⟨z, hzH⟩ : ↥H) := by
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hval] at h2
    exact Subgroup.mem_subgroupOf.mp h2

/-- A subgroup of the centralizer of `T` inside `H` lies in `C_{↥H}(T)`. -/
lemma l2p_centralizer_subgroupOf_le {L : Type} [Group L] {T H : Subgroup L} :
    (Subgroup.centralizer (T : Set L)).subgroupOf H ≤
      Subgroup.centralizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have h1 : (y : L) * (x : L) = (x : L) * (y : L) := hx (y : L) hy
  exact Subtype.ext (by simpa using h1)

theorem l2p_psl_main (ρ k p : ℕ) [Fact ρ.Prime] (hρ : Odd ρ) (hk : 5 ≤ ρ ^ k)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpρ : p ≠ ρ)
    (T H : Subgroup (PSL(2, GaloisField ρ k)))
    (hTH : T ≤ H) (hTcard : Nat.card T = p) (hpdvd : ¬ p ^ 2 ∣ Nat.card H)
    (hN : H ⊓ Subgroup.normalizer (T : Set _) ≤ Subgroup.centralizer (T : Set _)) :
    (∀ Z : Subgroup (PSL(2, GaloisField ρ k)), Z ≤ H → Nat.card Z = p → Z = T) ∨
    (∃ V : Subgroup (PSL(2, GaloisField ρ k)), V ≤ H ∧ Work.GW2.IsFourGroup V) ∨
    (∃ R : Subgroup (PSL(2, GaloisField ρ k)), Nat.card R = ρ ^ k ∧
        T ≤ Subgroup.normalizer (R : Set _) ∧
        ∀ Z : Subgroup (PSL(2, GaloisField ρ k)), Z ≤ H → Nat.card Z = p →
          ∃ c ∈ R ⊓ H, Z = Work.GW2.conjSub c T) := by
  classical
  haveI hpf : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hTpg : IsPGroup p T := IsPGroup.of_card (n := 1) (by rw [hTcard, pow_one])
  have hTodd : Odd (Nat.card T) := hTcard ▸ hpodd
  -- ## Step 1: `T.subgroupOf H` is a Sylow `p`-subgroup of `↥H`
  have hsub_map : ∀ K : Subgroup (PSL(2, GaloisField ρ k)), K ≤ H →
      Subgroup.map H.subtype (K.subgroupOf H) = K := by
    intro K hK
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK]
  have hTNcard : Nat.card (T.subgroupOf H) = p := by
    have h := Subgroup.card_subtype H (T.subgroupOf H)
    rw [hsub_map T hTH, hTcard] at h
    exact h.symm
  have hTNpg : IsPGroup p (T.subgroupOf H) :=
    IsPGroup.of_card (n := 1) (by rw [hTNcard, pow_one])
  have hpdvdH : ¬ p ^ 2 ∣ Nat.card ↥H := hpdvd
  let TN : Sylow p ↥H :=
    { toSubgroup := T.subgroupOf H
      isPGroup' := hTNpg
      is_maximal' := by
        intro Q hQ hle
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ
        have hQdvd : p ^ j ∣ Nat.card ↥H := by
          rw [← hj]
          have h := Subgroup.card_dvd_of_le (H := Q) (K := (⊤ : Subgroup ↥H)) le_top
          rwa [Subgroup.card_top] at h
        have hjle : j ≤ 1 := by
          by_contra hj2
          exact hpdvdH ((pow_dvd_pow p (by omega)).trans hQdvd)
        have hge : p ≤ Nat.card ↥Q := by
          rw [← hTNcard]
          exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
        have hQcard : Nat.card ↥Q = p := by
          rw [hj]
          interval_cases j
          · rw [hj] at hge
            have h2 := (Fact.out : Nat.Prime p).two_le
            have hge' : p ≤ 1 := by simpa using hge
            omega
          · rw [pow_one]
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, hTNcard])).symm }
  -- ## Step 2: the normalizer hypothesis, transported to `↥H`
  have hNorm : Subgroup.normalizer ((TN : Subgroup ↥H) : Set ↥H) ≤
      Subgroup.centralizer ((TN : Subgroup ↥H) : Set ↥H) := by
    intro x hx
    have hxN : (x : PSL(2, GaloisField ρ k)) ∈
        Subgroup.normalizer (T : Set (PSL(2, GaloisField ρ k))) :=
      l2p_map_normalizer_subgroupOf_le hTH hx
    have hxc : (x : PSL(2, GaloisField ρ k)) ∈
        Subgroup.centralizer (T : Set (PSL(2, GaloisField ρ k))) :=
      hN (Subgroup.mem_inf.mpr ⟨x.2, hxN⟩)
    exact l2p_centralizer_subgroupOf_le (Subgroup.mem_subgroupOf.mpr hxc)
  -- ## Step 3: Burnside's normal `p`-complement theorem
  obtain ⟨QN, hQNnorm, hQNcomp, hQNcop⟩ :=
    Work.CORE4.L2PAux.normal_complement_of_normalizer_le_centralizer TN hNorm
  set Q : Subgroup (PSL(2, GaloisField ρ k)) := QN.map H.subtype with hQdef
  have hQle : Q ≤ H := Subgroup.map_subtype_le QN
  have hQcard : Nat.card Q = Nat.card QN := Subgroup.card_subtype H QN
  have hpdvdQ : ¬ p ∣ Nat.card Q := by rw [hQcard]; exact hQNcop
  have hcopQ : Nat.Coprime p (Nat.card Q) := hp.coprime_iff_not_dvd.mpr hpdvdQ
  -- ## Step 4: `T` normalizes `Q`, and the order-`p` subgroups of `H`
  have hconj : ∀ t ∈ T, Work.GW2.conjSub t Q = Q := by
    intro t ht
    have htH : t ∈ H := hTH ht
    have h1 : Work.GW2.conjSub (⟨t, htH⟩ : ↥H) QN = QN :=
      l2p_conjSub_eq_self_of_normal QN hQNnorm _
    calc Work.GW2.conjSub t Q
        = Work.GW2.conjSub t (QN.map H.subtype) := by rw [hQdef]
      _ = (Work.GW2.conjSub (⟨t, htH⟩ : ↥H) QN).map H.subtype :=
            l2p_map_conj_map_subtype H QN ⟨t, htH⟩
      _ = QN.map H.subtype := by rw [h1]
      _ = Q := hQdef.symm
  have hTNQ : T ≤ Subgroup.normalizer (Q : Set (PSL(2, GaloisField ρ k))) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := hconj t ht
    constructor
    · intro hy
      have h1 : (MulAut.conj t) y ∈ Work.GW2.conjSub t Q := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rwa [h] at h1
    · intro hy
      have h1 : (MulAut.conj t) y ∈ Work.GW2.conjSub t Q := by rw [h]; exact hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp h1
      have h2 : t * x * t⁻¹ = t * y * t⁻¹ := by
        calc t * x * t⁻¹ = (MulEquiv.toMonoidHom (MulAut.conj t)) x := by
              rw [l2p_conj_toMonoidHom_apply]
          _ = (MulAut.conj t) y := hxy
          _ = t * y * t⁻¹ := by rw [MulAut.conj_apply]
      have h3 : x = y := mul_left_cancel (mul_right_cancel h2)
      rwa [← h3]
  have hOrderP : ∀ Z : Subgroup (PSL(2, GaloisField ρ k)), Z ≤ H → Nat.card Z = p →
      ∃ q ∈ Q, Z = Work.GW2.conjSub q T := by
    intro Z hZH hZcard
    have hZNcard : Nat.card (Z.subgroupOf H) = p := by
      have h := Subgroup.card_subtype H (Z.subgroupOf H)
      rw [hsub_map Z hZH, hZcard] at h
      exact h.symm
    obtain ⟨q, hq, hZeq⟩ := Work.CORE4.L2PAux.exists_conjSub_of_isComplement QN (T.subgroupOf H) (Z.subgroupOf H)
      hQNnorm hQNcomp hTNcard hZNcard hpdvdH
    refine ⟨(q : PSL(2, GaloisField ρ k)), Subgroup.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    have hh := congrArg (Subgroup.map H.subtype) hZeq
    simp only [Subgroup.map_map] at hh
    rw [hsub_map Z hZH] at hh
    have hhom : H.subtype.comp (MulAut.conj q).toMonoidHom =
        (MulAut.conj (q : PSL(2, GaloisField ρ k))).toMonoidHom.comp H.subtype := by
      ext x
      simp [MulAut.conj_apply]
    rw [hhom] at hh
    rw [← Subgroup.map_map, hsub_map T hTH] at hh
    exact hh
  -- ## Step 5: the centralizer `C` of `T` is a torus of order prime to `ρ`
  set C : Subgroup (PSL(2, GaloisField ρ k)) :=
    Subgroup.centralizer (T : Set (PSL(2, GaloisField ρ k))) with hCdef
  obtain ⟨hCcyc, hCcard, -⟩ :=
    Work.L2F.GW2Bridge.l2TorusNormalizerProp ρ k hρ hk p hp hp2 hpρ T hTcard
  have hCopC : Nat.Coprime (Nat.card C) ρ := by
    have hnotdvd : ¬ ρ ∣ Nat.card C := by
      intro hdvd
      have h2dvd : ρ ∣ 2 * Nat.card C := dvd_mul_of_dvd_right hdvd 2
      have hρpow : ρ ∣ ρ ^ k := dvd_pow_self ρ (by rintro rfl; simp at hk)
      have hkpos : 1 ≤ ρ ^ k := by omega
      rcases hCcard with h2 | h2
      · rw [h2] at h2dvd
        exact (Fact.out : Nat.Prime ρ).not_dvd_one
          ((Nat.dvd_add_iff_right hρpow).mpr h2dvd)
      · rw [h2] at h2dvd
        have h3 : ρ ^ k - 1 + 1 = ρ ^ k := Nat.sub_add_cancel hkpos
        exact (Fact.out : Nat.Prime ρ).not_dvd_one
          ((Nat.dvd_add_iff_right h2dvd).mpr (h3 ▸ hρpow))
    rwa [Nat.coprime_comm, (Fact.out : Nat.Prime ρ).coprime_iff_not_dvd]
  set CQ : Subgroup (PSL(2, GaloisField ρ k)) := Q ⊓ C with hCQdef
  -- ## Step 6: case analysis
  by_cases hfour : ∃ V : Subgroup (PSL(2, GaloisField ρ k)), V ≤ H ∧ Work.GW2.IsFourGroup V
  · exact Or.inr (Or.inl hfour)
  · push_neg at hfour
    have hQne : Nat.card Q ≠ 0 := Nat.card_pos.ne'
    have hCQdvd : Nat.card CQ ∣ Nat.card Q := Subgroup.card_dvd_of_le inf_le_left
    have hCopCQ : Nat.Coprime (Nat.card CQ) ρ :=
      Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le inf_le_right) hCopC
    have hℓdvd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ρ →
        ℓ ^ (Nat.card Q).factorization ℓ ∣ Nat.card CQ := by
      intro ℓ hℓpr hℓρ
      haveI : Fact ℓ.Prime := ⟨hℓpr⟩
      obtain ⟨R, hRQ, hRpg, hRcard, hTR⟩ := Work.CORE4.L2PAux.exists_invariant_sylow (ℓ := ℓ) Q T hTNQ hTpg hcopQ
      have hRC : R ≤ C := by
        rcases eq_or_ne ℓ 2 with h2eq | h2eq
        · rw [h2eq] at hRpg
          rcases Work.CORE4.L2PAux.twoSubgroup_le_centralizer_or_four_v2 hρ hk R T hRpg hTodd hTR with h | hV
          · exact h
          · obtain ⟨V, hVR, hVcard, hVsq⟩ := hV
            exact absurd ⟨hVcard, hVsq⟩ (hfour V (hVR.trans (hRQ.trans hQle)))
        · exact Work.CORE4.L2PAux.le_centralizer_of_normalized_isPGroup_odd hρ hk hℓpr h2eq hℓρ R T hRpg hTodd hTR
      have hle : R ≤ CQ := le_inf hRQ hRC
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le hle
    have harith : Nat.card CQ * ρ ^ (Nat.card Q).factorization ρ = Nat.card Q :=
      Work.CORE4.L2PAux.arith_aux Fact.out hQne hCQdvd hCopCQ hℓdvd
    by_cases hρQ : ρ ∣ Nat.card Q
    · -- ### the Sylow `ρ`-subgroup case
      have hvge1 : 1 ≤ (Nat.card Q).factorization ρ :=
        (Fact.out : Nat.Prime ρ).pow_dvd_iff_le_factorization hQne |>.mp (by simpa using hρQ)
      obtain ⟨Rρ, hRρQ, hRρpg, hRρcard, hTRρ⟩ :=
        Work.CORE4.L2PAux.exists_invariant_sylow (p := p) (ℓ := ρ) Q T hTNQ hTpg hcopQ
      have hRρne : Rρ ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hRρcard
        have hle2 : ρ ≤ ρ ^ (Nat.card Q).factorization ρ := by
          calc ρ = ρ ^ 1 := (pow_one ρ).symm
            _ ≤ ρ ^ (Nat.card Q).factorization ρ :=
                Nat.pow_le_pow_right (Fact.out : Nat.Prime ρ).pos hvge1
        rw [← hRρcard] at hle2
        have h2 := (Fact.out : Nat.Prime ρ).two_le
        omega
      have hCQcard : Nat.card CQ * Nat.card Rρ = Nat.card Q := by
        rw [hRρcard]; exact harith
      have hdisj : CQ ⊓ Rρ = ⊥ := by
        rw [← Subgroup.card_eq_one]
        have h1 : Nat.card ↥(CQ ⊓ Rρ) ∣ ρ ^ (Nat.card Q).factorization ρ := by
          rw [← hRρcard]
          exact Subgroup.card_dvd_of_le inf_le_right
        have hcop : Nat.Coprime (Nat.card ↥(CQ ⊓ Rρ)) ρ :=
          Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hCopCQ
        exact Nat.dvd_one.mp
          (Nat.Coprime.dvd_of_dvd_mul_left (hcop.pow_right _) (by simpa using h1))
      -- every element of `Q` is `u * c` with `u ∈ Rρ`, `c ∈ CQ`
      have hsurj : ∀ q ∈ Q, ∃ u ∈ Rρ, ∃ c ∈ CQ, q = u * c := by
        intro q hq
        let f : ↥Rρ × ↥CQ → ↥Q := fun x =>
          ⟨(x.1 : PSL(2, GaloisField ρ k)) * (x.2 : PSL(2, GaloisField ρ k)),
            Q.mul_mem (hRρQ x.1.2) ((Subgroup.mem_inf.mp x.2.2).1)⟩
        have hinj : Function.Injective f := by
          rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab
          have h1 : (a1 : PSL(2, GaloisField ρ k)) * (a2 : PSL(2, GaloisField ρ k)) =
              (b1 : PSL(2, GaloisField ρ k)) * (b2 : PSL(2, GaloisField ρ k)) :=
            congrArg Subtype.val hab
          have h2 : (b1 : PSL(2, GaloisField ρ k))⁻¹ * (a1 : PSL(2, GaloisField ρ k)) =
              (b2 : PSL(2, GaloisField ρ k)) * (a2 : PSL(2, GaloisField ρ k))⁻¹ := by
            calc (b1 : PSL(2, GaloisField ρ k))⁻¹ * (a1 : PSL(2, GaloisField ρ k))
                = ((b1 : PSL(2, GaloisField ρ k))⁻¹ *
                    ((a1 : PSL(2, GaloisField ρ k)) * (a2 : PSL(2, GaloisField ρ k)))) *
                    (a2 : PSL(2, GaloisField ρ k))⁻¹ := by group
              _ = ((b1 : PSL(2, GaloisField ρ k))⁻¹ *
                    ((b1 : PSL(2, GaloisField ρ k)) * (b2 : PSL(2, GaloisField ρ k)))) *
                    (a2 : PSL(2, GaloisField ρ k))⁻¹ := by rw [h1]
              _ = (b2 : PSL(2, GaloisField ρ k)) *
                    (a2 : PSL(2, GaloisField ρ k))⁻¹ := by group
          have h3 : (b1 : PSL(2, GaloisField ρ k))⁻¹ * (a1 : PSL(2, GaloisField ρ k)) ∈ Rρ :=
            Rρ.mul_mem (Rρ.inv_mem b1.2) a1.2
          have h4 : (b1 : PSL(2, GaloisField ρ k))⁻¹ * (a1 : PSL(2, GaloisField ρ k)) ∈ CQ := by
            rw [h2]
            exact CQ.mul_mem b2.2 (CQ.inv_mem a2.2)
          have h5 : (b1 : PSL(2, GaloisField ρ k))⁻¹ * (a1 : PSL(2, GaloisField ρ k)) = 1 := by
            have hmem : (b1 : PSL(2, GaloisField ρ k))⁻¹ * (a1 : PSL(2, GaloisField ρ k)) ∈
                CQ ⊓ Rρ := Subgroup.mem_inf.mpr ⟨h4, h3⟩
            rw [hdisj] at hmem
            simpa using hmem
          have ha1 : (a1 : PSL(2, GaloisField ρ k)) = (b1 : PSL(2, GaloisField ρ k)) := by
            have h6 := congrArg (fun z => (b1 : PSL(2, GaloisField ρ k)) * z) h5
            simpa using h6
          have ha2 : (a2 : PSL(2, GaloisField ρ k)) = (b2 : PSL(2, GaloisField ρ k)) := by
            rw [ha1] at h1
            exact mul_left_cancel h1
          exact Prod.ext (Subtype.ext ha1) (Subtype.ext ha2)
        have hcard : Nat.card (↥Rρ × ↥CQ) = Nat.card ↥Q := by
          rw [Nat.card_prod, mul_comm, hCQcard]
        have hrange : (Set.range f).ncard = Nat.card ↥Q := by
          rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
          exact hcard
        have huniv : Set.range f = Set.univ :=
          Set.eq_of_subset_of_ncard_le (s := Set.range f) (t := Set.univ)
            (Set.subset_univ _) (by rw [Set.ncard_univ, hrange])
        have hqmem : (⟨q, hq⟩ : ↥Q) ∈ Set.range f := by rw [huniv]; exact Set.mem_univ _
        obtain ⟨x, hx⟩ := Set.mem_range.mp hqmem
        exact ⟨(x.1 : PSL(2, GaloisField ρ k)), x.1.2, (x.2 : PSL(2, GaloisField ρ k)), x.2.2,
          (congrArg Subtype.val hx).symm⟩
      -- the Sylow `ρ`-subgroup `R` of `L` containing `Rρ`
      obtain ⟨Rsyl, hleR⟩ := hRρpg.exists_le_sylow
      have hRcard : Nat.card (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) = ρ ^ k := by
        rw [Sylow.card_eq_multiplicity (P := Rsyl), (Work.CORE4.L2PAux.factorization_card_psl2 ρ k hρ hk).1]
      have hconjRcard : ∀ t : PSL(2, GaloisField ρ k),
          Nat.card (Work.GW2.conjSub t (Rsyl : Subgroup (PSL(2, GaloisField ρ k)))) = ρ ^ k := by
        intro t
        rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective, hRcard]
      have hTNR : T ≤ Subgroup.normalizer ((Rsyl : Subgroup (PSL(2, GaloisField ρ k))) : Set _) := by
        intro t ht
        have hRρle : Rρ ≤ Work.GW2.conjSub t (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) := by
          intro x hx
          have hx' : t⁻¹ * x * t ∈ Rρ := by
            simpa using Subgroup.le_normalizer_iff.mp hTRρ t⁻¹ (T.inv_mem ht) x hx
          refine Subgroup.mem_map.mpr ⟨t⁻¹ * x * t, hleR hx', ?_⟩
          rw [l2p_conj_toMonoidHom_apply]
          group
        have hne : (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) ⊓
            Work.GW2.conjSub t (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) ≠ ⊥ := by
          intro hbot
          exact hRρne (le_bot_iff.mp (by rw [← hbot]; exact le_inf hleR hRρle))
        have heq : (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) =
            Work.GW2.conjSub t (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) :=
          Work.CORE4.L2PAux.sylow_prime_inter_eq_bot_or_eq hρ hk _ _ hRcard (hconjRcard t) hne
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hmem : t * y * t⁻¹ ∈ Work.GW2.conjSub t
              (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) :=
            Subgroup.mem_map.mpr ⟨y, hy, by rw [l2p_conj_toMonoidHom_apply]⟩
          rwa [← heq] at hmem
        · intro hy
          have hmem : t * y * t⁻¹ ∈ Work.GW2.conjSub t
              (Rsyl : Subgroup (PSL(2, GaloisField ρ k))) := by rw [← heq]; exact hy
          obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.mp hmem
          have h4 : t * y' * t⁻¹ = t * y * t⁻¹ := by
            rw [← hy'eq, l2p_conj_toMonoidHom_apply]
          have h3 : y' = y := mul_left_cancel (mul_right_cancel h4)
          rwa [← h3]
      refine Or.inr (Or.inr ⟨(Rsyl : Subgroup (PSL(2, GaloisField ρ k))), hRcard, hTNR, ?_⟩)
      intro Z hZH hZcard
      obtain ⟨q, hq, hZeq⟩ := hOrderP Z hZH hZcard
      obtain ⟨u, huRρ, c, hcCQ, hqu⟩ := hsurj q hq
      have hcC : c ∈ C := (Subgroup.mem_inf.mp hcCQ).2
      refine ⟨u, ⟨hleR huRρ, hQle (hRρQ huRρ)⟩, ?_⟩
      rw [hZeq, hqu, l2p_conjSub_mul, l2p_conjSub_eq_self_of_mem_centralizer hcC]
    · -- ### `ρ ∤ |Q|`: `T` is the unique order-`p` subgroup
      left
      have hfac0 : (Nat.card Q).factorization ρ = 0 := Nat.factorization_eq_zero_of_not_dvd hρQ
      have hCQcard : Nat.card CQ = Nat.card Q := by
        have h := harith
        rwa [hfac0, pow_zero, mul_one] at h
      have hCQeq : CQ = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hCQcard])
      intro Z hZH hZcard
      obtain ⟨q, hq, hZeq⟩ := hOrderP Z hZH hZcard
      have hqCQ : q ∈ CQ := by rw [hCQeq]; exact hq
      have hqC : q ∈ C := (Subgroup.mem_inf.mp hqCQ).2
      rw [hZeq, l2p_conjSub_eq_self_of_mem_centralizer hqC]

/-! ## Transport of normalizers and centralizers along an isomorphism -/

section Transport
variable {A B : Type} [Group A] [Group B]

lemma l2p_mem_normalizer_map_iff (φ : A ≃* B) (K : Subgroup A) (x : A) :
    x ∈ Subgroup.normalizer (K : Set A) ↔
      (φ x) ∈ Subgroup.normalizer (K.map φ.toMonoidHom : Set B) := by
  have hcoe : ∀ a : A, φ.toMonoidHom a = φ a := fun a => rfl
  constructor
  · intro hx
    have hx' := Subgroup.mem_normalizer_iff.mp hx
    have hxinv' := Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem (Subgroup.normalizer (K : Set A)) hx)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨x * k * x⁻¹, (hx' k).mp hk, ?_⟩
      simp [hcoe]
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hz
      rw [hcoe] at hkz
      refine Subgroup.mem_map.mpr ⟨x⁻¹ * k * x, by simpa using (hxinv' k).mp hk, ?_⟩
      have h3 : z = (φ x)⁻¹ * (φ k) * (φ x) := by rw [hkz]; group
      rw [h3]
      simp [hcoe]
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.mp
        ((hx (φ k)).mp (Subgroup.mem_map.mpr ⟨k, hk, by simp [hcoe]⟩))
      rw [hcoe] at hk'eq
      have h2 : x * k * x⁻¹ = k' := φ.injective (by rw [hk'eq]; simp [hcoe])
      rwa [h2]
    · intro hk
      obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.mp
        ((hx (φ k)).mpr (Subgroup.mem_map.mpr ⟨x * k * x⁻¹, hk, by simp [hcoe]⟩))
      rw [hcoe] at hk'eq
      have h2 : k = k' := φ.injective (by rw [hk'eq])
      rwa [h2]

lemma l2p_mem_centralizer_map_iff (φ : A ≃* B) (K : Subgroup A) (x : A) :
    x ∈ Subgroup.centralizer (K : Set A) ↔
      (φ x) ∈ Subgroup.centralizer (K.map φ.toMonoidHom : Set B) := by
  have hcoe : ∀ a : A, φ.toMonoidHom a = φ a := fun a => rfl
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    have h1 : k * x = x * k := h k hk
    show φ.toMonoidHom k * φ x = φ x * φ.toMonoidHom k
    rw [hcoe k, ← map_mul, ← map_mul, h1]
  · intro h k hk
    have h1 := h (φ k) (Subgroup.mem_map.mpr ⟨k, hk, by simp [hcoe]⟩)
    exact φ.injective (by simpa using h1)

lemma l2p_map_conj_eq_of_conj (φ : A ≃* B) (K : Subgroup A) (y : B) :
    (K.map φ.toMonoidHom).map (MulAut.conj y).toMonoidHom =
      (K.map (MulAut.conj (φ.symm y)).toMonoidHom).map φ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

end Transport

section TransportSubtype
variable {G : Type} [Group G]

lemma l2p_mem_normalizer_map_subtype {E : Subgroup G} (K : Subgroup ↥E) (x : ↥E) :
    x ∈ Subgroup.normalizer (K : Set ↥E) ↔
      (x : G) ∈ Subgroup.normalizer (K.map E.subtype : Set G) := by
  constructor
  · intro hx
    have hx' := Subgroup.mem_normalizer_iff.mp hx
    have hxinv' := Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem (Subgroup.normalizer (K : Set ↥E)) hx)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨x * k * x⁻¹, (hx' k).mp hk, ?_⟩
      simp
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hz
      simp only [Subgroup.coe_subtype] at hkz
      refine Subgroup.mem_map.mpr ⟨x⁻¹ * k * x, by simpa using (hxinv' k).mp hk, ?_⟩
      show ((x⁻¹ * k * x : ↥E) : G) = z
      rw [show ((x⁻¹ * k * x : ↥E) : G) = (x : G)⁻¹ * (k : G) * (x : G) by simp]
      rw [show (x : G)⁻¹ * (k : G) * (x : G) = z by rw [hkz]; group]
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.mp
        ((hx (k : G)).mp (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩))
      simp only [Subgroup.coe_subtype] at hk'eq
      have h2 : x * k * x⁻¹ = k' := Subtype.ext (by rw [hk'eq]; simp)
      rwa [h2]
    · intro hk
      obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.mp
        ((hx (k : G)).mpr (Subgroup.mem_map.mpr ⟨x * k * x⁻¹, hk, by simp⟩))
      simp only [Subgroup.coe_subtype] at hk'eq
      have h2 : k = k' := (Subtype.ext (by simpa using hk'eq)).symm
      rwa [h2]

lemma l2p_mem_centralizer_map_subtype {E : Subgroup G} (K : Subgroup ↥E) (x : ↥E) :
    x ∈ Subgroup.centralizer (K : Set ↥E) ↔
      (x : G) ∈ Subgroup.centralizer (K.map E.subtype : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    have h1 : k * x = x * k := h k hk
    show (k : G) * (x : G) = (x : G) * (k : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, h1]
  · intro h k hk
    have h1 : (k : G) * (x : G) = (x : G) * (k : G) :=
      h k (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
    exact Subtype.ext (by simpa using h1)

end TransportSubtype

/-! ## The transport of the model statement to `E ≅ PSL(2, r^e)` -/

theorem l2p_l2pLocal_of_model :
    ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (r e : ℕ) [Fact r.Prime], Odd r →
    5 ≤ r ^ e → Nonempty (E ≃* PSL(2, GaloisField r e)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ r →
    ∀ T H : Subgroup G, T ≤ H → H ≤ E → Nat.card T = p → ¬ p ^ 2 ∣ Nat.card H →
      H ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.centralizer (T : Set G) →
      (∀ Z : Subgroup G, Z ≤ H → Nat.card Z = p → Z = T) ∨
      (∃ V : Subgroup G, V ≤ H ∧ Work.GW2.IsFourGroup V) ∨
      (∃ R : Subgroup G, R ≤ E ∧ Nat.card R = r ^ e ∧ T ≤ Subgroup.normalizer (R : Set G) ∧
        ∀ Z : Subgroup G, Z ≤ H → Nat.card Z = p → ∃ c ∈ R ⊓ H, Z = Work.GW2.conjSub c T) := by
  intro G _ _ E r e _ hr hre hEiso p hp hp2 hpr T H hTH hHE hTcard hpdvd hcent
  classical
  obtain ⟨ψ⟩ := hEiso
  have hTE : T ≤ E := hTH.trans hHE
  have hsubmapE : ∀ K : Subgroup G, K ≤ E → Subgroup.map E.subtype (K.subgroupOf E) = K := by
    intro K hK
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK]
  have hTEcard : Nat.card (T.subgroupOf E) = p := by
    have h := Subgroup.card_subtype E (T.subgroupOf E)
    rw [hsubmapE T hTE, hTcard] at h
    exact h.symm
  have hHEcard : Nat.card (H.subgroupOf E) = Nat.card H := by
    have h := Subgroup.card_subtype E (H.subgroupOf E)
    rw [hsubmapE H hHE] at h
    exact h.symm
  -- cardinality of `subgroupOf` for an arbitrary `Z ≤ H ≤ E`
  have hcardZ : ∀ Z : Subgroup G, Z ≤ E → Nat.card (Z.subgroupOf E) = Nat.card Z := by
    intro Z hZ
    have h := Subgroup.card_subtype E (Z.subgroupOf E)
    rw [hsubmapE Z hZ] at h
    exact h.symm
  have hle' : (T.subgroupOf E).map ψ.toMonoidHom ≤ (H.subgroupOf E).map ψ.toMonoidHom := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨x, hTH (Subgroup.mem_subgroupOf.mp hx), rfl⟩
  have hT'card : Nat.card ((T.subgroupOf E).map ψ.toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hTEcard]
  have hH'card : Nat.card ((H.subgroupOf E).map ψ.toMonoidHom) = Nat.card H := by
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hHEcard]
  have hpdvd' : ¬ p ^ 2 ∣ Nat.card ((H.subgroupOf E).map ψ.toMonoidHom) := by
    rw [hH'card]; exact hpdvd
  have hcent' : (H.subgroupOf E).map ψ.toMonoidHom ⊓
        Subgroup.normalizer ((T.subgroupOf E).map ψ.toMonoidHom : Set _) ≤
      Subgroup.centralizer ((T.subgroupOf E).map ψ.toMonoidHom : Set _) := by
    intro y hy
    obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hy).1
    have hxN : x ∈ Subgroup.normalizer ((T.subgroupOf E) : Set ↥E) :=
      (l2p_mem_normalizer_map_iff ψ (T.subgroupOf E) x).mpr (Subgroup.mem_inf.mp hy).2
    have hxNG : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
      have h := (l2p_mem_normalizer_map_subtype (T.subgroupOf E) x).mp hxN
      rwa [hsubmapE T hTE] at h
    have hxCG : (x : G) ∈ Subgroup.centralizer (T : Set G) :=
      hcent (Subgroup.mem_inf.mpr ⟨hxH, hxNG⟩)
    have hxC : x ∈ Subgroup.centralizer ((T.subgroupOf E) : Set ↥E) := by
      have h := hxCG
      rw [← hsubmapE T hTE] at h
      exact (l2p_mem_centralizer_map_subtype (T.subgroupOf E) x).mpr h
    exact (l2p_mem_centralizer_map_iff ψ (T.subgroupOf E) x).mp hxC
  -- the model theorem
  rcases l2p_psl_main r e p hr hre hp hp2 hpr ((T.subgroupOf E).map ψ.toMonoidHom)
      ((H.subgroupOf E).map ψ.toMonoidHom) hle' hT'card hpdvd' hcent' with
    huniq | hfour | hRcase
  · -- `T` is the unique order-`p` subgroup of `H`
    refine Or.inl ?_
    intro Z hZH hZcard
    have hZE : Z ≤ E := hZH.trans hHE
    have hZ'card : Nat.card ((Z.subgroupOf E).map ψ.toMonoidHom) = p := by
      rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hcardZ Z hZE, hZcard]
    have hZ'le : (Z.subgroupOf E).map ψ.toMonoidHom ≤ (H.subgroupOf E).map ψ.toMonoidHom := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨x, hZH (Subgroup.mem_subgroupOf.mp hx), rfl⟩
    have heq : (Z.subgroupOf E).map ψ.toMonoidHom = (T.subgroupOf E).map ψ.toMonoidHom :=
      huniq _ hZ'le hZ'card
    have hinf : Z.subgroupOf E = T.subgroupOf E := Subgroup.map_injective ψ.injective heq
    have h3 := Subgroup.subgroupOf_inj.mp hinf
    rwa [inf_eq_left.mpr hZE, inf_eq_left.mpr hTE] at h3
  · -- `H` contains a four-group
    obtain ⟨V', hV'H', hV'card, hV'sq⟩ := hfour
    refine Or.inr (Or.inl ?_)
    refine ⟨(V'.comap ψ.toMonoidHom).map E.subtype, ?_, ?_, ?_⟩
    · have hVE : V'.comap ψ.toMonoidHom ≤ H.subgroupOf E := by
        intro x hx
        rw [Subgroup.mem_comap] at hx
        obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp (hV'H' hx)
        rwa [← ψ.injective hzeq]
      calc (V'.comap ψ.toMonoidHom).map E.subtype ≤ (H.subgroupOf E).map E.subtype :=
            Subgroup.map_mono hVE
        _ = H := hsubmapE H hHE
    · -- cardinality
      have h1 : Nat.card (V'.comap ψ.toMonoidHom) = Nat.card V' := by
        have h := Subgroup.card_map_of_injective (K := V'.comap ψ.toMonoidHom)
          (f := ψ.toMonoidHom) ψ.injective
        rw [Subgroup.map_comap_eq_self (by intro y _; exact ⟨ψ.symm y, ψ.apply_symm_apply y⟩)] at h
        exact h.symm
      rw [Subgroup.card_map_of_injective (f := E.subtype) E.subtype_injective, h1, hV'card]
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
      have hx' : (x : G) = (E.subtype x : G) := rfl
      have h1 : ((ψ x) : PSL(2, GaloisField r e)) ^ 2 = 1 := hV'sq (ψ x) (Subgroup.mem_comap.mp hx)
      have h2 : x ^ 2 = 1 := ψ.injective (by rw [map_pow, h1, map_one])
      show (E.subtype x) ^ 2 = 1
      rw [← map_pow (E.subtype) x 2, h2, map_one]
  · -- the other order-`p` subgroups are `R ∩ H`-conjugates of `T`
    obtain ⟨R', hR'card, hT'R', hR'conj⟩ := hRcase
    have hmap_eq : (R'.comap ψ.toMonoidHom).map ψ.toMonoidHom = R' :=
      Subgroup.map_comap_eq_self (by intro y _; exact ⟨ψ.symm y, ψ.apply_symm_apply y⟩)
    refine Or.inr (Or.inr ?_)
    refine ⟨(R'.comap ψ.toMonoidHom).map E.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
    · have h1 : Nat.card (R'.comap ψ.toMonoidHom) = Nat.card R' := by
        have h := Subgroup.card_map_of_injective (K := R'.comap ψ.toMonoidHom)
          (f := ψ.toMonoidHom) ψ.injective
        rw [hmap_eq] at h
        exact h.symm
      rw [Subgroup.card_map_of_injective (f := E.subtype) E.subtype_injective, h1, hR'card]
    · intro t ht
      have h1 : ψ (⟨t, hTE ht⟩ : ↥E) ∈ Subgroup.normalizer (R' : Set _) :=
        hT'R' (Subgroup.mem_map.mpr ⟨⟨t, hTE ht⟩, ht, rfl⟩)
      have h2 : (⟨t, hTE ht⟩ : ↥E) ∈
          Subgroup.normalizer ((R'.comap ψ.toMonoidHom) : Set ↥E) :=
        (l2p_mem_normalizer_map_iff ψ (R'.comap ψ.toMonoidHom) ⟨t, hTE ht⟩).mpr
          (by rw [hmap_eq]; exact h1)
      exact (l2p_mem_normalizer_map_subtype (R'.comap ψ.toMonoidHom) ⟨t, hTE ht⟩).mp h2
    · intro Z hZH hZcard
      have hZE : Z ≤ E := hZH.trans hHE
      have hZ'card : Nat.card ((Z.subgroupOf E).map ψ.toMonoidHom) = p := by
        rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hcardZ Z hZE, hZcard]
      have hZ'le : (Z.subgroupOf E).map ψ.toMonoidHom ≤ (H.subgroupOf E).map ψ.toMonoidHom := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_map.mpr ⟨x, hZH (Subgroup.mem_subgroupOf.mp hx), rfl⟩
      have hEx := hR'conj _ hZ'le hZ'card
      set c' := hEx.choose with hc'def
      have hc' : c' ∈ R' ⊓ (H.subgroupOf E).map ψ.toMonoidHom := hEx.choose_spec.1
      have hc'R' : c' ∈ R' := by
        have h := hc'
        rw [Subgroup.mem_inf] at h
        exact h.1
      have hc'H' : c' ∈ (H.subgroupOf E).map ψ.toMonoidHom := by
        have h := hc'
        rw [Subgroup.mem_inf] at h
        exact h.2
      have hconj : (Z.subgroupOf E).map ψ.toMonoidHom =
          Work.GW2.conjSub c' ((T.subgroupOf E).map ψ.toMonoidHom) := hEx.choose_spec.2
      have hc'RE : ψ.symm c' ∈ R'.comap ψ.toMonoidHom := by
        rw [Subgroup.mem_comap]
        simpa using hc'R'
      have hc'HE : ψ.symm c' ∈ H.subgroupOf E := by
        obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hc'H'
        have h2 : ψ.symm c' = z := by
          rw [← hzeq]
          exact ψ.symm_apply_apply z
        rwa [h2]
      refine ⟨((ψ.symm c' : ↥E) : G), ?_, ?_⟩
      · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨ψ.symm c', hc'RE, rfl⟩, hc'HE⟩
      · have h2map : (Z.subgroupOf E).map ψ.toMonoidHom =
            (((T.subgroupOf E).map (MulAut.conj (ψ.symm c')).toMonoidHom).map ψ.toMonoidHom) :=
          hconj.trans (l2p_map_conj_eq_of_conj ψ (T.subgroupOf E) c')
        have hZs : Z.subgroupOf E =
            (T.subgroupOf E).map (MulAut.conj (ψ.symm c')).toMonoidHom :=
          Subgroup.map_injective ψ.injective h2map
        have h := congrArg (Subgroup.map E.subtype) hZs
        simp only [Subgroup.map_map] at h
        rw [hsubmapE Z hZE] at h
        rw [show E.subtype.comp (MulAut.conj (ψ.symm c')).toMonoidHom =
            (MulAut.conj ((ψ.symm c' : ↥E) : G)).toMonoidHom.comp E.subtype from by
          ext x
          simp [MulAut.conj_apply]] at h
        rw [← Subgroup.map_map, hsubmapE T hTE] at h
        exact h

/-- Design-27 input `Work.GW2.C27.L2pLocalProp` (see `CORE4/Defs27.lean` and
`Submission/Work/NOTES_LEAD_gw_design27.md` §2).  This is the single remaining open input of the
§4 (12) amalgam count `Work.CORE4.Counting.PerXAmalgamCount`; it is a piece of Dickson theory for
`PSL(2,q)`, single copy, with NO fusion data.

Read the *unfolded* statement in `Submission/Work/_design_gw/Core27.lean:71`.  In words: let
`E ≅ PSL(2, r^e)` with `r` an odd prime and `r^e ≥ 5`; let `p` be an odd prime with `p ≠ r`; let
`T ≤ H ≤ E` with `|T| = p`, `p² ∤ |H|` (so `T` is a Sylow `p`-subgroup of `H`) and
`N_H(T) ≤ C_E(T)`.  Then either `T` is the only subgroup of order `p` of `H`, or `H` contains a
four-group, or there is a Sylow `r`-subgroup `R` of `E` with `T ≤ N(R)` and every order-`p`
subgroup of `H` is `T^c` for some `c ∈ R ⊓ H` (and then the number of them is `≡ 1 (mod 2p)` and
`≤ r^e`).

Route (Bender/Dickson-free; only proved `l2*` facts + Mathlib):
1. Burnside's normal `p`-complement theorem (`MonoidHom.ker_transferSylow_isComplement'`, since
   `T ≤ Z(N_H(T))`): `H = Q ⋊ T` with `Q` a normal `p`-complement, so the order-`p` subgroups of
   `H` are `T^c`, `c ∈ Q`.
2. For each prime `ℓ ∣ |Q|`, `T` fixes a Sylow `ℓ`-subgroup `Q_ℓ ≤ Q` (action on `Syl_ℓ(Q)`, size
   prime to `p`, `IsPGroup.card_modEq_card_fixedPoints`).
3. For odd `ℓ ≠ r`: `Q_ℓ` is cyclic, `N(Ω₁ Q_ℓ)` is dihedral with rotation part `C(Ω₁ Q_ℓ)`
   (`I`-free: `Submission.Work.L2F`'s `l2torusNorm`-style facts); `T` has odd order, so
   `T ≤ C(Ω₁ Q_ℓ)` and `[T, Q_ℓ] = 1`.  For `ℓ = 2`: if `[T, Q₂] ≠ 1` then `Ω₁(Z(Q₂))` is a
   four-group (else a reflection would force `T ≤ Q₂`).
4. `C_Q(T) ≤ C_E(T)` is cyclic of order `(q ± 1)/2`, prime to `r`, and by 3 it contains a Sylow
   `ℓ`-subgroup of `Q` for every `ℓ ≠ r`; hence `Q = Q_r · C_Q(T)` and `T^Q = T^{Q_r}`.
5. `Q_r ≤ R ∈ Syl_r(E)` and, if `Q_r ≠ 1`, `T ≤ N(R)` (Sylow `r`-subgroups of `L₂(q)` are TI:
   `l2ti`).  `Q_r = 1` gives the uniqueness of `T`.

Available tooling in the workspace: `Submission/Work/L2F/` (the `l2*` Props are cross-area `I`-free
lemmas), `Submission.Work.CORE4.Defs` (`IsFourGroup`, `conjSub`), and Mathlib's Burnside and
Sylow-counting API.  GAP corroboration: `_design_gw/Core27_l2plocal.g` (+ `.out`), all subgroups of
`PSL(2,q)` for `q ∈ {5,…,61,81,121}`, 0 failures (note: the shipped script's filter is the reverse
inclusion, so re-run with `N_H(T) ≤ C_L(T)` — also 0 failures).  Must be sorry-free:
`#print axioms Work.CORE4.L2pLocal` = `[propext, Classical.choice, Quot.sound]`. -/
theorem L2pLocal : Work.GW2.C27.L2pLocalProp := l2p_l2pLocal_of_model

end Work.CORE4
