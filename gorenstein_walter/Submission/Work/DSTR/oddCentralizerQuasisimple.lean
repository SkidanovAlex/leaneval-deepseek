import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.layerUnique

/-! GW design 25, part B: in a group with dihedral-or-cyclic Sylow 2-subgroups, the centralizer of
a quasisimple subgroup `E` has odd order (given DS4 `QuasisimpleSylowProp` and DS6
`QuasisimpleCenterOddProp`).  This supplies `Odd (Nat.card N)` at the `d110ii` call site
(`N = C_X(E).subgroupOf Y`). -/

namespace Work.DSTR

open Subgroup DihedralGroup

/-- In a dihedral 2-group, an involution centralizing a noncyclic subgroup `A` lies in `A`. -/
lemma mem_of_involution_centralizes_noncyclic {n : ℕ} (hn : n ≠ 0)
    (h2 : IsPGroup 2 (DihedralGroup n)) (A : Subgroup (DihedralGroup n)) (hnc : ¬ IsCyclic A)
    (s : DihedralGroup n) (hs : orderOf s = 2)
    (hsc : s ∈ Subgroup.centralizer (A : Set (DihedralGroup n))) : s ∈ A := by
  have : NeZero n := ⟨hn⟩
  by_cases hcase : ∃ i : ZMod n, (r i : DihedralGroup n) ∈ A ∧ 2 * i ≠ 0
  · obtain ⟨i, hiA, h2i⟩ := hcase
    -- `s` commutes with `r i`, so `s = r j` is a rotation
    have hsri : s ∈ Subgroup.centralizer ({r i} : Set (DihedralGroup n)) := by
      rw [Subgroup.mem_centralizer_iff] at hsc ⊢
      intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact hsc _ hiA
    obtain ⟨j, rfl⟩ := Work.Dihedral.mem_rot.mp (Work.DSTR.centralizer_r_le_rot i h2i hsri)
    have hj0 : j ≠ 0 := by
      rintro rfl; rw [r_zero, orderOf_one] at hs; exact absurd hs (by norm_num)
    have h2j : 2 * j = 0 := by
      have h := pow_orderOf_eq_one (r j : DihedralGroup n)
      rw [hs, pow_two, r_mul_r, ← r_zero] at h
      rw [two_mul]; exact r.inj h
    have hjh : j = ((n / 2 : ℕ) : ZMod n) :=
      (Work.DSTR.zmod_two_mul_eq_zero n j h2j).resolve_left hj0
    -- an involution in `⟨r i⟩ ≤ A`
    have hri1 : (r i : DihedralGroup n) ≠ 1 := by
      intro h; apply h2i; rw [← r_zero] at h; rw [r.inj h, mul_zero]
    obtain ⟨m, hm⟩ := h2 (r i)
    have hm0 : m ≠ 0 := by rintro rfl; exact hri1 (by simpa using hm)
    have hdvd : 2 ∣ Nat.card (Subgroup.zpowers (r i : DihedralGroup n)) := by
      rw [Nat.card_zpowers]
      have h' : orderOf (r i : DihedralGroup n) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
      obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h'
      have he0 : e ≠ 0 := by
        rintro rfl; rw [pow_zero, orderOf_eq_one_iff] at he; exact hri1 he
      rw [he]; exact dvd_pow_self 2 he0
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hwA : (w : DihedralGroup n) ∈ A :=
      (Subgroup.zpowers_le.mpr hiA) w.2
    have hwrot : (w : DihedralGroup n) ∈ Work.Dihedral.rot n :=
      (Subgroup.zpowers_le.mpr (Work.Dihedral.mem_rot.mpr ⟨i, rfl⟩)) w.2
    obtain ⟨k, hk⟩ := Work.Dihedral.mem_rot.mp hwrot
    have hw2 : orderOf (r k : DihedralGroup n) = 2 := by
      rw [← hk, Subgroup.orderOf_coe, hw]
    have hk0 : k ≠ 0 := by
      rintro rfl; rw [r_zero, orderOf_one] at hw2; exact absurd hw2 (by norm_num)
    have h2k : 2 * k = 0 := by
      have h := pow_orderOf_eq_one (r k : DihedralGroup n)
      rw [hw2, pow_two, r_mul_r, ← r_zero] at h
      rw [two_mul]; exact r.inj h
    have hkh : k = ((n / 2 : ℕ) : ZMod n) :=
      (Work.DSTR.zmod_two_mul_eq_zero n k h2k).resolve_left hk0
    rw [hjh, ← hkh, ← hk]; exact hwA
  · push Not at hcase
    exact Work.DSTR.centralizer_le_self_of_no_rot hn A hnc hcase hsc

/-- **`C_X(E)` is odd.** -/
theorem odd_card_centralizer_of_quasisimple (h4 : Work.GW2.QuasisimpleSylowProp)
    (h6 : Work.GW2.QuasisimpleCenterOddProp)
    {X : Type} [Group X] [Finite X] (hFT : Work.GW2.FeitThompsonProp)
    (hD : Work.GW2.DihOrCycSylow X) (E : Subgroup X) (hQ : Work.GW2.IsQuasisimple E) :
    Odd (Nat.card (Subgroup.centralizer (E : Set X))) := by
  set C := Subgroup.centralizer (E : Set X) with hC
  apply Nat.not_even_iff_odd.mp
  intro hev
  obtain ⟨s', hs'⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  set s : X := (s' : X) with hsdef
  have hs2 : orderOf s = 2 := by rw [hsdef, Subgroup.orderOf_coe, hs']
  have hsC : s ∈ C := s'.2
  have hsE : ∀ x ∈ E, x * s = s * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hsC x hx)
  -- Sylow 2-subgroup of `E`, noncyclic
  obtain ⟨A⟩ := Sylow.nonempty (p := 2) (G := ↥E)
  have hAnc : ¬ IsCyclic ↥(A : Subgroup ↥E) := h4 X hFT E hQ A
  set A' : Subgroup X := (A : Subgroup ↥E).map E.subtype with hA'def
  have hA'le : A' ≤ E := Subgroup.map_subtype_le _
  have hA'p : IsPGroup 2 ↥A' := (A.isPGroup').map E.subtype
  have hA'nc : ¬ IsCyclic ↥A' := fun hcyc => hAnc
    ((Subgroup.equivMapOfInjective (A : Subgroup ↥E) E.subtype
      Subtype.coe_injective).isCyclic.mpr hcyc)
  set B' : Subgroup X := Subgroup.zpowers s with hB'def
  have hB'p : IsPGroup 2 ↥B' := by
    exact IsPGroup.of_card (n := 1) (by rw [hB'def, Nat.card_zpowers, hs2, pow_one])
  have hnorm : A' ≤ Subgroup.normalizer (B' : Set X) := by
    have hcen : A' ≤ Subgroup.centralizer (B' : Set X) := by
      rw [hB'def, Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a ha; exact (hsE a (hA'le ha))
    exact hcen.trans (Subgroup.centralizer_le_normalizer (B' : Set X))
  have hSp : IsPGroup 2 ↥(A' ⊔ B') := IsPGroup.to_sup_of_normal_right' hA'p hB'p hnorm
  obtain ⟨P, hSP⟩ := IsPGroup.exists_le_sylow hSp
  have hA'P : A' ≤ (P : Subgroup X) := le_trans le_sup_left hSP
  have hsP : s ∈ (P : Subgroup X) := hSP (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  -- `s ∈ A'`
  have hsA' : s ∈ A' := by
    rcases hD P with hPcyc | ⟨n, ⟨e⟩⟩
    · haveI : IsCyclic ↥(P : Subgroup X) := hPcyc
      exact absurd (isCyclic_of_injective (Subgroup.inclusion hA'P)
        (Subgroup.inclusion_injective hA'P)) hA'nc
    · have hn0 : n ≠ 0 := by
        intro hn
        have h1 : Nat.card ↥(P : Subgroup X) = 0 := by
          rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn, mul_zero]
        have h2 : 0 < Nat.card ↥(P : Subgroup X) := Nat.card_pos
        omega
      have hDp : IsPGroup 2 (DihedralGroup n) :=
        (P.isPGroup').of_surjective e.toMonoidHom e.surjective
      set A₁ : Subgroup (DihedralGroup n) :=
        (A'.subgroupOf (P : Subgroup X)).map e.toMonoidHom with hA₁def
      have eA : ↥A' ≃* ↥A₁ :=
        (Subgroup.subgroupOfEquivOfLe hA'P).symm.trans
          (Subgroup.equivMapOfInjective (A'.subgroupOf (P : Subgroup X)) e.toMonoidHom e.injective)
      have hA₁nc : ¬ IsCyclic ↥A₁ := fun hc => hA'nc (eA.isCyclic.mpr hc)
      set s₁ : DihedralGroup n := e ⟨s, hsP⟩ with hs₁
      have hs₁2 : orderOf s₁ = 2 := by
        rw [hs₁, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hs2]
      have hs₁c : s₁ ∈ Subgroup.centralizer (A₁ : Set (DihedralGroup n)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        rw [Subgroup.mem_subgroupOf] at hx
        have hxy : x * ⟨s, hsP⟩ = ⟨s, hsP⟩ * x := Subtype.ext (hsE (x : X) (hA'le hx))
        rw [hs₁]; show e x * e ⟨s, hsP⟩ = e ⟨s, hsP⟩ * e x
        rw [← map_mul, ← map_mul, hxy]
      have hmem := mem_of_involution_centralizes_noncyclic hn0 hDp A₁ hA₁nc s₁ hs₁2 hs₁c
      obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hmem
      rw [Subgroup.mem_subgroupOf] at hx
      have : x = ⟨s, hsP⟩ := e.injective hxe
      rw [this] at hx; exact hx
  -- `s ∈ E ⊓ C_X(E) = Z(E)`, contradicting `h6`
  have hsE' : s ∈ E := hA'le hsA'
  set z : ↥E := ⟨s, hsE'⟩ with hz
  have hzc : z ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]; intro g
    exact Subtype.ext (hsE (g : X) g.2)
  have hz2 : orderOf (⟨z, hzc⟩ : Subgroup.center ↥E) = 2 := by
    rw [Subgroup.orderOf_mk, hz, Subgroup.orderOf_mk, hs2]
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥E) := hz2 ▸ orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.mpr (h6 X hD E hQ)) (even_iff_two_dvd.mpr hdvd)

end Work.DSTR
