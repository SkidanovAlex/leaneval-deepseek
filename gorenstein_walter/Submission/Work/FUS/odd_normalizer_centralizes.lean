import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.DSTR.dihedralSubgroup
import Submission.Work.FUS.AutFacts.mulAut_cyclic_eq_one_of_odd
import Submission.Work.FUS.AutFacts.mulAut_dihedral_eq_one_of_odd
import Submission.Work.FUS.AutFacts.mulAut_fourGroup_eq_one_of_odd

namespace Work.FUS

set_option linter.style.haveILetI false

open Subgroup

/-! ## Arithmetic helper: divisors of odd numbers are odd -/

lemma odd_of_dvd_odd {m d : ℕ} (hm : Odd m) (hd : d ∣ m) : Odd d := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨k, rfl⟩ := hd
  exact (Nat.not_odd_iff_even.mpr (h.mul_right k)) hm

/-! ## The automorphism of a subgroup induced by an element of its normalizer -/

/-- Conjugation by `g`, restricted to a subgroup `H` that `g` normalizes; a `MulAut H`. -/
noncomputable def conjAutSub {G : Type*} [Group G] (g : G) (H : Subgroup G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : MulAut H where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (H : Set G)).inv_mem hg) (x : G)).mp x.2
    simpa using h⟩
  left_inv x := by ext; group
  right_inv x := by ext; group
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group

@[simp] lemma conjAutSub_coe {G : Type*} [Group G] (g : G) (H : Subgroup G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (x : H) :
    ((conjAutSub g H hg x : H) : G) = g * (x : G) * g⁻¹ := rfl

lemma conjAutSub_pow_coe {G : Type*} [Group G] (g : G) (H : Subgroup G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    ∀ (n : ℕ) (x : H),
      (((conjAutSub g H hg) ^ n) x : G) = g ^ n * (x : G) * (g ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      change (((conjAutSub g H hg) ^ n) ((conjAutSub g H hg) x) : G) =
        g ^ (n + 1) * (x : G) * (g ^ (n + 1))⁻¹
      rw [ih ((conjAutSub g H hg) x), conjAutSub_coe, pow_succ']
      group

/-! ## Dihedral groups -/

/-- `DihedralGroup 2` is the Klein four-group: every element is an involution. -/
lemma dihedral_two_sq_eq_one : ∀ w : DihedralGroup 2, w ^ 2 = 1 := by decide

/-- An automorphism of odd order of a dihedral group whose order is a power of two `≥ 8`
is trivial. -/
lemma mulAut_dihedral_pow_two_eq_one_of_odd {m : ℕ} (hm : ∃ j : ℕ, 2 ≤ j ∧ m = 2 ^ j)
    (β : DihedralGroup m ≃* DihedralGroup m) (hodd : Odd (orderOf β)) : β = 1 := by
  obtain ⟨j, hj, rfl⟩ := hm
  exact AutFacts.mulAut_dihedral_eq_one_of_odd j hj β hodd

/-! ## Automorphisms of odd order of a `2`-subgroup of a dihedral group -/

/-- If `H` is a subgroup of a dihedral group that is a `2`-group, `t ∈ H` is a central
involution, and `β` is an automorphism of `H` of odd order fixing `t`, then `β = 1`.

Subgroups of a dihedral group are cyclic or dihedral, so `H` is a `2`-group that is cyclic
(where `Aut` is a `2`-group), a dihedral group of order `≥ 8` (where `Aut` is a `2`-group), or
the Klein four-group (where an odd order automorphism fixing a non-identity point is trivial). -/
lemma aut_eq_one_of_odd_subgroup_dihedral {n : ℕ} (hn : 2 ≤ n)
    (H : Subgroup (DihedralGroup n)) (hH : IsPGroup 2 H)
    (t : H) (ht2 : orderOf t = 2) (htc : ∀ x : H, x * t = t * x)
    (β : H ≃* H) (hβ : β t = t) (hodd : Odd (orderOf β)) : β = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hH
  by_cases hcyc : IsCyclic H
  · exact AutFacts.mulAut_cyclic_eq_one_of_odd hcyc k hk β hodd
  · rcases Work.DSTR.dihedralSubgroup n H with h | ⟨m, ⟨e⟩⟩
    · exact absurd h hcyc
    · have hm_card : 2 * m = 2 ^ k := by
        have h1 : Nat.card H = Nat.card (DihedralGroup m) := Nat.card_congr e.toEquiv
        rw [hk, DihedralGroup.nat_card] at h1
        exact h1.symm
      have hm0 : m ≠ 0 := by
        rintro rfl
        have : 0 < 2 ^ k := pow_pos (by norm_num) k
        omega
      have hm1 : m ≠ 1 := by
        intro hm1
        exact hcyc ((e.isCyclic).mpr ((DihedralGroup.isCyclic_iff (n := m)).mpr hm1))
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0; simp only [pow_zero] at hm_card; omega
        · exact hk0
      have hmpow : m = 2 ^ (k - 1) := by
        have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hk1]
        rw [h2] at hm_card
        exact Nat.mul_left_cancel (by norm_num) hm_card
      rcases lt_or_ge k 3 with hk3 | hk3
      · -- `k ≤ 2`, and `1 ≤ k`, so `k = 2` and `m = 2`: the Klein four-group.
        have hk2 : k = 2 := by
          rcases (show k = 1 ∨ k = 2 by omega) with h | h
          · exfalso
            exact hm1 (by rw [hmpow, h]; norm_num)
          · exact h
        subst hk2
        have hm2 : m = 2 := by rw [hmpow]; norm_num
        subst hm2
        have hcardH : Nat.card H = 4 := by rw [hk]; norm_num
        have hV2 : ∀ v : H, v ^ 2 = 1 := by
          intro v
          apply e.injective
          rw [map_pow, dihedral_two_sq_eq_one (e v), map_one]
        have ht1 : t ≠ 1 := by
          intro h; rw [h, orderOf_one] at ht2; norm_num at ht2
        exact AutFacts.mulAut_fourGroup_eq_one_of_odd hcardH hV2 t ht1 β hβ hodd
      · -- `k ≥ 3`: `m = 2 ^ (k-1)` with `k - 1 ≥ 2`.
        have hβ' : Odd (orderOf (MulAut.congr e β)) := by
          rw [MulEquiv.orderOf_eq]; exact hodd
        have hcongr1 : MulAut.congr e β = 1 :=
          mulAut_dihedral_pow_two_eq_one_of_odd ⟨k - 1, by omega, hmpow⟩
            (MulAut.congr e β) hβ'
        have key : (MulAut.congr e).symm (MulAut.congr e β) = (MulAut.congr e).symm 1 := by
          rw [hcongr1]
        rw [MulEquiv.symm_apply_apply, map_one] at key
        exact key

/-! ## The main lemma -/

theorem odd_normalizer_centralizes {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hn : 2 ≤ n) (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (t : G) (htS : t ∈ (S : Subgroup G)) (ht2 : orderOf t = 2)
    (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x)
    (X : Subgroup G) (hX : IsPGroup 2 X) (hXC : X ≤ Subgroup.centralizer ({t} : Set G))
    (y : G) (hyN : y ∈ Subgroup.normalizer (X : Set G))
    (hyC : y ∈ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf y)) :
    y ∈ Subgroup.centralizer (X : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero n := ⟨by omega⟩
  -- (1) `t` commutes with `X`, hence normalizes `X`.
  have hXt : ∀ x ∈ X, x * t = t * x :=
    fun x hx => (Subgroup.mem_centralizer_iff.mp (hXC hx) t (by simp)).symm
  have htN : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G)
      (Subgroup.mem_centralizer_iff.mpr hXt)
  -- (2) `P := X ⊔ ⟨t⟩` is a `2`-group containing `t`.
  set P : Subgroup G := X ⊔ Subgroup.zpowers t with hPdef
  have ht_memP : t ∈ P := by
    rw [hPdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    exact IsPGroup.to_sup_of_normal_left' hX
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num))
      (Subgroup.zpowers_le.mpr htN)
  -- (3) `t` is central in `P`.
  have hP_le_C : P ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [hPdef]
    exact sup_le hXC (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have htcP : ∀ p : P, p * ⟨t, ht_memP⟩ = ⟨t, ht_memP⟩ * p := by
    intro p
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hP_le_C p.2) t (by simp)).symm
  -- (4) `y` normalizes `P`.
  have hyNP : y ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hPdef, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN]
    suffices h : (Subgroup.zpowers t).map (MulAut.conj y : G →* G) = Subgroup.zpowers t by
      rw [h]
    rw [MonoidHom.map_zpowers]
    congr 1
    change y * t * y⁻¹ = t
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [hyt, mul_assoc, mul_inv_cancel, mul_one]
  -- The automorphism of `P` induced by `y`.
  set β : MulAut P := conjAutSub y P hyNP with hβdef
  have hβt : β ⟨t, ht_memP⟩ = ⟨t, ht_memP⟩ := by
    apply Subtype.ext
    rw [hβdef, conjAutSub_coe]
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [hyt, mul_assoc, mul_inv_cancel, mul_one]
  have hoddβ : Odd (orderOf β) := by
    have hpow : β ^ orderOf y = 1 := by
      apply MulEquiv.ext; intro x
      apply Subtype.ext
      rw [hβdef, conjAutSub_pow_coe, pow_orderOf_eq_one]; simp
    exact odd_of_dvd_odd hodd (orderOf_dvd_of_pow_eq_one hpow)
  -- (5) Embed `P` into a dihedral Sylow subgroup.
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hP2
  obtain ⟨eQS⟩ := (show Nonempty ((Q : Subgroup G) ≃* (S : Subgroup G)) from ⟨Sylow.equiv Q S⟩)
  obtain ⟨eS⟩ := hiso
  set φ : (Q : Subgroup G) ≃* DihedralGroup n := eQS.trans eS with hφdef
  set Pq : Subgroup (Q : Subgroup G) := P.subgroupOf (Q : Subgroup G) with hPqdef
  set H : Subgroup (DihedralGroup n) := Pq.map (φ : (Q : Subgroup G) →* DihedralGroup n) with hHdef
  set ee : P ≃* H :=
    (Subgroup.subgroupOfEquivOfLe hPQ).symm.trans (MulEquiv.subgroupMap φ Pq) with heedef
  have hH2 : IsPGroup 2 H := by
    rw [hHdef]
    exact (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPQ).symm).map
      (φ : (Q : Subgroup G) →* DihedralGroup n)
  set t' : H := ee ⟨t, ht_memP⟩ with ht'def
  have ht'c : ∀ x : H, x * t' = t' * x := by
    intro x
    rw [ht'def, ← MulEquiv.apply_symm_apply ee x, ← map_mul, ← map_mul,
      htcP (ee.symm x)]
  have ht'2 : orderOf t' = 2 := by
    rw [ht'def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ht2
  have hβHt : (MulAut.congr ee β) t' = t' := by
    rw [ht'def, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hβt]
  have hoddH : Odd (orderOf (MulAut.congr ee β)) := by
    rw [MulEquiv.orderOf_eq]; exact hoddβ
  have hβH1 : MulAut.congr ee β = 1 :=
    aut_eq_one_of_odd_subgroup_dihedral hn H hH2 t' ht'2 ht'c (MulAut.congr ee β) hβHt hoddH
  have hβ1 : β = 1 := by
    have key : (MulAut.congr ee).symm (MulAut.congr ee β) = (MulAut.congr ee).symm 1 := by
      rw [hβH1]
    rw [MulEquiv.symm_apply_apply, map_one] at key
    exact key
  -- (6) Conclude `y ∈ C_G(X)`.
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hmemP : h ∈ P := by rw [hPdef]; exact Subgroup.mem_sup_left hh
  have hfix : (β ⟨h, hmemP⟩ : P) = ⟨h, hmemP⟩ := by rw [hβ1]; rfl
  have hval : y * h * y⁻¹ = h := by
    have := congrArg (fun z : P => (z : G)) hfix
    rwa [hβdef, conjAutSub_coe] at this
  show h * y = y * h
  have key : y * h = h * y := by
    calc y * h = (y * h * y⁻¹) * y := by group
      _ = h * y := by rw [hval]
  exact key.symm

end Work.FUS
