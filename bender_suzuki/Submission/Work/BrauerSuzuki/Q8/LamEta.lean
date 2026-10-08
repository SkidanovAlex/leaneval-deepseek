import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.CharCore.exists_irr_of_monoidHom
import Submission.Work.CharCore.linear_char_iff_deg_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The linear character `λ` of `C*` with kernel `T · H*`

Glauberman (1974), §3 (`REFS/brauer_suzuki.md`), introduces the unique linear character `λ`
of `C* = C_G(X)` with kernel `T H*` (the quotient `C*/(T H*)` has order `2`).  Here `λ` is
the function `Work.BrauerSuzuki.Q8.lamFun x : ↥(Cstar x) → ℂ` which is `1` on `T H*` and
`-1` off it.

This file proves that `lamFun` is multiplicative (so that it is a linear character, hence
irreducible), that it is a class function (automatic for a homomorphism to the abelian group
`ℂˣ`), and records the values `λ = 1` on `T H*` and `λ = -1` on `A*`.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G] [Finite G]

/-- In a group of order `2`, any two elements different from `1` are equal. -/
theorem eq_of_ne_one_of_card_eq_two {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 2) {a b : Q} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  letI : Fintype Q := Fintype.ofFinite Q
  have hQ' : Fintype.card Q = 2 := by rw [← Nat.card_eq_fintype_card]; exact hQ
  have hsub : ({1, a} : Finset Q) ⊆ Finset.univ := Finset.subset_univ _
  have hcard : ({1, a} : Finset Q).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using (Ne.symm ha : (1 : Q) ≠ a)),
      Finset.card_singleton]
  have huniv : ({1, a} : Finset Q) = Finset.univ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_univ, hQ', hcard])
  have hb' : b ∈ ({1, a} : Finset Q) := by rw [huniv]; exact Finset.mem_univ b
  rw [Finset.mem_insert, Finset.mem_singleton] at hb'
  exact (hb'.resolve_left hb).symm

namespace Ctx

variable {x : G} {S : Sylow 2 G}

/-- `x` is central in `C* = C_G(⟨x⟩)`, so every element of `T = ⟨x²⟩` is central in `C*`. -/
theorem T_central (h : Ctx G x S) {y : G} (hy : y ∈ T x) (c : ↥(Cstar x)) :
    (c : G) * y * (c : G)⁻¹ = y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.T_le_X hy)
  have hcx : x * (c : G) = (c : G) * x :=
    (Subgroup.mem_centralizer_iff.mp c.2) x (Subgroup.mem_zpowers x)
  have hconj : (c : G) * x * (c : G)⁻¹ = x := by
    rw [← hcx, mul_assoc, mul_inv_cancel, mul_one]
  calc (c : G) * y * (c : G)⁻¹ = (c : G) * x ^ k * (c : G)⁻¹ := by rw [← hk]
    _ = ((c : G) * x * (c : G)⁻¹) ^ k := by rw [← conj_zpow]
    _ = x ^ k := by rw [hconj]
    _ = y := by rw [hk]

theorem THstar_le_Cstar (h : Ctx G x S) : T x ⊔ Hstar x ≤ Cstar x := by
  rw [← h.supC]
  exact sup_le (le_trans h.T_le_X le_sup_left) le_sup_right

/-- `T · H* = T ⊔ H*` is normal in `C*`. -/
theorem THstar_subgroupOf_normal (h : Ctx G x S) :
    ((T x ⊔ Hstar x).subgroupOf (Cstar x)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer h.THstar_le_Cstar,
    Subgroup.le_normalizer_iff]
  intro c hc m hm
  rw [Subgroup.sup_eq_closure] at hm ⊢
  have key : ∀ y ∈ Subgroup.closure ((T x : Set G) ∪ (Hstar x : Set G)),
      (c : G) * y * (c : G)⁻¹ ∈ Subgroup.closure ((T x : Set G) ∪ (Hstar x : Set G)) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with hz | hz
        · have h1 : (c : G) * z * (c : G)⁻¹ = z := h.T_central hz ⟨c, hc⟩
          rw [h1]
          exact Subgroup.subset_closure (Or.inl hz)
        · exact Subgroup.subset_closure (Or.inr (h.Hstar_conj hc hz))
    | one => simp
    | mul a b ha hb iha ihb =>
        rw [show (c : G) * (a * b) * (c : G)⁻¹ =
          ((c : G) * a * (c : G)⁻¹) * ((c : G) * b * (c : G)⁻¹) from by group]
        exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
        rw [show (c : G) * a⁻¹ * (c : G)⁻¹ = ((c : G) * a * (c : G)⁻¹)⁻¹ from by group]
        exact Subgroup.inv_mem _ iha
  exact key m hm

/-- The index of `T · H*` in `C*` is `2`. -/
theorem THstar_index_two (h : Ctx G x S) :
    ((T x ⊔ Hstar x).subgroupOf (Cstar x)).index = 2 := by
  have hle := h.THstar_le_Cstar
  have h1 : Nat.card ↥((T x ⊔ Hstar x).subgroupOf (Cstar x)) =
      Nat.card ↥(T x ⊔ Hstar x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 := Subgroup.card_mul_index ((T x ⊔ Hstar x).subgroupOf (Cstar x))
  rw [h1, h.card_T_sup_Hstar, h.card_Cstar] at h2
  have hH0 : Nat.card ↥(Hstar x) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, (Hstar x).one_mem⟩, inferInstance⟩
  have h3 : 2 * Nat.card ↥(Hstar x) * ((T x ⊔ Hstar x).subgroupOf (Cstar x)).index =
      2 * Nat.card ↥(Hstar x) * 2 := by
    rw [h2]; ring
  exact Nat.mul_left_cancel (Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hH0)) h3

theorem lamFun_eq_one_iff (h : Ctx G x S) (y : ↥(Cstar x)) :
    lamFun x y = 1 ↔ (y : G) ∈ (T x : Set G) * (Hstar x : Set G) := by
  have hd : lamFun x y = if (y : G) ∈ (T x : Set G) * (Hstar x : Set G) then (1 : ℂ) else -1 :=
    rfl
  rw [hd]
  by_cases hy : (y : G) ∈ (T x : Set G) * (Hstar x : Set G)
  · rw [if_pos hy]; exact ⟨fun _ => hy, fun _ => rfl⟩
  · rw [if_neg hy]
    exact ⟨fun hh => absurd hh (by norm_num), fun hh => absurd hh hy⟩

theorem lamFun_eq_neg_one_iff (h : Ctx G x S) (y : ↥(Cstar x)) :
    lamFun x y = -1 ↔ (y : G) ∉ (T x : Set G) * (Hstar x : Set G) := by
  have hd : lamFun x y = if (y : G) ∈ (T x : Set G) * (Hstar x : Set G) then (1 : ℂ) else -1 :=
    rfl
  rw [hd]
  by_cases hy : (y : G) ∈ (T x : Set G) * (Hstar x : Set G)
  · rw [if_pos hy]
    exact ⟨fun hh => absurd hh (by norm_num), fun hh => absurd hy hh⟩
  · rw [if_neg hy]
    exact ⟨fun _ => hy, fun _ => rfl⟩

theorem lamFun_one (h : Ctx G x S) : lamFun x 1 = 1 := by
  rw [h.lamFun_eq_one_iff]
  exact ⟨1, (T x).one_mem, 1, (Hstar x).one_mem, mul_one 1⟩

theorem lamFun_ne_zero (h : Ctx G x S) (y : ↥(Cstar x)) : lamFun x y ≠ 0 := by
  rw [lamFun]
  split <;> norm_num

/-- `λ` is multiplicative: `C*/(T H*)` has order `2`, so two elements of `C*` lie in the same
coset of `T H*` exactly when their product does. -/
theorem lamFun_mul (h : Ctx G x S) (y z : ↥(Cstar x)) :
    lamFun x (y * z) = lamFun x y * lamFun x z := by
  haveI hnorm := h.THstar_subgroupOf_normal
  set K : Subgroup ↥(Cstar x) := (T x ⊔ Hstar x).subgroupOf (Cstar x) with hK
  have hkerK : ∀ w : ↥(Cstar x), QuotientGroup.mk' K w = 1 ↔
      (w : G) ∈ (T x : Set G) * (Hstar x : Set G) := by
    intro w
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', hK, Subgroup.mem_subgroupOf,
      ← SetLike.mem_coe, h.coe_T_mul_Hstar]
  have hcardQ : Nat.card (↥(Cstar x) ⧸ K) = 2 := by
    rw [← Subgroup.index_eq_card]; exact h.THstar_index_two
  have hsq : ∀ w : ↥(Cstar x), QuotientGroup.mk' K w * QuotientGroup.mk' K w = 1 := by
    intro w
    have hdvd : orderOf (QuotientGroup.mk' K w) ∣ 2 := by
      rw [← hcardQ]; exact orderOf_dvd_natCard _
    have h1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    rwa [pow_two] at h1
  have hcoeyz : ((y * z : ↥(Cstar x)) : G) = (y : G) * (z : G) := Subgroup.coe_mul (Cstar x) y z
  by_cases hy : (y : G) ∈ (T x : Set G) * (Hstar x : Set G)
  · by_cases hz : (z : G) ∈ (T x : Set G) * (Hstar x : Set G)
    · have hyz : ((y * z : ↥(Cstar x)) : G) ∈ (T x : Set G) * (Hstar x : Set G) := by
        rw [hcoeyz]
        have hy' : (y : G) ∈ (T x ⊔ Hstar x : Subgroup G) := by
          rw [← SetLike.mem_coe, ← h.coe_T_mul_Hstar]; exact hy
        have hz' : (z : G) ∈ (T x ⊔ Hstar x : Subgroup G) := by
          rw [← SetLike.mem_coe, ← h.coe_T_mul_Hstar]; exact hz
        have hmem := (T x ⊔ Hstar x).mul_mem hy' hz'
        rwa [h.coe_T_mul_Hstar]
      rw [(h.lamFun_eq_one_iff (y * z)).mpr hyz, (h.lamFun_eq_one_iff y).mpr hy,
        (h.lamFun_eq_one_iff z).mpr hz]
      ring
    · have hyz : ((y * z : ↥(Cstar x)) : G) ∉ (T x : Set G) * (Hstar x : Set G) := by
        intro hcon
        have hqy : QuotientGroup.mk' K y = 1 := (hkerK y).mpr hy
        have h1 : QuotientGroup.mk' K (y * z) = 1 := (hkerK (y * z)).mpr hcon
        rw [map_mul, hqy, one_mul] at h1
        exact hz ((hkerK z).mp h1)
      rw [(h.lamFun_eq_neg_one_iff (y * z)).mpr hyz, (h.lamFun_eq_one_iff y).mpr hy,
        (h.lamFun_eq_neg_one_iff z).mpr hz]
      norm_num
  · by_cases hz : (z : G) ∈ (T x : Set G) * (Hstar x : Set G)
    · have hyz : ((y * z : ↥(Cstar x)) : G) ∉ (T x : Set G) * (Hstar x : Set G) := by
        intro hcon
        have hqz : QuotientGroup.mk' K z = 1 := (hkerK z).mpr hz
        have h1 : QuotientGroup.mk' K (y * z) = 1 := (hkerK (y * z)).mpr hcon
        rw [map_mul, hqz, mul_one] at h1
        exact hy ((hkerK y).mp h1)
      rw [(h.lamFun_eq_neg_one_iff (y * z)).mpr hyz, (h.lamFun_eq_neg_one_iff y).mpr hy,
        (h.lamFun_eq_one_iff z).mpr hz]
      norm_num
    · have hyz : ((y * z : ↥(Cstar x)) : G) ∈ (T x : Set G) * (Hstar x : Set G) := by
        have hqy : QuotientGroup.mk' K y ≠ 1 := fun hc => hy ((hkerK y).mp hc)
        have hqz : QuotientGroup.mk' K z ≠ 1 := fun hc => hz ((hkerK z).mp hc)
        have heq : QuotientGroup.mk' K y = QuotientGroup.mk' K z :=
          eq_of_ne_one_of_card_eq_two hcardQ hqy hqz
        have h1 : QuotientGroup.mk' K (y * z) = 1 := by
          rw [map_mul, heq, hsq z]
        exact (hkerK (y * z)).mp h1
      rw [(h.lamFun_eq_one_iff (y * z)).mpr hyz, (h.lamFun_eq_neg_one_iff y).mpr hy,
        (h.lamFun_eq_neg_one_iff z).mpr hz]
      norm_num

/-- `λ` as a `ℂˣ`-valued multiplicative character of `C*`. -/
noncomputable def lamHom (h : Ctx G x S) : ↥(Cstar x) →* ℂˣ where
  toFun y := Units.mk0 (lamFun x y) (h.lamFun_ne_zero y)
  map_one' := Units.ext (by rw [Units.val_mk0, h.lamFun_one, Units.val_one])
  map_mul' y z := Units.ext (by
    rw [Units.val_mk0, h.lamFun_mul y z, Units.val_mul, Units.val_mk0, Units.val_mk0])

theorem lamHom_coe (h : Ctx G x S) (y : ↥(Cstar x)) : ((h.lamHom y : ℂˣ) : ℂ) = lamFun x y :=
  Units.val_mk0 (h.lamFun_ne_zero y)

theorem lamFun_mem_Irr (h : Ctx G x S) [Fintype G] :
    lamFun x ∈ Work.CharCore.Irr ↥(Cstar x) := by
  obtain ⟨χ, hχ, hχeq⟩ := Work.CharCore.exists_irr_of_monoidHom h.lamHom
  have hχ' : χ = lamFun x := funext fun y => by rw [hχeq y]; exact h.lamHom_coe y
  rwa [hχ'] at hχ

/-- `λ` is a class function on `C*`: it takes values in the abelian group `ℂˣ`. -/
theorem isClassFun_lamFun (h : Ctx G x S) : Work.CharCore.IsClassFun (lamFun x) := by
  intro y z
  rw [← h.lamHom_coe (z * y * z⁻¹), ← h.lamHom_coe y]
  congr 1
  show h.lamHom (z * y * z⁻¹) = h.lamHom y
  rw [map_mul, map_mul, map_inv]
  rw [mul_assoc, mul_comm (h.lamHom y), ← mul_assoc, mul_inv_cancel, one_mul]

/-- `T` is normalized by `N*` (conjugation by `N*` preserves `⟨x⟩`, hence `⟨x²⟩`). -/
theorem T_conj_Nstar (h : Ctx G x S) {n y : G} (hn : n ∈ Nstar x) (hy : y ∈ T x) :
    n * y * n⁻¹ ∈ T x := by
  have hx2 : orderOf (x ^ 2) = 2 := by
    rw [← Nat.card_zpowers]; exact h.T_card
  rw [T] at hy ⊢
  rw [Nstar, Subgroup.mem_normalizer_iff] at hn
  have h1 : n * x * n⁻¹ ∈ Subgroup.zpowers x := (hn x).mp (Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  obtain ⟨i, _hi, hik⟩ := aux_zpow_mod (by norm_num) h.hx4 k
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨j, _hj, hjt⟩ := aux_zpow_mod (by norm_num) hx2 t
  rw [← ht, hjt]
  have h3 : n * x * n⁻¹ = x ^ i := by rw [← hik, hk]
  have h4 : n * x ^ 2 * n⁻¹ = (n * x * n⁻¹) ^ 2 := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have h5 : n * (x ^ 2) ^ j * n⁻¹ = (n * x ^ 2 * n⁻¹) ^ j := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have h6 : ((x ^ i) ^ 2) ^ j = (x ^ 2) ^ (i * j) := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h5, h4, h3, h6]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (x ^ 2)) (i * j)

/-- `T ⊔ H*` is normal in `N*`. -/
theorem THstar_normal_Nstar (h : Ctx G x S) {n m : G} (hn : n ∈ Nstar x)
    (hm : m ∈ T x ⊔ Hstar x) : n * m * n⁻¹ ∈ T x ⊔ Hstar x := by
  rw [Subgroup.sup_eq_closure] at hm ⊢
  have key : ∀ y ∈ Subgroup.closure ((T x : Set G) ∪ (Hstar x : Set G)),
      n * y * n⁻¹ ∈ Subgroup.closure ((T x : Set G) ∪ (Hstar x : Set G)) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with hz | hz
        · exact Subgroup.subset_closure (Or.inl (h.T_conj_Nstar hn hz))
        · exact Subgroup.subset_closure (Or.inr (h.Hstar_conj_Nstar hn hz))
    | one => simp
    | mul a b ha hb iha ihb =>
        rw [show n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) from by group]
        exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
        rw [show n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ from by group]
        exact Subgroup.inv_mem _ iha
  exact key m hm

/-- `λ` is invariant under conjugation by `N*`. -/
theorem lamFun_conj_Nstar (h : Ctx G x S) {n : G} (hn : n ∈ Nstar x) (y : ↥(Cstar x)) :
    lamFun x ⟨n * (y : G) * n⁻¹, h.Cstar_conj_Nstar hn y.2⟩ = lamFun x y := by
  have hnorm : n ∈ Subgroup.normalizer ↑(T x ⊔ Hstar x) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    exact ⟨fun hm => h.THstar_normal_Nstar hn hm, fun hm => by
      have h1 := h.THstar_normal_Nstar ((Nstar x).inv_mem hn) hm
      have h2 : n⁻¹ * (n * m * n⁻¹) * (n⁻¹)⁻¹ = m := by group
      rwa [h2] at h1⟩
  have hconv : ∀ z : G, z ∈ (T x : Set G) * (Hstar x : Set G) ↔ z ∈ (T x ⊔ Hstar x) := by
    intro z
    rw [h.coe_T_mul_Hstar]
    exact SetLike.mem_coe
  have hmem : n * (y : G) * n⁻¹ ∈ (T x : Set G) * (Hstar x : Set G) ↔
      (y : G) ∈ (T x : Set G) * (Hstar x : Set G) :=
    (hconv _).trans ((Subgroup.mem_normalizer_iff.mp hnorm y).symm.trans (hconv _).symm)
  by_cases hy : (y : G) ∈ (T x : Set G) * (Hstar x : Set G)
  · rw [(h.lamFun_eq_one_iff _).mpr (hmem.mpr hy), (h.lamFun_eq_one_iff y).mpr hy]
  · rw [(h.lamFun_eq_neg_one_iff _).mpr (fun hc => hy (hmem.mp hc)),
      (h.lamFun_eq_neg_one_iff y).mpr hy]

end Ctx

end Work.BrauerSuzuki.Q8
