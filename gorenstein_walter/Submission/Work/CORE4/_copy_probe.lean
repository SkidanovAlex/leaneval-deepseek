import Mathlib
import Submission.Work.LEAD.Core27
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.ProjOfInfBot
import Submission.Work.CORE4.PGroupCentralPrime
import Submission.Work.CORE4.SupProjPrimeOrder

namespace Work.CORE4

open Subgroup

variable {G : Type*}

/-- Decomposition existence in a commuting product. -/
theorem mem_sup_iff_exists_mul [Group G] (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (x : G) :
    x ∈ (P ⊔ E : Subgroup G) ↔ ∃ p ∈ P, ∃ e ∈ E, p * e = x := by
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer (E : Set G)
      (Subgroup.mem_centralizer_iff.mpr (fun b hb => (hcomm a ha b hb).symm))
  constructor
  · intro hx
    have hx' : x ∈ (↑(P ⊔ E) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P E hPE] at hx'
    exact Set.mem_mul.mp hx'
  · rintro ⟨p, hp, e, he, rfl⟩
    exact Subgroup.mul_mem_sup hp he

/-- Uniqueness of the decomposition in a commuting product with trivial intersection. -/
theorem mul_decomp_unique [Group G] (P E : Subgroup G)
    (_hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥)
    {a a' t t' : G} (ha : a ∈ P) (ha' : a' ∈ P) (ht : t ∈ E) (ht' : t' ∈ E)
    (h : a * t = a' * t') : a = a' ∧ t = t' := by
  have h1 : a'⁻¹ * a = t' * t⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * t) * t⁻¹ := by group
      _ = a'⁻¹ * (a' * t') * t⁻¹ := by rw [h]
      _ = t' * t⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ P ⊓ E :=
    ⟨P.mul_mem (P.inv_mem ha') ha, by rw [h1]; exact E.mul_mem ht' (E.inv_mem ht)⟩
  have h1' : a'⁻¹ * a = 1 := by
    have hh := hmem
    rw [hinf, Subgroup.mem_bot] at hh
    exact hh
  constructor
  · have : a = a' := by
      have hh : a' * (a'⁻¹ * a) = a' * 1 := by rw [h1']
      simpa using hh
    exact this
  · have h2 : t' * t⁻¹ = 1 := by rw [← h1, h1']
    have : t' = t := by
      have hh : (t' * t⁻¹) * t = 1 * t := by rw [h2]
      simpa [mul_assoc] using hh
    exact this.symm

/-- Equality criterion for the "diagonal" subgroups `⟨a t⟩`. -/
theorem zpowers_mul_eq_iff [Group G] (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥)
    {a t : G} (ha : a ∈ P) (ht : t ∈ E) {p : ℕ}
    (hord_a : orderOf a = p) (hord_t : orderOf t = p) :
    ∀ s ∈ E, Subgroup.zpowers (a * s) = Subgroup.zpowers (a * t) ↔ s = t := by
  intro s hs
  constructor
  · intro h
    have hmem : a * s ∈ Subgroup.zpowers (a * t) := by
      rw [← h]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hct : Commute a t := hcomm a ha t ht
    have hexp : a ^ k * t ^ k = a * s := by
      rw [← hk, hct.mul_zpow]
    obtain ⟨haeq, hteq⟩ := mul_decomp_unique P E hcomm hinf (P.zpow_mem ha k) ha
      (E.zpow_mem ht k) hs hexp
    have hk1 : a ^ (k - 1) = 1 := by
      rw [zpow_sub, haeq, zpow_one, mul_inv_cancel]
    have hdvd : ((p : ℕ) : ℤ) ∣ (k - 1) := by
      rw [← hord_a]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hk1
    obtain ⟨m, hm⟩ := hdvd
    have hk' : k = (p : ℤ) * m + 1 := by linarith
    have htp : t ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hord_t, pow_orderOf_eq_one]
    have ht' : t ^ k = t := by
      calc t ^ k = t ^ ((p : ℤ) * m + 1) := by rw [hk']
        _ = t ^ ((p : ℤ) * m) * t ^ (1 : ℤ) := zpow_add t _ _
        _ = (t ^ (p : ℤ)) ^ m * t := by rw [zpow_mul, zpow_one]
        _ = 1 ^ m * t := by rw [htp]
        _ = 1 * t := by rw [one_zpow]
        _ = t := one_mul t
    rw [← hteq, ht']
  · rintro rfl; rfl

/-- Cardinality of the image of a subgroup under an injective-on-it homomorphism. -/
theorem card_map_subgroupOf_eq [Group G] {W A : Subgroup G} (hA : A ≤ W) (φ : ↥W →* G)
    (hinj : ∀ x : ↥(A.subgroupOf W), φ x = 1 → x = 1) :
    Nat.card ↥((A.subgroupOf W).map φ) = Nat.card ↥A := by
  have h1 : Nat.card ↥(A.subgroupOf W) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have h2 : Nat.card ↥((A.subgroupOf W).map φ) = Nat.card ↥(A.subgroupOf W) := by
    let f : ↥(A.subgroupOf W) →* ↥((A.subgroupOf W).map φ) :=
      { toFun := fun x => ⟨φ x, Subgroup.mem_map_of_mem φ x.2⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp }
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have h1 : f (x * y⁻¹) = 1 := by
          rw [map_mul, map_inv, hxy, mul_inv_cancel]
        have h2 : φ (x * y⁻¹) = 1 := congrArg Subtype.val h1
        have h3 : x * y⁻¹ = 1 := hinj _ h2
        exact mul_inv_eq_one.mp h3
      · rintro ⟨y, hy⟩
        rw [Subgroup.mem_map] at hy
        obtain ⟨x, hx, hxy⟩ := hy
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact (Nat.card_congr (MulEquiv.ofBijective f hf).toEquiv).symm
  rw [h2, h1]

end Work.CORE4
