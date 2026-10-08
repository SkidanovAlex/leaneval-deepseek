import Submission.Work.FeitSibley.CharQ.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley`: the direct factors `S`, `Q₁` are normal in `H`

Since `|S|` and `|Q₁|` are coprime, an element `x = a * b` of the direct product `Q = S × Q₁`
satisfies `orderOf x = orderOf a * orderOf b`; hence

`x ∈ S ↔ x ∈ Q ∧ orderOf x ∣ |S|`  and  `x ∈ Q₁ ↔ x ∈ Q ∧ orderOf x ∣ |Q₁|`.

Conjugation by an element of `H` is an automorphism of `Q` preserving orders, so it preserves `S`
and `Q₁`; thus `S ⊴ H`, `Q₁ ⊴ H`, and also `Z(Q₁) ⊴ H`.  These are the facts that make
`S × Q₁` a decomposition into `H`-invariant pieces (in particular `Q₁D` is a Frobenius group).
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.FeitSibley

variable {G : Type} [Group G] [Fintype G]

namespace FSData

variable (h : FSData G)

theorem S_eq_order_dvd {x : G} : x ∈ h.S ↔ x ∈ h.Q ∧ orderOf x ∣ Nat.card h.S := by
  constructor
  · intro hx
    exact ⟨h.S_le_Q hx, Subgroup.orderOf_dvd_natCard h.S hx⟩
  · rintro ⟨hxQ, hxS⟩
    obtain ⟨a, ha, b, hb, hab⟩ := h.mem_Q_decomp hxQ
    subst hab
    have hcomm : Commute a b := h.commute a ha b hb
    have hpow : (a * b) ^ Nat.card h.S = 1 := orderOf_dvd_iff_pow_eq_one.mp hxS
    have hsplit : a ^ Nat.card h.S * b ^ Nat.card h.S = 1 := by
      rw [← hcomm.mul_pow]; exact hpow
    have hbS : b ^ Nat.card h.S ∈ h.S := by
      have h1 : b ^ Nat.card h.S = (a ^ Nat.card h.S)⁻¹ := mul_eq_one_iff_eq_inv'.mp hsplit
      rw [h1]
      exact inv_mem (pow_mem ha _)
    have hb1 : b ^ Nat.card h.S = 1 := by
      have : b ^ Nat.card h.S ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨hbS, pow_mem hb _⟩
      rw [h.S_inf_Q1] at this
      simpa using this
    have hbdvd : orderOf b ∣ 1 := by
      rw [← h.coprime_S_Q1]
      exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hb1)
        (Subgroup.orderOf_dvd_natCard h.Q1 hb)
    have hb1' : b = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hbdvd)
    rw [hb1', mul_one]
    exact ha

theorem Q1_eq_order_dvd {x : G} : x ∈ h.Q1 ↔ x ∈ h.Q ∧ orderOf x ∣ Nat.card h.Q1 := by
  constructor
  · intro hx
    exact ⟨h.Q1_le_Q hx, Subgroup.orderOf_dvd_natCard h.Q1 hx⟩
  · rintro ⟨hxQ, hxS⟩
    obtain ⟨a, ha, b, hb, hab⟩ := h.mem_Q_decomp hxQ
    subst hab
    have hcomm : Commute a b := h.commute a ha b hb
    have hpow : (a * b) ^ Nat.card h.Q1 = 1 := orderOf_dvd_iff_pow_eq_one.mp hxS
    have hsplit : a ^ Nat.card h.Q1 * b ^ Nat.card h.Q1 = 1 := by
      rw [← hcomm.mul_pow]; exact hpow
    have haQ1 : a ^ Nat.card h.Q1 ∈ h.Q1 := by
      have h1 : a ^ Nat.card h.Q1 = (b ^ Nat.card h.Q1)⁻¹ := mul_eq_one_iff_eq_inv.mp hsplit
      rw [h1]
      exact inv_mem (pow_mem hb _)
    have ha1 : a ^ Nat.card h.Q1 = 1 := by
      have : a ^ Nat.card h.Q1 ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨pow_mem ha _, haQ1⟩
      rw [h.S_inf_Q1] at this
      simpa using this
    have hadvd : orderOf a ∣ 1 := by
      rw [← h.coprime_S_Q1]
      exact Nat.dvd_gcd (Subgroup.orderOf_dvd_natCard h.S ha)
        (orderOf_dvd_iff_pow_eq_one.mpr ha1)
    have ha1' : a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hadvd)
    rw [ha1', one_mul]
    exact hb

theorem S_normal_in_H : h.H ≤ Subgroup.normalizer (h.S : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hyQ : y ∈ Subgroup.normalizer (h.Q : Set G) := h.Q_normal_in_H hy
  have hord : orderOf (y * x * y⁻¹) = orderOf x := MulEquiv.orderOf_eq (MulAut.conj y) x
  constructor
  · intro hx
    rw [h.S_eq_order_dvd]
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyQ x).mp (h.S_le_Q hx),
      by rw [hord]; exact (h.S_eq_order_dvd.mp hx).2⟩
  · intro hx
    have hxQ : y * x * y⁻¹ ∈ h.Q := (h.S_eq_order_dvd.mp hx).1
    have hx' : x ∈ h.Q := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hyQ) (y * x * y⁻¹)).mp hxQ
      have h3 : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [h3] at h2
    rw [h.S_eq_order_dvd]
    exact ⟨hx', by rw [← hord]; exact (h.S_eq_order_dvd.mp hx).2⟩

theorem Q1_normal_in_H : h.H ≤ Subgroup.normalizer (h.Q1 : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hyQ : y ∈ Subgroup.normalizer (h.Q : Set G) := h.Q_normal_in_H hy
  have hord : orderOf (y * x * y⁻¹) = orderOf x := MulEquiv.orderOf_eq (MulAut.conj y) x
  constructor
  · intro hx
    rw [h.Q1_eq_order_dvd]
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyQ x).mp (h.Q1_le_Q hx),
      by rw [hord]; exact (h.Q1_eq_order_dvd.mp hx).2⟩
  · intro hx
    have hxQ : y * x * y⁻¹ ∈ h.Q := (h.Q1_eq_order_dvd.mp hx).1
    have hx' : x ∈ h.Q := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hyQ) (y * x * y⁻¹)).mp hxQ
      have h3 : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [h3] at h2
    rw [h.Q1_eq_order_dvd]
    exact ⟨hx', by rw [← hord]; exact (h.Q1_eq_order_dvd.mp hx).2⟩

/-- The centre of `Q₁`, viewed as a subgroup of `G`. -/
noncomputable def centerQ1 : Subgroup G := (Subgroup.center ↥h.Q1).map h.Q1.subtype

theorem mem_centerQ1 {x : G} :
    x ∈ h.centerQ1 ↔ x ∈ h.Q1 ∧ ∀ y ∈ h.Q1, x * y = y * x := by
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    subst hzx
    refine ⟨z.2, fun y hy => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : ↥h.Q1))).symm
  · rintro ⟨hxQ, hxcent⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (by simpa using (hxcent (y : G) y.2).symm)

theorem centerQ1_le_Q1 : h.centerQ1 ≤ h.Q1 := fun x hx => (h.mem_centerQ1.mp hx).1

theorem centerQ1_normal_in_H : h.H ≤ Subgroup.normalizer (h.centerQ1 : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxQ1, hxcent⟩ := h.mem_centerQ1.mp hx
    have hyQ1 : y ∈ Subgroup.normalizer (h.Q1 : Set G) := h.Q1_normal_in_H hy
    have hyx : y * x * y⁻¹ ∈ h.Q1 := (Subgroup.mem_normalizer_iff.mp hyQ1 x).mp hxQ1
    refine h.mem_centerQ1.mpr ⟨hyx, fun z hz => ?_⟩
    have hz' : y⁻¹ * z * y ∈ h.Q1 := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hyQ1) z).mp hz
      simpa using h2
    have hstep : (y * x * y⁻¹) * z = y * (x * (y⁻¹ * z * y)) * y⁻¹ := by group
    have hstep2 : z * (y * x * y⁻¹) = y * ((y⁻¹ * z * y) * x) * y⁻¹ := by group
    rw [hstep, hstep2, hxcent (y⁻¹ * z * y) hz']
  · intro hx
    have hxQ1 : y * x * y⁻¹ ∈ h.Q1 := (h.mem_centerQ1.mp hx).1
    have hyQ1 : y ∈ Subgroup.normalizer (h.Q1 : Set G) := h.Q1_normal_in_H hy
    have hx' : x ∈ h.Q1 := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hyQ1) (y * x * y⁻¹)).mp hxQ1
      have h3 : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [h3] at h2
    refine h.mem_centerQ1.mpr ⟨hx', fun z hz => ?_⟩
    have hz' : y * z * y⁻¹ ∈ h.Q1 :=
      (Subgroup.mem_normalizer_iff.mp hyQ1 z).mp hz
    have hkey := (h.mem_centerQ1.mp hx).2 (y * z * y⁻¹) hz'
    have h1 : (y * x * y⁻¹) * (y * z * y⁻¹) = y * (x * z) * y⁻¹ := by group
    have h2 : (y * z * y⁻¹) * (y * x * y⁻¹) = y * (z * x) * y⁻¹ := by group
    have h3 : y * (x * z) * y⁻¹ = y * (z * x) * y⁻¹ := by rw [← h1, ← h2]; exact hkey
    simpa using congrArg (fun w => y⁻¹ * w * y) h3

end FSData

end Work.FeitSibley
