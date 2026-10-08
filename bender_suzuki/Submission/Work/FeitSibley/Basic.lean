import Submission.Work.FeitSibley.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley`: elementary structural facts about the Feit–Sibley set-up

`h : FSData G` packages the hypotheses of Peterfalvi II App. XII.  This module derives the
immediate group-theoretic consequences used everywhere else in the area:

* `Q₁ ≤ Q`, `S ≤ Q`, `Q₁ ≤ H`, `S ≤ H`;
* `Q ≠ ⊥`, `Q₁ ≠ ⊥` (the latter because `Q₁` is not a `2`-group and `⊥` is);
* `N_G(Q) = H` (`normalizer_Q_eq`) and hence `Q` is a T.I. subgroup of `G` in the sense of
  `Work.Induction.IsTI` (`isTI_Q`);
* the unique decomposition `H ∋ x = q * d` with `q ∈ Q`, `d ∈ D` (`mem_H_iff`,
  `mul_eq_of_decomp`), and likewise `Q ∋ x = a * b` with `a ∈ S`, `b ∈ Q₁`;
* `Q₁ ⊓ D = ⊥`, `S ⊓ D = ⊥`, `|D|` coprime to `|Q₁|` and to `|S|`.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.FeitSibley

variable {G : Type} [Group G] [Fintype G]

namespace FSData

variable (h : FSData G)

theorem Q1_le_Q : h.Q1 ≤ h.Q := by
  rw [← h.S_sup_Q1]; exact le_sup_right

theorem S_le_Q : h.S ≤ h.Q := by
  rw [← h.S_sup_Q1]; exact le_sup_left

theorem Q1_le_H : h.Q1 ≤ h.H := h.Q1_le_Q.trans h.Q_le_H

theorem S_le_H : h.S ≤ h.H := h.S_le_Q.trans h.Q_le_H

theorem Q1_ne_bot : h.Q1 ≠ ⊥ := fun hb => h.Q1_not_two (hb ▸ IsPGroup.of_bot)

theorem Q_ne_bot : h.Q ≠ ⊥ := fun hb => h.Q1_ne_bot (le_bot_iff.mp (hb ▸ h.Q1_le_Q))

theorem D_le_normalizer_Q : h.D ≤ Subgroup.normalizer (h.Q : Set G) :=
  le_trans h.D_le_H h.Q_normal_in_H

theorem D_beq : (h.H : Set G) = (h.Q : Set G) * (h.D : Set G) := by
  rw [← h.Q_sup_D, Subgroup.coe_mul_of_right_le_normalizer_left h.Q h.D h.D_le_normalizer_Q]

theorem mem_H_iff {x : G} : x ∈ h.H ↔ ∃ q ∈ h.Q, ∃ d ∈ h.D, q * d = x := by
  have hm : x ∈ (h.Q : Set G) * (h.D : Set G) ↔ ∃ q ∈ h.Q, ∃ d ∈ h.D, q * d = x :=
    Set.mem_mul
  rwa [← h.D_beq] at hm

/-- Every element of `H` is a product `q * d` with `q ∈ Q`, `d ∈ D`. -/
theorem mem_H_decomp {x : G} (hx : x ∈ h.H) : ∃ q ∈ h.Q, ∃ d ∈ h.D, x = q * d := by
  obtain ⟨q, hq, d, hd, hqd⟩ := h.mem_H_iff.mp hx
  exact ⟨q, hq, d, hd, hqd.symm⟩

/-- The decomposition of an element of `H` as `q * d` (`q ∈ Q`, `d ∈ D`) is unique. -/
theorem mul_eq_of_decomp {q q' : G} (hq : q ∈ h.Q) (hq' : q' ∈ h.Q) {d d' : G}
    (hd : d ∈ h.D) (hd' : d' ∈ h.D) (heq : q * d = q' * d') : q = q' ∧ d = d' := by
  have h1 : (q'⁻¹ * q) * d = d' := by
    have := congrArg (fun y => q'⁻¹ * y) heq
    simpa [mul_assoc] using this
  have hmem : q'⁻¹ * q = d' * d⁻¹ := by
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hQ : q'⁻¹ * q ∈ h.Q := mul_mem (inv_mem hq') hq
  have hD : d' * d⁻¹ ∈ h.D := mul_mem hd' (inv_mem hd)
  have hbot : q'⁻¹ * q = 1 := by
    have : q'⁻¹ * q ∈ h.Q ⊓ h.D := by rw [Subgroup.mem_inf]; exact ⟨hQ, hmem ▸ hD⟩
    rw [h.Q_inf_D] at this
    simpa using this
  have hqeq : q = q' := by
    have h2 := congrArg (fun y => q' * y) hbot
    simpa [mul_assoc] using h2
  refine ⟨hqeq, ?_⟩
  rw [hqeq] at heq
  exact mul_left_cancel heq

theorem Q1_inf_D : h.Q1 ⊓ h.D = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxQ1, hxD⟩ := Subgroup.mem_inf.mp hx
  have : x ∈ h.Q ⊓ h.D := Subgroup.mem_inf.mpr ⟨h.Q1_le_Q hxQ1, hxD⟩
  rw [h.Q_inf_D] at this
  simpa using this

theorem S_inf_D : h.S ⊓ h.D = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxS, hxD⟩ := Subgroup.mem_inf.mp hx
  have : x ∈ h.Q ⊓ h.D := Subgroup.mem_inf.mpr ⟨h.S_le_Q hxS, hxD⟩
  rw [h.Q_inf_D] at this
  simpa using this

/-- Conjugation by an element of `Q₁` fixes every element of `S` (they commute). -/
theorem conjB_eq_of_mem {y m : G} (hy : y ∈ h.Q1) (hm : m ∈ h.S) : y * m * y⁻¹ = m := by
  rw [← h.commute m hm y hy]; simp

/-- Conjugation by the inverse of an element of `Q₁` fixes every element of `S`. -/
theorem conjB_inv_eq_of_mem {y m : G} (hy : y ∈ h.Q1) (hm : m ∈ h.S) :
    y⁻¹ * m * y = m := by
  have h1 := h.conjB_eq_of_mem hy hm
  calc y⁻¹ * m * y = y⁻¹ * (y * m * y⁻¹) * y := by rw [h1]
    _ = m := by group

theorem Q1_le_normalizer_S : h.Q1 ≤ Subgroup.normalizer (h.S : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · rw [h.conjB_eq_of_mem hy hn]; exact hn
  · have h3 : n = y⁻¹ * (y * n * y⁻¹) * y := by group
    rw [h3, h.conjB_inv_eq_of_mem hy hn]
    exact hn

/-- Conjugation by an element of `S` fixes every element of `Q₁`. -/
theorem conjA_eq_of_mem {y m : G} (hy : y ∈ h.S) (hm : m ∈ h.Q1) : y * m * y⁻¹ = m := by
  rw [h.commute y hy m hm]; simp

theorem S_le_normalizer_Q1 : h.S ≤ Subgroup.normalizer (h.Q1 : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · rw [h.conjA_eq_of_mem hy hn]; exact hn
  · have h4 : y * (y * n * y⁻¹) * y⁻¹ = y * n * y⁻¹ := h.conjA_eq_of_mem hy hn
    have h5 : n = y * n * y⁻¹ := by
      have h6 : y⁻¹ * (y * n * y⁻¹) * y = n := by group
      calc n = y⁻¹ * (y * n * y⁻¹) * y := h6.symm
        _ = y⁻¹ * (y * (y * n * y⁻¹) * y⁻¹) * y := by rw [h4]
        _ = y * n * y⁻¹ := by group
    rw [h5]; exact hn

theorem mem_Q_iff {x : G} : x ∈ h.Q ↔ ∃ a ∈ h.S, ∃ b ∈ h.Q1, a * b = x := by
  have hcoe : (↑(h.S ⊔ h.Q1) : Set G) = (h.S : Set G) * (h.Q1 : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left h.S h.Q1 h.Q1_le_normalizer_S
  have hm : x ∈ (h.S : Set G) * (h.Q1 : Set G) ↔ ∃ a ∈ h.S, ∃ b ∈ h.Q1, a * b = x :=
    Set.mem_mul
  rw [← hcoe, h.S_sup_Q1] at hm
  exact hm

/-- Every element of `Q` is a product `a * b` with `a ∈ S`, `b ∈ Q₁`. -/
theorem mem_Q_decomp {x : G} (hx : x ∈ h.Q) : ∃ a ∈ h.S, ∃ b ∈ h.Q1, x = a * b := by
  obtain ⟨a, ha, b, hb, hab⟩ := h.mem_Q_iff.mp hx
  exact ⟨a, ha, b, hb, hab.symm⟩

/-- The decomposition of an element of `Q` as `a * b` (`a ∈ S`, `b ∈ Q₁`) is unique. -/
theorem mul_eq_of_Q_decomp {a a' : G} (ha : a ∈ h.S) (ha' : a' ∈ h.S) {b b' : G}
    (hb : b ∈ h.Q1) (hb' : b' ∈ h.Q1) (heq : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : (a'⁻¹ * a) * b = b' := by
    have := congrArg (fun y => a'⁻¹ * y) heq
    simpa [mul_assoc] using this
  have hmem : a'⁻¹ * a = b' * b⁻¹ := by
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hS : a'⁻¹ * a ∈ h.S := mul_mem (inv_mem ha') ha
  have hQ1 : b' * b⁻¹ ∈ h.Q1 := mul_mem hb' (inv_mem hb)
  have hbot : a'⁻¹ * a = 1 := by
    have : a'⁻¹ * a ∈ h.S ⊓ h.Q1 := by rw [Subgroup.mem_inf]; exact ⟨hS, hmem ▸ hQ1⟩
    rw [h.S_inf_Q1] at this
    simpa using this
  have haeq : a = a' := by
    have h2 := congrArg (fun y => a' * y) hbot
    simpa [mul_assoc] using h2
  refine ⟨haeq, ?_⟩
  rw [haeq] at heq
  exact mul_left_cancel heq

theorem card_Q1_dvd_card_Q : Nat.card h.Q1 ∣ Nat.card h.Q := by
  have h1 : Nat.card ↥(h.Q1.subgroupOf h.Q) ∣ Nat.card ↥h.Q :=
    Subgroup.card_subgroup_dvd_card (h.Q1.subgroupOf h.Q)
  have hcard : Nat.card ↥(h.Q1.subgroupOf h.Q) = Nat.card h.Q1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q1_le_Q).toEquiv
  rwa [hcard] at h1

theorem card_S_dvd_card_Q : Nat.card h.S ∣ Nat.card h.Q := by
  have h1 : Nat.card ↥(h.S.subgroupOf h.Q) ∣ Nat.card ↥h.Q :=
    Subgroup.card_subgroup_dvd_card (h.S.subgroupOf h.Q)
  have hcard : Nat.card ↥(h.S.subgroupOf h.Q) = Nat.card h.S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.S_le_Q).toEquiv
  rwa [hcard] at h1

theorem coprime_D_Q1 : Nat.Coprime (Nat.card h.D) (Nat.card h.Q1) :=
  h.coprime_D_Q.coprime_dvd_right h.card_Q1_dvd_card_Q

theorem coprime_D_S : Nat.Coprime (Nat.card h.D) (Nat.card h.S) :=
  h.coprime_D_Q.coprime_dvd_right h.card_S_dvd_card_Q

theorem normalizer_Q_eq : Subgroup.normalizer (h.Q : Set G) = h.H := by
  refine le_antisymm ?_ h.Q_normal_in_H
  intro x hx
  by_contra hxH
  have hconj : Submission.Blueprint.conj x h.Q = h.Q := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
      have hmem : q ∈ h.Q ↔ x * q * x⁻¹ ∈ h.Q :=
        (Subgroup.mem_normalizer_iff.mp hx) q
      rw [← hqy]
      exact (hmem.mp hq)
    · intro y hy
      have hmem : x⁻¹ * y * x ∈ h.Q := by
        have hx' : x⁻¹ ∈ Subgroup.normalizer (h.Q : Set G) := inv_mem hx
        simpa using (Subgroup.mem_normalizer_iff.mp hx' y).mp hy
      have hxy : MulAut.conj x (x⁻¹ * y * x) = y := by
        show x * (x⁻¹ * y * x) * x⁻¹ = y
        group
      rw [← hxy]
      exact Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, hmem, rfl⟩
  have hbot : h.Q ⊓ Submission.Blueprint.conj x h.Q = ⊥ := h.Q_TI x hxH
  rw [hconj, inf_idem] at hbot
  exact h.Q_ne_bot hbot

theorem isTI_Q : Work.Induction.IsTI h.Q := by
  intro x hx
  refine h.Q_TI x (fun hxH => hx ?_)
  show x ∈ Subgroup.normalizer (h.Q : Set G)
  rw [h.normalizer_Q_eq]
  exact hxH

end FSData

end Work.FeitSibley
