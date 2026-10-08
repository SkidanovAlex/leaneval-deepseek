
/-
# Transfer from the `C₄` group data to the finite-field core

This file sets up the three layers of the `C₄` situation (Higman's `L₁ = P/A`, `L₂ = A/A²`,
`L₃ = A² = Ω₁(P)`), the maps `β` (commutator), `f` (squaring) and `B` (the third-layer bracket),
and their elementary properties.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.H8.Clean.Nsd
import Submission.Work.Higman.c4_field_core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.H8.Clean

variable {P : Type} [Group P] [Finite P]

/-! ## Group-theoretic preliminaries -/

/-- `A` is normal (it is the derived subgroup). -/
theorem aux_Anormal (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) : A.Normal := nsd_normal hGs

/-- `[A, P] ≤ A²` (unipotence). -/
theorem aux_comm_le (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) :
    ⁅A, (⊤ : Subgroup P)⁆ ≤ powSub A 2 :=
  nsd_comm_le h hAxi hAab hGs

/-- The squaring map `P → A` is constant on the cosets of `A²`. -/
theorem aux_sq_wd (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (u : P) {a : P} (ha : a ∈ A) :
    (u * a) * (u * a) * (u * u)⁻¹ ∈ powSub A 2 :=
  nsd_coset_sq_wd h hAxi hAab hGs hsq u ha

/-- `(u * a)² = z * u²` with `z ∈ A²`. -/
theorem aux_sq_coset (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (u : P) {a : P} (ha : a ∈ A) :
    ∃ z ∈ powSub A 2, u * a * (u * a) = z * (u * u) := by
  obtain ⟨z, hzA, hz⟩ := (mem_powSub_iff hAab).mp (aux_sq_wd h hAxi hAab hGs hsq u ha)
  refine ⟨z ^ 2, pow_mem_powSub (n := 2) hzA, ?_⟩
  rw [hz]
  group

/-- The centrality of `A²`. -/
theorem aux_center (h : IsSuzuki2Grp P) {A : Subgroup P}
    (htop : powSub A 2 = omega1 P) : powSub A 2 ≤ Subgroup.center P := by
  rw [htop]; exact h.omega1_le_center

/-- Elements of `A²` are central. -/
theorem aux_conj_eq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (htop : powSub A 2 = omega1 P) :
    ∀ z ∈ powSub A 2, ∀ y : P, y * z * y⁻¹ = z := by
  intro z hz y
  have hc : Commute z y := (Subgroup.mem_center_iff.mp (aux_center h htop hz) y).symm
  calc y * z * y⁻¹ = y * (z * y⁻¹) := by group
    _ = y * (y⁻¹ * z) := by rw [(hc.inv_right).eq]
    _ = z := by group

/-- `(u * a) ^ 4 = u ^ 4` for `a ∈ A`. -/
theorem aux_sq4 (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (htop : powSub A 2 = omega1 P)
    (u : P) {a : P} (ha : a ∈ A) : (u * a) ^ 4 = u ^ 4 := by
  obtain ⟨z, hz, hzsq⟩ := aux_sq_coset h hAxi hAab hGs hsq u ha
  have hcz : (u * u) * z = z * (u * u) :=
    Subgroup.mem_center_iff.mp (aux_center h htop hz) (u * u)
  have hz2 : z * z = 1 := by
    have h1 : z ^ 2 = 1 := h.mem_omega1.mp (by rw [← htop]; exact hz)
    rwa [pow_two] at h1
  have h4 : (u * a) ^ 4 = ((u * a) * (u * a)) * ((u * a) * (u * a)) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have h4' : u ^ 4 = (u * u) * (u * u) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h4, hzsq, h4']
  have key : z * (u * u) * (z * (u * u)) = (z * z) * ((u * u) * (u * u)) := by
    rw [show z * (u * u) * (z * (u * u)) = z * ((u * u) * z) * (u * u) from by group, hcz]
    group
  rw [key, hz2, one_mul]

/-- The commutator of two elements lies in `A`. -/
theorem aux_comm_mem (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (u v : P) : ⁅u, v⁆ ∈ A := by
  rw [← hGs]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

/-- The commutator is well defined modulo `A²` on both sides. -/
theorem aux_comm_sq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u v : P) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹ ∈ powSub A 2 :=
  nsd_comm_pairing_wd h hAxi hAab hGs (aux_center h htop) u v ha hb

/-- The third-layer bracket lies in `A²`. -/
theorem aux_bracket_mem (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (u : P) {b : P} (hb : b ∈ A) :
    ⁅u, b⁆ ∈ powSub A 2 := by
  have hmem : ⁅u, b⁆ ∈ ⁅(⊤ : Subgroup P), A⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top u) hb
  rw [Subgroup.commutator_comm] at hmem
  exact aux_comm_le h hAxi hAab hGs hmem

/-- Changing `u` by an element of `A` changes `⁅u, a⁆` by an element of `A²`. -/
theorem aux_bracket_wd (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u : P) {a : P} (ha : a ∈ A) {c : P} (hc : c ∈ A) :
    ⁅u * c, a⁆ * ⁅u, a⁆⁻¹ ∈ powSub A 2 := by
  have h1 : ⁅u * c, a⁆ = u * ⁅c, a⁆ * u⁻¹ * ⁅u, a⁆ := commutator_mul_left_eq u c a
  have h2 : ⁅c, a⁆ ∈ powSub A 2 :=
    aux_bracket_mem h hAxi hAab hGs c ha
  have hconj : u * ⁅c, a⁆ * u⁻¹ ∈ powSub A 2 := by
    rw [aux_conj_eq h htop ⁅c, a⁆ h2 u]
    exact h2
  rw [h1]
  have h3 : u * ⁅c, a⁆ * u⁻¹ * ⁅u, a⁆ * ⁅u, a⁆⁻¹ = u * ⁅c, a⁆ * u⁻¹ := by group
  rw [h3]
  exact hconj

/-- The third-layer bracket is biadditive in its second variable, modulo `A²`. -/
theorem aux_bracket_mul (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u : P) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅u, a * b⁆ * (⁅u, a⁆ * ⁅u, b⁆)⁻¹ ∈ powSub A 2 := by
  have hmb : ⁅u, b⁆ ∈ A := aux_comm_mem h hGs u b
  have h1 : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := commutator_mul_right_eq u a b
  have h3 : a * ⁅u, b⁆ * a⁻¹ = ⁅a, ⁅u, b⁆⁆ * ⁅u, b⁆ := by
    rw [commutatorElement_def]; group
  have h4 : ⁅a, ⁅u, b⁆⁆ ∈ powSub A 2 := aux_bracket_mem h hAxi hAab hGs a hmb
  have hXcomm : ∀ y : P, ⁅a, ⁅u, b⁆⁆ * y = y * ⁅a, ⁅u, b⁆⁆ :=
    fun y => (Subgroup.mem_center_iff.mp (aux_center h htop h4) y).symm
  have hc := aux_conj_eq h htop ⁅a, ⁅u, b⁆⁆ h4 (⁅u, a⁆ * ⁅u, b⁆)
  rw [h1, h3]
  have hmain : ⁅u, a⁆ * (⁅a, ⁅u, b⁆⁆ * ⁅u, b⁆) * (⁅u, a⁆ * ⁅u, b⁆)⁻¹ = ⁅a, ⁅u, b⁆⁆ := by
    rw [show ⁅u, a⁆ * (⁅a, ⁅u, b⁆⁆ * ⁅u, b⁆) * (⁅u, a⁆ * ⁅u, b⁆)⁻¹
        = (⁅u, a⁆ * ⁅u, b⁆) * ⁅a, ⁅u, b⁆⁆ * (⁅u, a⁆ * ⁅u, b⁆)⁻¹ from by
      rw [hXcomm ⁅u, b⁆]; group]
    exact hc
  rw [hmain]
  exact h4

/-- `[A,P] ≠ ⊥`. -/
theorem aux_comm_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : powSub A 2 = omega1 P) : ⁅A, (⊤ : Subgroup P)⁆ ≠ ⊥ :=
  nsd_comm_eq_bot_false h hAab hNA hGs hsq htop

/-- `A² ≠ ⊥`. -/
theorem aux_A2_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : powSub A 2 = omega1 P) : powSub A 2 ≠ ⊥ := by
  intro hbot
  exact aux_comm_ne_bot h hAab hNA hGs hsq htop
    (le_bot_iff.mp ((aux_comm_le h hAxi hAab hGs).trans (le_of_eq hbot)))

/-- The commutator pairing is non-zero: `[P,P] = A ⊄ A²`. -/
theorem aux_beta_ne (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2) :
    ∃ u v : P, ⁅u, v⁆ ∉ powSub A 2 := by
  by_contra hcon
  have hle : A ≤ powSub A 2 := by
    have h1 : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ powSub A 2 := by
      rw [Subgroup.commutator_le]
      intro u _ v _
      by_contra hmem
      exact hcon ⟨u, v, hmem⟩
    rwa [hGs] at h1
  have hA2 : A = powSub A 2 := le_antisymm hle (powSub_le (by norm_num))
  have hOm : omega1 P = A := by rw [← htop, ← hA2]
  have hc : Nat.card ↥A = (Nat.card ↥A) ^ 2 := by
    rw [hOm] at hcard
    exact hcard
  have h4 : 4 ≤ Nat.card ↥A := by
    rw [← hOm]
    exact h.omega1_card_ge_four
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  nlinarith

/-! ## An elementary abelian-group fact -/

theorem sq_mul_of_abelian {A : Subgroup P} (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {x y : P} (hx : x ∈ A) (hy : y ∈ A) : (x * y) * (x * y) = (x * x) * (y * y) := by
  rw [show (x * y) * (x * y) = x * (y * x) * y from by group, (hAab x hx y hy).symm]
  group

/-! ## Third-layer membership -/

theorem pow4_mem (h : IsSuzuki2Grp P) {A : Subgroup P} (htop : powSub A 2 = omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (u : P) : u ^ 4 ∈ omega1 P := by
  have h2 : u ^ 2 ∈ A := hsq u
  have h4 : u ^ 4 = (u ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul]
  rw [h4, ← htop]
  exact pow_mem_powSub (n := 2) h2

theorem comm_sq_mem (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P) (u v : P) :
    ⁅u, v⁆ ^ 2 ∈ omega1 P := by
  have h1 : ⁅u, v⁆ ∈ A := aux_comm_mem h hGs u v
  rw [← htop]
  exact pow_mem_powSub (n := 2) h1

theorem bracket_mem_omega1 (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u : P) {a : P} (ha : a ∈ A) : ⁅u, a⁆ ∈ omega1 P := by
  rw [← htop]
  exact aux_bracket_mem h hAxi hAab hGs u ha

theorem pow4_eq_sq_sq (u : P) : u ^ 4 = (u ^ 2) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul]

/-! ## Exact computations in the third layer -/

/-- `⁅u * c, a⁆ = ⁅u, a⁆` for `c ∈ A`, `a ∈ A`. -/
theorem bracket_mul_left_exact (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (u : P) {a c : P} (ha : a ∈ A) (hc : c ∈ A) :
    ⁅u * c, a⁆ = ⁅u, a⁆ := by
  have h2 : ⁅u * c, a⁆ = u * ⁅c, a⁆ * u⁻¹ * ⁅u, a⁆ := commutator_mul_left_eq u c a
  have hca : ⁅c, a⁆ = 1 := by
    rw [commutatorElement_def, hAab c hc a ha]; group
  rw [h2, hca]
  group

/-- `⁅u, a * b⁆ = ⁅u, a⁆ * ⁅u, b⁆` for `a, b ∈ A`. -/
theorem bracket_mul_exact (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (u : P) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅u, a * b⁆ = ⁅u, a⁆ * ⁅u, b⁆ := by
  have h1 : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := commutator_mul_right_eq u a b
  have h2 : a * ⁅u, b⁆ * a⁻¹ = ⁅u, b⁆ := by
    have hcomm : a * ⁅u, b⁆ = ⁅u, b⁆ * a := hAab a ha ⁅u, b⁆ (aux_comm_mem h hGs u b)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1, h2]

/-- `⁅u, a * z⁆ = ⁅u, a⁆` for `a ∈ A` and `z ∈ A²`. -/
theorem bracket_mul_central (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u : P) {a z : P} (ha : a ∈ A) (hz : z ∈ powSub A 2) :
    ⁅u, a * z⁆ = ⁅u, a⁆ := by
  have h1 : ⁅u, a * z⁆ = ⁅u, a⁆ * (a * ⁅u, z⁆ * a⁻¹) := commutator_mul_right_eq u a z
  have huz : ⁅u, z⁆ = 1 := by
    rw [commutatorElement_def, aux_conj_eq h htop z hz u]
    group
  rw [h1, huz]
  group

/-- `(u * a) ^ 4 = u ^ 4` for `a ∈ A`. -/
theorem pow4_congr (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (htop : powSub A 2 = omega1 P)
    (u : P) {a : P} (ha : a ∈ A) : (u * a) ^ 4 = u ^ 4 :=
  aux_sq4 h hAxi hAab hGs hsq htop u ha

/-- `⁅u * a, v * b⁆ ^ 2 = ⁅u, v⁆ ^ 2` for `a, b ∈ A`. -/
theorem comm_sq_congr (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u v : P) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅u * a, v * b⁆ ^ 2 = ⁅u, v⁆ ^ 2 := by
  have h1 : ⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹ ∈ powSub A 2 := aux_comm_sq h hAxi hAab hGs htop u v ha hb
  have hwA : ⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹ ∈ A := powSub_le (by norm_num) h1
  have hvu : ⁅u, v⁆ ∈ A := aux_comm_mem h hGs u v
  have h2 : ⁅u * a, v * b⁆ = (⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹) * ⁅u, v⁆ := by group
  have h3 : (⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹) * (⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹) = 1 := by
    have h' : (⁅u * a, v * b⁆ * ⁅u, v⁆⁻¹) ^ 2 = 1 := h.mem_omega1.mp (by rw [← htop]; exact h1)
    rwa [pow_two] at h'
  rw [h2, pow_two, sq_mul_of_abelian hAab hwA hvu, h3, one_mul, pow_two]

/-! ## Biadditivity of the two pairings -/

/-- `⁅u * v, a⁆ = ⁅u, a⁆ * ⁅v, a⁆` for `a ∈ A`. -/
theorem bracket_mul_omega (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u v : P) {a : P} (ha : a ∈ A) : ⁅u * v, a⁆ = ⁅u, a⁆ * ⁅v, a⁆ := by
  have hua : ⁅u, a⁆ ∈ powSub A 2 := aux_bracket_mem h hAxi hAab hGs u ha
  have hva : ⁅v, a⁆ ∈ powSub A 2 := aux_bracket_mem h hAxi hAab hGs v ha
  have h1 : ⁅u * v, a⁆ = (u * ⁅v, a⁆ * u⁻¹) * ⁅u, a⁆ := commutator_mul_left_eq u v a
  rw [h1, aux_conj_eq h htop ⁅v, a⁆ hva u]
  exact hAab ⁅v, a⁆ (powSub_le (by norm_num) hva) ⁅u, a⁆ (powSub_le (by norm_num) hua)

/-- `(⁅u * v, w⁆) ^ 2 = (⁅u, w⁆) ^ 2 * (⁅v, w⁆) ^ 2`. -/
theorem comm_sq_mul_left (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u v w : P) : (⁅u * v, w⁆) ^ 2 = (⁅u, w⁆) ^ 2 * (⁅v, w⁆) ^ 2 := by
  have hvw : ⁅v, w⁆ ∈ A := aux_comm_mem h hGs v w
  have huw : ⁅u, w⁆ ∈ A := aux_comm_mem h hGs u w
  set X : P := ⁅u, ⁅v, w⁆⁆ with hXdef
  set Y : P := ⁅v, w⁆ * ⁅u, w⁆ with hYdef
  have hX : X ∈ powSub A 2 := aux_bracket_mem h hAxi hAab hGs u hvw
  have hX1 : X * X = 1 := by
    have h' : X ^ 2 = 1 := h.mem_omega1.mp (by rw [← htop]; exact hX)
    rwa [pow_two] at h'
  have hXY : ∀ Z : P, Z * X = X * Z := by
    intro Z
    have h2 := aux_conj_eq h htop X hX Z
    calc Z * X = Z * X * Z⁻¹ * Z := by group
      _ = X * Z := by rw [h2]
  have hY : Y ∈ A := A.mul_mem hvw huw
  have h1 : ⁅u * v, w⁆ = X * Y := by
    rw [hXdef, hYdef]
    rw [commutatorElement_def]
    rw [show u * v * w * (u * v)⁻¹ * w⁻¹ = u * (v * w * v⁻¹) * u⁻¹ * w⁻¹ from by group]
    rw [show v * w * v⁻¹ = ⁅v, w⁆ * w from by rw [commutatorElement_def]; group]
    rw [show u * (⁅v, w⁆ * w) * u⁻¹ * w⁻¹
        = (u * ⁅v, w⁆ * u⁻¹) * (u * w * u⁻¹ * w⁻¹) from by group]
    rw [show u * ⁅v, w⁆ * u⁻¹ = ⁅u, ⁅v, w⁆⁆ * ⁅v, w⁆ from by
      rw [commutatorElement_def]; group]
    rw [show u * w * u⁻¹ * w⁻¹ = ⁅u, w⁆ from rfl]
    group
  have h2 : Y * Y = (⁅u, w⁆ * ⁅u, w⁆) * (⁅v, w⁆ * ⁅v, w⁆) := by
    rw [hYdef, sq_mul_of_abelian hAab hvw huw]
    exact hAab (⁅v, w⁆ * ⁅v, w⁆) (A.mul_mem hvw hvw)
      (⁅u, w⁆ * ⁅u, w⁆) (A.mul_mem huw huw)
  have h3 : (X * Y) * (X * Y) = (⁅u, w⁆ ^ 2) * (⁅v, w⁆ ^ 2) := by
    calc (X * Y) * (X * Y) = X * (Y * X) * Y := by group
      _ = X * (X * Y) * Y := by rw [hXY Y]
      _ = (X * X) * (Y * Y) := by group
      _ = Y * Y := by rw [hX1, one_mul]
      _ = (⁅u, w⁆ ^ 2) * (⁅v, w⁆ ^ 2) := by rw [h2, pow_two, pow_two]
  rw [h1]
  rw [show (X * Y) ^ 2 = (X * Y) * (X * Y) from pow_two _]
  exact h3

/-- `(⁅u, v * w⁆) ^ 2 = (⁅u, v⁆) ^ 2 * (⁅u, w⁆) ^ 2`. -/
theorem comm_sq_mul_right (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : powSub A 2 = omega1 P)
    (u v w : P) : (⁅u, v * w⁆) ^ 2 = (⁅u, v⁆) ^ 2 * (⁅u, w⁆) ^ 2 := by
  have hw : ⁅u, w⁆ ∈ A := aux_comm_mem h hGs u w
  have hv : ⁅u, v⁆ ∈ A := aux_comm_mem h hGs u v
  have hX : v * ⁅u, w⁆ * v⁻¹ ∈ A := by
    haveI hAn : A.Normal := aux_Anormal h hGs
    exact hAn.conj_mem ⁅u, w⁆ hw v
  have h2 : (v * ⁅u, w⁆ * v⁻¹) * (v * ⁅u, w⁆ * v⁻¹) = ⁅u, w⁆ * ⁅u, w⁆ := by
    rw [show v * ⁅u, w⁆ * v⁻¹ * (v * ⁅u, w⁆ * v⁻¹) = v * (⁅u, w⁆ * ⁅u, w⁆) * v⁻¹ from by
      group]
    exact aux_conj_eq h htop (⁅u, w⁆ * ⁅u, w⁆) (by rw [← pow_two]; exact pow_mem_powSub hw) v
  have h1 : ⁅u, v * w⁆ = ⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹) := commutator_mul_right_eq u v w
  have h3 : (⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹)) ^ 2 = (⁅u, v⁆) ^ 2 * (⁅u, w⁆) ^ 2 := by
    have h4 : (⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹)) * (⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹))
        = (⁅u, v⁆ * ⁅u, v⁆) * (⁅u, w⁆ * ⁅u, w⁆) := by
      rw [sq_mul_of_abelian hAab hv hX, h2]
    rw [show (⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹)) ^ 2
        = (⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹)) * (⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹)) from pow_two _, h4,
      pow_two, pow_two]
  rw [h1, h3]

end Work.Higman.H8.Clean
