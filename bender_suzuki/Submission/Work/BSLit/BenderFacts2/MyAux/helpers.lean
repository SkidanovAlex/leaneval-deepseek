import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs
import Submission.Work.BSLit.BenderFacts2.sz_centralizer_involution_eq_U
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.Models.Port.BenderAction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BSLit.BenderFacts2.MyAux

open LeanEval.GroupTheory.Defs

variable {n : ℕ}

/-- The Weyl element is an involution of `SzModel n`. -/
lemma szWgMS_mul_self (n : ℕ) : szWgMS n * szWgMS n = 1 := by
  apply Subtype.ext
  show Submission.Sz.szWg n * Submission.Sz.szWg n = 1
  exact Submission.Sz.szWg_mul_self n

/-- `u(0,c) * u(0,c) = 1`. -/
lemma szUgS_zero_mul_self (n : ℕ) (c : Submission.Sz.SzField n) :
    szUgS n 0 c * szUgS n 0 c = 1 := by
  have h := szUgS_mul n 0 c 0 c
  rw [h]
  have h2 : c + c = 0 := by
    rw [← two_mul, Submission.Sz.szField_two_eq_zero n, zero_mul]
  rw [show (0 : Submission.Sz.SzField n) + 0 = 0 from rfl,
    show c + c + (0 : Submission.Sz.SzField n) * 0 ^ (2 ^ (n + 1)) = 0 from by
      rw [h2, zero_mul, add_zero],
    szUgS_zero]

/-- The Suzuki `2`-group meets the centralizer of the Weyl element trivially. -/
theorem szTwoGroupS_inf_centralizer_szWgMS (n : ℕ) :
    Submission.Sz.szTwoGroupS n ⊓
      Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨hyU, hyC⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC
  have hyW : y ∈ (Submission.Sz.szBorelS n).map (MulAut.conj (szWgMS n)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨y, Submission.Sz.szTwoGroupS_le_szBorelS n hyU, ?_⟩
    show MulAut.conj (szWgMS n) y = y
    rw [MulAut.conj_apply, ← hyC, mul_assoc, mul_inv_cancel, mul_one]
  have hyT : y ∈ Submission.Sz.szTS n := by
    rw [← Submission.Sz.szBorelS_inf_map_conj_eq n]
    exact Subgroup.mem_inf.mpr ⟨Submission.Sz.szTwoGroupS_le_szBorelS n hyU, hyW⟩
  have hmem : y ∈ Submission.Sz.szTwoGroupS n ⊓ Submission.Sz.szTS n := ⟨hyU, hyT⟩
  rwa [Submission.Sz.szTS_inf_szTwoGroupS n] at hmem

/-- Conjugation by `u(0,c)` inverts `g = u(0,c) * w`. -/
lemma szUgS_conj_mul_szWgMS (n : ℕ) (c : Submission.Sz.SzField n) :
    szUgS n 0 c * (szUgS n 0 c * szWgMS n) * (szUgS n 0 c)⁻¹ =
      (szUgS n 0 c * szWgMS n)⁻¹ := by
  have hu : (szUgS n 0 c)⁻¹ = szUgS n 0 c :=
    inv_eq_of_mul_eq_one_right (szUgS_zero_mul_self n c)
  have hw : (szWgMS n)⁻¹ = szWgMS n := inv_eq_of_mul_eq_one_right (szWgMS_mul_self n)
  rw [hu, mul_inv_rev, hu, hw]
  rw [show szUgS n 0 c * (szUgS n 0 c * szWgMS n) * szUgS n 0 c =
      (szUgS n 0 c * szUgS n 0 c) * (szWgMS n * szUgS n 0 c) by group]
  rw [szUgS_zero_mul_self, one_mul]

/-- A centralizer of an element equals the centralizer of its inverse. -/
lemma centralizer_inv_eq {G : Type*} [Group G] (z : G) :
    Subgroup.centralizer ({z⁻¹} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h3 : z * x * z⁻¹ = x := by
      calc z * x * z⁻¹ = z * (x * z⁻¹) := by group
        _ = z * (z⁻¹ * x) := by rw [h]
        _ = x := by group
    calc x * z = (z * x * z⁻¹) * z := by rw [h3]
      _ = z * x := by group
  · intro h
    calc x * z⁻¹ = z⁻¹ * (z * x) * z⁻¹ := by group
      _ = z⁻¹ * (x * z) * z⁻¹ := by rw [h]
      _ = z⁻¹ * x := by group

end Work.BSLit.BenderFacts2.MyAux
