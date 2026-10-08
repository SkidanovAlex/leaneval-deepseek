import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.OddFib
import Submission.Work.ZassenhausSuzuki.CountingDefs
import Submission.Work.Models.Port.Sz.Bruhat
import Submission.Work.Models.Port.Sz.TwoTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderFacts2.sz_centralizer_mem_Vals`

The centraliser of `u(0,c)·w` (`c ≠ 0`, `u(0,c)` an involution of the Suzuki `2`-group, `w` the
Weyl element) has an order that occurs in `ℱ`; equivalently the centraliser itself lies in the
Bender–Suzuki family `FinsetCZ` of `Work.ZassenhausSuzuki.Odd`.

The point is that `u(0,c)·w` is a product of two involutions (so *strongly real*) and is *not*
itself an involution: `(u(0,c)·w)² = 1` would say that the involution `u(0,c) ∈ U` commutes with
`w`, contradicting `U ⊓ C(w) = ⊥`.  Hence `C(u(0,c)·w)` is `C(x)` for some strongly real `x`
of order `> 2`, i.e. a member of `FinsetCZ`, and the order map on `FinsetCZ` realises its
cardinality as an element of `Vals`.
-/

set_option linter.unusedVariables false

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs

/-- The Weyl element `w = szWgMS n` is an involution. -/
lemma szWgMS_mul_self_Vals (n : ℕ) : szWgMS n * szWgMS n = 1 := by
  apply Subtype.ext
  show Submission.Sz.szWg n * Submission.Sz.szWg n = 1
  exact Submission.Sz.szWg_mul_self n

/-- The Suzuki `2`-group meets the centraliser of the Weyl element trivially. -/
lemma sz_twoGroupS_inf_centralizer_szWgMS_Vals (n : ℕ) :
    Submission.Sz.szTwoGroupS n ⊓
      Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨hyU, hyC⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC
  have hwinv : (szWgMS n)⁻¹ = szWgMS n :=
    inv_eq_of_mul_eq_one_right (szWgMS_mul_self_Vals n)
  have hyW : y ∈ (Submission.Sz.szBorelS n).map (MulAut.conj (szWgMS n)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨y, Submission.Sz.szTwoGroupS_le_szBorelS n hyU, ?_⟩
    show szWgMS n * y * (szWgMS n)⁻¹ = y
    rw [hwinv, ← hyC, mul_assoc y (szWgMS n) (szWgMS n), szWgMS_mul_self_Vals n, mul_one]
  have hyT : y ∈ Submission.Sz.szTS n := by
    rw [← Submission.Sz.szBorelS_inf_map_conj_eq n]
    exact Subgroup.mem_inf.mpr ⟨Submission.Sz.szTwoGroupS_le_szBorelS n hyU, hyW⟩
  have hmem : y ∈ Submission.Sz.szTwoGroupS n ⊓ Submission.Sz.szTS n := ⟨hyU, hyT⟩
  rw [Submission.Sz.szTS_inf_szTwoGroupS n] at hmem
  exact hmem

theorem sz_centralizer_mem_Vals (n : ℕ) (hn : 1 ≤ n) {c : Submission.Sz.SzField n} (hc : c ≠ 0) :
    Nat.card ↥(Subgroup.centralizer
      ({Work.BSLit.BenderFacts2.szUgS n 0 c * Work.BSLit.BenderFacts2.szWgMS n} :
        Set (LeanEval.GroupTheory.Defs.SzModel n)))
      ∈ Work.ZassenhausSuzuki.Odd.Vals (LeanEval.GroupTheory.Defs.SzModel n) := by
  -- `u(0,c)` is an involution of the Suzuki `2`-group.
  have hu2 : szUgS n 0 c * szUgS n 0 c = 1 := by
    rw [← pow_two]; exact (szUgS_sq_eq_one_iff n 0 c).mpr rfl
  have hw2 : szWgMS n * szWgMS n = 1 := szWgMS_mul_self_Vals n
  -- `u(0,c)·w` is not an involution: its square would make `u(0,c)` commute with `w`.
  have hg2 : (szUgS n 0 c * szWgMS n) * (szUgS n 0 c * szWgMS n) ≠ 1 := by
    intro h
    have hcomm : szUgS n 0 c * szWgMS n = szWgMS n * szUgS n 0 c := by
      have hu_inv : (szUgS n 0 c)⁻¹ = szUgS n 0 c := inv_eq_of_mul_eq_one_right hu2
      have hw_inv : (szWgMS n)⁻¹ = szWgMS n := inv_eq_of_mul_eq_one_right hw2
      have h1 : (szUgS n 0 c * szWgMS n)⁻¹ = szWgMS n * szUgS n 0 c := by
        rw [mul_inv_rev, hu_inv, hw_inv]
      have h2 : (szUgS n 0 c * szWgMS n)⁻¹ = szUgS n 0 c * szWgMS n :=
        inv_eq_of_mul_eq_one_right h
      rw [h2] at h1; exact h1
    have hmem : szUgS n 0 c ∈ Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hcomm
    have hinf : szUgS n 0 c ∈ Submission.Sz.szTwoGroupS n ⊓
        Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) :=
      ⟨szUgS_mem_U n 0 c, hmem⟩
    rw [sz_twoGroupS_inf_centralizer_szWgMS_Vals n] at hinf
    have hu1 : szUgS n 0 c = 1 := Subgroup.mem_bot.mp hinf
    have hord := orderOf_szUgS_zero n hc
    rw [hu1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hg_ne : szUgS n 0 c * szWgMS n ≠ 1 := fun h => hg2 (by rw [h, one_mul])
  -- So `g := u(0,c)·w` is strongly real, non-identity, and not an involution.
  have hsr : Work.ZassenhausSuzuki.IsStronglyReal (szUgS n 0 c * szWgMS n) :=
    ⟨szUgS n 0 c, szWgMS n, hu2, hw2, rfl⟩
  have hcz : Work.ZassenhausSuzuki.Odd.IsCZ
      (Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n))) :=
    ⟨szUgS n 0 c * szWgMS n, hsr, hg_ne, hg2, rfl⟩
  -- Its centraliser is therefore a member of the Bender–Suzuki family `FinsetCZ`.
  rw [Work.ZassenhausSuzuki.Odd.mem_Vals]
  exact ⟨Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)),
    (Work.ZassenhausSuzuki.Odd.mem_FinsetCZ).mpr hcz, rfl⟩

end Work.BSLit.BenderFacts2
