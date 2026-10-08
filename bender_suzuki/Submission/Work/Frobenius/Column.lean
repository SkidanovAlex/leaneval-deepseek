import Mathlib
import Submission.Work.Frobenius.Pair
import Submission.Work.Frobenius.ClassFun
import Submission.Work.Frobenius.Irr.charPair_irr_eq_ite
import Submission.Work.Frobenius.Irr.isIrr_one
import Submission.Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Column orthogonality: a nontrivial element is not annihilated by all nonprincipal
irreducible characters

The regular character `freg y = if y = 1 then |H| else 0` is a class function, hence lies in
the span of `Irr H` (`mem_span_Irr_of_isClassFun`); orthonormality identifies its coefficients
with the degrees `θ 1`, so `freg = ∑ θ, θ 1 • θ` and evaluating at `h ≠ 1` gives
`∑_{θ ≠ 1} θ 1 * θ h = -1`, in particular some nonprincipal `θ` does not vanish at `h`.
This is the classical column orthogonality relation, in the form needed to show that the
Frobenius kernel meets the complement trivially.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius

variable {H : Type*} [Group H] [Fintype H]

/-- The regular character as a function. -/
noncomputable def regChar (H : Type*) [Group H] : H → ℂ :=
  fun y => if y = 1 then (Nat.card H : ℂ) else 0

/-- The regular character is a class function. -/
theorem isClassFun_regChar : IsClassFun (regChar H) := by
  intro a b
  by_cases hb : b * a * b⁻¹ = 1
  · have : a = 1 := by
      have := congrArg (fun z => b⁻¹ * z * b) hb
      simpa [mul_assoc] using this
    subst this; simp [regChar]
  · have ha : a ≠ 1 := fun ha => hb (by rw [ha]; group)
    simp [regChar, hb, ha]

theorem regChar_apply_one : regChar H 1 = (Nat.card H : ℂ) := by simp [regChar]

theorem regChar_apply_ne_one {y : H} (hy : y ≠ 1) : regChar H y = 0 := by simp [regChar, hy]

/-- The pairing of the regular character with any function is its value at `1`. -/
theorem charPair_regChar (a : H → ℂ) : charPair (regChar H) a = a 1 := by
  rw [charPair_apply]
  have hcard : ((Nat.card H : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; simp
  have hsum : (∑ y : H, regChar H y * a y⁻¹) = (Nat.card H : ℂ) * a 1 := by
    rw [Finset.sum_eq_single 1]
    · rw [regChar_apply_one]; simp
    · intro y _ hy1; rw [regChar_apply_ne_one hy1, zero_mul]
    · intro hnot; exact absurd (Finset.mem_univ 1) hnot
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- **Column orthogonality.**  A nontrivial element of a finite group is not killed by every
nonprincipal irreducible character. -/
theorem exists_irr_ne_one_apply_ne_zero {h : H} (hh : h ≠ 1) :
    ∃ θ ∈ Irr H, θ ≠ 1 ∧ θ h ≠ 0 := by
  classical
  obtain ⟨c, t, hts, -, hsum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp (CharZero.mem_span_Irr_of_isClassFun (G := H) isClassFun_regChar)
  have hcoeff : ∀ a ∈ t, c a = a 1 := by
    intro a ha
    have hca : charPair (regChar H) a = c a := by
      rw [← hsum, charPair_sum_smul_left]
      have hsingle : (∑ b ∈ t, c b * charPair b a) = c a * charPair a a := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro b hb hba
          rw [Work.Frobenius.Irr.charPair_irr_eq_ite (hts hb) (hts ha), ite_eq_right hba]
          ring
        · intro hnot; exact absurd ha hnot
      rw [hsingle, Work.Frobenius.Irr.charPair_irr_eq_ite (hts ha) (hts ha), ite_eq_left rfl, mul_one]
    rw [← hca, charPair_regChar]
  have hone : (1 : H → ℂ) ∈ t := by
    by_contra hnot
    have hzero : charPair (regChar H) (1 : H → ℂ) = 0 := by
      rw [← hsum, charPair_sum_smul_left]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [Work.Frobenius.Irr.charPair_irr_eq_ite (hts ha) Work.Frobenius.Irr.isIrr_one, ite_eq_right]
      · ring
      · intro hEq; exact hnot (hEq ▸ ha)
    rw [charPair_regChar] at hzero
    simp at hzero
  have heval : (∑ a ∈ t, c a * a h) = 0 := by
    have hthis := congrFun hsum h
    rw [Finset.sum_apply] at hthis
    simp only [Pi.smul_apply, smul_eq_mul] at hthis
    rw [regChar_apply_ne_one hh] at hthis
    rw [← hthis]
  have hsplit : (∑ a ∈ t, c a * a h) = 1 + ∑ a ∈ t.erase 1, c a * a h := by
    rw [← Finset.sum_erase_add _ _ hone, hcoeff 1 hone, Pi.one_apply, Pi.one_apply, mul_one]
    ring
  have hne : (∑ a ∈ t.erase 1, c a * a h) ≠ 0 := by
    intro hcon
    rw [hsplit] at heval
    rw [hcon, add_zero] at heval
    exact one_ne_zero heval
  obtain ⟨a, ha, haval⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨a, hts (Finset.mem_erase.mp ha).2, (Finset.mem_erase.mp ha).1, ?_⟩
  intro hah
  exact haval (by rw [hah, mul_zero])

/-- **Column orthogonality**, form used for the Frobenius kernel: a nontrivial element `x` of a
finite group is not fixed by all nonprincipal irreducible characters, i.e. some nonprincipal
irreducible character does not take the value `θ 1` at `x`. -/
theorem exists_irr_ne_one_apply_ne_apply_one {x : H} (hx : x ≠ 1) :
    ∃ θ ∈ Irr H, θ ≠ 1 ∧ θ x ≠ θ 1 := by
  classical
  by_contra hcon
  have hcon' : ∀ θ ∈ Irr H, θ ≠ 1 → θ x = θ 1 := by
    intro θ hθ hθ1
    by_contra hne
    exact hcon ⟨θ, hθ, hθ1, hne⟩
  obtain ⟨c, t, hts, -, hsum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp
      (CharZero.mem_span_Irr_of_isClassFun (G := H) isClassFun_regChar)
  have hcoeff : ∀ a ∈ t, c a = a 1 := by
    intro a ha
    have hca : charPair (regChar H) a = c a := by
      rw [← hsum, charPair_sum_smul_left]
      have hsingle : (∑ b ∈ t, c b * charPair b a) = c a * charPair a a := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro b hb hba
          rw [Work.Frobenius.Irr.charPair_irr_eq_ite (hts hb) (hts ha), ite_eq_right hba]
          ring
        · intro hnot; exact absurd ha hnot
      rw [hsingle, Work.Frobenius.Irr.charPair_irr_eq_ite (hts ha) (hts ha), ite_eq_left rfl, mul_one]
    rw [← hca, charPair_regChar]
  have hone : (1 : H → ℂ) ∈ t := by
    by_contra hnot
    have hzero : charPair (regChar H) (1 : H → ℂ) = 0 := by
      rw [← hsum, charPair_sum_smul_left]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [Work.Frobenius.Irr.charPair_irr_eq_ite (hts ha) Work.Frobenius.Irr.isIrr_one, ite_eq_right]
      · ring
      · intro hEq; exact hnot (hEq ▸ ha)
    rw [charPair_regChar] at hzero
    simp at hzero
  have heval : (∑ a ∈ t, c a * a x) = 0 := by
    have hthis := congrFun hsum x
    rw [Finset.sum_apply] at hthis
    simp only [Pi.smul_apply, smul_eq_mul] at hthis
    rw [regChar_apply_ne_one hx] at hthis
    rw [← hthis]
  have hsplit : (∑ a ∈ t, c a * a x) = 1 + ∑ a ∈ t.erase 1, c a * a x := by
    rw [← Finset.sum_erase_add _ _ hone, hcoeff 1 hone, Pi.one_apply, Pi.one_apply, mul_one]
    ring
  have hsq : (∑ a ∈ t.erase 1, (a 1) ^ 2) = -1 := by
    have hzero := heval
    rw [hsplit] at hzero
    have hcongr : (∑ a ∈ t.erase 1, c a * a x) = ∑ a ∈ t.erase 1, (a 1) ^ 2 := by
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha_t : a ∈ t := Finset.mem_of_mem_erase ha
      have ha1 : a ≠ 1 := (Finset.mem_erase.mp ha).1
      rw [hcoeff a ha_t, hcon' a (hts ha_t) ha1]
      ring
    rw [hcongr] at hzero
    rw [add_comm] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hnonneg : (0 : ℝ) ≤ (∑ a ∈ t.erase 1, (a 1) ^ 2).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun a ha => ?_
    obtain ⟨d, hd⟩ := mem_Irr_iff.mp (hts (Finset.mem_of_mem_erase ha))
    rw [← hd, Representation.char_one, ← Nat.cast_pow]
    simp only [Complex.natCast_re]
    positivity
  have hre : (∑ a ∈ t.erase 1, (a 1) ^ 2).re = -1 := by rw [hsq]; norm_num
  linarith

end Work.Frobenius
