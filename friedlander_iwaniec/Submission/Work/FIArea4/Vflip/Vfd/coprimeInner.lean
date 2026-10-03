import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.coprimeMoebius

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip.Vfd
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Work.FIArea4

lemma sum_Icc_div_restrict {M : Type*} [AddCommMonoid M] (R ρ : ℕ) (f : ℕ → M)
    (hf : ∀ u, u ∈ Finset.Icc 1 (2*R) → ¬ (u ≤ 2*R/ρ) → f u = 0) :
    ∑ u ∈ Finset.Icc 1 (2*R), f u = ∑ u ∈ Finset.Icc 1 (2*R/ρ), f u := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, by have := Nat.div_le_self (2*R) ρ; omega⟩
  · intro x hx hnx
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
    refine hf x hx (fun hle => ?_)
    exact hnx (Finset.mem_Icc.mpr ⟨hx1, hle⟩)

lemma big_mul {R ρ u : ℕ} (hρ : 1 ≤ ρ) (h : ¬ (u ≤ 2*R/ρ)) : 2*R < ρ*u := by
  have h1 : 2*R/ρ < u := Nat.lt_of_not_le h
  have h3 : 2*R % ρ < ρ := Nat.mod_lt _ (by omega)
  calc 2*R = ρ*(2*R/ρ) + 2*R%ρ := (Nat.div_add_mod (2*R) ρ).symm
    _ < ρ*(2*R/ρ) + ρ := by omega
    _ = ρ*(2*R/ρ+1) := by ring
    _ ≤ ρ*u := Nat.mul_le_mul_left ρ h1

lemma inner_term_eq (d ρ u1 s1 u2 s2 : ℕ) (hd : 1 ≤ d)
    (u v : ℕ → ℕ → ℂ) (hu : ∀ r s, u r s ≠ 0 → Odd r) :
    (if (((ρ*u1*s2:ℕ):ZMod d) = ((ρ*u2*s1:ℕ):ZMod d)) then
       u (ρ*u1) s1 * star (v (ρ*u2) s2) *
         ((jacobiSym (((ρ*u1:ℕ)):ℤ) (Work.FIPlan.oddPart d) *
           jacobiSym (((ρ*u2:ℕ)):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0)
    = (if Nat.Coprime ρ (Work.FIPlan.oddPart d) then
        (if (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d)) then
           u (ρ*u1) s1 * star (v (ρ*u2) s2) *
             ((jacobiSym ((u1:ℕ):ℤ) (Work.FIPlan.oddPart d) *
               jacobiSym ((u2:ℕ):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0)
       else 0) := by
  have hA : (jacobiSym (((ρ*u1:ℕ)):ℤ) (Work.FIPlan.oddPart d) *
        jacobiSym (((ρ*u2:ℕ)):ℤ) (Work.FIPlan.oddPart d) : ℤ)
      = (jacobiSym ((ρ:ℕ):ℤ) (Work.FIPlan.oddPart d))^2 *
        (jacobiSym ((u1:ℕ):ℤ) (Work.FIPlan.oddPart d) *
         jacobiSym ((u2:ℕ):ℤ) (Work.FIPlan.oddPart d)) := by
    rw [show (((ρ*u1:ℕ)):ℤ) = ((ρ:ℕ):ℤ)*((u1:ℕ):ℤ) by push_cast; ring,
        show (((ρ*u2:ℕ)):ℤ) = ((ρ:ℕ):ℤ)*((u2:ℕ):ℤ) by push_cast; ring,
        jacobiSym.mul_left, jacobiSym.mul_left]; ring
  have hAcast : ((jacobiSym (((ρ*u1:ℕ)):ℤ) (Work.FIPlan.oddPart d) *
        jacobiSym (((ρ*u2:ℕ)):ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
      = (if Nat.Coprime ρ (Work.FIPlan.oddPart d) then (1:ℂ) else 0) *
        ((jacobiSym ((u1:ℕ):ℤ) (Work.FIPlan.oddPart d) *
          jacobiSym ((u2:ℕ):ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ) := by
    rw [hA, jacobiSym_sq_eq ρ d hd]
    push_cast
    by_cases hcop : Nat.Coprime ρ (Work.FIPlan.oddPart d) <;> simp [hcop]
  rw [hAcast]
  by_cases hcop : Nat.Coprime ρ (Work.FIPlan.oddPart d)
  · rw [if_pos hcop, if_pos hcop]
    by_cases hodd : Odd ρ
    · have hcd : Nat.Coprime ρ d := coprime_oddPart_of_coprime hodd hcop
      have hunit : IsUnit ((ρ:ℕ):ZMod d) := (ZMod.isUnit_iff_coprime ρ d).mpr hcd
      by_cases hC : (((ρ*u1*s2:ℕ):ZMod d) = ((ρ*u2*s1:ℕ):ZMod d))
      · rw [if_pos hC, if_pos ((zmod_scale_eq_iff hunit).mp hC)]; ring
      · rw [if_neg hC, if_neg (fun h => hC ((zmod_scale_eq_iff hunit).mpr h))]
    · rw [Nat.not_odd_iff_even] at hodd
      have hzero : u (ρ*u1) s1 = 0 := by
        by_contra hne
        exact (Nat.not_even_iff_odd.mpr (hu (ρ*u1) s1 hne)) (hodd.mul_right u1)
      rw [hzero]; simp
  · rw [if_neg hcop]
    simp [hcop]

lemma inner_eq (R S d ρ : ℕ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (u v : ℕ → ℕ → ℂ)
    (hu : ∀ r s, u r s ≠ 0 → Odd r) (huR : ∀ r s, u r s ≠ 0 → r ≤ 2*R)
    (hv : ∀ r s, v r s ≠ 0 → Odd r) (hvR : ∀ r s, v r s ≠ 0 → r ≤ 2*R) :
    (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
      ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
       (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
          u r1 s1 * star (v r2 s2) *
            ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
        else 0))
    = (if Nat.Coprime ρ (Work.FIPlan.oddPart d) then
        Work.FIArea4.pairSum R S d (shiftCoef ρ u) (shiftCoef ρ v) else 0) := by
  have hL : (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
      ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
       (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
          u r1 s1 * star (v r2 s2) *
            ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
        else 0))
      = ∑ u1 ∈ Finset.Icc 1 (2*R/ρ), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ u2 ∈ Finset.Icc 1 (2*R/ρ), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if ((((ρ*u1)*s2:ℕ):ZMod d) = (((ρ*u2)*s1:ℕ):ZMod d)) then
             u (ρ*u1) s1 * star (v (ρ*u2) s2) *
               ((jacobiSym (((ρ*u1:ℕ)):ℤ) (Work.FIPlan.oddPart d) *
                 jacobiSym (((ρ*u2:ℕ)):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0) := by
    have hstep : (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
         (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
            u r1 s1 * star (v r2 s2) *
              ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
          else 0))
        = ∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
          ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if ρ ∣ r1 ∧ ρ ∣ r2 then
             (if (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
                u r1 s1 * star (v r2 s2) *
                  ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
              else 0)
           else 0) := by
      refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
        Finset.sum_congr rfl (fun r2 _ => Finset.sum_congr rfl (fun s2 _ => ?_))))
      by_cases h1 : ρ ∣ r1 <;> by_cases h2 : ρ ∣ r2 <;>
        by_cases hC : (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) <;> simp [h1, h2, hC]
    rw [hstep]
    rw [reindex_twice R S ρ hρ (fun r1 s1 r2 s2 =>
      (if (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
         u r1 s1 * star (v r2 s2) *
           ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
       else 0))]
  have hP : Work.FIArea4.pairSum R S d (shiftCoef ρ u) (shiftCoef ρ v)
      = ∑ u1 ∈ Finset.Icc 1 (2*R/ρ), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ u2 ∈ Finset.Icc 1 (2*R/ρ), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d)) then
             u (ρ*u1) s1 * star (v (ρ*u2) s2) *
               ((jacobiSym ((u1:ℕ):ℤ) (Work.FIPlan.oddPart d) *
                 jacobiSym ((u2:ℕ):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0) := by
    simp only [Work.FIArea4.pairSum, shiftCoef_apply]
    rw [sum_Icc_div_restrict R ρ (fun u1 => ∑ s1 ∈ Finset.Icc 1 (2*S),
      ∑ u2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
        (if (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d)) then
           u (ρ*u1) s1 * star (v (ρ*u2) s2) *
             ((jacobiSym ((u1:ℕ):ℤ) (Work.FIPlan.oddPart d) *
               jacobiSym ((u2:ℕ):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0)) ?_]
    · refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun s1 _ => ?_))
      rw [sum_Icc_div_restrict R ρ (fun u2 => ∑ s2 ∈ Finset.Icc 1 (2*S),
        (if (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d)) then
           u (ρ*u1) s1 * star (v (ρ*u2) s2) *
             ((jacobiSym ((u1:ℕ):ℤ) (Work.FIPlan.oddPart d) *
               jacobiSym ((u2:ℕ):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0)) ?_]
      · intro u2 _ hbig
        refine Finset.sum_eq_zero (fun s2 _ => ?_)
        by_cases hC : (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d))
        · rw [if_pos hC]
          have hz : v (ρ*u2) s2 = 0 := by
            by_contra hne
            exact absurd (hvR (ρ*u2) s2 hne) (by have := big_mul (R := R) (ρ := ρ) (u := u2) hρ hbig; omega)
          simp [hz]
        · rw [if_neg hC]
    · intro u1 _ hbig
      refine Finset.sum_eq_zero (fun s1 _ => Finset.sum_eq_zero (fun u2 _ => Finset.sum_eq_zero (fun s2 _ => ?_)))
      by_cases hC : (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d))
      · rw [if_pos hC]
        have hz : u (ρ*u1) s1 = 0 := by
          by_contra hne
          exact absurd (huR (ρ*u1) s1 hne) (by have := big_mul (R := R) (ρ := ρ) (u := u1) hρ hbig; omega)
        simp [hz]
      · rw [if_neg hC]
  rw [hL, hP]
  have hfin : (∑ u1 ∈ Finset.Icc 1 (2*R/ρ), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ u2 ∈ Finset.Icc 1 (2*R/ρ), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if ((((ρ*u1)*s2:ℕ):ZMod d) = (((ρ*u2)*s1:ℕ):ZMod d)) then
             u (ρ*u1) s1 * star (v (ρ*u2) s2) *
               ((jacobiSym (((ρ*u1:ℕ)):ℤ) (Work.FIPlan.oddPart d) *
                 jacobiSym (((ρ*u2:ℕ)):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0))
      = ∑ u1 ∈ Finset.Icc 1 (2*R/ρ), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ u2 ∈ Finset.Icc 1 (2*R/ρ), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if Nat.Coprime ρ (Work.FIPlan.oddPart d) then
             (if (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d)) then
                u (ρ*u1) s1 * star (v (ρ*u2) s2) *
                  ((jacobiSym ((u1:ℕ):ℤ) (Work.FIPlan.oddPart d) *
                    jacobiSym ((u2:ℕ):ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ) else 0)
            else 0) := by
    refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun s1 _ =>
      Finset.sum_congr rfl (fun u2 _ => Finset.sum_congr rfl (fun s2 _ =>
        inner_term_eq d ρ u1 s1 u2 s2 hd u v hu))))
  rw [hfin]
  by_cases hcop : Nat.Coprime ρ (Work.FIPlan.oddPart d) <;> simp [hcop]


/-- Bubbling the innermost `ρ`-sum out of the four box sums. -/
lemma bubble_rho {M : Type*} [AddCommMonoid M] (a b c e : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → M) :
    (∑ r1 ∈ Finset.Icc 1 a, ∑ s1 ∈ Finset.Icc 1 b, ∑ r2 ∈ Finset.Icc 1 c,
      ∑ s2 ∈ Finset.Icc 1 e, ∑ ρ ∈ Finset.Icc 1 a, F r1 s1 r2 s2 ρ)
    = ∑ ρ ∈ Finset.Icc 1 a, ∑ r1 ∈ Finset.Icc 1 a, ∑ s1 ∈ Finset.Icc 1 b,
      ∑ r2 ∈ Finset.Icc 1 c, ∑ s2 ∈ Finset.Icc 1 e, F r1 s1 r2 s2 ρ := by
  calc (∑ r1 ∈ Finset.Icc 1 a, ∑ s1 ∈ Finset.Icc 1 b, ∑ r2 ∈ Finset.Icc 1 c,
        ∑ s2 ∈ Finset.Icc 1 e, ∑ ρ ∈ Finset.Icc 1 a, F r1 s1 r2 s2 ρ)
      = ∑ r1 ∈ Finset.Icc 1 a, ∑ s1 ∈ Finset.Icc 1 b, ∑ r2 ∈ Finset.Icc 1 c,
        ∑ ρ ∈ Finset.Icc 1 a, ∑ s2 ∈ Finset.Icc 1 e, F r1 s1 r2 s2 ρ := by
        refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
          Finset.sum_congr rfl (fun r2 _ => Finset.sum_comm)))
    _ = ∑ r1 ∈ Finset.Icc 1 a, ∑ s1 ∈ Finset.Icc 1 b, ∑ ρ ∈ Finset.Icc 1 a,
        ∑ r2 ∈ Finset.Icc 1 c, ∑ s2 ∈ Finset.Icc 1 e, F r1 s1 r2 s2 ρ := by
        refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
          Finset.sum_comm))
    _ = ∑ r1 ∈ Finset.Icc 1 a, ∑ ρ ∈ Finset.Icc 1 a, ∑ s1 ∈ Finset.Icc 1 b,
        ∑ r2 ∈ Finset.Icc 1 c, ∑ s2 ∈ Finset.Icc 1 e, F r1 s1 r2 s2 ρ := by
        refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_comm)
    _ = ∑ ρ ∈ Finset.Icc 1 a, ∑ r1 ∈ Finset.Icc 1 a, ∑ s1 ∈ Finset.Icc 1 b,
        ∑ r2 ∈ Finset.Icc 1 c, ∑ s2 ∈ Finset.Icc 1 e, F r1 s1 r2 s2 ρ :=
        Finset.sum_comm

/-- **The Möbius identity for the coprime pair sum.** -/
theorem pairSumCo_eq_moebius (R S d : ℕ) (hd : 1 ≤ d) (u v : ℕ → ℕ → ℂ)
    (hu : ∀ r s, u r s ≠ 0 → Odd r) (huR : ∀ r s, u r s ≠ 0 → r ≤ 2*R)
    (hv : ∀ r s, v r s ≠ 0 → Odd r) (hvR : ∀ r s, v r s ≠ 0 → r ≤ 2*R) :
    pairSumCo R S d u v
      = ∑ ρ ∈ Finset.Icc 1 (2*R), ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
          (if Nat.Coprime ρ (Work.FIPlan.oddPart d) then
            Work.FIArea4.pairSum R S d (shiftCoef ρ u) (shiftCoef ρ v) else 0) := by
  simp only [pairSumCo]
  have hstep : (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
         (if Nat.Coprime r1 r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
            u r1 s1 * star (v r2 s2) *
              ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
          else 0))
      = ∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
        ∑ ρ ∈ Finset.Icc 1 (2*R),
          (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
             ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
               (u r1 s1 * star (v r2 s2) *
                 ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ))
           else 0) := by
    refine Finset.sum_congr rfl (fun r1 hr1 => Finset.sum_congr rfl (fun s1 _ =>
      Finset.sum_congr rfl (fun r2 hr2 => Finset.sum_congr rfl (fun s2 _ => ?_))))
    exact summand_moebius R r1 r2 (Finset.mem_Icc.mp hr1).1 (Finset.mem_Icc.mp hr2).1
      (Finset.mem_Icc.mp hr1).2 (Finset.mem_Icc.mp hr2).2
      (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d))
      (u r1 s1 * star (v r2 s2) *
        ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ))
  rw [hstep]
  rw [bubble_rho (2*R) (2*S) (2*R) (2*S) (fun r1 s1 r2 s2 ρ =>
      (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
         ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
           (u r1 s1 * star (v r2 s2) *
             ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ))
       else 0))]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  have hfac : (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
             ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
               (u r1 s1 * star (v r2 s2) *
                 ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ))
           else 0))
      = ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
        (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
          ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
             u r1 s1 * star (v r2 s2) *
               ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
           else 0)) := by
    have key : ∀ r1 s1 r2 s2 : ℕ,
        (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
           ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
             (u r1 s1 * star (v r2 s2) *
               ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ))
         else 0)
        = ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
          (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) then
             u r1 s1 * star (v r2 s2) *
               ((jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
           else 0) := by
      intro r1 s1 r2 s2
      by_cases hc : ρ ∣ r1 ∧ ρ ∣ r2 ∧ (((r1*s2:ℕ):ZMod d) = ((r2*s1:ℕ):ZMod d)) <;>
        simp [hc]
    simp only [key]
    simp only [Finset.mul_sum]
  rw [hfac, inner_eq R S d ρ hd (Finset.mem_Icc.mp hρ).1 u v hu huR hv hvR]

end
end Work.FIArea4.Vflip.Vfd
