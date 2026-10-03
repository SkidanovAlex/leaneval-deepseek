/-
# Vocabulary for the "bilinear" form of the dyadic dual variance

After the Poisson step, the dyadic dual variance `Wdyad` is bounded by the bilinear form in the
coefficients `γ` whose kernel is `KK (𝓕 (gmajorC S))` (see `Work.FIArea4.Wdyad_bilinear`).  This
module collects

* `Expo`, the explicit Poisson-expanded form of `normSq (TZ D R S γ r s)` at a fixed `r`
  (i.e. the right-hand side of `Work.FIArea4.Wdyad_expansion` with `F = gmajorC S`),
* the pointwise identity `normSq_TZ_expansion` expressing the squared modulus of the class sum
  `TZ` as a sum over pairs `d₁,d₂` of a single residue class modulo `[d₁,d₂]` (this is what makes
  Poisson summation applicable), together with its ingredients.

Everything here is elementary; the analytic content (Poisson summation, summability) lives in
the modules that use these definitions.
-/
import Mathlib
import Submission.Work.FIArea4.WdyadSetup
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Work.FIArea4.WdyadExpansionDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators FourierTransform

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-- The Poisson-expanded form of `normSq (TZ D R S γ r s)`: the right-hand side of the expansion
of `Submission/Work/FIArea4/Wdyad_expansion.lean` evaluated at `F = gmajorC S`. -/
def Expo (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
    (if Nat.Coprime r (d1 * d2) then
      ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
        ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ) *
        ((1 / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
          ∑' k : ℤ, (FourierTransform.fourier (gmajorC (S : ℝ)))
              ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (Nat.lcm d1 d2),
              γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
                  ((Nat.lcm d1 d2 : ℕ) : ℝ))))
    else 0)

/-! ## The entries `MentryZ` as a Jacobi symbol times an indicator -/

lemma MentryZ_eq (d a r : ℕ) (s : ℤ) :
    MentryZ d a r s
      = (if Nat.Coprime r d
         then ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ) * cind d s (r * a)
         else 0) := by
  unfold MentryZ cind
  rw [Nat.cast_mul]
  by_cases h : Nat.Coprime r d <;>
    by_cases h2 : (s : ZMod d) = (r : ZMod d) * (a : ZMod d) <;> simp [h, h2]

lemma conj_cind (d : ℕ) (s : ℤ) (c : ℕ) : (starRingEnd ℂ) (cind d s c) = cind d s c := by
  unfold cind; split <;> simp

lemma conj_MentryZ_eq (d a r : ℕ) (s : ℤ) :
    (starRingEnd ℂ) (MentryZ d a r s)
      = (if Nat.Coprime r d
         then ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ) * cind d s (r * a)
         else 0) := by
  rw [MentryZ_eq]
  by_cases h : Nat.Coprime r d
  · rw [if_pos h, map_mul, map_intCast, conj_cind]
  · rw [if_neg h, map_zero]

/-- The Jacobi weight `wChar` is the product of the two local Jacobi symbols. -/
lemma wChar_eq (d1 d2 r : ℕ) [NeZero (Work.FIPlan.oddPart d1)] [NeZero (Work.FIPlan.oddPart d2)] :
    wChar d1 d2 r
      = (if Nat.Coprime r (d1 * d2) then
          ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
            ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)
         else 0) := by
  unfold wChar
  by_cases h : Nat.Coprime r (d1 * d2)
  · rw [if_pos h, if_pos h, jacobiSym.mul_right]
    push_cast
    ring
  · rw [if_neg h, if_neg h]

/-! ## The pairwise expansion -/

/-- The product of the two `d`-th class sums, evaluated: it is the Jacobi symbol times a single
sum over the residue classes modulo `[d₁,d₂]`. -/
lemma pair_eq_expansion {d1 d2 r : ℕ} [NeZero d1] [NeZero d2] [NeZero (Nat.lcm d1 d2)]
    (hc : Nat.Coprime r (d1 * d2)) (γ : ℕ → ℕ → ℂ) (s : ℤ) :
    (∑ a ∈ Finset.range d1, γ a d1 * MentryZ d1 a r s) *
        (∑ a ∈ Finset.range d2, (starRingEnd ℂ) (γ a d2 * MentryZ d2 a r s))
      = ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
          ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ) *
          (∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              cind (Nat.lcm d1 d2) s (r * a)) := by
  obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hc
  rw [Finset.sum_mul_sum]
  have hcd := cind_double (d1 := d1) (d2 := d2) (r := r) hc
      (fun a1 a2 => γ a1 d1 * (starRingEnd ℂ) (γ a2 d2)) s
  have hterm : ∀ a1 ∈ Finset.range d1, ∀ a2 ∈ Finset.range d2,
      (γ a1 d1 * MentryZ d1 a1 r s) * (starRingEnd ℂ) (γ a2 d2 * MentryZ d2 a2 r s)
        = ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
            ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ) *
            (γ a1 d1 * (starRingEnd ℂ) (γ a2 d2) * cind d1 s (r * a1) * cind d2 s (r * a2)) := by
    intro a1 _ a2 _
    rw [MentryZ_eq, if_pos h1, map_mul, MentryZ_eq, if_pos h2, map_mul, map_intCast, conj_cind]
    ring
  rw [Finset.sum_congr rfl (fun a1 ha1 => Finset.sum_congr rfl (fun a2 ha2 => hterm a1 ha1 a2 ha2))]
  simp only [← Finset.mul_sum]
  rw [hcd]

/-- **The pointwise expansion of the squared modulus of the class sum.** -/
theorem normSq_TZ_expansion (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ) (s : ℤ) :
    ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ)
      = ∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
          (if Nat.Coprime r (d1 * d2) then
            ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
              ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ) *
              (∑ a ∈ Finset.range (Nat.lcm d1 d2),
                γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                  cind (Nat.lcm d1 d2) s (r * a))
          else 0) := by
  rw [Complex.normSq_eq_conj_mul_self, mul_comm]
  unfold TZ
  rw [map_sum]
  simp only [map_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => ?_))
  obtain ⟨hd1a, hd1b⟩ := Finset.mem_Ioc.mp hd1
  obtain ⟨hd2a, hd2b⟩ := Finset.mem_Ioc.mp hd2
  have hd1ne : d1 ≠ 0 := by omega
  have hd2ne : d2 ≠ 0 := by omega
  haveI : NeZero d1 := ⟨hd1ne⟩
  haveI : NeZero d2 := ⟨hd2ne⟩
  haveI : NeZero (Nat.lcm d1 d2) := ⟨Nat.lcm_ne_zero hd1ne hd2ne⟩
  by_cases hc : Nat.Coprime r (d1 * d2)
  · rw [if_pos hc]
    exact pair_eq_expansion hc γ s
  · rw [if_neg hc]
    have hnotand : ¬ (Nat.Coprime r d1 ∧ Nat.Coprime r d2) :=
      fun h => hc (Nat.coprime_mul_iff_right.mpr h)
    rcases not_and_or.mp hnotand with h | h
    · have hz : (∑ a ∈ Finset.range d1, γ a d1 * MentryZ d1 a r s) = 0 := by
        apply Finset.sum_eq_zero; intro a _
        rw [MentryZ_eq, if_neg h, mul_zero]
      rw [hz, zero_mul]
    · have hz : (∑ a ∈ Finset.range d2, (starRingEnd ℂ) (γ a d2 * MentryZ d2 a r s)) = 0 := by
        apply Finset.sum_eq_zero; intro a _
        rw [MentryZ_eq, if_neg h, mul_zero, map_zero]
      rw [hz, mul_zero]

end

end Work.FIArea4
