/-
# Setup for the coprime-constrained large sieve (`pairSum_large_sieve_coprime`)

This module collects the definitions and elementary lemmas used by the proof of
`Work.FIArea4.Vflip.Vfd.pairSum_large_sieve_coprime`:

* `moebius_sum_eq`: the Möbius indicator `∑_{d | n} μ d = [n = 1]`;
* `sum_filter_dvd_Icc`: reindexing the multiples of `ρ` in `[1, 2R]`;
* `shiftCoef ρ α`: the array `(r,s) ↦ α (ρ * r) s`;
* `pairSumCo R S d u v`: the pair sum with the extra coprimality condition `(r₁, r₂) = 1`.
-/
import Mathlib
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `∑_{d | n} μ(d) = [n = 1]`, over `ℤ`. -/
lemma moebius_sum_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius)]
  rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- The complex version of `moebius_sum_eq`. -/
lemma moebius_sum_eq_complex (n : ℕ) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (moebius_sum_eq n)
  simpa using h

/-- Reindexing the multiples of `ρ` in `[1, 2R]` by `u ↦ ρ * u`. -/
lemma sum_filter_dvd_Icc {ρ R : ℕ} (hρ : 1 ≤ ρ) (g : ℕ → ℂ) :
    ∑ r ∈ (Finset.Icc 1 (2*R)).filter (fun r => ρ ∣ r), g r
      = ∑ u ∈ Finset.Icc 1 (2*R/ρ), g (ρ*u) := by
  apply Finset.sum_bij (fun r _ => r / ρ)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hr1, hr2⟩, ⟨k, hk⟩⟩ := hr
    subst hk
    simp only [Finset.mem_Icc]
    rw [Nat.mul_div_cancel_left k hρ]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp at hr1
      · exact hk0
    · rw [Nat.le_div_iff_mul_le hρ]
      calc k * ρ = ρ * k := by ring
        _ ≤ 2*R := hr2
  · intro r1 hr1 r2 hr2 h
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr1 hr2
    obtain ⟨-, ⟨k1, hk1⟩⟩ := hr1
    obtain ⟨-, ⟨k2, hk2⟩⟩ := hr2
    rw [hk1, hk2, Nat.mul_div_cancel_left k1 hρ, Nat.mul_div_cancel_left k2 hρ] at h
    rw [hk1, hk2, h]
  · intro u hu
    simp only [Finset.mem_Icc] at hu
    refine ⟨ρ*u, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith [hu.1], ?_⟩, dvd_mul_right ρ u⟩
      calc ρ * u ≤ ρ * (2*R/ρ) := Nat.mul_le_mul_left ρ hu.2
        _ ≤ 2*R := Nat.mul_div_le _ _
    · exact Nat.mul_div_cancel_left u hρ
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨-, ⟨k, hk⟩⟩ := hr
    subst hk
    rw [Nat.mul_div_cancel_left k hρ]

/-- The coefficient array `α` with its first coordinate scaled by `ρ`: `(r,s) ↦ α (ρ*r) s`. -/
def shiftCoef (ρ : ℕ) (α : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ := fun r s => α (ρ * r) s

@[simp] lemma shiftCoef_apply (ρ : ℕ) (α : ℕ → ℕ → ℂ) (r s : ℕ) :
    shiftCoef ρ α r s = α (ρ * r) s := rfl

/-- Scaling preserves a support lying on odd `r`. -/
lemma shiftCoef_odd {ρ : ℕ} {α : ℕ → ℕ → ℂ} (hα : ∀ r s, α r s ≠ 0 → Odd r) :
    ∀ r s, shiftCoef ρ α r s ≠ 0 → Odd r := by
  intro r s h
  rw [shiftCoef_apply] at h
  exact (Nat.odd_mul.mp (hα (ρ*r) s h)).2

/-- If `α` is supported on `r ≤ 2R`, then `shiftCoef ρ α` is supported on `r ≤ 2R/ρ`. -/
lemma shiftCoef_support {ρ R : ℕ} {α : ℕ → ℕ → ℂ}
    (hα : ∀ r s, α r s ≠ 0 → r ≤ 2*R) (hρ : 1 ≤ ρ) :
    ∀ r s, shiftCoef ρ α r s ≠ 0 → r ≤ 2*R/ρ := by
  intro r s h
  rw [shiftCoef_apply] at h
  rw [Nat.le_div_iff_mul_le hρ]
  calc r * ρ = ρ * r := by ring
    _ ≤ 2*R := hα (ρ*r) s h

/-- The pair sum with the extra coprimality condition `(r₁, r₂) = 1`. -/
def pairSumCo (R S d : ℕ) (u v : ℕ → ℕ → ℂ) : ℂ :=
  ∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
    ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
      (if Nat.Coprime r1 r2 ∧ ((r1*s2 : ℕ) : ZMod d) = ((r2*s1 : ℕ) : ZMod d) then
        u r1 s1 * star (v r2 s2) *
          ((jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
       else 0)

/-- The complex Möbius indicator of coprimality, for arguments in the box `[1, 2R]`. -/
lemma coprime_indicator_sum (R r1 r2 : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    (h1 : r1 ≤ 2*R) (h2 : r2 ≤ 2*R) :
    (if Nat.Coprime r1 r2 then (1:ℂ) else 0)
      = ∑ ρ ∈ Finset.Icc 1 (2*R),
          (if ρ ∣ r1 ∧ ρ ∣ r2 then ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) else 0) := by
  have hr1' : 0 < r1 := by omega
  rw [← Finset.sum_filter]
  have hset : (Finset.Icc 1 (2*R)).filter (fun ρ => ρ ∣ r1 ∧ ρ ∣ r2)
      = (Nat.gcd r1 r2).divisors := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hρ1, hρ2⟩, hd1, hd2⟩
      exact ⟨Nat.dvd_gcd hd1 hd2, (Nat.gcd_pos_of_pos_left r2 hr1').ne'⟩
    · rintro ⟨hg, -⟩
      have hgcdpos : 0 < Nat.gcd r1 r2 := Nat.gcd_pos_of_pos_left r2 hr1'
      have hρpos : 0 < ρ := Nat.pos_of_dvd_of_pos hg hgcdpos
      have hle1 : ρ ≤ Nat.gcd r1 r2 := Nat.le_of_dvd hgcdpos hg
      have hle2 : Nat.gcd r1 r2 ≤ r1 := Nat.gcd_le_left r2 hr1'
      exact ⟨⟨hρpos, by omega⟩, hg.trans (Nat.gcd_dvd_left r1 r2),
        hg.trans (Nat.gcd_dvd_right r1 r2)⟩
  rw [hset, ← moebius_sum_eq_complex (Nat.gcd r1 r2)]

/-- The square of a Jacobi symbol `(ρ | d')` with `d' = oddPart d` is the coprimality indicator. -/
lemma jacobiSym_sq_eq (ρ d : ℕ) (hd : 1 ≤ d) :
    jacobiSym ((ρ:ℕ):ℤ) (Work.FIPlan.oddPart d) ^ 2
      = if Nat.Coprime ρ (Work.FIPlan.oddPart d) then 1 else 0 := by
  have hb : Work.FIPlan.oddPart d ≠ 0 := by
    have hmul : 2 ^ d.factorization 2 * Work.FIPlan.oddPart d = d := by
      unfold Work.FIPlan.oddPart
      exact Nat.mul_div_cancel' (Nat.ordProj_dvd d 2)
    intro h; rw [h, mul_zero] at hmul; omega
  by_cases hc : Nat.Coprime ρ (Work.FIPlan.oddPart d)
  · rw [if_pos hc, jacobiSym.sq_one]
    rw [Nat.Coprime, ← Int.gcd_natCast_natCast ρ (Work.FIPlan.oddPart d)] at hc
    exact hc
  · rw [if_neg hc]
    have h0 : jacobiSym ((ρ:ℕ):ℤ) (Work.FIPlan.oddPart d) = 0 := by
      rw [jacobiSym.eq_zero_iff]
      refine ⟨hb, ?_⟩
      intro hg
      exact hc (by rw [Nat.Coprime, ← Int.gcd_natCast_natCast ρ (Work.FIPlan.oddPart d)]; exact hg)
    rw [h0]; ring

/-- For a unit `ρ` modulo `d`, the congruence `ρ u₁ s₂ ≡ ρ u₂ s₁ (mod d)` is equivalent to
`u₁ s₂ ≡ u₂ s₁ (mod d)`. -/
lemma zmod_scale_eq_iff {d ρ u1 s1 u2 s2 : ℕ} (hu : IsUnit ((ρ:ℕ):ZMod d)) :
    (((ρ*u1*s2 : ℕ):ZMod d) = ((ρ*u2*s1 : ℕ):ZMod d))
      ↔ (((u1*s2:ℕ):ZMod d) = ((u2*s1:ℕ):ZMod d)) := by
  have e1 : ((ρ*u1*s2 : ℕ):ZMod d) = ((ρ:ℕ):ZMod d) * ((u1*s2 : ℕ):ZMod d) := by
    push_cast; ring
  have e2 : ((ρ*u2*s1 : ℕ):ZMod d) = ((ρ:ℕ):ZMod d) * ((u2*s1 : ℕ):ZMod d) := by
    push_cast; ring
  rw [e1, e2]
  exact ⟨hu.mul_left_cancel, fun h => by rw [h]⟩


/-- The four terms of the bracket `p14T11` (in the order `D^{-1/2}RS`, `D√(RS)(RS)^ε`,
`RS^{3/4}(RS)^ε`, `SR^{3/4}(RS)^ε`). -/
def pT1 (D R S : ℕ) : ℝ := (D:ℝ) ^ (-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)
def pT2 (D R S : ℕ) (ε : ℝ) : ℝ := (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^ε)
def pT3 (D R S : ℕ) (ε : ℝ) : ℝ := (R:ℝ) * (S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε)
def pT4 (D R S : ℕ) (ε : ℝ) : ℝ := (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε)

/-- `p14T11` is the sum of its four terms. -/
lemma p14T11_eq_sum (D R S : ℕ) (ε : ℝ) :
    Work.FIArea4.p14T11 D R S ε = pT1 D R S + pT2 D R S ε + pT3 D R S ε + pT4 D R S ε := by
  rw [Work.FIArea4.p14T11]; unfold pT1 pT2 pT3 pT4; ring

lemma pT1_nonneg (D R S : ℕ) : 0 ≤ pT1 D R S := by unfold pT1; positivity
lemma pT2_nonneg (D R S : ℕ) (ε : ℝ) : 0 ≤ pT2 D R S ε := by unfold pT2; positivity
lemma pT3_nonneg (D R S : ℕ) (ε : ℝ) : 0 ≤ pT3 D R S ε := by unfold pT3; positivity
lemma pT4_nonneg (D R S : ℕ) (ε : ℝ) : 0 ≤ pT4 D R S ε := by unfold pT4; positivity


end

end Work.FIArea4.Vflip.Vfd
