import Mathlib
import Submission.Work.FIArea2.Count.sec9_Z_defs
import Submission.Work.FIArea2.Count.class_delta_sum_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Divisors.sum_filter_dvd_reindex
import Submission.Work.FIArea2.Count.ZAc_fiber
import Submission.Work.FIArea2.Count.ZAc_gcdsum
import Submission.Work.FIArea2.Count.ZAc_log

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary combinatorial lemmas for the assembly -/

/-- Splitting a fivefold conjunction of indicators: the two threshold conditions attached to the
outer variables `A`, `C` and the non-degeneracy `E` are pulled out of the conjunction; the two
conditions on the inner variables `B`, `D` stay together. -/
private lemma ZAc_bound_ite_split5 (A B C D E : Prop) [Decidable A] [Decidable B] [Decidable C]
    [Decidable D] [Decidable E] (x : ℝ) :
    (if A ∧ B ∧ C ∧ D ∧ E then x else 0)
      = (if A ∧ C ∧ E then (if B ∧ D then x else 0) else 0) := by
  by_cases ha : A <;> by_cases hb : B <;> by_cases hc : C <;> by_cases hd : D <;>
    by_cases he : E <;> simp [ha, hb, hc, hd, he]

/-- A propositional factor independent of the summation indices can be pulled out of a double
sum. -/
private lemma ZAc_bound_sum₂_ite_pull {α β : Type*} (s : Finset α) (t : Finset β) (P : Prop)
    [Decidable P] (g : α → β → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, (if P then g x y else 0)) = (if P then ∑ x ∈ s, ∑ y ∈ t, g x y else 0) := by
  by_cases hP : P <;> simp [hP]

/-- **§9 (9.5), the non-degenerate half `Re Λ ≠ 0`, in coordinates.**

With `I = Finset.Icc (-R) R`, `0 ≤ R`, `0 < ϑ ≤ 1`, `Nr ≥ 1`, `thr = √(ϑ Nr)`, `2R+1 ≤ 8√Nr`:

  `ZAc R h₁ h₂ thr = Σ_{(r₁,s₁,r₂,s₂) ∈ I⁴} [thr < |r₁|, |s₁|, |r₂|, |s₂|] [Re Λ ≠ 0] τ(Δ)³(Λ,Δ)/|Δ|`

(`Δ = r₁s₂−r₂s₁`, `Re Λ = r₁h₁²−r₂h₂²`, `(Λ,Δ) = gcd(|Re Λ|,|Im Λ|,|Δ|)`) is
`≤ C ϑ^{-1/2}(log(Nr+2))⁸ · UB R h₁ h₂`, where
`UB R h₁ h₂ = Σ_{(u₁,u₂) ∈ I²} (u₁,u₂)·τ(u₁h₁²−u₂h₂²)⁴`.

Plan: `(Λ,Δ) = Σ_{d | (Λ,Δ)} φ(d)` (`Nat.sum_totient`), so with `d` ranging over `Icc 1 Dm`
(valid because the hypothesis gives `cdg ≤ Dm`), group the four-fold sum by `(r₁,r₂)` and bound,
for each pair, the `(s₁,s₂)`-sum by `Work.FIArea2.Count.class_delta_sum_le`
(`Σ_{d | Δ ≠ 0} τ(Δ)³/|Δ| ≤ C(1 + (r₁,r₂)(2R+1)/|r₁|)(τ(d)³/d)(log(2R²+2))⁸`); the count factor
is `≤ 9 ϑ^{-1/2}(r₁,r₂)` since `thr < |r₁|` and `thr = √(ϑ Nr)` give
`(2R+1)/|r₁| ≤ 8√Nr/√(ϑNr) = 8ϑ^{-1/2}`; then swap the `d`- and `(r₁,r₂)`-sums back and use
`Σ_{d | m} φ(d)τ(d)³/d ≤ τ(m)⁴` (`m = Re Λ ≠ 0`, `φ(d) ≤ d`, `τ(d) ≤ τ(m)` for `d | m`); finally
`(log(2R²+2))⁸ ≤ (1+log34)⁸(log(Nr+2))⁸` because `R ≤ 4√Nr`. -/
theorem ZAc_bound_eight :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (h1 h2 : ℤ) (thr Nr ϑ : ℝ) (Dm : ℕ),
      0 < ϑ → ϑ ≤ 1 → 1 ≤ Nr → 0 ≤ R → thr = Real.sqrt (ϑ * Nr) →
      (2 * (R : ℝ) + 1) ≤ 8 * Real.sqrt Nr → 1 ≤ Dm →
      (∀ r1 ∈ Finset.Icc (-R) R, ∀ s1 ∈ Finset.Icc (-R) R, ∀ r2 ∈ Finset.Icc (-R) R,
        ∀ s2 ∈ Finset.Icc (-R) R, Work.FIArea2.Count.cdg h1 h2 r1 s1 r2 s2 ≤ Dm) →
      Work.FIArea2.Count.ZAc R h1 h2 thr
        ≤ C * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ (8 : ℕ) * Work.FIArea2.Count.UB R h1 h2 := by
  obtain ⟨Cf, hCfpos, hCf⟩ := ZAc_fiber
  obtain ⟨Cg, hCgpos, hCg⟩ := ZAc_gcdsum
  obtain ⟨Cl, hClpos, hCl⟩ := ZAc_log
  refine ⟨Cf * Cl * Cg, by positivity, ?_⟩
  intro R h1 h2 thr Nr ϑ Dm hϑpos hϑle hNr hR0 hthr h2R hDm1 hcdg
  -- `thr > 0`, since `thr = √(ϑ Nr)` with `ϑ > 0`, `Nr ≥ 1`.
  have hthrpos : 0 < thr := by
    rw [hthr]
    exact Real.sqrt_pos_of_pos (by positivity)
  -- ## Step 1: group `ZAc` by the pair `(r₁,r₂)` and pull the `(s₁,s₂)`-sum inside.
  have hZeq : ZAc R h1 h2 thr
      = ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
            (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
              (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
          else 0) := by
    have hstep1 : (∑ r1 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          ∑ s2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(s1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ thr < |(s2 : ℝ)|
              ∧ tA h1 h2 r1 r2 ≠ 0 then ZW h1 h2 r1 s1 r2 s2 else 0))
        = (∑ r1 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          ∑ s2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
            (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0)
          else 0)) :=
      Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
        Finset.sum_congr rfl (fun r2 _ => Finset.sum_congr rfl (fun s2 _ =>
          ZAc_bound_ite_split5 (thr < |(r1 : ℝ)|) (thr < |(s1 : ℝ)|) (thr < |(r2 : ℝ)|)
            (thr < |(s2 : ℝ)|) (tA h1 h2 r1 r2 ≠ 0) (ZW h1 h2 r1 s1 r2 s2)))))
    have hstep2 : (∑ r1 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          ∑ s2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
            (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0)
          else 0))
        = (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R,
          ∑ s2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
            (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0)
          else 0)) :=
      Finset.sum_congr rfl (fun r1 _ => Finset.sum_comm)
    have hstep3 : (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R,
          ∑ s2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
            (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0)
          else 0))
        = (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
            (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
              (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
          else 0)) := by
      apply Finset.sum_congr rfl
      intro r1 _
      apply Finset.sum_congr rfl
      intro r2 _
      exact ZAc_bound_sum₂_ite_pull (Finset.Icc (-R) R) (Finset.Icc (-R) R)
        (thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0)
        (fun s1 s2 => (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
    simp only [ZAc]
    exact hstep1.trans (hstep2.trans hstep3)
  -- ## Step 2: nonnegativity of the per-pair weight.
  have hXnn : ∀ r1 r2 : ℤ,
      0 ≤ (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
          * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4) := by
    intro r1 r2
    apply mul_nonneg _ (by positivity)
    have h2R1 : (0 : ℝ) ≤ 2 * (R : ℝ) + 1 := by
      have hR0' : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR0
      linarith
    exact add_nonneg zero_le_one (div_nonneg (mul_nonneg (by positivity) h2R1) (abs_nonneg _))
  -- ## Step 3: the per-`(r₁,r₂)` fiber bound (`ZAc_fiber`).
  have hpt : ∀ r1 ∈ Finset.Icc (-R) R, ∀ r2 ∈ Finset.Icc (-R) R,
      (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
        (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
          (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
      else 0)
      ≤ (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
        (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
          (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
            * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4)
        else 0) := by
    intro r1 hr1 r2 hr2
    by_cases hP : thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0
    · rw [if_pos hP]
      have hr1ne : r1 ≠ 0 := by
        have hgt : (0 : ℝ) < |(r1 : ℝ)| := lt_trans hthrpos hP.1
        intro h0
        rw [h0] at hgt
        simp at hgt
      have hfib := hCf R h1 h2 r1 r2 thr Dm hR0 hDm1 hr1 hr2 hr1ne hP.2.2
        (fun s1 hs1 s2 hs2 => hcdg r1 hr1 s1 hs1 r2 hr2 s2 hs2)
      rw [if_pos ⟨hP.1, hP.2.1⟩]
      exact le_trans hfib (le_of_eq (by ring))
    · rw [if_neg hP]
      by_cases hQ : thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)|
      · rw [if_pos hQ]
        exact mul_nonneg (mul_nonneg hCfpos.le (by positivity)) (hXnn r1 r2)
      · rw [if_neg hQ]
        simp
  -- ## Step 4: sum the per-pair bounds and factor out the constant and the logarithm.
  have hsum : (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
        (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
          (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
            (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
        else 0))
      ≤ (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
        (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
            (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
              * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4)
          else 0)) := by
    have hA1 : (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ tA h1 h2 r1 r2 ≠ 0 then
            (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
              (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
          else 0))
        ≤ (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
            (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
              (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
                (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
                  * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4)
              else 0)) :=
      Finset.sum_le_sum (fun r1 hr1 => Finset.sum_le_sum (fun r2 hr2 => hpt r1 hr1 r2 hr2))
    have hA2 : (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
            (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
              (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
                (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
                  * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4)
              else 0))
        = (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
            (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
              (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
                (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
                  * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4)
              else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r1 _
      rw [Finset.mul_sum]
      try rfl
    exact hA1.trans (le_of_eq hA2)
  have hmain : ZAc R h1 h2 thr
      ≤ (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
        (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
            (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
              * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4)
          else 0)) := by
    rw [hZeq]
    exact hsum
  -- ## Step 5: the arithmetic core, the logarithmic conversion, and the assembly.
  have hg := hCg R h1 h2 thr Nr ϑ hϑpos hϑle hNr hR0 hthr h2R
  have hl := hCl R Nr hR0 hNr h2R
  have hUBnn : 0 ≤ UB R h1 h2 := by
    rw [UB]
    apply Finset.sum_nonneg
    intro u1 _
    apply Finset.sum_nonneg
    intro u2 _
    exact mul_nonneg (by positivity) (by positivity)
  have hϑinvnn : 0 ≤ ϑ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hϑpos.le _
  have hKnn : 0 ≤ Cg * ϑ ^ (-(1 : ℝ) / 2) * UB R h1 h2 :=
    mul_nonneg (mul_nonneg hCgpos.le hϑinvnn) hUBnn
  have hLnn : 0 ≤ (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8 := by positivity
  have s1 : (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
        (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
            (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
              * (((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) ^ 4)
          else 0))
      ≤ (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
        (Cg * ϑ ^ (-(1 : ℝ) / 2) * UB R h1 h2) :=
    mul_le_mul_of_nonneg_left hg (mul_nonneg hCfpos.le hLnn)
  have s2 : (Cf * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8) *
        (Cg * ϑ ^ (-(1 : ℝ) / 2) * UB R h1 h2)
      ≤ (Cf * (Cl * (Real.log (Nr + 2)) ^ 8)) *
        (Cg * ϑ ^ (-(1 : ℝ) / 2) * UB R h1 h2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hCfpos.le) hKnn
  have s3 : (Cf * (Cl * (Real.log (Nr + 2)) ^ 8)) *
        (Cg * ϑ ^ (-(1 : ℝ) / 2) * UB R h1 h2)
      = (Cf * Cl * Cg) * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8 * UB R h1 h2 := by
    ring
  exact le_trans (le_trans (le_trans hmain s1) s2) (le_of_eq s3)

end Work.FIArea2.Count
