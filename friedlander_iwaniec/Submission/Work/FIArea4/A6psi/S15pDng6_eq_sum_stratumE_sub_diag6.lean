import Mathlib
import Submission.Work.FIArea4.A6psi.Dng6Defs

namespace Work.FIArea4.A6psi

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary `if` identities -/

/-- `(if A ∧ B then f else 0) = if A then (if B then f else 0) else 0`. -/
private lemma ite_and_ite {A B : Prop} [Decidable A] [Decidable B] {M : Type*} [Zero M] (f : M) :
    (if A ∧ B then f else (0 : M)) = (if A then (if B then f else 0) else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- Splitting off the pairs with `Δ = 0`: for `Δ : ℕ`,
`(if 4d ∣ Δ then f else 0) = (if Δ = 0 then f else 0) + (if 4d ∣ Δ ∧ 0 < Δ then f else 0)`. -/
private lemma ite_dvd_eq_zero_split {d Δ : ℕ} {M : Type*} [AddCommMonoid M]
    [Decidable (4 * d ∣ Δ)] (f : M) :
    (if 4 * d ∣ Δ then f else 0)
      = (if Δ = 0 then f else 0) + (if 4 * d ∣ Δ ∧ 0 < Δ then f else 0) := by
  by_cases hΔ0 : Δ = 0
  · subst hΔ0
    simp
  · have hpos : 0 < Δ := Nat.pos_of_ne_zero hΔ0
    by_cases h4 : 4 * d ∣ Δ <;> simp [hΔ0, hpos, h4]

/-! ## The fibre decomposition of `Σ_{e | d} stratumSumE6 e` -/

/-- **Fibre decomposition of the `gcd` map**: the sum over the divisors `e` of `d` of the `e`-strata
is the sum over all pairs with the conditions `X < d`, `4d ∣ |Δ|`. -/
private lemma sum_stratumSumE6_eq (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hd : 1 ≤ d) :
    (∑ e ∈ d.divisors, stratumSumE6 Pa X j d β ℓ u t e)
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
            S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
              * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0) := by
  classical
  have hd0 : d ≠ 0 := by omega
  have hmem : ∀ z1 ∈ Work.FITop.boxN Pa, Nat.gcd d z1.re.natAbs ∈ d.divisors := by
    intro z1 hz1
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left d z1.re.natAbs, hd0⟩
  simp only [stratumSumE6]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z1 hz1 => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z2 hz2 => ?_)
  have hstep : (∑ x ∈ d.divisors,
        (if Nat.gcd d z1.re.natAbs = x ∧ (X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)
          then S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
            * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0))
      = ∑ x ∈ d.divisors,
        (if Nat.gcd d z1.re.natAbs = x
          then (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
            then S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
              * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0) else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact ite_and_ite (M := ℂ) _
  rw [hstep]
  rw [Finset.sum_ite_eq (s := d.divisors) (a := Nat.gcd d z1.re.natAbs)
    (b := fun _ => (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
        S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
          * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0))]
  rw [if_pos (hmem z1 hz1)]

/-! ## The split `Δ = 0` / `Δ ≠ 0` -/

/-- The sum over the pairs with `X < d`, `4d ∣ |Δ|` is the diagonal part (`Δ = 0`) plus `S15pDng6`
(the pairs with `Δ ≠ 0`). -/
private lemma sum_split_diag (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) :
    (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
          S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
            * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0))
      = diagSum6 Pa X j d β ℓ u t + S15pDng6 Pa X j d β ℓ u t := by
  classical
  have hpt : ∀ z1 z2 : GaussianInt,
      (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
        S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
          * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0)
        = (if Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d then
            S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
              * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0)
          + (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2 then
              S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
                * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0) := by
    intro z1 z2
    by_cases hX : X < d
    · have hthis := ite_dvd_eq_zero_split (M := ℂ) (d := d) (Δ := Work.FIPlan.absDelta z1 z2)
        (f := S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
          * Work.FIArea4.S15phase X j u t ((z1, z2), d))
      simp only [hX, true_and, and_true] at hthis ⊢
      exact hthis.trans (by ring)
    · simp [hX]
  calc (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
          S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
            * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0))
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ((if Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d then
              S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
                * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0)
            + (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
                ∧ 0 < Work.FIPlan.absDelta z1 z2 then
                S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
                  * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0)) :=
        Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => hpt z1 z2))
    _ = (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d then
            S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
              * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0))
        + (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
              ∧ 0 < Work.FIPlan.absDelta z1 z2 then
            S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
              * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ = diagSum6 Pa X j d β ℓ u t + S15pDng6 Pa X j d β ℓ u t := rfl

/-- **The round-6 per-modulus §15 sum as its strata minus the diagonal part.** -/
theorem S15pDng6_eq_sum_stratumE_sub_diag6 (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hd : 1 ≤ d) :
    Work.FIArea4.A6psi.S15pDng6 Pa X j d β ℓ u t
      = (∑ e ∈ d.divisors, Work.FIArea4.A6psi.stratumSumE6 Pa X j d β ℓ u t e)
        - Work.FIArea4.A6psi.diagSum6 Pa X j d β ℓ u t := by
  have hfib := sum_stratumSumE6_eq Pa X j d β ℓ u t hd
  have hsplit := sum_split_diag Pa X j d β ℓ u t
  rw [hfib, hsplit]
  ring

end

end Work.FIArea4.A6psi
