import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farPre
import Submission.Work.FIArea4.Vflip.Vfd.farGadgets
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.far_reduction
import Submission.Work.FIArea4.Vflip.Vfd.farInner_dyadic_bound
import Submission.Work.FIArea4.Vflip.Vfd.farInner_mc_bound
import Submission.Work.FIArea4.Vflip.Vfd.far_sum_numerics
import Submission.Work.FIArea4.A4varbounds

/-!
# The far part of the flipped-moduli bound (FI §12, (12.10)–(12.17))

The bound for the *far* part of the smoothly cut bilinear form,
`Σ_{p,q ∈ boxF} α p.1 p.2 · conj (α q.1 q.2) · nearCut a b (xPair p q) · pairWeight D p q`.

The strategy is the paper's §12: reduce the pair by its common divisor `c`, flip the modulus `d`
to the complementary divisor `q` of `pairAbs`, separate the variables by the Fourier–Mellin
transform (`separation_ineq_nearCut`), apply the large sieve (`pairSum_large_sieve`) in each
dyadic range of `q`, and sum over `q`, `m ∣ c` and `c`.

The assembly is the one described in `NOTES_REMAINING.md` (P8): the combinatorial reduction
`far_reduction`, the per-`(m,c)` dyadic numerics `farInner_mc_bound` (built on the Fourier–Mellin
separation and the twisted coprime large sieve, `farInner_dyadic_bound`), and the `(m,c)`-summation
`far_sum_numerics`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary lemmas for the bookkeeping -/

lemma p14L2_zero_left (S : ℕ) (β : ℕ → ℕ → ℂ) : Work.FIArea4.p14L2 0 S β = 0 := by
  simp [Work.FIArea4.p14L2]

lemma farInner_eq_zero_of_not_dvd (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c Q1 Q2 : ℕ)
    (h : ¬ m ∣ c) : farInner D R S a b α m c Q1 Q2 = 0 := by
  rw [farInner]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  obtain ⟨-, -, -, -, -, -, -, hfc⟩ := mem_farSet.mp hi
  exact absurd hfc.2.2.2.2.2.2.2.2.2.2.1 h

lemma farInner_eq_zero_of_c_eq_zero (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m Q1 Q2 : ℕ) :
    farInner D R S a b α m 0 Q1 Q2 = 0 := by
  rw [farInner]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  obtain ⟨-, -, -, -, -, -, -, hfc⟩ := mem_farSet.mp hi
  exact absurd hfc.1 (by norm_num)

/-- The sum of the norms of the dyadic `(m,c,Q)`-pieces against the `(m,c)`-term of the numerics
`far_sum_numerics`. -/
theorem Vflip_far_bound (h11 : Work.FIArea4.p14Prop111All) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (H a b : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) →
      a = 2 * (S : ℝ) / (H * (R : ℝ)) → b = 2 * (S : ℝ) / (R : ℝ) →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      (∀ r s, α r s ≠ 0 → ∀ r' s', α r' s' ≠ 0 → r % 8 = r' % 8) →
      ‖∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
          α p.1 p.2 * star (α q.1 q.2) *
            ((Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q) : ℝ)
              * Work.FIArea4.Vflip.pairWeight D p q)‖
        ≤ C * ((Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
                * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
              + (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
                * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
                    + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                    + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)))
            * Work.FIArea4.p14Ener R S α := by
  obtain ⟨Cd, hCd, hdy⟩ := farInner_dyadic_bound h11 ε hε
  obtain ⟨Cnum, hCnum, hnum⟩ := far_sum_numerics ε hε
  have hmcF := farInner_mc_bound Cd ε hCd hε hdy
  refine ⟨100 * Cd * Cnum, by positivity, ?_⟩
  intro D R S H a b α hD hR hS hDle hDsq hH ha hb hcop hbox hcls
  have hHpos : 0 < H := far_H_pos hR hS hD hH
  have hapos : 0 < a := far_a_pos hR hS hHpos ha
  have hred := far_reduction D R S a b α hapos hcop hcls
  have hnum' := hnum D R S H α hD hR hS hDle hDsq hH hbox
  -- The per-`(m,c)` comparison of the reduced sum with the LHS of `far_sum_numerics`.
  have hmc : (∑ m ∈ Finset.range (2*R+1), ∑ c ∈ Finset.range (2*R+1),
        ((∑ j ∈ Finset.range (4*R*S),
            ‖farInner D R S a b α m c (2^j) (2^(j+1))‖)
          + ‖farInner D R S a b α m c 0 1‖))
      ≤ (100 * Cd) * (∑ m ∈ Finset.range (2*R+1), ∑ c ∈ Finset.range (2*R+1),
          if m ∣ c then
            (Real.log (2*H)+1)^2 * (Real.log (2*(cR c R : ℝ))+1) *
              ( (m * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
                + ((R:ℝ)*(S:ℝ))^(ε/4)
                  * ( m * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
                      + (Real.log (160*H)+1) * ((cR c R:ℝ)*(S:ℝ)^((3:ℝ)/4)
                          + (S:ℝ)*(cR c R:ℝ)^((3:ℝ)/4)) ) )
              * Work.FIArea4.p14L2 (cR c R) S (redA c α)
          else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m hm => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun c hc => ?_)
    by_cases hdvd : m ∣ c
    · rw [if_pos hdvd]
      by_cases hc0 : c = 0
      · subst hc0
        have hL1 : (∑ j ∈ Finset.range (4*R*S),
              ‖farInner D R S a b α m 0 (2^j) (2^(j+1))‖) = 0 :=
          Finset.sum_eq_zero (fun j _ => by
            rw [farInner_eq_zero_of_c_eq_zero D R S a b α m (2^j) (2^(j+1)), norm_zero])
        have hL2 : ‖farInner D R S a b α m 0 0 1‖ = 0 := by
          rw [farInner_eq_zero_of_c_eq_zero D R S a b α m 0 1, norm_zero]
        have hX0 : cR 0 R = 0 := by simp [cR]
        rw [hL1, hL2, add_zero, hX0]
        simp [Work.FIArea4.p14L2]
      · have hcpos : 1 ≤ c := by omega
        have hmpos : 1 ≤ m := Nat.pos_of_dvd_of_pos hdvd (by omega)
        exact le_trans
          (hmcF D R S m c a b H α hD hR hS hmpos hcpos hdvd hDle hDsq hH ha hb hcop hbox)
          (le_of_eq (mul_assoc _ _ _))
    · rw [if_neg hdvd]
      have hL1 : (∑ j ∈ Finset.range (4*R*S),
            ‖farInner D R S a b α m c (2^j) (2^(j+1))‖) = 0 :=
          Finset.sum_eq_zero (fun j _ => by
            rw [farInner_eq_zero_of_not_dvd D R S a b α m c (2^j) (2^(j+1)) hdvd, norm_zero])
      have hL2 : ‖farInner D R S a b α m c 0 1‖ = 0 := by
        rw [farInner_eq_zero_of_not_dvd D R S a b α m c 0 1 hdvd, norm_zero]
      rw [hL1, hL2, add_zero, mul_zero]
  calc ‖∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
        α p.1 p.2 * star (α q.1 q.2) *
          ((Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q) : ℝ)
            * Work.FIArea4.Vflip.pairWeight D p q)‖
      ≤ ∑ m ∈ Finset.range (2*R+1), ∑ c ∈ Finset.range (2*R+1),
          ((∑ j ∈ Finset.range (4*R*S),
              ‖farInner D R S a b α m c (2^j) (2^(j+1))‖)
            + ‖farInner D R S a b α m c 0 1‖) := hred
    _ ≤ (100 * Cd) * (∑ m ∈ Finset.range (2*R+1), ∑ c ∈ Finset.range (2*R+1),
          if m ∣ c then
            (Real.log (2*H)+1)^2 * (Real.log (2*(cR c R : ℝ))+1) *
              ( (m * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
                + ((R:ℝ)*(S:ℝ))^(ε/4)
                  * ( m * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
                      + (Real.log (160*H)+1) * ((cR c R:ℝ)*(S:ℝ)^((3:ℝ)/4)
                          + (S:ℝ)*(cR c R:ℝ)^((3:ℝ)/4)) ) )
              * Work.FIArea4.p14L2 (cR c R) S (redA c α)
          else 0) := hmc
    _ ≤ (100 * Cd) * (Cnum * ((Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
                * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
              + (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
                * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
                    + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                    + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)))
            * Work.FIArea4.p14Ener R S α) := by
        refine mul_le_mul_of_nonneg_left hnum' (by positivity)
    _ = (100 * Cd * Cnum) * ((Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
                * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
              + (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
                * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
                    + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                    + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)))
            * Work.FIArea4.p14Ener R S α := by ring

end

end Work.FIArea4.Vflip.Vfd
