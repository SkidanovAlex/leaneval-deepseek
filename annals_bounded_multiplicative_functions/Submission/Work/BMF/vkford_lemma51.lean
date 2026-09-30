import Mathlib
import Submission.Work.BMF.vkford_defs
import Submission.Work.BMF.TentDefs
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.kern_hasSum
import Submission.Work.BMF.kern_summable
import Submission.Work.BMF.one_le_kern
import Submission.Work.BMF.Xsum_norm_pow
import Submission.Work.BMF.tsum_pi_prod
import Submission.Work.BMF.count_resonant_le
import Submission.Work.BMF.card_diff_le_Jincom
import Submission.Work.BMF.Dset_card_le_fordW
import Submission.Work.BMF.pair_tent_sum_le
import Submission.Work.BMF.Tker_eq
import Submission.Work.BMF.Ssum_le_Usum
import Submission.Work.BMF.Usum_pow_le_Tker
import Submission.Work.BMF.AB_eq
import Submission.Work.BMF.root_le
import Submission.Work.BMF.sum_fin_succ_eq
import Submission.Work.BMF.pi_sq_le_ten

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ford's Lemma 5.1 (the Vinogradov extraction)

Assembly of `Work.BMF.vkford_lemma51` from the pieces proved in the sibling files:

* `Ssum_le_Usum` (Ford's (5.2)): the partial sum is bounded by `(N/(M₁M₂))|U| + 2M₁M₂ + ...`
* `Usum_pow_le_Tker` (Ford's (5.3) and the Hölder steps)
* `Tker_eq` (the Poisson/tent evaluation of `T`)
* `pair_tent_sum_le` and `Dset_card_le_fordW` (the resonance count)
* `AB_eq`, `root_le` (the final algebra)
-/

namespace Work.BMF

open Finset
open scoped BigOperators

noncomputable section

/-- The Ford kernel is nonnegative. -/
lemma kern_nonneg (K : ℕ) (c : ℤ) : 0 ≤ kern K c :=
  mul_nonneg (by positivity) (tentCoeff_nonneg (by positivity) c)

/-- `Tker` is a sum of nonnegative terms. -/
lemma Tker_nonneg (r s M₁ M₂ k : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) :
    0 ≤ Tker r s M₁ M₂ k γ ε := by
  rw [Tker]
  exact tsum_nonneg fun c =>
    mul_nonneg (Finset.prod_nonneg fun j _ => kern_nonneg _ _) (pow_nonneg (norm_nonneg _) _)

/-- `fordW` is nonnegative under the standing hypotheses. -/
lemma fordW_nonneg (r s t N M₁ M₂ : ℝ) (j : ℕ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (ht : 0 < t) (hN : 0 < N) (hj : 1 ≤ j) :
    0 ≤ fordW r s t N M₁ M₂ j := by
  rw [fordW]
  have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hnum1 : (0 : ℝ) ≤ 2 * s * M₂ ^ j := mul_nonneg (mul_nonneg (by norm_num) hs) (pow_nonneg hM₂ j)
  have hnum2 : (0 : ℝ) ≤ s * t * M₂ ^ j := mul_nonneg (mul_nonneg hs ht.le) (pow_nonneg hM₂ j)
  have hnum3 : (0 : ℝ) ≤ 4 * Real.pi * (j : ℝ) * (2 * N) ^ j :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (by positivity))
      (pow_nonneg (by linarith) j)
  refine le_min ?_ ?_
  · exact hnum1
  · have h1 : (0 : ℝ) ≤ r * M₁ ^ j := mul_nonneg hr (pow_nonneg hM₁ j)
    have h2 : (0 : ℝ) < Real.pi * (j : ℝ) * N ^ j := by positivity
    have h3 : (0 : ℝ) ≤ r * t * M₁ ^ j := mul_nonneg (mul_nonneg hr ht.le) (pow_nonneg hM₁ j)
    exact add_nonneg (add_nonneg (add_nonneg
      (div_nonneg hnum1 h1)
      (div_nonneg hnum2 h2.le))
      (div_nonneg hnum3 h3)) (by norm_num)

/-- A product of phases of modulus at most one has norm at most one. -/
lemma norm_epsp_le (ε : ℕ → ℂ) (hε : ∀ b, ‖ε b‖ ≤ 1) {s M₂ : ℕ} (p : Pair s M₂) :
    ‖epsp ε p‖ ≤ 1 := by
  rw [epsp, norm_prod]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_mul, norm_star]
  nlinarith [hε (p.1 i).1, hε (p.2 i).1, norm_nonneg (ε (p.2 i).1)]

/-- For a real constant `a`, a nonnegative real `b` and a nonnegative real `c`:
`‖(a:ℂ)^2 * (b:ℂ) / 2 * (c:ℂ)‖ = a^2 * b / 2 * c`. -/
lemma norm_coe_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ‖((a : ℂ)) ^ 2 * (b : ℂ) / (2 : ℂ) * (c : ℂ)‖ = a ^ 2 * b / 2 * c := by
  rw [show ((a : ℂ)) ^ 2 * (b : ℂ) / (2 : ℂ) * (c : ℂ) = ((a ^ 2 * b / 2 * c : ℝ) : ℂ) by
    push_cast
    ring]
  rw [Complex.norm_real, Real.norm_of_nonneg]
  positivity

/-- `Pprod` is nonnegative. -/
lemma Pprod_nonneg (k r s h g : ℕ) (N t : ℝ) (M₁ M₂ : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hh : 1 ≤ h)
    (ht : 0 < t) (hN : 0 < N) :
    0 ≤ Pprod k r s h g N t M₁ M₂ := by
  rw [Pprod]
  have hJ : (0 : ℝ) ≤ LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ := by
    rw [LeanEval.NumberTheory.VinogradovMeanValue.J]
    exact Nat.cast_nonneg _
  have hI : (0 : ℝ) ≤ Jincom s g h (Icc 1 M₂) := by
    rw [Jincom]
    exact Nat.cast_nonneg _
  have hW : (0 : ℝ) ≤ ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j :=
    Finset.prod_nonneg fun j hj => fordW_nonneg _ _ t N _ _ j (Nat.cast_nonneg r)
      (Nat.cast_nonneg s) (Nat.cast_nonneg M₁) (Nat.cast_nonneg M₂) ht (by linarith)
      (le_trans hh (Finset.mem_Icc.mp hj).1)
  have h0 : (0 : ℝ) ≤ (5 * (r : ℝ)) ^ k := by positivity
  have h1 : (0 : ℝ) ≤ (M₂ : ℝ) ^ (-(2 * (s : ℝ))) := Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ (M₁ : ℝ) ^ (-(2 * (r : ℝ)) + (k : ℝ) * ((k : ℝ) + 1) / 2) :=
    Real.rpow_nonneg (by positivity) _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 h1) h2) hJ) hI) hW

/-- Ford's `T` (with the Fourier kernel) is bounded by the resonance count. -/
lemma Tker_le (k r s h g : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hh : 1 ≤ h) (hhg : h ≤ g) (hgk : g ≤ k)
    (N t z : ℝ) (ht : 0 < t) (hN : 0 < N) (hz : N < z) (hz2 : z ≤ 2 * N)
    (M₁ M₂ : ℕ) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (γ : Fin k → ℝ) (hγ : ∀ j : Fin k, γ j = gam ((j : ℕ) + 1) t z)
    (ε : ℕ → ℂ) (hε : ∀ b, ‖ε b‖ ≤ 1) :
    Tker r s M₁ M₂ k γ ε ≤ (5 * (r : ℝ)) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2)
      * Jincom s g h (Icc 1 M₂) * ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j := by
  have hTnn : 0 ≤ Tker r s M₁ M₂ k γ ε := Tker_nonneg r s M₁ M₂ k γ ε
  have hS1 : Tker r s M₁ M₂ k γ ε = ‖(Tker r s M₁ M₂ k γ ε : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hTnn]
  rw [hS1, Tker_eq r s M₁ M₂ k hM₁ hM₂ γ ε]
  have hS2 : ‖∑ p : Pair s M₂, epsp ε p * ∏ j : Fin k,
      ((Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
        * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
            (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) : ℂ))‖
      ≤ ∑ p : Pair s M₂, ∏ j : Fin k,
        (Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
          * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    have hfac : ∀ j : Fin k, 0 ≤ Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
        * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
            (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) :=
      fun j => mul_nonneg (by positivity) (tent_nonneg _ _)
    calc ‖epsp ε p * ∏ j : Fin k,
          ((Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
            * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
                (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) : ℂ))‖
        = ‖epsp ε p‖ * ∏ j : Fin k,
            (Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
              * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
                  (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))) := by
          rw [norm_mul, norm_prod]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          have h1 : ((Real.pi : ℂ) ^ 2 * (((↑(r * M₁ ^ ((j : ℕ) + 1)) : ℝ)) : ℂ) / 2
                * (((tent (1 / (2 * (↑(r * M₁ ^ ((j : ℕ) + 1)) : ℝ)))
                    (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))) : ℂ))
              = (((Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
                  * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
                      (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))) : ℝ) : ℂ) := by
            push_cast
            ring
          rw [h1, Complex.norm_real, Real.norm_of_nonneg (hfac j)]
      _ ≤ 1 * ∏ j : Fin k,
            (Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
              * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
                  (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (norm_epsp_le ε hε p)
            (Finset.prod_nonneg fun j _ => hfac j)
      _ = ∏ j : Fin k,
            (Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
              * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
                  (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))) := by rw [one_mul]
  refine hS2.trans ?_
  have hS3 : (∑ p : Pair s M₂, ∏ j : Fin k,
        (Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
          * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))))
      = (Real.pi ^ 2 * (r : ℝ) / 2) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2)
        * ∑ p : Pair s M₂, ∏ j : Fin k,
            tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hC : ∀ j : Fin k, (Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2)
        = (Real.pi ^ 2 * (r : ℝ) / 2) * (M₁ : ℝ) ^ ((j : ℕ) + 1) := by
      intro j
      push_cast
      ring
    calc ∏ j : Fin k, ((Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2)
          * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))
        = ∏ j : Fin k, (((Real.pi ^ 2 * (r : ℝ) / 2) * (M₁ : ℝ) ^ ((j : ℕ) + 1))
          * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))) := by
          refine Finset.prod_congr rfl fun j _ => by rw [hC j]
      _ = (∏ j : Fin k, ((Real.pi ^ 2 * (r : ℝ) / 2) * (M₁ : ℝ) ^ ((j : ℕ) + 1)))
          * ∏ j : Fin k, tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) := by
          rw [Finset.prod_mul_distrib]
      _ = ((Real.pi ^ 2 * (r : ℝ) / 2) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2))
          * ∏ j : Fin k, tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
            sum_fin_succ_eq, Finset.card_univ, Fintype.card_fin]
  rw [hS3]
  have hS4 : (∑ p : Pair s M₂, ∏ j : Fin k,
        tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
          (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))
      ≤ Jincom s g h (Icc 1 M₂)
        * ∏ j ∈ Icc h g, ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ) := by
    have hp := pair_tent_sum_le r s M₁ M₂ k h g hr hs hM₁ hM₂ N t z ht hz hz2 hh hhg hgk
    simpa only [hγ] using hp
  have hS5 : (∏ j ∈ Icc h g, ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ))
      ≤ ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j := by
    refine Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j hj => ?_
    exact Dset_card_le_fordW r s M₁ M₂ j hr hs hM₁ hM₂ N t z ht hz hz2
      (le_trans hh (Finset.mem_Icc.mp hj).1)
  have hS6 : (Real.pi ^ 2 * (r : ℝ) / 2) ^ k ≤ (5 * (r : ℝ)) ^ k := by
    have hp := pi_sq_le_ten
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h1 : Real.pi ^ 2 * (r : ℝ) / 2 = (Real.pi ^ 2 / 2) * (r : ℝ) := by ring
    rw [h1]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hp hr0) k
  have hI : (0 : ℝ) ≤ Jincom s g h (Icc 1 M₂) := by
    rw [Jincom]
    exact Nat.cast_nonneg _
  have hA5 : (0 : ℝ) ≤ ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j :=
    Finset.prod_nonneg fun j hj => fordW_nonneg _ _ t N _ _ j (Nat.cast_nonneg r)
      (Nat.cast_nonneg s) (Nat.cast_nonneg M₁) (Nat.cast_nonneg M₂) ht (by linarith)
      (le_trans hh (Finset.mem_Icc.mp hj).1)
  calc (Real.pi ^ 2 * (r : ℝ) / 2) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2)
        * (∑ p : Pair s M₂, ∏ j : Fin k,
            tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
              (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))
      ≤ (Real.pi ^ 2 * (r : ℝ) / 2) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2)
        * (Jincom s g h (Icc 1 M₂)
          * ∏ j ∈ Icc h g, ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left hS4 (by positivity)
    _ ≤ (Real.pi ^ 2 * (r : ℝ) / 2) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2)
        * (Jincom s g h (Icc 1 M₂)
          * ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hS5 hI
    _ ≤ (5 * (r : ℝ)) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2)
        * (Jincom s g h (Icc 1 M₂)
          * ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hI hA5)
        exact mul_le_mul_of_nonneg_right hS6 (by positivity)
    _ = (5 * (r : ℝ)) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2) * Jincom s g h (Icc 1 M₂)
        * ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j := by ring

/-- The bound for `U = Usum`. -/
lemma Usum_le_Pprod (k r s h g : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hh : 1 ≤ h) (hhg : h ≤ g)
    (hgk : g ≤ k) (N t z : ℝ) (ht : 0 < t) (hN : 0 < N) (hz : N < z) (hz2 : z ≤ 2 * N)
    (M₁ M₂ : ℕ) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (γ : Fin k → ℝ) (hγ : ∀ j : Fin k, γ j = gam ((j : ℕ) + 1) t z) :
    ‖Usum k M₁ M₂ γ‖
      ≤ (M₁ : ℝ) * (M₂ : ℝ) * (Pprod k r s h g N t M₁ M₂) ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))) := by
  obtain ⟨ε, hε, hU⟩ := Usum_pow_le_Tker k r s M₁ M₂ hr hs hM₁ hM₂ γ
  have hT := Tker_le k r s h g hr hs hh hhg hgk N t z ht hN hz hz2 M₁ M₂ hM₁ hM₂ γ hγ ε hε
  have hA : (0 : ℝ) ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2))
      * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ := by
    have hJ : (0 : ℝ) ≤ LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ := by
      rw [LeanEval.NumberTheory.VinogradovMeanValue.J]
      exact Nat.cast_nonneg _
    positivity
  have hAB : ‖Usum k M₁ M₂ γ‖ ^ (2 * r * s)
      ≤ ((M₁ : ℝ) * (M₂ : ℝ)) ^ (2 * r * s) * Pprod k r s h g N t M₁ M₂ := by
    rw [Pprod]
    calc ‖Usum k M₁ M₂ γ‖ ^ (2 * r * s)
        ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2))
            * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ * Tker r s M₁ M₂ k γ ε := hU
      _ ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2))
            * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁
            * ((5 * (r : ℝ)) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2)
                * Jincom s g h (Icc 1 M₂)
                * ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j) :=
          mul_le_mul_of_nonneg_left hT hA
      _ = ((M₁ : ℝ) * (M₂ : ℝ)) ^ (2 * r * s)
            * ((5 * (r : ℝ)) ^ k * (M₂ : ℝ) ^ (-(2 * (s : ℝ)))
                * (M₁ : ℝ) ^ (-(2 * (r : ℝ)) + (k : ℝ) * ((k : ℝ) + 1) / 2)
                * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁
                * Jincom s g h (Icc 1 M₂)
                * ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j) :=
          AB_eq k r s M₁ M₂ _ _ _ hr hs hM₁ hM₂
  have hP : (0 : ℝ) ≤ Pprod k r s h g N t M₁ M₂ :=
    Pprod_nonneg k r s h g N t M₁ M₂ hr hs hM₁ hM₂ hh ht hN
  have hA0 : (0 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by positivity
  exact root_le _ _ _ r s hr hs (norm_nonneg _) hA0 hP hAB

/-- **Ford's Lemma 5.1** (the Vinogradov extraction), in the form needed by the
MRTTZ argument: with `B = [1,M₂]` (so that `M₂/|B| = 1`). -/
theorem vkford_lemma51
    (k r s h g : ℕ) (hr : 2 ≤ r) (hs : 1 ≤ s) (hh : 1 ≤ h) (hhg : h ≤ g) (hgk : g ≤ k)
    (N t u R : ℝ) (M₁ M₂ : ℕ) (hN : 1 ≤ N) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (hMprod : (M₁ : ℝ) * (M₂ : ℝ) ≤ N) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u ≤ 1) (hR : N < R) (hR2 : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 2 * (M₁ : ℝ) * (M₂ : ℝ) + t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 1) / ((k : ℝ) * N ^ k)
        + N * ((5 * (r : ℝ)) ^ k * (M₂ : ℝ) ^ (-(2 * (s : ℝ)))
              * (M₁ : ℝ) ^ (-(2 * (r : ℝ)) + (k : ℝ) * ((k : ℝ) + 1) / 2)
            * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁
            * Work.BMF.Jincom s g h (Finset.Icc 1 M₂)
            * ∏ j ∈ Finset.Icc h g, Work.BMF.fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j)
          ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))) := by
  have hk : 1 ≤ k := le_trans hh (le_trans hhg hgk)
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨z, hz1, hz2, hS⟩ :=
    Ssum_le_Usum k hk N t u R M₁ M₂ hM₁ hM₂ hMprod ht hu hu1 hN hR hR2
  have hU := Usum_le_Pprod k r s h g hr1 hs hh hhg hgk N t z ht hNpos hz1 hz2 M₁ M₂ hM₁ hM₂
    (fun j : Fin k => gam ((j : ℕ) + 1) t z) (fun _ => rfl)
  have hMpos : (0 : ℝ) < (M₁ : ℝ) * (M₂ : ℝ) := by positivity
  have hMne : ((M₁ : ℝ) * (M₂ : ℝ)) ≠ 0 := ne_of_gt hMpos
  have hfin : N / ((M₁ : ℝ) * (M₂ : ℝ))
        * ((M₁ : ℝ) * (M₂ : ℝ)
          * (Pprod k r s h g N t M₁ M₂) ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))))
      = N * (Pprod k r s h g N t M₁ M₂) ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))) := by
    rw [← mul_assoc, div_mul_cancel₀ N hMne]
  calc ‖Ssum N u t R‖
      ≤ 2 * ((M₁ : ℝ) * (M₂ : ℝ))
          + t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 1) / ((k : ℝ) * N ^ k)
          + (N / ((M₁ : ℝ) * (M₂ : ℝ)))
              * ‖Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t z)‖ := hS
    _ ≤ 2 * ((M₁ : ℝ) * (M₂ : ℝ))
          + t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 1) / ((k : ℝ) * N ^ k)
          + (N / ((M₁ : ℝ) * (M₂ : ℝ)))
              * ((M₁ : ℝ) * (M₂ : ℝ)
                * (Pprod k r s h g N t M₁ M₂) ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ)))) := by
        gcongr
    _ = 2 * ((M₁ : ℝ) * (M₂ : ℝ))
          + t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 1) / ((k : ℝ) * N ^ k)
          + N * (Pprod k r s h g N t M₁ M₂) ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))) := by
        rw [hfin]
    _ = 2 * (M₁ : ℝ) * (M₂ : ℝ)
          + t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 1) / ((k : ℝ) * N ^ k)
          + N * ((5 * (r : ℝ)) ^ k * (M₂ : ℝ) ^ (-(2 * (s : ℝ)))
              * (M₁ : ℝ) ^ (-(2 * (r : ℝ)) + (k : ℝ) * ((k : ℝ) + 1) / 2)
            * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁
            * Work.BMF.Jincom s g h (Finset.Icc 1 M₂)
            * ∏ j ∈ Finset.Icc h g, Work.BMF.fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j)
          ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))) := by
        rw [Pprod]
        ring

end

end Work.BMF
