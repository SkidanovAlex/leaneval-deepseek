import Mathlib.Computability.Reduce
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.Theta
import Submission.Work.BoseRowsFS.sum_exp_div_norm_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Gaussian lattice sums in `ℤ³`

Explicit bounds and summability for the Gaussian sums `Σ_m e^{-c‖m‖²}` used to estimate the
*far* images of the periodic heat kernel.  The one-dimensional Gaussian over `ℤ` is split into
its nonnegative and negative halves, each bounded by the half-line sum
`Σ_{n:ℕ} e^{-cn²} ≤ 1 + 1/√c` (`gauss_tsum_exp_neg_sq_le`); the three-dimensional sum is the
product of three copies.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseRowsFS

set_option autoImplicit false

/-- Summability of the one-dimensional Gaussian on `ℕ`. -/
lemma summable_nat_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-(c * (n : ℝ) ^ 2))) := by
  have hs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have h := summable_exp_neg_sq_nat (c := Real.sqrt c) (Real.sqrt_pos.mpr hc)
  simpa only [hs] using h

/-- `Σ_{n:ℕ} e^{-cn²} ≤ 1 + 1/√c` for `c > 0`. -/
lemma tsum_nat_exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-(c * (n : ℝ) ^ 2))) ≤ 1 + 1 / Real.sqrt c := by
  have hs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have h := gauss_tsum_exp_neg_sq_le (c := Real.sqrt c) (Real.sqrt_pos.mpr hc)
  simpa only [hs] using h

/-- Summability of the one-dimensional Gaussian on `ℤ`. -/
lemma summable_int_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2))) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact summable_nat_exp_neg_mul_sq hc
  · refine (summable_nat_exp_neg_mul_sq hc).congr (fun n => ?_)
    simp only [Int.cast_neg, Int.cast_natCast, neg_sq]

/-- `Σ_{n:ℤ} e^{-cn²} ≤ 2(1 + 1/√c)` for `c > 0`. -/
lemma tsum_int_exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℤ, Real.exp (-(c * (n : ℝ) ^ 2))) ≤ 2 * (1 + 1 / Real.sqrt c) := by
  set F : ℤ → ℝ := fun n => Real.exp (-(c * (n : ℝ) ^ 2)) with hF
  have hsumm : Summable F := summable_int_exp_neg_mul_sq hc
  -- the two halves
  have h1s : Summable ((Set.Ici (0 : ℤ)).indicator F) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsumm
    · rw [Set.indicator_apply]; split <;> positivity
    · rw [Set.indicator_apply]; split
      · exact le_rfl
      · exact (Real.exp_pos _).le
  have h2s : Summable ((Set.Iio (0 : ℤ)).indicator F) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsumm
    · rw [Set.indicator_apply]; split <;> positivity
    · rw [Set.indicator_apply]; split
      · exact le_rfl
      · exact (Real.exp_pos _).le
  have hsplit : (∑' n : ℤ, F n)
      = (∑' n : ℤ, (Set.Ici (0 : ℤ)).indicator F n)
        + (∑' n : ℤ, (Set.Iio (0 : ℤ)).indicator F n) := by
    rw [← Summable.tsum_add h1s h2s]
    exact tsum_congr (fun n => by
      by_cases h : (0 : ℤ) ≤ n
      · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h), Set.indicator_of_notMem
          (by simp only [Set.mem_Iio]; omega), add_zero]
      · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ici]; omega),
          Set.indicator_of_mem (Set.mem_Iio.mpr (by omega)), zero_add])
  -- identify each half with an `ℕ`-sum
  have hpos1 : ∀ k : ℕ, (0 : ℤ) ≤ (k : ℤ) := fun k => Int.natCast_nonneg k
  let φ₁ : ℕ → {n : ℤ // 0 ≤ n} := fun k => ⟨(k : ℤ), hpos1 k⟩
  have hφ₁ : ∀ k : ℕ, ((φ₁ k : {n : ℤ // 0 ≤ n}) : ℤ).toNat = k := fun k => Int.toNat_natCast k
  have hψ₁ : ∀ n : {n : ℤ // 0 ≤ n}, φ₁ (((n : ℤ)).toNat) = n := fun n =>
    Subtype.ext (Int.toNat_of_nonneg n.2)
  let e₁ : ℕ ≃ {n : ℤ // 0 ≤ n} :=
    { toFun := φ₁, invFun := fun n => ((n : ℤ)).toNat, left_inv := hφ₁, right_inv := hψ₁ }
  have hneg2 : ∀ k : ℕ, -((k : ℤ) + 1) < 0 := fun k => by omega
  let φ₂ : ℕ → {n : ℤ // n < 0} := fun k => ⟨-((k : ℤ) + 1), hneg2 k⟩
  have hφ₂ : ∀ k : ℕ, (-((φ₂ k : {n : ℤ // n < 0}) : ℤ) - 1).toNat = k := by
    intro k
    have h : (-((φ₂ k : {n : ℤ // n < 0}) : ℤ) - 1 : ℤ) = (k : ℤ) := by
      show (-(-((k : ℤ) + 1)) - 1 : ℤ) = (k : ℤ)
      ring
    rw [h]
    exact Int.toNat_natCast k
  have hψ₂ : ∀ n : {n : ℤ // n < 0}, φ₂ ((-((n : ℤ)) - 1).toNat) = n := by
    intro n
    refine Subtype.ext ?_
    show (-(((( -((n : ℤ)) - 1).toNat : ℤ)) + 1)) = (n : ℤ)
    have h : (((-((n : ℤ)) - 1).toNat : ℤ)) = -((n : ℤ)) - 1 :=
      Int.toNat_of_nonneg (by have := n.2; omega)
    rw [h]
    ring
  let e₂ : ℕ ≃ {n : ℤ // n < 0} :=
    { toFun := φ₂, invFun := fun n => (-((n : ℤ)) - 1).toNat, left_inv := hφ₂, right_inv := hψ₂ }
  have e1 : (∑' n : ℤ, (Set.Ici (0 : ℤ)).indicator F n)
      = ∑' k : ℕ, Real.exp (-(c * (k : ℝ) ^ 2)) := by
    rw [← tsum_subtype (Set.Ici (0 : ℤ)) F]
    rw [show (∑' (x : ↑(Set.Ici (0 : ℤ))), F ↑x)
        = ∑' (b : {n : ℤ // 0 ≤ n}), F (b : ℤ) from rfl]
    rw [← Equiv.tsum_eq (e := e₁) (fun b : {n : ℤ // 0 ≤ n} => F (b : ℤ))]
    refine tsum_congr (fun k => ?_)
    have hk : (((e₁ k : {n : ℤ // 0 ≤ n}) : ℤ) : ℝ) = (k : ℝ) := by
      have h1 : ((e₁ k : {n : ℤ // 0 ≤ n}) : ℤ) = (k : ℤ) := rfl
      rw [h1]; push_cast; ring
    simp only [F, hk]
  have e2 : (∑' n : ℤ, (Set.Iio (0 : ℤ)).indicator F n)
      = ∑' k : ℕ, Real.exp (-(c * ((k : ℝ) + 1) ^ 2)) := by
    rw [← tsum_subtype (Set.Iio (0 : ℤ)) F]
    rw [show (∑' (x : ↑(Set.Iio (0 : ℤ))), F ↑x)
        = ∑' (b : {n : ℤ // n < 0}), F (b : ℤ) from rfl]
    rw [← Equiv.tsum_eq (e := e₂) (fun b : {n : ℤ // n < 0} => F (b : ℤ))]
    refine tsum_congr (fun k => ?_)
    have hk : (((e₂ k : {n : ℤ // n < 0}) : ℤ) : ℝ) = -((k : ℝ) + 1) := by
      have h1 : ((e₂ k : {n : ℤ // n < 0}) : ℤ) = -((k : ℤ) + 1) := rfl
      rw [h1]; push_cast; ring
    simp only [F, hk]
    ring
  rw [hsplit, e1, e2]
  have hstep : (∑' k : ℕ, Real.exp (-(c * ((k : ℝ) + 1) ^ 2)))
      ≤ ∑' k : ℕ, Real.exp (-(c * (k : ℝ) ^ 2)) := by
    have hsumm2 : Summable (fun k : ℕ => Real.exp (-(c * ((k : ℝ) + 1) ^ 2))) := by
      refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
        (summable_nat_exp_neg_mul_sq hc)
      refine Real.exp_le_exp.mpr ?_
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    exact Summable.tsum_le_tsum (fun k => Real.exp_le_exp.mpr (by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith)) hsumm2 (summable_nat_exp_neg_mul_sq hc)
  linarith [tsum_nat_exp_neg_mul_sq_le hc]

/-- The three-dimensional Gaussian lattice sum is summable. -/
lemma summable_pi3_exp_neg_mul_normSq {c : ℝ} (hc : 0 < c) :
    Summable (fun m : Fin 3 → ℤ => Real.exp (-(c * ‖vecZ m‖ ^ 2))) := by
  have hprod : Summable (fun m : Fin 3 → ℤ =>
      ∏ i, Real.exp (-(c * (m i : ℝ) ^ 2))) :=
    summable_pi3_prod_of_nonneg (F := fun _ (n : ℤ) => Real.exp (-(c * (n : ℝ) ^ 2)))
      (fun _ _ => (Real.exp_pos _).le) (fun _ => summable_int_exp_neg_mul_sq hc)
  refine hprod.congr (fun m => ?_)
  rw [← Real.exp_sum, norm_vecZ_sq, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- `Σ_{m ∈ ℤ³} e^{-c‖m‖²} ≤ (2(1+1/√c))³`. -/
lemma tsum_pi3_exp_neg_mul_normSq_le {c : ℝ} (hc : 0 < c) :
    (∑' m : Fin 3 → ℤ, Real.exp (-(c * ‖vecZ m‖ ^ 2)))
      ≤ (2 * (1 + 1 / Real.sqrt c)) ^ 3 := by
  have hprod : (∑' m : Fin 3 → ℤ, ∏ i, Real.exp (-(c * (m i : ℝ) ^ 2)))
      = ∏ i : Fin 3, ∑' n : ℤ, Real.exp (-(c * (n : ℝ) ^ 2)) :=
    pi3_prod_tsum_real _ (fun _ => summable_int_exp_neg_mul_sq hc)
  have hpt : ∀ m : Fin 3 → ℤ, Real.exp (-(c * ‖vecZ m‖ ^ 2))
      = ∏ i, Real.exp (-(c * (m i : ℝ) ^ 2)) := by
    intro m
    rw [← Real.exp_sum, norm_vecZ_sq, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [tsum_congr hpt, hprod]
  calc ∏ i : Fin 3, ∑' n : ℤ, Real.exp (-(c * (n : ℝ) ^ 2))
      ≤ ∏ _i : Fin 3, (2 * (1 + 1 / Real.sqrt c)) := by
        refine Finset.prod_le_prod₀ (fun i _ => tsum_nonneg (fun n => (Real.exp_pos _).le)) ?_
        intro i _
        exact tsum_int_exp_neg_mul_sq_le hc
    _ = (2 * (1 + 1 / Real.sqrt c)) ^ 3 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Work.BoseRowsFS
