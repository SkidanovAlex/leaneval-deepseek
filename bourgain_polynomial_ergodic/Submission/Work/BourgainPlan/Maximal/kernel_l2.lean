import Mathlib
import Submission.Work.BourgainPlan.Maximal.foundations
import Submission.Work.BourgainPlan.Maximal.z_defs
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.deg_le_one
import Submission.Work.BourgainPlan.Maximal.model_pre
import Submission.Work.BourgainPlan.Maximal.model_maximal_pre
import Submission.Work.BourgainPlan.Maximal.poly_dyadic_of_model
import Submission.Work.BourgainPlan.Maximal.poly_dyadic_reduction_z
import Submission.Work.BourgainPlan.Maximal.poly_shift_transfer

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Submission.BourgainPlan (NonnegOnNat discAvg)

/-- A polynomial that is nonnegative on `ℕ` and has degree at least two has positive leading
coefficient.  Otherwise `P.eval x → -∞` along `x → +∞` in `ℝ`, contradicting `P ≥ 0` on `ℕ`. -/
lemma leadingCoeff_pos_of_nonnegOnNat (P : Polynomial ℤ) (hP : NonnegOnNat P)
    (hd : 2 ≤ P.natDegree) : 0 < P.leadingCoeff := by
  have hne : P ≠ 0 := by
    intro h0; rw [h0] at hd; simp at hd
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  by_contra hcon
  have hlt : P.leadingCoeff < 0 := lt_of_le_of_ne (not_lt.mp hcon) hlc
  set Q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hQdef
  have hQnat : Q.natDegree = P.natDegree := by
    rw [hQdef]
    exact Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective P
  have hQdeg : 0 < Q.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hQnat]
    omega
  have hQlc : Q.leadingCoeff = (P.leadingCoeff : ℝ) := by
    rw [hQdef, Polynomial.leadingCoeff_map_of_injective Int.cast_injective P]
    rfl
  have hQlc' : Q.leadingCoeff ≤ 0 := by
    rw [hQlc]; exact_mod_cast le_of_lt hlt
  have htend : Tendsto (fun x : ℝ => Q.eval x) atTop atBot :=
    Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hQdeg hQlc'
  rw [Filter.tendsto_atBot] at htend
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (htend (-1))
  obtain ⟨k, hk⟩ := exists_nat_ge a
  have hthis : Q.eval (k : ℝ) ≤ -1 := ha (k : ℝ) hk
  have hval : Q.eval (k : ℝ) = ((P.eval (k : ℤ) : ℤ) : ℝ) := by
    rw [hQdef, Polynomial.eval_map]
    exact Polynomial.eval₂_at_natCast _ k
  have h2 : (0 : ℝ) ≤ ((P.eval (k : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hP k
  linarith

/-- **The `p = 2` maximal inequality for a polynomial of degree at least two**, assembled from the
uniform major-arc model approximation (`model_pre`), the `ℓ²` maximal estimate for the model
(`model_maximal_pre`), the dyadic reduction on `ℤ` (`poly_dyadic_reduction_z`) and the `ℤ → ℕ`
transfer (`poly_shift_transfer`). -/
lemma kernel_l2_chain (P : Polynomial ℤ) (hP : NonnegOnNat P) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff)
    (hmaj : ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ (N : ℕ) (θ : ℝ), 3 ≤ N → 0 ≤ θ → θ ≤ 1 →
      ‖polyWeylKernel P N θ - polyMajorArcModelPre P ((1 : ℝ) / 4) N θ‖
        ≤ C * (N : ℝ) ^ (-c₀))
    (hmodel : ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkMax P g s k x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n : ℕ, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ n : ℕ, ‖g n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
  poly_shift_transfer P hP (poly_dyadic_reduction_z P (poly_dyadic_of_model P hc hd hmaj hmodel))

/-- **The `ℓ²` maximal inequality for the polynomial density kernels, every
`P : ℤ[X]` nonnegative on `ℕ`.**  This is the `p = 2` case of
`Submission.BourgainPlan.MaximalStatement`, i.e. `Work.BourgainPlan.Maximal.L2Statement` at `P`.

Route (Bourgain 1989, §6; the pure-power template is
`Commons.Analysis.ExponentialSums.pure_power_kernel_maximal_l2`, whose assembly is
`pow_shift_transfer d (pow_dyadic_reduction_z d (pow_dyadic_of_model d hd (pow_model_maximal d hd)))`):

* `P.natDegree ≤ 1`: use `Work.BourgainPlan.Maximal.deg_le_one` (already proved), which gives every
  `1 < p`, hence also `p = 2`.
* `P.natDegree ≥ 2` (then `0 ≤ P.coeff n` forces `0 < P.leadingCoeff`):
  1. `Work.BourgainPlan.Maximal.shift_fourier_coeff_conj` writes the average
     `N⁻¹∑_{i<N} g (m + P i)` as the Fourier coefficient of `conj(polyWeylKernel P N θ)` times the
     Fourier series of `g`; this converts the maximal inequality into a multiplier statement;
  2. `Work.BourgainPlan.Maximal.model_pre` replaces `polyWeylKernel` by the model
     `polyMajorArcModelPre`, and `Work.BourgainPlan.Maximal.model_maximal_pre` bounds the model's
     dyadic maximal function on `ℓ²` (Bourgain's `(log Q)²` multi-frequency lemma);
  3. the standard dyadic reduction (the full `sup_N` against `N = 2^k`, cf.
     `Commons.Analysis.ExponentialSums.pow_dyadic_reduction_z`) and the `ℤ → ℕ` transfer (cf.
     `Commons.Analysis.ExponentialSums.quadratic_kernel_shift_transfer_lp`) finish.  The pieces 2
     and 3 exist for `P = X^d` in `pure_power_kernel_maximal_l2.lean` and can be mirrored. -/
theorem kernel_l2 (P : Polynomial ℤ) (hP : Submission.BourgainPlan.NonnegOnNat P) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n : ℕ, (⨆ N : ℕ, ‖Submission.BourgainPlan.discAvg P N g n‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ n : ℕ, ‖g n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  by_cases hdeg : P.natDegree ≤ 1
  · obtain ⟨C, hC, hb⟩ := deg_le_one P hP hdeg 2 (by norm_num)
    refine ⟨C + 1, by linarith, fun g hg => ?_⟩
    refine le_trans (hb g hg) ?_
    have h1 : ENNReal.ofReal (C ^ (2 : ℝ)) ≤ ENNReal.ofReal ((C + 1) ^ 2) := by
      rw [Real.rpow_ofNat]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    gcongr
  · have hd : 2 ≤ P.natDegree := by omega
    have hc : 0 < P.leadingCoeff := leadingCoeff_pos_of_nonnegOnNat P hP hd
    exact kernel_l2_chain P hP hd hc (model_pre P hc hd) (model_maximal_pre P hc hd)

/-- `kernel_l2` packaged as the `p = 2` half of `Submission.BourgainPlan.MaximalStatement`
(the hypothesis `h2` of `Work.BourgainPlan.Maximal.maximal_statement_of_l2_and_subtwo`). -/
theorem L2Statement_of_kernel_l2 : L2Statement := fun P hP => kernel_l2 P hP

end Work.BourgainPlan.Maximal
