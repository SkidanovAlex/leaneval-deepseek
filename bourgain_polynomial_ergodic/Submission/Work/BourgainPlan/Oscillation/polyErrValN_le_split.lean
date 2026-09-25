import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le

/-!
# The pointwise profile-replacement error at an arbitrary scale

`polyErrValN P β N = ‖Φ_N(β) − 1_{|N^d β| ≤ 1}‖` is the error made in replacing the oscillatory
profile `Φ_N(β) = polyProfile P N β` (Bourgain's `𝔞_N`) by its *sharp* window.  Two elementary
estimates control it, uniformly in the scale `N ≥ 1`:

* **plateau / mean value** (`polyProfile_sub_one_le`):
  `‖Φ_N(β) − 1‖ ≤ 4π (Σ_i |c_i|) · |β| N^d`;
* **decay** (van der Corput, `polyProfile_decay_N_gen` below):
  `‖Φ_N(β)‖ ≤ C · (|β| N^d)^{-1/d}` once `|β| N^d ≥ 1`.

Along the two regimes of the sharp indicator the two estimates give the two-piece bound of
`polyErrValN_le_split`,
`polyErrValN P β N ≤ K · (|β| N^d)` for `|β| N^d ≤ 1` and
`polyErrValN P β N ≤ K · (|β| N^d)^{-1/d}` for `|β| N^d > 1`,
which is the form consumed by the lacunary-oscillation assembly.
-/

namespace Work.BourgainPlan.Oscillation

open MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.Maximal

/-- **van der Corput decay of the polynomial profile at an arbitrary scale.**
Let `P : ℤ[X]` have degree `d = P.natDegree ≥ 2`.  There is `C > 0` such that for every scale
`N ≥ 1` and every frequency `β` with `1 ≤ |β| · N^d`,
`‖polyProfile P N β‖ ≤ C · (|β| · N^d)^{-(1/d)}`.

This is `polyProfile_decay_sharp` with an arbitrary `N ≥ 1` in place of the dyadic scale `2^k`:
the phase `s ↦ 2π β P(N s)` has constant `d`-th derivative `2π β d! (lead P) N^d` on `[0,1]`, so
`Commons.Analysis.Oscillatory.van_der_corput_bound` applies for every `N ≠ 0`. -/
theorem polyProfile_decay_N_gen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ β : ℝ, 1 ≤ |β| * (N : ℝ) ^ P.natDegree →
      ‖polyProfile P N β‖
        ≤ C * (|β| * (N : ℝ) ^ P.natDegree) ^ (-(1 / (P.natDegree : ℝ))) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Commons.Analysis.Oscillatory.van_der_corput_bound P.natDegree hd
  set Q : Polynomial ℝ := toRealPoly P with hQdef
  have hQdeg : Q.natDegree = P.natDegree := by
    rw [hQdef, toRealPoly]
    exact Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hQlc : Q.leadingCoeff = (P.leadingCoeff : ℝ) := by
    rw [hQdef, toRealPoly]
    exact Polynomial.leadingCoeff_map_of_injective Int.cast_injective P
  have hPne : P ≠ 0 := by intro h; rw [h] at hd; simp at hd
  have hlc_ne : Q.leadingCoeff ≠ 0 := by
    rw [hQlc]
    exact_mod_cast (Polynomial.leadingCoeff_ne_zero.mpr hPne)
  set A : ℝ := 2 * Real.pi * (P.natDegree.factorial : ℝ) * |Q.leadingCoeff| with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    have := abs_pos.mpr hlc_ne
    positivity
  refine ⟨C₁ / A ^ ((1 : ℝ) / (P.natDegree : ℝ)),
    div_pos hC₁pos (Real.rpow_pos_of_pos hApos _), ?_⟩
  intro N hN β hβ
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hXpos : 0 < |β| * (N : ℝ) ^ P.natDegree := lt_of_lt_of_le zero_lt_one hβ
  set φ : ℝ → ℝ := fun s => 2 * Real.pi * (β * Q.eval ((N : ℝ) * s)) with hφdef
  have hφcd : ContDiffOn ℝ P.natDegree φ (Set.Icc 0 1) := by
    apply ContDiff.contDiffOn
    rw [hφdef]
    exact contDiff_const.mul (contDiff_const.mul
      ((Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) Q (P.natDegree : WithTop ℕ∞)).comp
        (contDiff_const.mul contDiff_id)))
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      A * (|β| * (N : ℝ) ^ P.natDegree) ≤ |iteratedDeriv P.natDegree φ t| := by
    intro t _ht
    have hcomp := iteratedDeriv_comp_eval (N := (N : ℝ)) Q (ne_of_gt hNpos) t
    rw [hQdeg] at hcomp
    have hval : iteratedDeriv P.natDegree φ t
        = 2 * Real.pi * β *
            ((P.natDegree.factorial : ℝ) * Q.leadingCoeff * (N : ℝ) ^ P.natDegree) := by
      rw [hφdef, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, hcomp]
      ring
    rw [hval]
    have hfac : (0 : ℝ) < (P.natDegree.factorial : ℝ) :=
      by exact_mod_cast Nat.factorial_pos _
    have hNpow : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
    simp only [abs_mul]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos, abs_of_pos hfac,
      abs_of_pos hNpow]
    rw [hAdef]
    exact le_of_eq (by ring)
  have hvc := hC₁ (a := (0 : ℝ)) (b := 1) zero_le_one (φ := φ)
      (lam := A * (|β| * (N : ℝ) ^ P.natDegree)) (by positivity) hφcd hderiv
  have hprof : polyProfile P N β = ∫ s in (0 : ℝ)..1, Complex.exp (Complex.I * (φ s : ℂ)) := by
    rw [polyProfile, hφdef]
    apply intervalIntegral.integral_congr
    intro s _
    rw [← hQdef]
    push_cast
    ring_nf
  rw [hprof]
  refine le_trans hvc (le_of_eq ?_)
  rw [div_rpow_mul_eq C₁ A (|β| * (N : ℝ) ^ P.natDegree) ((1 : ℝ) / (P.natDegree : ℝ))
    hApos hXpos.le]

/-- `|polyDilN P N · β| = |β| · N^{deg P}` for `N ≥ 1` (the dilation is non-negative). -/
lemma abs_polyDilN_mul (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    |polyDilN P N * β| = |β| * (N : ℝ) ^ P.natDegree := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  rw [polyDilN, abs_mul, abs_of_nonneg (pow_nonneg hNpos.le _), mul_comm]

/-- **The pointwise profile-replacement error is bounded by the two-piece window.**  This is the
arbitrary-scale statement consumed by the lacunary-oscillation assembly: off the plateau the error
decays like `(|β| N^d)^{-1/d}`, on the plateau it is controlled by `|β| N^d`. -/
theorem polyErrValN_le_split (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ β : ℝ,
      Work.BourgainPlan.Oscillation.polyErrValN P β N ≤ K *
        (if |β| * (N : ℝ) ^ P.natDegree ≤ 1 then |β| * (N : ℝ) ^ P.natDegree
          else (|β| * (N : ℝ) ^ P.natDegree) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) := by
  obtain ⟨C1, hC1pos, hdec⟩ := polyProfile_decay_N_gen P hd
  set A : ℝ := 4 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
    with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    positivity
  refine ⟨A + C1, by linarith, ?_⟩
  intro N hN β
  have hpowpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := by
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact pow_pos (by linarith) _
  have habs : |polyDilN P N * β| = |β| * (N : ℝ) ^ P.natDegree := abs_polyDilN_mul P hN β
  have hy0 : 0 ≤ |β| * (N : ℝ) ^ P.natDegree :=
    mul_nonneg (abs_nonneg _) hpowpos.le
  by_cases hy : (|β| * (N : ℝ) ^ P.natDegree) ≤ 1
  · -- on the plateau the sharp window is `1`, and the mean-value bound applies
    rw [if_pos hy]
    have h1 : polyErrValN P β N ≤ A * (|β| * (N : ℝ) ^ P.natDegree) := by
      rw [polyErrValN, habs, if_pos hy]
      exact polyProfile_sub_one_le P N hN β
    calc polyErrValN P β N ≤ A * (|β| * (N : ℝ) ^ P.natDegree) := h1
      _ ≤ (A + C1) * (|β| * (N : ℝ) ^ P.natDegree) := by nlinarith [hA0, hC1pos, hy0]
  · -- off the plateau the sharp window is `0`, and van der Corput applies
    have hy' : 1 < |β| * (N : ℝ) ^ P.natDegree := not_le.mp hy
    rw [if_neg hy]
    have h1 : polyErrValN P β N
        ≤ C1 * (|β| * (N : ℝ) ^ P.natDegree) ^ (-(1 / (P.natDegree : ℝ))) := by
      rw [polyErrValN, habs, if_neg hy, sub_zero]
      exact hdec N hN β hy'.le
    calc polyErrValN P β N ≤ C1 * (|β| * (N : ℝ) ^ P.natDegree) ^ (-(1 / (P.natDegree : ℝ))) := h1
      _ ≤ (A + C1) * (|β| * (N : ℝ) ^ P.natDegree) ^ (-(1 / (P.natDegree : ℝ))) := by
          have hr : 0 ≤ (|β| * (N : ℝ) ^ P.natDegree) ^ (-(1 / (P.natDegree : ℝ))) :=
            Real.rpow_nonneg hy0 _
          nlinarith [hA0, hr]

end Work.BourgainPlan.Oscillation
