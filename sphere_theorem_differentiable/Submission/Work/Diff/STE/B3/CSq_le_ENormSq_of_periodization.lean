import Mathlib
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization_pdVec
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.B3.periodicIntegralLeCube
import Submission.Work.Diff.STE.B3.parseval_cube
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.poincare_cube
import Submission.Work.Diff.STE.B3.norm_setIntegral_le_integral_norm_pd
import Submission.Work.Diff.STE.B3.ENormSq_ge_weighted_fourierCoeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CSq k (fourierCoeff P) ≤ C · ENormSq k P` for a periodisation `P`

For a smooth function `R` supported in the *open* unit cube `(-1/2,1/2)^ι` and its periodisation
`P z = ∑' m, R (z + m)`, the weighted `ℓ²` norm of the Fourier coefficients of `P` is bounded by
the physical `Hᵏ` energy `ENormSq k P` — *without* the extra `ENormSq 0` term that the general
Sobolev comparison `CSq_le_ENormSq` needs, at least for `k ≥ 1`.

The point is that the hypothesis `P = periodisation of R` forces `P` to vanish on every half
integer hyperplane (the `i`-th coordinate of `z + m` is `1/2 + mᵢ`, never in `(-1/2,1/2)`, so
every summand vanishes), and this vanishing controls the mean of `P` by the first derivative
(`Work.Diff.STE.B3.norm_setIntegral_le_integral_norm_pd`).

## Route

* `CSq_le_ENormSq` reduces the claim to `ENormSq 0 P ≤ C' ENormSq k P`, i.e. (by `ENormSq_zero`)
  to the `L²` bound `∫ ‖P‖² ≤ C' ENormSq k P`.
* Parseval (`parseval_cube`) turns the `L²` norm into the `ℓ²` sum `Σ_m ‖P̂(m)‖²`, and
  `Summable.tsum_eq_add_tsum_ite` splits off the `m = 0` term.
* The `m = 0` term is `‖∫_{cube} P‖²`, bounded by the mean bound above; the `m ≠ 0` terms are
  bounded by `B := Σ_m (Σ_i mᵢ²)^k ‖P̂(m)‖² ≤ (2π)^{-2k} ENormSq k P`
  (`ENormSq_ge_weighted_fourierCoeff`).
* Finally `∫ ‖∂ᵢ P‖² = Σ_m (2π mᵢ)² ‖P̂(m)‖² ≤ (2π)² B ≤ (2π)^{2k} B ≤ ENormSq k P`
  (`fourierCoeff_pd`, `parseval_cube`, `ENormSq_ge_weighted_fourierCoeff`).
-/

namespace Work.Diff.STE.B3

/-! ## Elementary facts about the weight `∑ j, (m j)²` on `ℤ^ι` -/

lemma sq_le_sum_sq {ι : Type*} [Fintype ι] (m : ι → ℤ) (i : ι) :
    ((m i : ℤ) : ℝ) ^ 2 ≤ ∑ j, (((m j : ℤ) : ℝ)) ^ 2 :=
  Finset.single_le_sum (f := fun j : ι => (((m j : ℤ) : ℝ)) ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

lemma one_le_sum_sq_of_ne_zero {ι : Type*} [Fintype ι] {m : ι → ℤ} (hm : m ≠ 0) :
    (1 : ℝ) ≤ ∑ j, (((m j : ℤ) : ℝ)) ^ 2 := by
  have hne : ∃ j, m j ≠ 0 := by
    simpa using (Function.ne_iff.mp hm)
  obtain ⟨j, hj⟩ := hne
  have hj1 : (1 : ℝ) ≤ (((m j : ℤ) : ℝ)) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (m j) ^ 2 := by
      have h0 : (0 : ℤ) ≤ (m j) ^ 2 := sq_nonneg _
      have h2 : (m j) ^ 2 ≠ 0 := pow_ne_zero 2 hj
      omega
    exact_mod_cast h1
  exact le_trans hj1 (sq_le_sum_sq m j)

lemma pow_le_pow_weight {ι : Type*} [Fintype ι] (k : ℕ) (hk : 1 ≤ k) (i : ι) (m : ι → ℤ) :
    ((m i : ℤ) : ℝ) ^ 2 ≤ (∑ j, (((m j : ℤ) : ℝ)) ^ 2) ^ k := by
  by_cases hm : m = 0
  · subst hm
    have h0 : (∑ j : ι, ((((0 : ι → ℤ)) j : ℤ) : ℝ) ^ 2) = 0 := by simp
    rw [h0, zero_pow (by omega : k ≠ 0)]
    simp
  · exact le_trans (sq_le_sum_sq m i)
      (le_self_pow₀ (n := k) (one_le_sum_sq_of_ne_zero hm) (by omega : k ≠ 0))

/-- **The Sobolev comparison for a periodisation.**  There is a constant `C` such that for every
smooth `R` supported in the open unit cube and every smooth `1`-periodic `P` which is the
periodisation of `R`, the weighted `ℓ²` norm of the Fourier coefficients of `P` is bounded by
`C` times the `Hᵏ` energy of `P`. -/
theorem CSq_le_ENormSq_of_periodization {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R P : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) R →
      Function.support R ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)) →
      ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
      (∀ z : ι → ℝ, P z = ∑' m : ι → ℤ, R (z + Work.Diff.STE.iVec m)) →
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff P) ≤ C * Work.Diff.STE.ENormSq k P := by
  classical
  obtain ⟨C₁, hC₁nn, hC₁⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := ι) k
  refine ⟨3 * C₁, by positivity, ?_⟩
  intro R P hR hsupp hP hper hrepr
  have hPc : Continuous P := hP.continuous
  have hPk : ContDiff ℝ k P := hP.of_le (by exact_mod_cast le_top)
  have hP1 : ContDiff ℝ 1 P := hPk.of_le (by exact_mod_cast hk)
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hpd_cont : Continuous (Work.Diff.STE.pd i P) := Work.Diff.STE.continuous_pd hP1 i
  -- ## the vanishing of `P` on the hyperplane `{z | z i = 1/2}`
  have hPz : ∀ z : ι → ℝ, z i = (1 / 2 : ℝ) → P z = 0 := by
    intro z hz
    rw [hrepr z]
    rw [show (∑' m : ι → ℤ, R (z + Work.Diff.STE.iVec m))
        = ∑' _m : ι → ℤ, (0 : ℂ) from tsum_congr (fun m => ?_)]
    · simp
    · have hcoord : (z + Work.Diff.STE.iVec m) i = (1 / 2 : ℝ) + (m i : ℝ) := by
        rw [Pi.add_apply, Work.Diff.STE.iVec, hz]
      have hnot : (z + Work.Diff.STE.iVec m) i ∉ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
        intro h
        have hlt : (1 / 2 : ℝ) + (m i : ℝ) < 1 / 2 := by simpa [hcoord] using h.2
        have hgt : -(1 / 2 : ℝ) < (1 / 2 : ℝ) + (m i : ℝ) := by simpa [hcoord] using h.1
        by_cases hm : 0 ≤ (m i : ℤ)
        · have hm' : (0 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm
          linarith
        · have hm' : (m i : ℤ) ≤ -1 := by omega
          have hm'' : ((m i : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hm'
          linarith
      exact Function.notMem_support.mp (fun hmem =>
        hnot (Set.mem_pi.mp (hsupp hmem) i (Set.mem_univ i)))
  -- ## summability and Parseval
  have hsumP : Summable (fun m : ι → ℤ => ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) :=
    (Work.Diff.STE.bessel_continuous P hPc).1
  have hparsP : (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖P x‖ ^ 2)
      = ∑' m : ι → ℤ, ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2 :=
    parseval_cube P hPc
  have hpars_pd : (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ ^ 2)
      = ∑' m : ι → ℤ, ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd i P) m‖ ^ 2 :=
    parseval_cube (Work.Diff.STE.pd i P) hpd_cont
  have hmult : ∀ m : ι → ℤ,
      ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd i P) m‖ ^ 2
        = (2 * Real.pi * (m i : ℝ)) ^ 2 * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2 :=
    fun m => Work.Diff.STE.fourierCoeff_pd_norm_sq i P m hP1 hper
  -- ## the weighted Fourier sum `B` and its bound `(2π)^{2k} B ≤ ENormSq k P`
  obtain ⟨hBs, hBC⟩ := ENormSq_ge_weighted_fourierCoeff (ι := ι) k hk P hPk hper
  set B : ℝ := ∑' m : ι → ℤ,
    (∑ j, (((m j : ℤ) : ℝ)) ^ 2) ^ k * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2 with hBdef
  have hBs' : Summable (fun m : ι → ℤ =>
      (∑ j, (((m j : ℤ) : ℝ)) ^ 2) ^ k * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) := hBs
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact tsum_nonneg (fun m => by positivity)
  have hBC' : (2 * Real.pi) ^ (2 * k) * B ≤ Work.Diff.STE.ENormSq k P := by
    rw [hBdef]; exact hBC
  have h2π : (1 : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hpow2 : (2 * Real.pi) ^ 2 ≤ (2 * Real.pi) ^ (2 * k) := by
    obtain ⟨j, hj⟩ : ∃ j, 2 * k = 2 + j := ⟨2 * k - 2, by omega⟩
    rw [hj, pow_add]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ h2π)
  have hB_le : B ≤ Work.Diff.STE.ENormSq k P :=
    le_trans (le_mul_of_one_le_left hBnn (one_le_pow₀ h2π)) hBC'
  have hB_le' : (2 * Real.pi) ^ 2 * B ≤ Work.Diff.STE.ENormSq k P :=
    le_trans (mul_le_mul_of_nonneg_right hpow2 hBnn) hBC'
  -- ## the derivative integral is bounded by `(2π)² B`
  have hpd_le : (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ ^ 2)
      ≤ (2 * Real.pi) ^ 2 * B := by
    rw [hpars_pd, hBdef]
    rw [tsum_congr hmult]
    have hle : ∀ m : ι → ℤ, (2 * Real.pi * (m i : ℝ)) ^ 2
          * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2
        ≤ (2 * Real.pi) ^ 2 * ((∑ j, (((m j : ℤ) : ℝ)) ^ 2) ^ k
          * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) := by
      intro m
      have hw := pow_le_pow_weight (ι := ι) k hk i m
      calc (2 * Real.pi * (m i : ℝ)) ^ 2 * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2
          = (2 * Real.pi) ^ 2 * (((m i : ℤ) : ℝ) ^ 2
              * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) := by ring
        _ ≤ (2 * Real.pi) ^ 2 * ((∑ j, (((m j : ℤ) : ℝ)) ^ 2) ^ k
              * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (by positivity))
              (by positivity)
    have hM : Summable (fun m : ι → ℤ =>
        (2 * Real.pi * (m i : ℝ)) ^ 2 * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun m => by positivity) hle (hBs'.mul_left ((2 * Real.pi) ^ 2))
    calc (∑' m : ι → ℤ, (2 * Real.pi * (m i : ℝ)) ^ 2 * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2)
        ≤ ∑' m : ι → ℤ, (2 * Real.pi) ^ 2 * ((∑ j, (((m j : ℤ) : ℝ)) ^ 2) ^ k
            * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) :=
          Summable.tsum_le_tsum hle hM (hBs'.mul_left _)
      _ = (2 * Real.pi) ^ 2 * (∑' m : ι → ℤ, (∑ j, (((m j : ℤ) : ℝ)) ^ 2) ^ k
            * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) := tsum_mul_left
  -- ## the mean and the tail
  have hmean : ‖∫ x in Work.Diff.STE.unitCube (ι := ι), P x‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * B :=
    le_trans (norm_setIntegral_le_integral_norm_pd i hP1 hPz) hpd_le
  have htailSumm : Summable (fun m : ι → ℤ =>
      if m = 0 then 0 else ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hsumP
    by_cases hm : m = 0
    · subst hm; simp
    · rw [ite_eq_right hm]
  have htail : (∑' m : ι → ℤ, (if m = 0 then 0 else ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2))
      ≤ B := by
    rw [hBdef]
    refine Summable.tsum_le_tsum (fun m => ?_) htailSumm hBs'
    by_cases hm : m = 0
    · subst hm
      simp [zero_pow (by omega : k ≠ 0)]
    · rw [ite_eq_right hm]
      exact le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (one_le_sum_sq_of_ne_zero hm))
  -- ## the `L²` bound `ENormSq 0 P ≤ 2 ENormSq k P`
  have hsplit := hsumP.tsum_eq_add_tsum_ite (0 : ι → ℤ)
  have hEN0 : Work.Diff.STE.ENormSq 0 P ≤ 2 * Work.Diff.STE.ENormSq k P := by
    rw [Work.Diff.STE.ENormSq_zero, hparsP, hsplit]
    have h1 : ‖Work.Diff.STE.fourierCoeff P 0‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * B := by
      have h0 : Work.Diff.STE.fourierCoeff P 0
          = ∫ x in Work.Diff.STE.unitCube (ι := ι), P x := by
        simp [Work.Diff.STE.fourierCoeff, Work.Diff.STE.fourierExp]
      rw [h0]
      exact hmean
    have h2 := htail
    linarith [h1, h2, hB_le, hB_le']
  -- ## conclusion
  calc Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff P)
      ≤ C₁ * (Work.Diff.STE.ENormSq k P + Work.Diff.STE.ENormSq 0 P) := hC₁ P hPk hper
    _ ≤ C₁ * (Work.Diff.STE.ENormSq k P + 2 * Work.Diff.STE.ENormSq k P) :=
        mul_le_mul_of_nonneg_left (by linarith [hEN0]) hC₁nn
    _ = (3 * C₁) * Work.Diff.STE.ENormSq k P := by ring

end Work.Diff.STE.B3
