import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea1.count_annulus

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary consequences of `Params` used in the assembly -/

/-- `θ ≤ 1`: the smoothing parameter (4.15) is `< 1` because `log x > 1` and `A' > 0`.  This is
what turns the polar box (5.14) `|z|² ≤ (1+θ)N` into the `|z|² ≤ 2N` of the lattice count. -/
lemma theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : 1 ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    exact le_of_lt (lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx3))
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have h2 : (0 : ℝ) < 2 * Pa.A + 2 ^ (20 : ℕ) := by
      have := Pa.hA; positivity
    linarith [Pa.hA']
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)

/-- The polar box (5.14) gives `|z|² ≤ (1+θ)N ≤ 2N`. -/
lemma gnorm_le_two_mul_N {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hbox : Work.FITop3.InPolarBox Pa φ z) :
    (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
  obtain ⟨-, -, hle, -⟩ := hbox
  have hθ := theta_le_one Pa
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  nlinarith

/-- **The number of non-coprime `w`'s over a fixed `z`** (*FI* (5.10), the counting half).

For `β` a coefficient of (4.13)+(5.13) with `β z ≠ 0`, the number of `w` in the dyadic annulus
`annM Pa` that are not coprime to `z` in `ℤ[i]` and for which `Re(wz)` is a square is

  `≤ 400 (MN)^{1/4} (1 + √M/(Pz√N)) · ω(|z|²)`.

*Proof route*, from `Submission.Work.FIArea1.count_annulus` and `Basic`:
1. `hβ` gives (`beta_ne_zero_structure`) `Squarefree |z|²`, `N < |z|² ≤ (1+θ)N ≤ 2N`,
   `NoSmallPrimes Pa z` (so every prime `p ∣ |z|²` satisfies `Pz ≤ p`, and `p > 2` because `hP2`),
   and `z ∈ boxN Pa`.
2. Each counted `w` has a common rational prime `p ∣ |z|²`, `p ∣ |w|²`
   (`common_prime_of_not_coprime`); `∃ c, cForm w z = c²` holds since `Zc w z ≠ 0`.  So the counted
   set is contained in the union over `p ∈ (gnorm z).primeFactors` of the sets counted by
   `count_annulus`; the union bound (`Finset.card_biUnion_le`) gives
   `# ≤ Σ_{p ∈ primeFactors} 200 (MN)^{1/4}(1+√M/(p√N))`.
3. `1/p ≤ 1/Pz` for `p ∈ primeFactors` (`NoSmallPrimes`), so the sum is
   `≤ ω(|z|²) · 200 (MN)^{1/4}(1+√M/(Pz√N))`, and `200 ≤ 400`. -/
theorem noncoprime_count {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
      ≤ 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
  obtain ⟨hsq, hbox, hnsp⟩ := beta_ne_zero_structure hβ hz
  have hzhi : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := gnorm_le_two_mul_N hbox
  have hzlo : (Pa.N : ℝ) < (Work.FIPlan.gnorm z : ℝ) := hbox.2.1
  set A : ℝ := (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) with hA
  set B : ℝ := Real.sqrt Pa.M / Real.sqrt Pa.N with hB
  have hMN0 : (0 : ℝ) ≤ Pa.M * Pa.N := by nlinarith [Pa.hM1, Pa.hN1]
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.rpow_nonneg hMN0 _
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set n : ℕ := Work.FIPlan.gnorm z with hn
  have hnpos : 0 < n := by
    have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
    have : (0 : ℝ) < (n : ℝ) := by linarith [hzlo, hN1]
    exact_mod_cast this
  -- Every counted `w` shares a rational prime with `|z|²`, so the counted set is contained in the
  -- union over `p ∈ (gnorm z).primeFactors` of the sets of `count_annulus`.
  have hsub : (Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)
      ⊆ n.primeFactors.biUnion (fun p => (Work.FITop3.annM Pa).filter
          (fun w => p ∣ Work.FIPlan.gnorm w ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwann, hnc, c, hc⟩ := hw
    obtain ⟨p, hpp, hpw, hpz⟩ := common_prime_of_not_coprime hnc
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]; exact ⟨hpp, by rw [hn]; exact hpz, ne_of_gt hnpos⟩
    · rw [Finset.mem_filter]; exact ⟨hwann, hpw, c, hc⟩
  -- `count_annulus` for each prime, in the shape of the `p`-sum
  have hper : ∀ p ∈ n.primeFactors,
      (((Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
        ≤ 200 * A * (1 + B / (p : ℝ)) := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    have hlt : Pa.Pz < p := by
      by_contra hle
      exact hnsp p hpp (le_of_not_gt hle) (by rw [← hn]; exact hpd)
    have hp2 : 2 < p := by have := Pa.hP2; omega
    have hmain := count_annulus (Pa := Pa) (z := z) (p := p) hpp hp2 hzlo hzhi hsq
      (by rw [← hn]; exact hpd)
    have heq : 200 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((p : ℝ) * Real.sqrt Pa.N)) = 200 * A * (1 + B / (p : ℝ)) := by
      rw [hA, hB]
      rw [show Real.sqrt Pa.M / ((p : ℝ) * Real.sqrt Pa.N)
            = (Real.sqrt Pa.M / Real.sqrt Pa.N) / (p : ℝ) by ring]
    rwa [heq] at hmain
  calc (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
      ≤ ((n.primeFactors.biUnion (fun p => (Work.FITop3.annM Pa).filter
          (fun w => p ∣ Work.FIPlan.gnorm w ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ p ∈ n.primeFactors, ((Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ p ∈ n.primeFactors, (((Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ) := by push_cast; ring
    _ ≤ ∑ p ∈ n.primeFactors, 200 * A * (1 + B / (p : ℝ)) := Finset.sum_le_sum hper
    _ = 200 * A * ∑ p ∈ n.primeFactors, (1 + B / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 200 * A * ((n.primeFactors.card : ℝ) * (1 + B / (Pa.Pz : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hPz0 : (0 : ℝ) < (Pa.Pz : ℝ) := by
          have := Pa.hP2; positivity
        calc ∑ p ∈ n.primeFactors, (1 + B / (p : ℝ))
            ≤ ∑ _p ∈ n.primeFactors, (1 + B / (Pa.Pz : ℝ)) := by
              apply Finset.sum_le_sum
              intro p hp
              obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
              have hlt : Pa.Pz < p := by
                by_contra hle
                exact hnsp p hpp (le_of_not_gt hle) (by rw [← hn]; exact hpd)
              have hle : (Pa.Pz : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlt.le
              have : B / (p : ℝ) ≤ B / (Pa.Pz : ℝ) :=
                div_le_div_of_nonneg_left hB0 hPz0 hle
              linarith
          _ = (n.primeFactors.card : ℝ) * (1 + B / (Pa.Pz : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ = 200 * (A * ((n.primeFactors.card : ℕ) : ℝ) * (1 + B / (Pa.Pz : ℝ))) := by ring
    _ ≤ 400 * (A * ((n.primeFactors.card : ℕ) : ℝ) * (1 + B / (Pa.Pz : ℝ))) :=
        mul_le_mul_of_nonneg_right (by norm_num : (200 : ℝ) ≤ 400)
          (mul_nonneg (mul_nonneg hA0 (by positivity)) (by positivity))
    _ = 400 * A * (1 + B / (Pa.Pz : ℝ)) * ((n.primeFactors.card : ℕ) : ℝ) := by ring
    _ = 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
        rw [hA, hB, hn]
        rw [show Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)
              = (Real.sqrt Pa.M / Real.sqrt Pa.N) / (Pa.Pz : ℝ) by ring]

end

end Work.FIArea1
