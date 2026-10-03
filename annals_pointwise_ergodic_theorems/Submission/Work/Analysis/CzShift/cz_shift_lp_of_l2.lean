import Mathlib
import Submission.Work.Analysis.CzShift.offdiag_le
import Submission.Work.Analysis.CzShift.lp_bound_large_p

/-!
# The `L^p` bound of the shifted Calderón–Zygmund theorem, from the `L²` bound

This module proves `Work.Analysis.CzShift.cz_shift_lp_of_l2`, the final statement of
Appendix B of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. **195** (2022): for a family of shifted convolution
kernels `x ↦ σ i⁻¹ Ψ((x − t i σ i)/σ i)` attached to a lacunary family of scales `σ` and
shifts `t` bounded by `2 ^ K`, an `L²` bound with constant `Cm` implies an `L^p` bound for
every `1 < p`, with constant `C (B (1 + K) + 1)`.

The proof combines

* the off-diagonal (Hörmander) estimate `offdiag_le` for the kernel family, with constant
  `C_off B (1 + K)`,
* the `L^p` theory `lp_bound_small_p` (`1 < p < 2`, Marcinkiewicz interpolation between the
  weak-type `(1,1)` bound and the `L²` bound) and `lp_bound_large_p` (`2 < p`, by duality),

and, in the case `p = 2`, the `L²` bound itself.

The off-diagonal constant `C_off` provided by `offdiag_le` is *uniform* in the index type
`ι` (it is the closed constant `(2π+1)/(1−λ⁻¹) + 2π(1 + log 2/log λ)` of its proof), but
`offdiag_le` is stated with `{ι}` outside the existential, so the uniform form is recorded
separately below as `offdiag_uniform`.
-/

namespace Work.Analysis.CzShift

open MeasureTheory Finset
open scoped ENNReal

universe u

/-- **The off-diagonal estimate, with the index type inside the existential.**  This is
`offdiag_le` with the constant chosen once and for all, so that it can be used in a
statement whose `∃ C` quantifier precedes the universal quantifier over `ι`.  (The proof is
that of `offdiag_le`, with the explicit constant `(2π+1)/(1−λ⁻¹) + 2π(1 + log 2/log λ)`.) -/
private theorem offdiag_uniform (lam : ℝ) (hlam : 1 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (D : Finset ι) (σ t : ι → ℝ) (Ψ Ψ' : ℝ → ℝ)
      (B K : ℝ),
      LacunaryFam lam D σ → IsCZSeed Ψ Ψ' B → 1 ≤ K → (∀ i ∈ D, |t i| ≤ 2 ^ K) →
      ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
        ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - y) - shiftKernel Ψ (σ i) (t i) x‖
          ≤ ENNReal.ofReal (C * B * (1 + K)) := by
  set C : ℝ := (2 * Real.pi + 1) / (1 - lam⁻¹)
    + 2 * Real.pi * (1 + Real.log 2 / Real.log lam) with hC
  have hCpos : 0 < C := by
    rw [hC]
    have hu : 0 < 1 - lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam)
    have hl : 0 < Real.log lam := Real.log_pos hlam
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro ι D σ t Ψ Ψ' B K hlac hseed hK ht L hL y hyL
  have hB : 0 ≤ B := le_trans zero_lt_one.le hseed.one_le
  rcases eq_or_ne y 0 with rfl | hy0
  · have hzero : ∀ i : ι, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - 0) - shiftKernel Ψ (σ i) (t i) x‖ = 0 := by
      intro i
      simp
    rw [Finset.sum_eq_zero (fun i _ => hzero i)]
    exact bot_le
  · have hρpos : 0 < |y| := abs_pos.mpr hy0
    have hρL : 2 * |y| ≤ L := by linarith [abs_nonneg y, hyL]
    have hper : ∀ i ∈ D, (∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - y) - shiftKernel Ψ (σ i) (t i) x‖)
        ≤ ENNReal.ofReal (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
            else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
            else 2 * Real.pi * B) := by
      intro i hi
      have hσi : 0 < σ i := hlac.1 i hi
      by_cases h1 : 2 * |y| ≤ σ i
      · rw [if_pos h1]
        exact offdiag_case_large hseed hσi h1 hL
      · rw [if_neg h1]
        by_cases h2 : |t i * σ i| ≤ 45 * L
        · rw [if_pos h2]
          exact offdiag_case_near hseed hσi hL hyL h2
        · rw [if_neg h2]
          exact offdiag_case_far hseed hσi hL
    have hnn : ∀ i ∈ D, 0 ≤ (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
        else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
        else 2 * Real.pi * B) := by
      intro i hi
      have hσi : 0 < σ i := hlac.1 i hi
      by_cases h1 : 2 * |y| ≤ σ i
      · rw [if_pos h1]; positivity
      · rw [if_neg h1]
        by_cases h2 : |t i * σ i| ≤ 45 * L
        · rw [if_pos h2]; positivity
        · rw [if_neg h2]; positivity
    calc ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - y) - shiftKernel Ψ (σ i) (t i) x‖
        ≤ ∑ i ∈ D, ENNReal.ofReal (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
            else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
            else 2 * Real.pi * B) := Finset.sum_le_sum hper
      _ = ENNReal.ofReal (∑ i ∈ D, (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
            else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
            else 2 * Real.pi * B)) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
      _ ≤ ENNReal.ofReal (C * B * (1 + K)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsum := lacunary_offdiag_sum lam |y| L B K hlam hρpos hL hρL hB hK D σ t hlac ht
          have hCv : C = (2 * Real.pi + 1) / (1 - lam⁻¹)
              + 2 * Real.pi * (1 + Real.log 2 / Real.log lam) := hC
          have hprod : B * (1 + K) * ((2 * Real.pi + 1) / (1 - lam⁻¹)
                + 2 * Real.pi * (1 + Real.log 2 / Real.log lam)) = C * B * (1 + K) := by
            rw [hCv]; ring
          rw [hprod] at hsum
          exact hsum

/-! ## The main reduction: from the `L²` bound to the `L^p` bound -/

/-- The reduction of `cz_shift_lp_of_l2` to an abstract `L^p` provider: given a theorem
bounding `czOp D K ε` on `L^p` by `C₁ (A₂² + A_k + 1)` under an `L²` bound `A₂` and an
off-diagonal condition `A_k`, the shifted kernel family `shiftKernelFam Ψ σ t` satisfies the
conclusion of `cz_shift_lp_of_l2`. -/
private theorem shiftKernel_lp_of_provider (lam B Cm p C1 : ℝ)
    (hlam : 1 < lam) (hB : 1 ≤ B) (hCm : 0 ≤ Cm) (hC1 : 0 < C1)
    (hprov : ∀ {ι : Type} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (Ak A2 : ℝ)
      (hAk : 0 ≤ Ak) (hA2 : 0 < A2) (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
      (hKmeas : ∀ i ∈ D, AEStronglyMeasurable (K i) volume)
      (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
      (hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
        ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖K i (x - y) - K i x‖ ≤ ENNReal.ofReal Ak)
      (hL2 : ∀ f : ℝ → H, Integrable f → MemLp f 2 volume →
        eLpNorm (czOp D K ε f) 2 volume ≤ ENNReal.ofReal A2 * eLpNorm f 2 volume),
      ∀ f : ℝ → H, Integrable f →
        eLpNorm (czOp D K ε f) (ENNReal.ofReal p) volume
          ≤ ENNReal.ofReal (C1 * (A2 ^ 2 + Ak + 1)) * eLpNorm f (ENNReal.ofReal p) volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (σ t : ι → ℝ) (Ψ Ψ' : ℝ → ℝ) (K : ℝ)
      (hlac : LacunaryFam lam D σ) (hseed : IsCZSeed Ψ Ψ' B) (hK : 1 ≤ K)
      (ht : ∀ i ∈ D, |t i| ≤ 2 ^ K)
      (hL2 : ∀ (ε : ι → ℂ), (∀ i ∈ D, ‖ε i‖ ≤ 1) → ∀ f : ℝ → H,
        MeasureTheory.Integrable f → MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal Cm * MeasureTheory.eLpNorm f 2 MeasureTheory.volume),
      ∀ (ε : ι → ℂ), (∀ i ∈ D, ‖ε i‖ ≤ 1) → ∀ f : ℝ → H,
        MeasureTheory.Integrable f → MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) (ENNReal.ofReal p)
            MeasureTheory.volume
          ≤ ENNReal.ofReal (C * (B * (1 + K) + 1))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
  obtain ⟨Coff, hCoffpos, hCoff⟩ := offdiag_uniform lam hlam
  refine ⟨C1 * (Coff + ((Cm + 1) ^ 2 + 1) / 3), ?_, ?_⟩
  · have h1 : (0 : ℝ) < ((Cm + 1) ^ 2 + 1) / 3 := by positivity
    exact mul_pos hC1 (by linarith)
  · intro ι H _ _ _ D σ t Ψ Ψ' K hlac hseed hK ht hL2 ε hε f hf _
    have hKmeas : ∀ i ∈ D, AEStronglyMeasurable (shiftKernelFam Ψ σ t i) volume :=
      fun i _ => (continuous_shiftKernel hseed (σ i) (t i)).aestronglyMeasurable
    have hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖shiftKernelFam Ψ σ t i x‖ ≤ C :=
      fun i hi => ⟨B / σ i, fun x => (kernel_bounds hseed).1 (σ i) (t i) (hlac.1 i hi) x⟩
    have hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
        ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖shiftKernelFam Ψ σ t i (x - y) - shiftKernelFam Ψ σ t i x‖
            ≤ ENNReal.ofReal (Coff * B * (1 + K)) :=
      hCoff D σ t Ψ Ψ' B K hlac hseed hK ht
    have hAk : (0 : ℝ) ≤ Coff * B * (1 + K) :=
      mul_nonneg (mul_nonneg hCoffpos.le (lt_of_lt_of_le zero_lt_one hB).le)
        (by linarith : (0 : ℝ) ≤ 1 + K)
    have hA2 : (0 : ℝ) < Cm + 1 := by linarith
    have hL2' : ∀ g : ℝ → H, Integrable g → MemLp g 2 volume →
        eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε g) 2 volume
          ≤ ENNReal.ofReal (Cm + 1) * eLpNorm g 2 volume := by
      intro g hg hgm
      refine (hL2 ε hε g hg hgm).trans ?_
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le
    have hmain := hprov D (shiftKernelFam Ψ σ t) ε (Coff * B * (1 + K)) (Cm + 1)
        hAk hA2 hε hKmeas hKbdd hoff hL2' f hf
    refine hmain.trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    have hBK : (2 : ℝ) ≤ B * (1 + K) := by
      have h1 : (2 : ℝ) ≤ 1 + K := by linarith
      calc (2 : ℝ) = 1 * 2 := by ring
        _ ≤ B * (1 + K) := mul_le_mul hB h1 (by norm_num) (by linarith)
    have hS : (3 : ℝ) ≤ B * (1 + K) + 1 := by linarith
    have hX0 : (0 : ℝ) ≤ (Cm + 1) ^ 2 + 1 := by positivity
    have hXle : (Cm + 1) ^ 2 + 1 ≤ ((Cm + 1) ^ 2 + 1) / 3 * (B * (1 + K) + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hX0, hS]
    calc C1 * ((Cm + 1) ^ 2 + Coff * B * (1 + K) + 1)
        = C1 * ((Cm + 1) ^ 2 + 1) + C1 * Coff * B * (1 + K) := by ring
      _ ≤ C1 * (((Cm + 1) ^ 2 + 1) / 3 * (B * (1 + K) + 1))
            + C1 * (Coff * (B * (1 + K) + 1)) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hXle hC1.le
          · have h1 : B * (1 + K) ≤ B * (1 + K) + 1 := by linarith
            have h2 : Coff * B * (1 + K) ≤ Coff * (B * (1 + K) + 1) := by
              calc Coff * B * (1 + K) = Coff * (B * (1 + K)) := by ring
                _ ≤ Coff * (B * (1 + K) + 1) := mul_le_mul_of_nonneg_left h1 hCoffpos.le
            calc C1 * Coff * B * (1 + K) = C1 * (Coff * B * (1 + K)) := by ring
              _ ≤ C1 * (Coff * (B * (1 + K) + 1)) := mul_le_mul_of_nonneg_left h2 hC1.le
      _ = C1 * (Coff + ((Cm + 1) ^ 2 + 1) / 3) * (B * (1 + K) + 1) := by ring

theorem cz_shift_lp_of_l2 (lam B Cm : ℝ) (hlam : 1 < lam) (hB : 1 ≤ B) (hCm : 0 ≤ Cm)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (σ t : ι → ℝ) (Ψ Ψ' : ℝ → ℝ) (K : ℝ)
      (hlac : LacunaryFam lam D σ) (hseed : IsCZSeed Ψ Ψ' B) (hK : 1 ≤ K)
      (ht : ∀ i ∈ D, |t i| ≤ 2 ^ K)
      (hL2 : ∀ (ε : ι → ℂ), (∀ i ∈ D, ‖ε i‖ ≤ 1) → ∀ f : ℝ → H,
        MeasureTheory.Integrable f → MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal Cm * MeasureTheory.eLpNorm f 2 MeasureTheory.volume),
      ∀ (ε : ι → ℂ), (∀ i ∈ D, ‖ε i‖ ≤ 1) → ∀ f : ℝ → H,
        MeasureTheory.Integrable f → MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) (ENNReal.ofReal p)
            MeasureTheory.volume
          ≤ ENNReal.ofReal (C * (B * (1 + K) + 1))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
  rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
  · obtain ⟨C1, hC1pos, hC1⟩ := lp_bound_small_p hp hp2
    exact shiftKernel_lp_of_provider lam B Cm p C1 hlam hB hCm hC1pos hC1
  · subst hp2
    refine ⟨(Cm + 1) / 3, ?_, ?_⟩
    · positivity
    · intro ι H _ _ _ D σ t Ψ Ψ' K hlac hseed hK ht hL2 ε hε f hf hmem
      have hcm : MemLp f 2 volume := by simpa only [ENNReal.ofReal_ofNat] using hmem
      have hmain := hL2 ε hε f hf hcm
      have hS : (3 : ℝ) ≤ B * (1 + K) + 1 := by
        have h1 : (2 : ℝ) ≤ 1 + K := by linarith
        have h2 : (2 : ℝ) ≤ B * (1 + K) := by
          calc (2 : ℝ) = 1 * 2 := by ring
            _ ≤ B * (1 + K) := mul_le_mul hB h1 (by norm_num) (by linarith)
        linarith
      have hconst : Cm ≤ (Cm + 1) / 3 * (B * (1 + K) + 1) := by
        nlinarith [hS, hCm]
      calc eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) (ENNReal.ofReal 2) volume
          = eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) 2 volume := by
            rw [ENNReal.ofReal_ofNat]
        _ ≤ ENNReal.ofReal Cm * eLpNorm f 2 volume := hmain
        _ ≤ ENNReal.ofReal ((Cm + 1) / 3 * (B * (1 + K) + 1)) * eLpNorm f 2 volume :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hconst) zero_le
        _ = ENNReal.ofReal ((Cm + 1) / 3 * (B * (1 + K) + 1))
              * eLpNorm f (ENNReal.ofReal 2) volume := by rw [ENNReal.ofReal_ofNat]
  · obtain ⟨C1, hC1pos, hC1⟩ := lp_bound_large_p hp2
    exact shiftKernel_lp_of_provider lam B Cm p C1 hlam hB hCm hC1pos hC1

end Work.Analysis.CzShift
