import Mathlib
import Submission.Work.NN.Core.czB_L2_bounded_C0
import Submission.Work.NN.Core.beltramiHomogeneous_pointwise
import Submission.Work.NN.Core.lintegral_normSq_sum_le
import Submission.Work.NN.Core.czB_L2_bounded_continuous
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.DbarCnPertAux

/-!
# Uniqueness of the homogeneous implicit Beltrami fixed point

The implicit Beltrami system in the flat model `ℂⁿ = Fin n → ℂ` reads

  `V_i = γ⁻¹ Σ_j β_ij ∂_j (Φ V) - Σ_j conj(β_ij) V_j + G_i`

with `Φ = bmPotential` the Bochner–Martinelli potential and `γ = bmGamma`.  This file proves the
**homogeneous** (`G = 0`) statement: any continuous compactly supported field `E` whose potential
`Φ E` is `C¹` and which satisfies the equation with vanishing datum must vanish, provided the
`C^{0,α}`-norm of the coefficients `β` is small.

The argument is the energy (or `L²`) argument of `Work.NN.Core.beltramiImplicit_unique`, which
needs only the pointwise bound `Work.NN.Core.beltramiHomogeneous_pointwise` (valid for an
arbitrary `C^{0,α}`-bounded coefficient family), the `L²` Schauder-type bound
`Work.NN.Core.czB_L2_bounded_C0` on the potential, and the pointwise-to-integral step
`Work.NN.Core.lintegral_normSq_sum_le`.  No smoothness or support hypothesis on `β` is used.

* `beltramiHomogeneous_pointwise` gives, with `A = 2 n² ‖γ⁻¹‖² η²` and `B = 2 n² η²`,
  `∑_i |E_i z|² ≤ A ∑_j |∂_j (Φ E)(z)|² + B ∑_j |E_j z|²` pointwise;
* integrating and applying the `L²` bound `∫ ∑_j |∂_j (Φ E)|² ≤ C² ∫ ∑_j |E_j|²` gives
  `𝓔(E) ≤ (A C² + B) 𝓔(E)` with `𝓔` the `L²`-energy;
* `η` is chosen so that `A C² + B ≤ 1/2`, whence `𝓔(E) = 0`, and continuity forces `E = 0`.
-/

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.NN.Core

theorem implicit_fixpoint_eq_zero {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (β : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) (E : Fin n → Work.NN.Core.Cn n → ℂ),
        (∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ ≤ ENNReal.ofReal η) →
        (∀ j, Continuous (E j)) → (∀ j, HasCompactSupport (E j)) →
        ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential E) →
        (∀ j z, E j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
              (∑ l, β j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z)
            - (∑ l, (starRingEnd ℂ (β j l z)) * E l z)) →
        E = 0 := by
  classical
  obtain ⟨C, hC0, hCbound⟩ := czB_L2_bounded_C0 hn
  set η : ℝ := 1 / (2 * ((n : ℝ) * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1))) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  refine ⟨η, hηpos, ?_⟩
  intro β E hβnorm hEc hEcs hΦE hEeq
  have hpt : ∀ z, (∑ i, ‖E i z‖ ^ 2)
      ≤ 2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2
          * (∑ j, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2)
        + 2 * (n : ℝ) ^ 2 * η ^ 2 * (∑ j, ‖E j z‖ ^ 2) :=
    beltramiHomogeneous_pointwise hn (le_of_lt hηpos) hβnorm hEeq
  set Ee : ENNReal := ∫⁻ z, ∑ j, ENNReal.ofReal (‖E j z‖ ^ 2) with hEedef
  set Le : ENNReal := ∫⁻ z, ∑ j, ENNReal.ofReal
    (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2) with hLedef
  have hEeRaw : (∫⁻ z, ∑ i, ENNReal.ofReal (‖E i z‖ ^ 2))
      ≤ ENNReal.ofReal
          (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2)
          * (∫⁻ z, ∑ j, ENNReal.ofReal
              (‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2))
        + ENNReal.ofReal (2 * (n : ℝ) ^ 2 * η ^ 2)
          * (∫⁻ z, ∑ j, ENNReal.ofReal (‖E j z‖ ^ 2)) :=
    lintegral_normSq_sum_le
      (A := 2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2)
      (B := 2 * (n : ℝ) ^ 2 * η ^ 2) (by positivity) (by positivity) hEc hΦE hpt
  have hEe' : Ee ≤ ENNReal.ofReal
        (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * Le
      + ENNReal.ofReal (2 * (n : ℝ) ^ 2 * η ^ 2) * Ee := by
    rw [hEedef, hLedef]
    exact hEeRaw
  have hEeE : Ee = ENNReal.ofReal (czEnergy E) := by
    rw [hEedef]; exact lintegral_sum_ofReal_normSq E hEc hEcs
  have hcz := hCbound E hEc hEcs hΦE
  have hczLe : Le ≤ ENNReal.ofReal (C ^ 2) * Ee := by
    have h1 : Le = ∫⁻ z, ∑ j, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2 := by
      rw [hLedef]
      exact lintegral_congr fun z =>
        Finset.sum_congr rfl fun j _ => ENNReal.ofReal_pow (norm_nonneg _) 2
    have h2 : Ee = ∫⁻ z, ∑ j, ENNReal.ofReal ‖E j z‖ ^ 2 := by
      rw [hEedef]
      exact lintegral_congr fun z =>
        Finset.sum_congr rfl fun j _ => ENNReal.ofReal_pow (norm_nonneg _) 2
    rw [h1, h2]
    exact hcz
  have hstep1 : ENNReal.ofReal
        (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * Le
      ≤ ENNReal.ofReal
          (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2)
        * (ENNReal.ofReal (C ^ 2) * Ee) :=
    mul_le_mul_of_nonneg_left hczLe bot_le
  have hstep2 : ENNReal.ofReal
        (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2)
      * (ENNReal.ofReal (C ^ 2) * Ee)
      = ENNReal.ofReal
          ((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2)
        * Ee := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul
      (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2
        * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2)]
  have hq : Ee ≤ ENNReal.ofReal
      ((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
        + 2 * (n : ℝ) ^ 2 * η ^ 2) * Ee := by
    calc Ee ≤ ENNReal.ofReal
            (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * Le
          + ENNReal.ofReal (2 * (n : ℝ) ^ 2 * η ^ 2) * Ee := hEe'
      _ ≤ ENNReal.ofReal
            (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2)
            * (ENNReal.ofReal (C ^ 2) * Ee)
          + ENNReal.ofReal (2 * (n : ℝ) ^ 2 * η ^ 2) * Ee := add_le_add_left hstep1 _
      _ = ENNReal.ofReal
            ((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2) * Ee
          + ENNReal.ofReal (2 * (n : ℝ) ^ 2 * η ^ 2) * Ee := by rw [hstep2]
      _ = ENNReal.ofReal
            ((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
              + 2 * (n : ℝ) ^ 2 * η ^ 2) * Ee := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hq0 : 0 ≤ (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
      + 2 * (n : ℝ) ^ 2 * η ^ 2 := by positivity
  have hE : czEnergy E ≤ ((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2)
        * C ^ 2 + 2 * (n : ℝ) ^ 2 * η ^ 2) * czEnergy E := by
    have hEE : ENNReal.ofReal (czEnergy E) ≤ ENNReal.ofReal
        (((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
          + 2 * (n : ℝ) ^ 2 * η ^ 2) * czEnergy E) := by
      calc ENNReal.ofReal (czEnergy E) = Ee := hEeE.symm
        _ ≤ ENNReal.ofReal
              ((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
                + 2 * (n : ℝ) ^ 2 * η ^ 2) * Ee := hq
        _ = ENNReal.ofReal
              ((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
                + 2 * (n : ℝ) ^ 2 * η ^ 2) * ENNReal.ofReal (czEnergy E) := by rw [hEeE]
        _ = ENNReal.ofReal
              (((2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
                + 2 * (n : ℝ) ^ 2 * η ^ 2) * czEnergy E) :=
            (ENNReal.ofReal_mul hq0).symm
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hq0 (czEnergy_nonneg E))).mp hEE
  have hq_le : (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
      + 2 * (n : ℝ) ^ 2 * η ^ 2 ≤ 1 / 2 := by
    have hgC : ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * C ^ 2 + 1
        ≤ (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1) ^ 2 := by
      nlinarith [mul_nonneg (norm_nonneg ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) hC0]
    have hqid : (2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * η ^ 2) * C ^ 2
        + 2 * (n : ℝ) ^ 2 * η ^ 2
        = 2 * (n : ℝ) ^ 2 * η ^ 2
          * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * C ^ 2 + 1) := by
      ring
    rw [hqid, hηdef]
    have hhalf : 2 * (n : ℝ) ^ 2
          * (1 / (2 * ((n : ℝ) * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1)))) ^ 2
          * ((‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1) ^ 2) ≤ 1 / 2 := by
      have hd : (2 * ((n : ℝ) * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1))) ≠ 0 := by
        positivity
      field_simp
      norm_num
    calc 2 * (n : ℝ) ^ 2
            * (1 / (2 * ((n : ℝ) * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1)))) ^ 2
            * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * C ^ 2 + 1)
        ≤ 2 * (n : ℝ) ^ 2
            * (1 / (2 * ((n : ℝ) * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1)))) ^ 2
            * ((‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C + 1) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hgC; positivity
      _ ≤ 1 / 2 := hhalf
  have hE0 : czEnergy E = 0 := by
    have h2 : czEnergy E ≤ (1 / 2) * czEnergy E :=
      hE.trans (mul_le_mul_of_nonneg_right hq_le (czEnergy_nonneg E))
    nlinarith [czEnergy_nonneg E]
  have hEzero : E = 0 := by
    have hsum : (∑ j, ∫ z, ‖E j z‖ ^ 2) = 0 := by simpa only [czEnergy] using hE0
    have hterm : ∀ j, ∫ z, ‖E j z‖ ^ 2 = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => integral_nonneg fun z => by positivity)).mp hsum j (Finset.mem_univ j)
    funext j z
    have hint : Integrable (fun z => ‖E j z‖ ^ 2) := integrable_normSq (E j) (hEc j) (hEcs j)
    have hae : (fun z => ‖E j z‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint).mp (hterm j)
    have hfun : (fun z => ‖E j z‖ ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq volume ((hEc j).norm.pow 2) continuous_const).mp hae
    have h3 : ‖E j z‖ ^ 2 = 0 := by simpa using congrFun hfun z
    have h4 : ‖E j z‖ = 0 := sq_eq_zero_iff.mp h3
    exact norm_eq_zero.mp h4
  exact hEzero

end Work.NN.Core
