import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.siegelAbelGrow
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.pairCountHeight_dom

namespace Work.LinnikAreas

open scoped Classical BigOperators

/-- **The mass of one dyadic height layer of high zeros, against the `λ₁`-free count.**
`v` is a finite set of genuine zero-pairs, all *high* (`1 < |Im ρ|`), none of them `(χ₁,β₁)`, all
lying in the dyadic layer `j` (`Nat.log 2 ⌊|Im ρ|⌋ = j`).  Given the `λ₁`-free pair count at height
`2^{j+1}·log q` with constant `C₂·(2^{j+1})^{3/2}` (an instance of `LogFreeFamHeight (5/2) (3/2)`),
the multiplicity-weighted kernel sum over `v` is at most
`400·C₂·(4^j)⁻¹·(2^{j+1})^{3/2}·(log q)^{-2}`.

Proof recipe: `Work.LinnikAreas.high_kernel_le` gives
`mult·‖Hk (11/2) (3/10) ((1-ρ)𝓛)‖ ≤ 4·mult·e^{-(49/10)λ}/(|Im ρ|𝓛)²`; on the layer `hfib` and
`Nat.lt_pow_succ_log_self` give `4^j ≤ |Im ρ|²`, so the kernel factor is `≤ 4·(4^j)⁻¹·𝓛^{-2}`;
then `Work.LinnikAreas.siegelTailAbel` with `D = (2^{j+1})^{3/2}` and `lam = Λ = min_{z∈v} λ(z) > 0`
(`Finset.exists_mem_eq_inf'`, `zeroMult_re_pos`, `boxMaxZeroAux.zeroMult_re_lt_one`, `lamOf`) gives
`Σ_{z∈v} mult·e^{-(49/10)λ} ≤ 100·C₂·(2^{j+1})^{3/2}`. -/
theorem highDyadicLayerFree {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q)
    (β₁ : ℂ) {C₂ : ℝ} (hC₂ : 0 < C₂) (j : ℕ)
    (hgrow : ∀ t : ℝ, 0 < t → t ≤ Real.log q →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t ((2 : ℝ) ^ (j + 1) * Real.log q)
        ≤ C₂ * Real.exp ((5 / 2) * t) * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ))
    (v : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ v, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hhigh : ∀ z ∈ v, 1 < |z.2.im|)
    (hexc : ∀ z ∈ v, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (hfib : ∀ z ∈ v, Nat.log 2 (Nat.floor |z.2.im|) = j) :
    (∑ z ∈ v, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ 400 * C₂ * ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
          * ((Real.log q) ^ 2)⁻¹ := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  set D : ℝ := ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) with hDdef
  set T₀ : ℝ := (2 : ℝ) ^ (j + 1) * Real.log (q : ℝ) with hT₀def
  have hDpos : 0 < D := by rw [hDdef]; positivity
  rcases v.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty]
    positivity
  · -- the minimal `λ` over `v`
    set Λ : ℝ := (v.image (fun z => Work.LinnikContract.lamOf q z.2)).min'
      (Finset.image_nonempty.mpr hne) with hΛdef
    have hΛmem : Λ ∈ v.image (fun z => Work.LinnikContract.lamOf q z.2) := by
      rw [hΛdef]; exact Finset.min'_mem _ _
    have hΛle : ∀ z ∈ v, Λ ≤ Work.LinnikContract.lamOf q z.2 := by
      intro z hz
      rw [hΛdef]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hz)
    have hΛpos : 0 < Λ := by
      obtain ⟨z, hz, hzΛ⟩ := Finset.mem_image.mp hΛmem
      have h1 : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
      have h2 : z.2.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzm z hz)
      rw [← hzΛ, Work.LinnikContract.lamOf]
      exact mul_pos (by linarith) hlog
    -- `1 ≤ T₀`
    have hT0 : 1 ≤ T₀ := by
      rw [hT₀def]
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
          _ ≤ (2 : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hl2 : (1 / 2 : ℝ) ≤ Real.log (q : ℝ) := by
        have h1 : Real.log 2 ≤ Real.log (q : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hq)
        have h2' := Real.log_two_gt_d9
        linarith
      have hprod : (2 : ℝ) * (1 / 2) ≤ (2 : ℝ) ^ (j + 1) * Real.log (q : ℝ) :=
        mul_le_mul h2 hl2 (by norm_num) (by positivity)
      linarith
    -- `|Im z| · log q ≤ T₀` on the layer
    have him : ∀ z ∈ v, |z.2.im| * Real.log (q : ℝ) ≤ T₀ := by
      intro z hz
      rw [hT₀def]
      have hlt : |z.2.im| < (2 : ℝ) ^ (j + 1) := by
        have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
        rw [hfib z hz] at h1
        have h2 : Nat.floor |z.2.im| + 1 ≤ 2 ^ (j + 1) := h1
        have h3 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
        have h4 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast h2
        linarith
      exact mul_le_mul_of_nonneg_right hlt.le hlog.le
    -- the `λ₁`-free tail bound
    have hAb : (∑ z ∈ v, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2)) ≤ 100 * C₂ * D := by
      have htail := siegelTailAbel (q := q) hq χ₁ β₁ (C₂ := C₂) (D := D) (lam := Λ)
        (T₀ := T₀) hC₂ hDpos hΛpos hT0 hgrow v hzm hexc him hΛle
      refine le_trans htail ?_
      have hexp1 : Real.exp (-(49 / 10 - 5 / 2) * Λ) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hΛpos])
      calc 100 * C₂ * D * Real.exp (-(49 / 10 - 5 / 2) * Λ) ≤ 100 * C₂ * D * 1 :=
            mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = 100 * C₂ * D := by ring
    -- per-element kernel bound
    have hstep : ∀ z ∈ v,
        4 * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
            / (|z.2.im| * Real.log (q : ℝ)) ^ 2
          ≤ (4 * ((4 : ℝ) ^ j)⁻¹ * ((Real.log (q : ℝ)) ^ 2)⁻¹)
              * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
                  * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2)) := by
      intro z hz
      have him1 : 1 < |z.2.im| := hhigh z hz
      have h4 : (4 : ℝ) ^ j ≤ |z.2.im| ^ 2 := by
        have hle : (2 : ℝ) ^ j ≤ |z.2.im| := by
          have hn1 : 1 ≤ Nat.floor |z.2.im| := Nat.floor_pos.mpr him1.le
          have hn : Nat.floor |z.2.im| ≠ 0 := by omega
          have hh := Nat.pow_log_le_self 2 hn
          have h1 : (2 : ℝ) ^ j ≤ (Nat.floor |z.2.im| : ℝ) := by
            have h2 : (((2 : ℕ) ^ Nat.log 2 (Nat.floor |z.2.im|) : ℕ) : ℝ)
                ≤ (Nat.floor |z.2.im| : ℝ) := Nat.cast_le.mpr hh
            push_cast at h2
            rwa [hfib z hz] at h2
          have h3 : (Nat.floor |z.2.im| : ℝ) ≤ |z.2.im| := Nat.floor_le (abs_nonneg _)
          linarith
        have h4eq : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
          exact (pow_mul (2 : ℝ) 2 j).symm.trans (pow_mul' (2 : ℝ) 2 j)
        rw [h4eq]
        exact pow_le_pow_left₀ (by positivity) hle 2
      have hpos : 0 < (4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2 := by positivity
      have hle2 : (4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2
          ≤ |z.2.im| ^ 2 * (Real.log (q : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      calc 4 * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
            / (|z.2.im| * Real.log (q : ℝ)) ^ 2
          = 4 * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
            / (|z.2.im| ^ 2 * (Real.log (q : ℝ)) ^ 2) := by rw [mul_pow]
        _ ≤ 4 * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
            / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) hpos hle2
        _ = (4 * ((4 : ℝ) ^ j)⁻¹ * ((Real.log (q : ℝ)) ^ 2)⁻¹)
              * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
                  * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2)) := by
            rw [div_eq_mul_inv, mul_inv]
            ring
    calc (∑ z ∈ v, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
        ≤ ∑ z ∈ v, 4 * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
            / (|z.2.im| * Real.log (q : ℝ)) ^ 2 :=
          Finset.sum_le_sum (fun z hz => high_kernel_le hq z (hzm z hz) (hhigh z hz))
      _ ≤ (4 * ((4 : ℝ) ^ j)⁻¹ * ((Real.log (q : ℝ)) ^ 2)⁻¹)
            * ∑ z ∈ v, ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum hstep
      _ ≤ (4 * ((4 : ℝ) ^ j)⁻¹ * ((Real.log (q : ℝ)) ^ 2)⁻¹) * (100 * C₂ * D) :=
          mul_le_mul_of_nonneg_left hAb (by positivity)
      _ = 400 * C₂ * ((4 : ℝ) ^ j)⁻¹ * D * ((Real.log (q : ℝ)) ^ 2)⁻¹ := by ring

end Work.LinnikAreas
