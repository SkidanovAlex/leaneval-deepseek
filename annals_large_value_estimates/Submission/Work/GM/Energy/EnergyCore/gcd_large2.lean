import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.EnergyCore.Setup2
import Submission.Work.GM.Energy.Basic.card_sq_le_energy
import Submission.Work.GM.Energy.Basic.energy_le_three_mul_cube
import Submission.Work.GM.Energy.EnergyCore.sum_Md_le2
import Submission.Work.GM.Energy.EnergyCore.sum_Md_sq_le2
import Submission.Work.GM.Energy.EnergyCore.cs_reduction2
import Submission.Work.GM.Energy.EnergyCore.gcd_decomp2
import Submission.Work.GM.Energy.EnergyCore.second_moment_sum_le2
import Submission.Work.GM.Energy.EnergyCore.fourth_moment_sum_le2
import Submission.Work.GM.Energy.EnergyCore.assembly_le2

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary sums

`Smom N A W p` is `Σ_{d ∈ [A,2N]} Σ_{n₁,n₂ ∈ [⌈N/d⌉,2⌈N/d⌉]} ‖R(n₁/n₂)‖^p`. -/

/-- `Σ_{d ∈ [A,2N]} Σ_{n₁,n₂ ∈ [⌈N/d⌉,2⌈N/d⌉]} ‖R(n₁/n₂)‖^p`. -/
noncomputable def Smom (N A : ℕ) (W : Finset ℝ) (p : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc A (2 * N),
    ∑ n1 ∈ Finset.Icc (Md N d) (2 * Md N d),
      ∑ n2 ∈ Finset.Icc (Md N d) (2 * Md N d),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ p

/-- `Σ_{n₁,n₂ ∈ [⌈N/d⌉,2⌈N/d⌉]} ‖R(n₁/n₂)‖^p` (fixed `d`). -/
noncomputable def SmomD (N d : ℕ) (W : Finset ℝ) (p : ℕ) : ℝ :=
  ∑ n1 ∈ Finset.Icc (Md N d) (2 * Md N d),
    ∑ n2 ∈ Finset.Icc (Md N d) (2 * Md N d),
      ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ p

/-! ## Temporary placeholders for the delegated lemmas still in progress. -/





/-- **GM Lemma 11.9** (large GCD terms), given the discrete second and fourth moment bounds
(GM Lemmas 11.5, 11.6, each with its own `T^ε` loss) at *every* scale `M`, and with `D = N²/T`:
`Σ_{gcd(n₁,n₂)≥D} ‖R(n₁/n₂)‖³ ⪅ N²ᵋ (N|W|³ + NT^{1/4}|W|^{21/8} + E(W)^{1/2}|W|^{1/2}N²)`.
(The conclusion records `N^{2ε}` because the two Cauchy–Schwarz factors each carry `T^ε = N^{6ε/5}`;
see the route: `n₁ = d n₁'`, `n₂ = d n₂'` with `M = N/d`, Cauchy–Schwarz with the second and fourth
moment bounds, summing over `d ≥ D` by Cauchy–Schwarz, then the case analysis `|W| ⋚ T^{2/3}` using
`N ≥ T^{3/4}`, `E(W) ≤ |W|³` and `E(W) ≥ |W|²`.) -/
theorem gcd_large2 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (C₂ : ℝ), 0 < C₂ → ∀ (C₄ : ℝ), 0 < C₄ →
      (∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
        (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
          ≤ C₂ * T ^ ε * ((W.card : ℝ) ^ 2 * (M : ℝ) + (W.card : ℝ) * (M : ℝ) ^ 2
              + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ))) →
      (∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
        (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
          ≤ C₄ * T ^ ε * ((W.card : ℝ) ^ 4 * (M : ℝ)
              + (M : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
              + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                  * T ^ ((1 : ℝ) / 2) * (M : ℝ))) →
      ∀ (N : ℕ), 100 ≤ N → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
        Submission.GM.Separated W 1 →
        (∑ n1 ∈ Finset.Icc N (2 * N),
            ∑ n2 ∈ (Finset.Icc N (2 * N)).filter
              (fun n2 => (N : ℝ) ^ 2 / Submission.LargeValues.M N ≤ (Nat.gcd n1 n2 : ℝ)),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
          ≤ C * (C₂ + 1) ^ ((1 : ℝ) / 2) * (C₄ + 1) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (2 * ε) *
              ((N : ℝ) * (W.card : ℝ) ^ 3
                + (N : ℝ) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 4)
                    * (W.card : ℝ) ^ ((21 : ℝ) / 8)
                + (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2) * (W.card : ℝ) ^ ((1 : ℝ) / 2)
                    * (N : ℝ) ^ 2) := by
  obtain ⟨C0, hC0pos, hC0bd⟩ := assembly_le ε hε
  obtain ⟨cL, hcLpos, hcLbd⟩ := exists_log_bound ε hε
  refine ⟨20 * C0 * (cL + 1) ^ 2 + 1, by positivity, ?_⟩
  intro C₂ hC₂ C₄ hC₄ h2 h4 N hN W hW hsep
  have hN1 : 1 ≤ N := by linarith
  set T : ℝ := Submission.LargeValues.M N with hTdef
  set K : ℝ := (W.card : ℝ) with hKdef
  set E : ℝ := (Submission.GM.energy W : ℝ) with hEdef
  set Λ : ℝ := 1 + Real.log (2 * (N : ℝ)) with hΛdef
  set D : ℝ := (N : ℝ) ^ 2 / Submission.LargeValues.M N with hDdef
  set A0 : ℕ := ⌈D⌉₊ with hA0def
  have hT1 : 1 ≤ T := by rw [hTdef]; exact one_le_MN hN1
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTe0 : (0 : ℝ) ≤ T ^ ε := Real.rpow_nonneg hTpos.le ε
  have hTsqrt : T ^ ((1 : ℝ) / 2) ≤ (N : ℝ) := by
    rw [hTdef]; exact MN_rpow_half_le_N hN1
  have hT32 : T ^ ((3 : ℝ) / 2) ≤ (N : ℝ) ^ 2 := by
    rw [hTdef, Submission.LargeValues.M,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    have h1 : (6 : ℝ) / 5 * ((3 : ℝ) / 2) = 9 / 5 := by norm_num
    rw [h1]
    calc (N : ℝ) ^ (9 / 5 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
      _ = (N : ℝ) ^ 2 := Real.rpow_two (N : ℝ)
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hKE2 : K ^ 2 ≤ E := by
    rw [hKdef, hEdef]; exact Basic.card_sq_le_energy W
  have hKE3 : E ≤ 3 * K ^ 3 := by
    rw [hKdef, hEdef]; exact Basic.energy_le_three_mul_cube hsep
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛdef]
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hΛb : Λ ≤ cL * (N : ℝ) ^ (ε / 5) := by rw [hΛdef]; exact hcLbd N hN1
  have hDle : D ≤ (A0 : ℝ) := by rw [hA0def]; exact Nat.le_ceil D
  have hA0ge : 1 ≤ A0 := by
    rw [hA0def]
    have hDpos : 0 < D := by
      rw [hDdef]
      exact div_pos (by positivity) (by rw [← hTdef]; exact hTpos)
    exact Nat.ceil_pos.mpr hDpos
  set S1 : ℝ := ∑ d ∈ Finset.Icc A0 (2 * N), (Md N d : ℝ) with hS1def
  set S2 : ℝ := ∑ d ∈ Finset.Icc A0 (2 * N), (Md N d : ℝ) ^ 2 with hS2def
  have hS1' : (∑ d ∈ Finset.Icc A0 (2 * N), (Md N d : ℝ))
      ≤ 4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) :=
    sum_Md_le N A0 hN1 hA0ge
  have hS2' : (∑ d ∈ Finset.Icc A0 (2 * N), (Md N d : ℝ) ^ 2)
      ≤ 20 * Submission.LargeValues.M N := by
    refine sum_Md_sq_le N A0 hN1 hA0ge ?_
    rw [← hDdef]; exact hDle
  have hS1 : S1 ≤ 4 * (N : ℝ) * Λ := by rw [hS1def, hΛdef]; exact hS1'
  have hS2 : S2 ≤ 20 * T := by rw [hS2def, hTdef]; exact hS2'
  set Tsum : ℝ := (N : ℝ) * K ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
      + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2 with hTsumdef
  have hTsum0 : 0 ≤ Tsum := by rw [hTsumdef]; positivity
  -- Step 1: gcd decomposition
  have hLHS : (∑ n1 ∈ Finset.Icc N (2 * N),
      ∑ n2 ∈ (Finset.Icc N (2 * N)).filter
        (fun n2 => (N : ℝ) ^ 2 / Submission.LargeValues.M N ≤ (Nat.gcd n1 n2 : ℝ)),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3) ≤ Smom N A0 W 3 := by
    have h := gcd_decomp N hN1 D W
    rw [← hA0def] at h
    rw [hDdef] at h
    simpa only [Smom, SmomD] using h
  -- Step 2: Cauchy–Schwarz
  have hCS : Smom N A0 W 3 ≤ Real.sqrt (Smom N A0 W 2) * Real.sqrt (Smom N A0 W 4) := by
    have h := cs_reduction N A0 W
    simpa only [Smom, SmomD] using h
  have hP0 : 0 ≤ Smom N A0 W 2 := by
    unfold Smom
    exact Finset.sum_nonneg (fun d _ =>
      Finset.sum_nonneg (fun n1 _ => Finset.sum_nonneg (fun n2 _ =>
        pow_nonneg (norm_nonneg _) 2)))
  have hQ0 : 0 ≤ Smom N A0 W 4 := by
    unfold Smom
    exact Finset.sum_nonneg (fun d _ =>
      Finset.sum_nonneg (fun n1 _ => Finset.sum_nonneg (fun n2 _ =>
        pow_nonneg (norm_nonneg _) 4)))
  -- Step 3: the second and fourth moment sums
  have hSmom2 : Smom N A0 W 2 ≤ (20 * (C₂ + 1) * T ^ ε) *
      (K ^ 2 * ((N : ℝ) * Λ) + K * T
        + K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) := by
    have h := second_moment_sum_le ε C₂ hC₂ h2 N A0 hN1 hA0ge W hW hsep
      (by rw [← hS1def]; exact hS1') (by rw [← hS2def]; exact hS2')
    rw [← hTdef] at h
    rw [← hKdef] at h
    rw [← hΛdef] at h
    refine le_trans h ?_
    have hα0 : 0 ≤ K ^ 2 * ((N : ℝ) * Λ) + K * T
        + K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) := by positivity
    have hcoef : 20 * C₂ * T ^ ε ≤ 20 * (C₂ + 1) * T ^ ε := by nlinarith [hTe0, hC₂.le]
    exact mul_le_mul_of_nonneg_right hcoef hα0
  have hSmom4 : Smom N A0 W 4 ≤ (20 * (C₄ + 1) * T ^ ε) *
      (K ^ 4 * ((N : ℝ) * Λ) + E * T
        + E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) := by
    have h := fourth_moment_sum_le ε C₄ hC₄ h4 N A0 hN1 hA0ge W hW hsep
      (by rw [← hS1def]; exact hS1') (by rw [← hS2def]; exact hS2')
    rw [← hTdef] at h
    rw [← hKdef] at h
    rw [← hEdef] at h
    rw [← hΛdef] at h
    refine le_trans h ?_
    have hβ0 : 0 ≤ K ^ 4 * ((N : ℝ) * Λ) + E * T
        + E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) := by positivity
    have hcoef : 20 * C₄ * T ^ ε ≤ 20 * (C₄ + 1) * T ^ ε := by nlinarith [hTe0, hC₄.le]
    exact mul_le_mul_of_nonneg_right hcoef hβ0
  -- Step 4: the real-variable assembly
  have hAsm := hC0bd N hN T K E (20 * (C₂ + 1) * T ^ ε) (20 * (C₄ + 1) * T ^ ε) Λ cL
    (Smom N A0 W 2) (Smom N A0 W 4)
    hTdef hT1 hTsqrt hT32 hΛ1 hcLpos.le hΛb hK0 hKE2 hKE3
    (by positivity) (by positivity) hP0 hQ0 hSmom2 hSmom4
  -- Step 5: square-root arithmetic
  have hsqrt1 : Real.sqrt ((20 * (C₂ + 1) * T ^ ε) * (20 * (C₄ + 1) * T ^ ε))
      = 20 * Real.sqrt ((C₂ + 1) * (C₄ + 1)) * T ^ ε := by
    have h2 : (20 * (C₂ + 1) * T ^ ε) * (20 * (C₄ + 1) * T ^ ε)
        = (400 * ((C₂ + 1) * (C₄ + 1))) * (T ^ ε) ^ 2 := by ring
    rw [h2, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 400 * ((C₂ + 1) * (C₄ + 1))),
      Real.sqrt_sq hTe0]
    rw [show (400 : ℝ) * ((C₂ + 1) * (C₄ + 1)) = 20 ^ 2 * ((C₂ + 1) * (C₄ + 1)) by
          norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (20 : ℝ) ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (20 : ℝ))]
  have hsqrt2 : Real.sqrt ((C₂ + 1) * (C₄ + 1))
      = (C₂ + 1) ^ ((1 : ℝ) / 2) * (C₄ + 1) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ C₂ + 1),
      ← Real.sqrt_eq_rpow (C₂ + 1), ← Real.sqrt_eq_rpow (C₄ + 1)]
  have hNmul : (N : ℝ) ^ (4 * ε / 5) * T ^ ε = (N : ℝ) ^ (2 * ε) := by
    have hTeq : T ^ ε = (N : ℝ) ^ ((6 : ℝ) / 5 * ε) := by
      rw [hTdef]; exact MN_rpow_eps ε N
    rw [hTeq, ← Real.rpow_add (by positivity : (0 : ℝ) < (N : ℝ))]
    congr 1
    ring
  have hnonneg : 0 ≤ (C₂ + 1) ^ ((1 : ℝ) / 2) * (C₄ + 1) ^ ((1 : ℝ) / 2)
      * (N : ℝ) ^ (2 * ε) * Tsum := by
    have h1 : (0 : ℝ) ≤ (C₂ + 1) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ (C₄ + 1) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) ≤ (N : ℝ) ^ (2 * ε) := Real.rpow_nonneg (by positivity) _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hTsum0
  calc (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter
          (fun n2 => (N : ℝ) ^ 2 / Submission.LargeValues.M N ≤ (Nat.gcd n1 n2 : ℝ)),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
      ≤ Smom N A0 W 3 := hLHS
    _ ≤ Real.sqrt (Smom N A0 W 2) * Real.sqrt (Smom N A0 W 4) := hCS
    _ = Real.sqrt (Smom N A0 W 2 * Smom N A0 W 4) := (Real.sqrt_mul hP0 _).symm
    _ ≤ C0 * (cL + 1) ^ 2 * Real.sqrt ((20 * (C₂ + 1) * T ^ ε) * (20 * (C₄ + 1) * T ^ ε))
          * (N : ℝ) ^ (4 * ε / 5) * Tsum := by rw [hTsumdef]; exact hAsm
    _ = 20 * C0 * (cL + 1) ^ 2 * Real.sqrt ((C₂ + 1) * (C₄ + 1))
          * (N : ℝ) ^ (4 * ε / 5) * T ^ ε * Tsum := by rw [hsqrt1]; ring
    _ = 20 * C0 * (cL + 1) ^ 2 * Real.sqrt ((C₂ + 1) * (C₄ + 1))
          * ((N : ℝ) ^ (4 * ε / 5) * T ^ ε) * Tsum := by ring
    _ = 20 * C0 * (cL + 1) ^ 2 * Real.sqrt ((C₂ + 1) * (C₄ + 1))
          * (N : ℝ) ^ (2 * ε) * Tsum := by rw [hNmul]
    _ ≤ (20 * C0 * (cL + 1) ^ 2 + 1) * (C₂ + 1) ^ ((1 : ℝ) / 2) * (C₄ + 1) ^ ((1 : ℝ) / 2)
          * (N : ℝ) ^ (2 * ε) * Tsum := by
        rw [hsqrt2]
        nlinarith [hnonneg]

end Work.GM.Energy.EnergyCore
