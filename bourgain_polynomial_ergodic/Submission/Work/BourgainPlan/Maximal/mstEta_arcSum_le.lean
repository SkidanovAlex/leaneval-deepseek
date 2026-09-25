import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.sigmaN_nested
import Submission.Work.BourgainPlan.Maximal.mstEta_support

/-!
# The level-`s` major-arc mass of the MST route is uniformly bounded

The MST §5 level pieces `ν_n^s` are built from the bump sum
`ξ ↦ Σ_{β ∈ 𝒰(s+1) ∖ 𝒰(s)} η_s(ξ − β)` with the **level-`s`** bump
`η_s(ξ) = η(2^{s(d−χ)} · iwRep ξ)`, supported in the ball of radius `(1/2)·2^{−s(d−χ)}`.

Two regimes meet:

* for **small** `s` there are only finitely many levels and each sum is a finite sum of
  terms bounded by `‖η‖_∞`;
* for **large** `s` the bump width `(1/2)·2^{−s(d−χ)}` is *below* half the separation
  `2 exp(−(s+1)^{1/10})` of the points of `𝒰(s+1)` (`sigmaN_separated`), which decays only
  subexponentially while the bump width decays exponentially; hence at most one summand is
  non-zero.

This file records the uniform bound `∃ M, ∀ s ξ, Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} ‖η_s(ξ−β)‖ ≤ M`.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false

noncomputable section

local notation "𝕋" => Work.BourgainPlan.IonescuWainger.Circle

/-- The level bump `η_s` vanishes off the ball of radius `1/(2·2^{s(d−χ)})`: if such a ball
does not contain `ζ` then `η_s ζ = η(2^{s(d−χ)} · iwRep ζ) = 0`, because `η` is supported in
`[-1/2,1/2]`. -/
lemma mstEta_eq_zero_of_support {d : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) {ζ : 𝕋}
    (h : 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) < ‖ζ‖) :
    mstEta d χ η s ζ = 0 := by
  rw [norm_eq_abs_iwRep] at h
  rw [mstEta_apply]
  by_contra hne
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlt : |(2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * iwRep ζ| < 1 / 2 := by
    by_contra hge
    exact hne (hηsup _ (not_lt.mp hge))
  rw [abs_mul, abs_of_pos hpos] at hlt
  have hkey : |iwRep ζ| < 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))]
    nlinarith [hlt]
  linarith

/-- **A sum of a narrow bump over a separated arc set.**  If `φ` is bounded by `M`, vanishes off
the ball of radius `ε`, and the points of `E` are `δ`-separated with `2ε < δ`, then
`Σ_{β ∈ E} ‖φ(ξ − β)‖ ≤ M`: at most one summand is non-zero. -/
lemma sum_norm_le_of_support_sep {φ : 𝕋 → ℂ} {E : Finset 𝕋} {ε δ M : ℝ}
    (hφbd : ∀ z : 𝕋, ‖φ z‖ ≤ M)
    (hφsupp : ∀ z : 𝕋, ε < ‖z‖ → φ z = 0)
    (hsep : ∀ β ∈ E, ∀ β' ∈ E, β ≠ β' → δ ≤ ‖β - β'‖)
    (hδε : 2 * ε < δ) (ξ : 𝕋) :
    ∑ β ∈ E, ‖φ (ξ - β)‖ ≤ M := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hφbd 0)
  by_cases hex : ∃ β ∈ E, φ (ξ - β) ≠ 0
  · obtain ⟨β₀, hβ₀, hne₀⟩ := hex
    have hsingle : ∀ β ∈ E, β ≠ β₀ → φ (ξ - β) = 0 := by
      intro β hβ hbne
      by_contra hφ
      have hle1 : ‖ξ - β‖ ≤ ε := by
        by_contra hc
        exact hφ (hφsupp _ (not_le.mp hc))
      have hle2 : ‖ξ - β₀‖ ≤ ε := by
        by_contra hc
        exact hne₀ (hφsupp _ (not_le.mp hc))
      have hsub : β - β₀ = (ξ - β₀) - (ξ - β) := by abel
      have htri : ‖β - β₀‖ ≤ 2 * ε := by
        rw [hsub]
        linarith [norm_sub_le (ξ - β₀) (ξ - β)]
      linarith [hsep β hβ β₀ hβ₀ hbne]
    rw [Finset.sum_eq_single β₀ (fun β hβ hne => by rw [hsingle β hβ hne, norm_zero])
      (fun h => absurd hβ₀ h)]
    exact hφbd _
  · have hzero : ∀ β ∈ E, φ (ξ - β) = 0 := by
      intro β hβ
      by_contra h
      exact hex ⟨β, hβ, h⟩
    rw [Finset.sum_eq_zero (fun β hβ => by rw [hzero β hβ, norm_zero])]
    exact hM

/-- **Subexponential versus linear.**  For every `σ > 0` there is `s₀` with
`(s+1)^{1/10} < s·σ·log 2 + log 2` for all `s ≥ s₀`. -/
lemma exists_rpow_ten_add_one_lt (σ : ℝ) (hσ : 0 < σ) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ((s : ℝ) + 1) ^ (1 / 10 : ℝ) < (s : ℝ) * σ * Real.log 2 + Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨n₁, hn₁⟩ := rpow_ten_inv_le_mul (σ * Real.log 2 / 2) (by positivity)
  refine ⟨max n₁ 1, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hsn : n₁ ≤ s := le_trans (le_max_left _ _) hs
  have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hsRpos : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le zero_lt_one hsR1
  have hb : (s : ℝ) ^ (1 / 10 : ℝ) ≤ (σ * Real.log 2 / 2) * (s : ℝ) := hn₁ s hsn
  have hstep : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ 2 * (s : ℝ) ^ (1 / 10 : ℝ) := by
    have hle : ((s : ℝ) + 1) ≤ 2 * (s : ℝ) := by linarith
    have h1 : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (2 * (s : ℝ)) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hle (by norm_num)
    have h2 : (2 * (s : ℝ)) ^ (1 / 10 : ℝ)
        = (2 : ℝ) ^ (1 / 10 : ℝ) * (s : ℝ) ^ (1 / 10 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have h3 : (2 : ℝ) ^ (1 / 10 : ℝ) ≤ 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    calc ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (2 * (s : ℝ)) ^ (1 / 10 : ℝ) := h1
      _ = (2 : ℝ) ^ (1 / 10 : ℝ) * (s : ℝ) ^ (1 / 10 : ℝ) := h2
      _ ≤ 2 * (s : ℝ) ^ (1 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hsRpos.le _)
  have hfin : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ σ * Real.log 2 * (s : ℝ) := by
    calc ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ 2 * (s : ℝ) ^ (1 / 10 : ℝ) := hstep
      _ ≤ 2 * ((σ * Real.log 2 / 2) * (s : ℝ)) := by linarith
      _ = σ * Real.log 2 * (s : ℝ) := by ring
  linarith

/-- Turning the subexponential inequality into the shape used for the support/disjointness
comparison: `1/(2·2^{sσ}) < exp(−(s+1)^{1/10})`. -/
lemma inv_two_mul_two_rpow_lt_exp {s : ℕ} {σ : ℝ}
    (h : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) < (s : ℝ) * σ * Real.log 2 + Real.log 2) :
    1 / (2 * (2 : ℝ) ^ ((s : ℝ) * σ)) < Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hden : (0 : ℝ) < 2 * (2 : ℝ) ^ ((s : ℝ) * σ) := by positivity
  have hprod : (2 * (2 : ℝ) ^ ((s : ℝ) * σ))
      = Real.exp (((s : ℝ) * σ + 1) * Real.log 2) := by
    rw [show (2 : ℝ) * (2 : ℝ) ^ ((s : ℝ) * σ) = (2 : ℝ) ^ (1 + (s : ℝ) * σ) by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]]
    rw [Real.rpow_def_of_pos h2pos]
    congr 1
    ring
  have hkey : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) < ((s : ℝ) * σ + 1) * Real.log 2 := by
    have heq : (s : ℝ) * σ * Real.log 2 + Real.log 2 = ((s : ℝ) * σ + 1) * Real.log 2 := by ring
    linarith
  rw [div_lt_iff₀ hden, hprod, ← Real.exp_add]
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ)) + ((s : ℝ) * σ + 1) * Real.log 2) :=
        Real.exp_lt_exp.mpr (by linarith)

/-- **Separation of the MST level sets in the form the level pieces need.**  There is `s₁` such
that for `s ≥ s₁` any two distinct points of `𝒰(s+1) = mstU l (s+1)` are at distance at least
`2 exp(−(s+1)^{1/10})`. -/
lemma mstU_separated (l : ℕ) (hl : 1 ≤ l) : ∃ s₁ : ℕ, ∀ s : ℕ, s₁ ≤ s →
    ∀ β ∈ mstU l (s + 1), ∀ β' ∈ mstU l (s + 1), β ≠ β' →
      2 * Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) ≤ ‖β - β'‖ := by
  have hρ : 0 < mstRho l := by rw [mstRho]; positivity
  obtain ⟨N₁, hN₁⟩ := sigmaN_separated hρ
  refine ⟨N₁, fun s hs β hβ β' hβ' hne => ?_⟩
  have hNge : N₁ ≤ (s + 1) ^ l := by
    have h2 : s + 1 ≤ (s + 1) ^ l := by
      calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
        _ ≤ (s + 1) ^ l := Nat.pow_le_pow_right (by omega) hl
    omega
  have hb : β ∈ sigmaLeFinset (taoSetS (mstRho l) ((s + 1) ^ l)) (⌊2 / mstRho l⌋₊ + 1) := by
    simpa [mstU, iwSigma, iwK] using hβ
  have hb' : β' ∈ sigmaLeFinset (taoSetS (mstRho l) ((s + 1) ^ l)) (⌊2 / mstRho l⌋₊ + 1) := by
    simpa [mstU, iwSigma, iwK] using hβ'
  have h := hN₁ ((s + 1) ^ l) hNge β hb β' hb' hne
  have hpoweq : ((((s + 1) ^ l : ℕ) : ℝ)) ^ (mstRho l) = ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    have h2 := mstRho_pow_eq l hl (s + 1) (by omega : 1 ≤ s + 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h2
  rwa [hpoweq] at h

/-- **Uniform bound on the level-`s` major-arc bump mass.**  The sum
`Σ_{β ∈ 𝒰(s+1) ∖ 𝒰(s)} ‖η_s(ξ − β)‖` — the level-`s` piece of the MST major-arc symbol — is
bounded uniformly in the level `s` and the frequency `ξ`. -/
theorem mstEta_arcSum_le (l : ℕ) (hl : 1 ≤ l) (d : ℕ) (hd : 1 ≤ d) (χ : ℝ) (hχ : 0 < χ)
    (hχd : χ < (d : ℝ)) (η : ℝ → ℂ) (hcont : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (s : ℕ) (ξ : Work.BourgainPlan.IonescuWainger.Circle),
      ∑ β ∈ (mstU l (s + 1)) \ (mstU l s), ‖mstEta d χ η s (ξ - β)‖ ≤ M := by
  have hσ : 0 < (d : ℝ) - χ := by linarith
  -- a global `L^∞`-bound on the bump `η`
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖η x‖ ≤ C := by
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Set.Icc (-(1 / 2) : ℝ) (1 / 2)) hcont.continuousOn
    refine ⟨max D 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : |x| ≤ 1 / 2
    · refine le_trans (hD x ?_) (le_max_left _ _)
      rw [Set.mem_Icc]
      exact abs_le.mp hx
    · rw [hηsup x (le_of_lt (not_le.mp hx)), norm_zero]
      exact le_max_right _ _
  -- the two thresholds
  obtain ⟨s₀₁, hs₀₁⟩ := exists_rpow_ten_add_one_lt ((d : ℝ) - χ) hσ
  obtain ⟨s₁, hs₁⟩ := mstU_separated l hl
  set T : ℕ := s₀₁ + s₁ + 1 with hT
  have hsum_nonneg : ∀ n : ℕ, 0 ≤ ∑ i ∈ Finset.range n, (((mstU l (i + 1)).card : ℝ) * C) :=
    fun n => Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) hC0)
  refine ⟨(∑ i ∈ Finset.range T, (((mstU l (i + 1)).card : ℝ) * C)) + C + 1, ?_, ?_⟩
  · linarith [hsum_nonneg T]
  · intro s ξ
    rcases lt_or_ge s T with hs | hs
    · -- small level: a finite sum of terms bounded by `C`
      have hmem : s ∈ Finset.range T := Finset.mem_range.mpr hs
      have hsingle := Finset.single_le_sum
        (f := fun i : ℕ => (((mstU l (i + 1)).card : ℝ) * C))
        (fun i _ => mul_nonneg (Nat.cast_nonneg _) hC0) hmem
      have hCeta : ∀ ζ : 𝕋, ‖mstEta d χ η s ζ‖ ≤ C := by
        intro ζ
        rw [mstEta_apply]
        exact hC _
      have hsum : ∑ β ∈ (mstU l (s + 1)) \ (mstU l s), ‖mstEta d χ η s (ξ - β)‖
          ≤ ((mstU l (s + 1)).card : ℝ) * C := by
        calc ∑ β ∈ (mstU l (s + 1)) \ (mstU l s), ‖mstEta d χ η s (ξ - β)‖
            ≤ ∑ _β ∈ (mstU l (s + 1)) \ (mstU l s), C :=
              Finset.sum_le_sum (fun β _ => hCeta (ξ - β))
          _ = (((mstU l (s + 1)) \ (mstU l s)).card : ℝ) * C := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ ((mstU l (s + 1)).card : ℝ) * C := by
              have hcard : ((mstU l (s + 1)) \ (mstU l s)).card ≤ (mstU l (s + 1)).card :=
                card_le_card sdiff_subset
              have h2 : (((mstU l (s + 1)) \ (mstU l s)).card : ℝ)
                  ≤ ((mstU l (s + 1)).card : ℝ) := Nat.cast_le.mpr hcard
              nlinarith [hC0]
      linarith [hsum_nonneg T]
    · -- large level: the level bump is narrower than the separation, so at most one summand
      have hs₀₁le : s₀₁ ≤ s := by rw [hT] at hs; omega
      have hs₁le : s₁ ≤ s := by rw [hT] at hs; omega
      have hδε : 2 * (1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))))
          < 2 * Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := by
        have h := inv_two_mul_two_rpow_lt_exp (s := s) (σ := (d : ℝ) - χ) (hs₀₁ s hs₀₁le)
        linarith
      have hbound := sum_norm_le_of_support_sep
        (φ := mstEta d χ η s) (E := (mstU l (s + 1)) \ (mstU l s))
        (ε := 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))))
        (δ := 2 * Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ)))) (M := C)
        (fun ζ => by rw [mstEta_apply]; exact hC _)
        (fun ζ hζ => mstEta_eq_zero_of_support hηsup s hζ)
        (fun β hβ β' hβ' hne =>
          hs₁ s hs₁le β (mem_sdiff.mp hβ).1 β' (mem_sdiff.mp hβ').1 hne)
        hδε ξ
      linarith [hbound, hsum_nonneg T]

end

end Work.BourgainPlan.Maximal
