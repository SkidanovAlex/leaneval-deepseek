/-
# The value bound for the lacunary modulated difference symbol (Area A7)

For a `Lam`-lacunary scale sequence `σ` (`σ (n+1) ≥ Lam σ n`, `Lam > 1`), a modulation `λ` with
`|λ (n+1) - λ n| ≤ cbar σ n`, arbitrary coefficients `‖ε n‖ ≤ 1`, and a bump `Φ` which is bounded
by `M0`, vanishes off `[-1,1]`, and is *flat* on `[-del, del]` (`Φ = Φ 0` there), the symbol

  `ξ ↦ ∑_{n < K} ε n · (modBlock Φ (σ (n+1)) (λ (n+1)) ξ - modBlock Φ (σ n) (λ n) ξ)`

satisfies `‖·‖ ≤ C (1 + cbar)^2`, with a constant `C` depending only on `Lam`, `del` and `M0`,
uniformly in the number of terms `K`, the signs `ε`, the frequency `ξ` and the parameters.

This is the "value" estimate of the Mikhlin bound `lacunaryModulatedDiffs_mikhlin` (the companions
`lacModDiff_deriv_bound` and `lacModDiff_deriv2_bound` carry the `|ξ|` and `|ξ|²` factors).  The
mechanism is:

* split the difference of two consecutive blocks into a *phase* part
  `Φ (σ (n+1) ξ) · (e (λ (n+1) ξ) - e (λ n ξ))` and an *amplitude* part
  `(Φ (σ (n+1) ξ) - Φ (σ n ξ)) · e (λ n ξ)`;
* the phase part is bounded by `M0 · 2π cbar σ n |ξ|`, which can only be nonzero while
  `σ (n+1) |ξ| < 1`; lacunarity sums that geometric weight to `2 M0 (2π cbar) / (1 - Lam⁻¹)`
  (this is `lacunarySum_norm_bound`);
* the amplitude part vanishes unless `σ n |ξ| < 1 < del⁻¹ σ (n+1) |ξ|`, and the number of such
  indices is bounded by `2 + |log del⁻¹| / log Lam`, uniformly in `ξ` and `K`: the two constraints
  `σ n |ξ| < 1` and `σ (n+1) |ξ| > del` cut out an interval of a lacunary sequence, and the growth
  of a lacunary sequence between the flat region and the support region is at most geometric
  (this is `succWindow_card_le`).

Hence the total is `≤ (4π M0 / (1 - Lam⁻¹) + 2 M0 B) (1 + cbar)²` for `B = 2 + |log del⁻¹|/log Lam`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacModDiffDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped BigOperators
open Finset

noncomputable section

/-! ## Elementary facts on the modulated block -/

/-- The difference of two modulated blocks, split into a phase and an amplitude part. -/
private lemma modBlock_sub_eq (Φ : ℝ → ℂ) (s s' l l' ξ : ℝ) :
    modBlock Φ s' l' ξ - modBlock Φ s l ξ
      = Φ (s' * ξ) * (ee (l' * ξ) - ee (l * ξ)) + (Φ (s' * ξ) - Φ (s * ξ)) * ee (l * ξ) := by
  simp only [modBlock]; ring

/-- A modulated block is bounded by the bound on `Φ`. -/
private lemma modBlock_norm_le {M0 : ℝ} {Φ : ℝ → ℂ} (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0)
    (s l ξ : ℝ) : ‖modBlock Φ s l ξ‖ ≤ M0 := by
  simp only [modBlock]
  calc ‖Φ (s * ξ) * ee (l * ξ)‖ ≤ ‖Φ (s * ξ)‖ * ‖ee (l * ξ)‖ := norm_mul_le _ _
    _ ≤ M0 * 1 := by
        rw [norm_ee_eq_one]
        exact mul_le_mul_of_nonneg_right (hΦb _) (by norm_num)
    _ = M0 := mul_one M0

/-- A modulated block vanishes where `Φ` does. -/
private lemma modBlock_eq_zero {Φ : ℝ → ℂ} (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0)
    {s l ξ : ℝ} (h : 1 ≤ |s * ξ|) : modBlock Φ s l ξ = 0 := by
  simp only [modBlock, hΦsupp (s * ξ) h, zero_mul]

/-- On the flatness region, a modulated block is just the character. -/
private lemma modBlock_eq_flat {del : ℝ} {Φ : ℝ → ℂ}
    (hΦflat : ∀ u : ℝ, |u| ≤ del → Φ u = Φ 0) {s l ξ : ℝ} (h : |s * ξ| ≤ del) :
    modBlock Φ s l ξ = Φ 0 * ee (l * ξ) := by
  simp only [modBlock, hΦflat (s * ξ) h]

/-! ## Lacunarity of the scale sequence -/

/-- A lacunary sequence of positive reals with `Lam > 1` is strictly increasing. -/
private lemma strictMono_of_lacunary {Lam : ℝ} (hLam : 1 < Lam) {sigma : ℕ → ℝ}
    (hpos : ∀ n : ℕ, 0 < sigma n) (hstep : ∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) :
    StrictMono sigma := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  have h : sigma n < Lam * sigma n := by nlinarith [hpos n, hLam]
  linarith [hstep n]

/-- The shifted and rescaled scale family `n ↦ σ (n+1) · c` (`c > 0`) is lacunary whenever `σ`
is. -/
private lemma lacunaryFam_succ_mul {Lam c : ℝ} (hc : 0 < c) {sigma : ℕ → ℝ}
    (hLam : 1 < Lam) (hpos : ∀ n : ℕ, 0 < sigma n)
    (hstep : ∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) (K : ℕ) :
    Work.Analysis.CzShift.LacunaryFam Lam (Finset.range K) (fun n => sigma (n + 1) * c) := by
  have hsmono : StrictMono sigma := strictMono_of_lacunary hLam hpos hstep
  refine ⟨fun n _ => mul_pos (hpos (n + 1)) hc, ?_⟩
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have h1 : sigma (i + 1) ≤ sigma (j + 1) := hsmono.monotone (Nat.succ_le_succ hlt.le)
    have h2 : Lam * sigma (i + 1) ≤ sigma (j + 1) := by
      have h3 : sigma (i + 2) ≤ sigma (j + 1) := hsmono.monotone (by omega)
      have h4 := hstep (i + 1)
      linarith
    rw [min_eq_left (mul_le_mul_of_nonneg_right h1 hc.le),
      max_eq_right (mul_le_mul_of_nonneg_right h1 hc.le)]
    have := mul_le_mul_of_nonneg_right h2 hc.le
    linarith
  · have h1 : sigma (j + 1) ≤ sigma (i + 1) := hsmono.monotone (Nat.succ_le_succ hlt.le)
    have h2 : Lam * sigma (j + 1) ≤ sigma (i + 1) := by
      have h3 : sigma (j + 2) ≤ sigma (i + 1) := hsmono.monotone (by omega)
      have h4 := hstep (j + 1)
      linarith
    rw [min_eq_right (mul_le_mul_of_nonneg_right h1 hc.le),
      max_eq_left (mul_le_mul_of_nonneg_right h1 hc.le)]
    have := mul_le_mul_of_nonneg_right h2 hc.le
    linarith

/-! ## Counting the indices at which the amplitude part can be nonzero -/

/-- For a `Lam`-lacunary sequence of positive scales `σ`, the number of indices `n < K` with
`σ n |ξ| < 1 < del⁻¹ σ (n+1) |ξ|` is bounded by `2 + |log del⁻¹| / log Lam`, uniformly in `ξ`
and `K`. -/
private lemma succWindow_card_le {Lam del : ℝ} (hLam : 1 < Lam) (hdel : 0 < del) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {sigma : ℕ → ℝ}, (∀ n : ℕ, 0 < sigma n) →
      (∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) →
      ∀ (K : ℕ) (ξ : ℝ),
        (((Finset.range K).filter
            (fun n => sigma n * |ξ| < 1 ∧ del < sigma (n + 1) * |ξ|)).card : ℝ) ≤ B := by
  have hlogLam : 0 < Real.log Lam := Real.log_pos hLam
  have habs : 0 ≤ |Real.log del⁻¹| / Real.log Lam := div_nonneg (abs_nonneg _) hlogLam.le
  refine ⟨2 + |Real.log del⁻¹| / Real.log Lam, by linarith, ?_⟩
  intro sigma hpos hstep K ξ
  by_cases hξ : ξ = 0
  · have hset : (Finset.range K).filter
        (fun n => sigma n * |ξ| < 1 ∧ del < sigma (n + 1) * |ξ|) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨n, hn⟩ := hne
      rw [Finset.mem_filter] at hn
      rw [hξ] at hn
      simp only [abs_zero, mul_zero] at hn
      linarith [hn.2.2, hdel]
    rw [hset, Finset.card_empty, Nat.cast_zero]
    linarith
  · have hξpos : 0 < |ξ| := abs_pos.mpr hξ
    set S : Finset ℕ := (Finset.range K).filter
      (fun n => sigma n * |ξ| < 1 ∧ del < sigma (n + 1) * |ξ|) with hS
    -- the part of `S` where `σ (n+1) |ξ| ≥ 1`
    have hS₁le : (S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|)).card ≤ 1 := by
      rcases Finset.eq_empty_or_nonempty (S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|)) with hem | hne
      · rw [hem]; simp
      · obtain ⟨n₀, hn₀⟩ := hne
        have hn₀S : n₀ ∈ S := (Finset.mem_filter.mp hn₀).1
        have hn₀1 : 1 ≤ sigma (n₀ + 1) * |ξ| := (Finset.mem_filter.mp hn₀).2
        have hsub : S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|) ⊆ {n₀} := by
          intro m hm
          have hmS : m ∈ S := (Finset.mem_filter.mp hm).1
          have hm1 : 1 ≤ sigma (m + 1) * |ξ| := (Finset.mem_filter.mp hm).2
          have hmS' : sigma m * |ξ| < 1 := (Finset.mem_filter.mp hmS).2.1
          have hn₀S' : sigma n₀ * |ξ| < 1 := (Finset.mem_filter.mp hn₀S).2.1
          rw [Finset.mem_singleton]
          by_contra hne'
          rcases lt_or_gt_of_ne hne' with hlt | hlt
          · have hmono : sigma (m + 1) ≤ sigma n₀ :=
              (strictMono_of_lacunary hLam hpos hstep).monotone (Nat.succ_le_of_lt hlt)
            have hle : sigma (m + 1) * |ξ| ≤ sigma n₀ * |ξ| :=
              mul_le_mul_of_nonneg_right hmono (abs_nonneg ξ)
            linarith
          · have hmono : sigma (n₀ + 1) ≤ sigma m :=
              (strictMono_of_lacunary hLam hpos hstep).monotone (Nat.succ_le_of_lt hlt)
            have hle : sigma (n₀ + 1) * |ξ| ≤ sigma m * |ξ| :=
              mul_le_mul_of_nonneg_right hmono (abs_nonneg ξ)
            linarith
        calc (S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|)).card
            ≤ ({n₀} : Finset ℕ).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton n₀
    by_cases hdel1 : del ≤ 1
    · -- the part of `S` where `σ (n+1) |ξ| < 1` lives in a fixed window of a lacunary family
      have hS₂ : ((S.filter (fun n => ¬ (1 ≤ sigma (n + 1) * |ξ|))).card : ℝ)
          ≤ 1 + Real.log (del⁻¹) / Real.log Lam := by
        have hsub : S.filter (fun n => ¬ (1 ≤ sigma (n + 1) * |ξ|)) ⊆
            (Finset.range K).filter
              (fun n => del ≤ sigma (n + 1) * |ξ| ∧ sigma (n + 1) * |ξ| < 1) := by
          intro n hn
          obtain ⟨hnS, hn1⟩ := Finset.mem_filter.mp hn
          obtain ⟨hnK, _, hn3⟩ := Finset.mem_filter.mp hnS
          exact Finset.mem_filter.mpr ⟨hnK, le_of_lt hn3, lt_of_not_ge hn1⟩
        have hcard := (Work.Analysis.CzShift.lacunary_sums (Finset.range K)
          (fun n => sigma (n + 1) * |ξ|) hLam
          (lacunaryFam_succ_mul hξpos hLam hpos hstep K)).1 del 1 hdel hdel1
        calc ((S.filter (fun n => ¬ (1 ≤ sigma (n + 1) * |ξ|))).card : ℝ)
            ≤ (((Finset.range K).filter
                (fun n => del ≤ sigma (n + 1) * |ξ| ∧ sigma (n + 1) * |ξ| < 1)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ 1 + Real.log (1 / del) / Real.log Lam := hcard
          _ = 1 + Real.log (del⁻¹) / Real.log Lam := by rw [one_div]
      have hsplit : (S.card : ℝ) ≤
          ((S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|)).card : ℝ)
            + ((S.filter (fun n => ¬ (1 ≤ sigma (n + 1) * |ξ|))).card : ℝ) := by
        have htot := Finset.card_filter_add_card_filter_not (s := S)
          (p := fun n : ℕ => 1 ≤ sigma (n + 1) * |ξ|)
        have heq : (S.card : ℝ) =
            ((S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|)).card : ℝ)
              + ((S.filter (fun n => ¬ (1 ≤ sigma (n + 1) * |ξ|))).card : ℝ) := by
          rw [← htot]
          push_cast
          ring
        linarith [heq.le]
      have hlogdel : 0 ≤ Real.log del⁻¹ := Real.log_nonneg ((one_le_inv₀ hdel).mpr hdel1)
      have hS₁ : ((S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|)).card : ℝ) ≤ 1 := by
        exact_mod_cast hS₁le
      rw [abs_of_nonneg hlogdel]
      linarith
    · -- when `del > 1` the second part is empty: `1 < del < σ (n+1) |ξ|`
      have hdel1' : 1 < del := not_le.mp hdel1
      have hsub : S ⊆ S.filter (fun n => 1 ≤ sigma (n + 1) * |ξ|) := by
        intro n hn
        obtain ⟨-, -, hn3⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨hn, le_of_lt (lt_trans hdel1' hn3)⟩
      have h1 : (S.card : ℝ) ≤ 1 := by
        exact_mod_cast le_trans (Finset.card_le_card hsub) hS₁le
      have h2 : (0 : ℝ) ≤ |Real.log del⁻¹| / Real.log Lam :=
        div_nonneg (abs_nonneg _) hlogLam.le
      linarith

/-! ## The phase and amplitude estimates -/

/-- Phase part of the modulated difference: the character difference times the *later* amplitude.
The `Φ (σ (n+1) ξ)` factor vanishes as soon as `1 < σ (n+1) |ξ|`, so only the lacunary window
`σ (n+1) |ξ| ≤ 1` contributes, and there the phase increment is at most `2π cbar σ n |ξ|`. -/
private lemma phaseSum_le {Lam M0 : ℝ} (hLam : 1 < Lam) (hM0 : 0 ≤ M0) {Φ : ℝ → ℂ}
    (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0) (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0)
    {cbar : ℝ} (hcbar : 0 ≤ cbar) {sigma : ℕ → ℝ} (hpos : ∀ n : ℕ, 0 < sigma n)
    (hstep : ∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) {lam : ℕ → ℝ}
    (hlamd : ∀ n : ℕ, |lam (n + 1) - lam n| ≤ cbar * sigma n)
    (K : ℕ) (eps : ℕ → ℂ) (heps : ∀ n : ℕ, ‖eps n‖ ≤ 1) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖∑ n ∈ Finset.range K,
        eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))‖
      ≤ (4 * Real.pi * M0 / (1 - Lam⁻¹)) * (1 + cbar) ^ 2 := by
  have hKpos : 0 < 1 - Lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hLam)
  have hCnn : 0 ≤ M0 * (2 * Real.pi * cbar) := by
    have h : 0 ≤ 2 * Real.pi * cbar := by positivity
    nlinarith
  have hlac := lacunaryFam_range hLam hpos hstep K
  have hkey : ∑ n ∈ Finset.range K,
      ‖Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ))‖
      ≤ 2 * (M0 * (2 * Real.pi * cbar)) / (1 - Lam⁻¹) := by
    refine lacunarySum_norm_bound (D := Finset.range K) (σ := sigma)
      (f := fun n => Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))
      hLam hlac hξ hCnn ?_ ?_
    · intro i _ _
      have hb1 : ‖Φ (sigma (i + 1) * ξ)‖ ≤ M0 := hΦb _
      have hb2 : ‖ee (lam (i + 1) * ξ) - ee (lam i * ξ)‖
          ≤ 2 * Real.pi * (|lam (i + 1) - lam i| * |ξ|) := by
        have h := norm_ee_sub_le (lam (i + 1) * ξ) (lam i * ξ)
        rwa [← sub_mul, abs_mul] at h
      have hb3 : |lam (i + 1) - lam i| * |ξ| ≤ (cbar * sigma i) * |ξ| :=
        mul_le_mul_of_nonneg_right (hlamd i) (abs_nonneg ξ)
      have hb4 : 2 * Real.pi * (|lam (i + 1) - lam i| * |ξ|)
          ≤ 2 * Real.pi * ((cbar * sigma i) * |ξ|) :=
        mul_le_mul_of_nonneg_left hb3 (by positivity)
      calc ‖Φ (sigma (i + 1) * ξ) * (ee (lam (i + 1) * ξ) - ee (lam i * ξ))‖
          ≤ ‖Φ (sigma (i + 1) * ξ)‖ * ‖ee (lam (i + 1) * ξ) - ee (lam i * ξ)‖ :=
            norm_mul_le _ _
        _ ≤ M0 * (2 * Real.pi * (|lam (i + 1) - lam i| * |ξ|)) :=
            mul_le_mul hb1 hb2 (norm_nonneg _) (le_trans (norm_nonneg _) hb1)
        _ ≤ M0 * (2 * Real.pi * ((cbar * sigma i) * |ξ|)) :=
            mul_le_mul_of_nonneg_left hb4 hM0
        _ = (M0 * (2 * Real.pi * cbar)) * (sigma i * |ξ|) := by ring
    · intro i _ hgt
      have h1 : 1 ≤ |sigma (i + 1) * ξ| := by
        have hmono : sigma i ≤ sigma (i + 1) :=
          (strictMono_of_lacunary hLam hpos hstep).monotone (Nat.le_succ i)
        have h2 : sigma i * |ξ| ≤ sigma (i + 1) * |ξ| :=
          mul_le_mul_of_nonneg_right hmono (abs_nonneg ξ)
        rw [abs_mul, abs_of_pos (hpos (i + 1))]
        linarith
      rw [hΦsupp (sigma (i + 1) * ξ) h1, zero_mul]
  calc ‖∑ n ∈ Finset.range K,
        eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))‖
      ≤ ∑ n ∈ Finset.range K,
          ‖eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range K,
          ‖Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ))‖ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        calc ‖eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))‖
            ≤ ‖eps n‖ * ‖Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ))‖ :=
              norm_mul_le _ _
          _ ≤ 1 * ‖Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ))‖ :=
              mul_le_mul_of_nonneg_right (heps n) (norm_nonneg _)
          _ = ‖Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ))‖ := one_mul _
    _ ≤ 2 * (M0 * (2 * Real.pi * cbar)) / (1 - Lam⁻¹) := hkey
    _ = (4 * Real.pi * M0 / (1 - Lam⁻¹)) * cbar := by ring
    _ ≤ (4 * Real.pi * M0 / (1 - Lam⁻¹)) * (1 + cbar) ^ 2 := by
        have hcp : 0 ≤ 4 * Real.pi * M0 / (1 - Lam⁻¹) := div_nonneg (by positivity) hKpos.le
        have hle : cbar ≤ (1 + cbar) ^ 2 := by nlinarith [hcbar, sq_nonneg cbar]
        exact mul_le_mul_of_nonneg_left hle hcp

/-- Amplitude part of the modulated difference: the difference of the two amplitudes times a
character.  It vanishes unless `σ n |ξ| < 1 < del⁻¹ σ (n+1) |ξ|`, so the count `hcard` bounds it
by `2 M0` times the number of such indices. -/
private lemma ampSum_le {Lam del M0 B : ℝ} (hLam : 1 < Lam) (_hdel : 0 < del) (hM0 : 0 ≤ M0)
    (_hB : 0 ≤ B) {Φ : ℝ → ℂ} (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0)
    (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0)
    (hΦflat : ∀ u : ℝ, |u| ≤ del → Φ u = Φ 0)
    (hcard : ∀ {sigma : ℕ → ℝ}, (∀ n : ℕ, 0 < sigma n) →
      (∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) → ∀ (K : ℕ) (ξ : ℝ),
        (((Finset.range K).filter
            (fun n => sigma n * |ξ| < 1 ∧ del < sigma (n + 1) * |ξ|)).card : ℝ) ≤ B)
    {sigma : ℕ → ℝ} (hpos : ∀ n : ℕ, 0 < sigma n)
    (hstep : ∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) {lam : ℕ → ℝ}
    (K : ℕ) (eps : ℕ → ℂ) (heps : ∀ n : ℕ, ‖eps n‖ ≤ 1) (ξ : ℝ) :
    ‖∑ n ∈ Finset.range K,
        eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ))‖
      ≤ 2 * M0 * B := by
  classical
  set S : Finset ℕ := (Finset.range K).filter
    (fun n => sigma n * |ξ| < 1 ∧ del < sigma (n + 1) * |ξ|) with hS
  have hcardS : (S.card : ℝ) ≤ B := by
    rw [hS]
    exact hcard hpos hstep K ξ
  have hzero : ∀ n ∈ Finset.range K, n ∉ S →
      ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖ = 0 := by
    intro n hn hnS
    have hp : ¬ (sigma n * |ξ| < 1 ∧ del < sigma (n + 1) * |ξ|) := by
      intro hcon
      exact hnS (by rw [hS]; exact Finset.mem_filter.mpr ⟨hn, hcon⟩)
    rw [not_and_or] at hp
    rcases hp with h1 | h2
    · have h1' : 1 ≤ |sigma n * ξ| := by
        rw [abs_mul, abs_of_pos (hpos n)]
        exact le_of_not_gt h1
      have h2' : 1 ≤ |sigma (n + 1) * ξ| := by
        rw [abs_mul, abs_of_pos (hpos (n + 1))]
        have hmono : sigma n ≤ sigma (n + 1) :=
          (strictMono_of_lacunary hLam hpos hstep).monotone (Nat.le_succ n)
        have hle : sigma n * |ξ| ≤ sigma (n + 1) * |ξ| :=
          mul_le_mul_of_nonneg_right hmono (abs_nonneg ξ)
        linarith
      rw [hΦsupp (sigma (n + 1) * ξ) h2', hΦsupp (sigma n * ξ) h1', sub_zero, zero_mul,
        norm_zero]
    · have h2' : |sigma (n + 1) * ξ| ≤ del := by
        rw [abs_mul, abs_of_pos (hpos (n + 1))]
        exact le_of_not_gt h2
      have h3' : |sigma n * ξ| ≤ del := by
        rw [abs_mul, abs_of_pos (hpos n)]
        have hmono : sigma n ≤ sigma (n + 1) :=
          (strictMono_of_lacunary hLam hpos hstep).monotone (Nat.le_succ n)
        have hle : sigma n * |ξ| ≤ sigma (n + 1) * |ξ| :=
          mul_le_mul_of_nonneg_right hmono (abs_nonneg ξ)
        linarith
      rw [hΦflat (sigma (n + 1) * ξ) h2', hΦflat (sigma n * ξ) h3', sub_self, zero_mul,
        norm_zero]
  have hsum1 : (∑ n ∈ Finset.range K,
        ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖)
      = ∑ n ∈ S, ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖ := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [hS] at hn
      exact (Finset.mem_filter.mp hn).1
    · intro n hn hnS
      exact hzero n hn hnS
  have hsum2 : (∑ n ∈ S, ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖)
      ≤ 2 * M0 * (S.card : ℝ) := by
    calc ∑ n ∈ S, ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖
        ≤ ∑ _n ∈ S, (2 * M0) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          calc ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖
              = ‖Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)‖ := by
                rw [norm_mul, norm_ee_eq_one, mul_one]
            _ ≤ ‖Φ (sigma (n + 1) * ξ)‖ + ‖Φ (sigma n * ξ)‖ := norm_sub_le _ _
            _ ≤ M0 + M0 := add_le_add (hΦb _) (hΦb _)
            _ = 2 * M0 := by ring
      _ = (S.card : ℝ) * (2 * M0) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * M0 * (S.card : ℝ) := by ring
  calc ‖∑ n ∈ Finset.range K,
        eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ))‖
      ≤ ∑ n ∈ Finset.range K,
          ‖eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range K,
          ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        calc ‖eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ))‖
            ≤ ‖eps n‖ * ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖ :=
              norm_mul_le _ _
          _ ≤ 1 * ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖ :=
              mul_le_mul_of_nonneg_right (heps n) (norm_nonneg _)
          _ = ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖ := one_mul _
    _ = ∑ n ∈ S, ‖(Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)‖ := hsum1
    _ ≤ 2 * M0 * (S.card : ℝ) := hsum2
    _ ≤ 2 * M0 * B := mul_le_mul_of_nonneg_left hcardS (by linarith : (0 : ℝ) ≤ 2 * M0)

/-! ## The value bound -/

theorem lacModDiff_value_bound {Lam del M0 : ℝ} (hLam : 1 < Lam) (hdel : 0 < del)
    (hM0 : 0 ≤ M0) {Φ : ℝ → ℂ} (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0)
    (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0)
    (hΦflat : ∀ u : ℝ, |u| ≤ del → Φ u = Φ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {cbar : ℝ}, 0 ≤ cbar →
      ∀ {sigma : ℕ → ℝ}, (∀ n : ℕ, 0 < sigma n) →
        (∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) →
      ∀ {lam : ℕ → ℝ}, (∀ n : ℕ, |lam n| ≤ cbar * sigma n) →
        (∀ n : ℕ, |lam (n + 1) - lam n| ≤ cbar * sigma n) →
      ∀ (K : ℕ) (eps : ℕ → ℂ), (∀ n : ℕ, ‖eps n‖ ≤ 1) → ∀ ξ : ℝ,
        ‖∑ n ∈ Finset.range K, eps n * (modBlock Φ (sigma (n + 1)) (lam (n + 1)) ξ
          - modBlock Φ (sigma n) (lam n) ξ)‖ ≤ C * (1 + cbar) ^ 2 := by
  classical
  obtain ⟨B, hBnn, hBcard⟩ := succWindow_card_le hLam hdel
  have hKpos : 0 < 1 - Lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hLam)
  have hPnn : 0 ≤ 4 * Real.pi * M0 / (1 - Lam⁻¹) := div_nonneg (by positivity) hKpos.le
  have hQnn : 0 ≤ 2 * M0 * B := by nlinarith [hBnn, hM0]
  refine ⟨4 * Real.pi * M0 / (1 - Lam⁻¹) + 2 * M0 * B, by linarith, ?_⟩
  intro cbar hcbar sigma hpos hstep lam hlam hlamd K eps heps ξ
  have hpoint : ∀ n : ℕ, eps n * (modBlock Φ (sigma (n + 1)) (lam (n + 1)) ξ
      - modBlock Φ (sigma n) (lam n) ξ)
      = eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))
        + eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)) := by
    intro n
    rw [modBlock_sub_eq Φ (sigma n) (sigma (n + 1)) (lam n) (lam (n + 1)) ξ]
    ring
  rw [Finset.sum_congr rfl (fun n _ => hpoint n), Finset.sum_add_distrib]
  by_cases hξ : ξ = 0
  · have h1 : (∑ n ∈ Finset.range K,
        eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))) = 0 := by
      refine Finset.sum_eq_zero (fun n _ => ?_)
      simp [hξ]
    have h2 : (∑ n ∈ Finset.range K,
        eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ))) = 0 := by
      refine Finset.sum_eq_zero (fun n _ => ?_)
      simp [hξ]
    rw [h1, h2, add_zero, norm_zero]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  · have hphase := phaseSum_le hLam hM0 hΦb hΦsupp hcbar hpos hstep hlamd K eps heps ξ hξ
    have hamp := ampSum_le (lam := lam) hLam hdel hM0 hBnn hΦb hΦsupp hΦflat hBcard hpos hstep K eps heps ξ
    calc ‖(∑ n ∈ Finset.range K,
          eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ))))
        + (∑ n ∈ Finset.range K,
          eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ)))‖
        ≤ ‖∑ n ∈ Finset.range K,
            eps n * (Φ (sigma (n + 1) * ξ) * (ee (lam (n + 1) * ξ) - ee (lam n * ξ)))‖
          + ‖∑ n ∈ Finset.range K,
            eps n * ((Φ (sigma (n + 1) * ξ) - Φ (sigma n * ξ)) * ee (lam n * ξ))‖ :=
          norm_add_le _ _
      _ ≤ (4 * Real.pi * M0 / (1 - Lam⁻¹)) * (1 + cbar) ^ 2 + 2 * M0 * B := by linarith
      _ ≤ (4 * Real.pi * M0 / (1 - Lam⁻¹) + 2 * M0 * B) * (1 + cbar) ^ 2 := by
          have hone : (1 : ℝ) ≤ (1 + cbar) ^ 2 := by nlinarith [hcbar, sq_nonneg cbar]
          have hle : 2 * M0 * B ≤ 2 * M0 * B * (1 + cbar) ^ 2 := by
            calc 2 * M0 * B = 2 * M0 * B * 1 := (mul_one _).symm
              _ ≤ 2 * M0 * B * (1 + cbar) ^ 2 := mul_le_mul_of_nonneg_left hone hQnn
          linarith

end

end Work.KMTAreas.A7
