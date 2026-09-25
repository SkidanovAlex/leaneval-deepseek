import Mathlib
import Submission.Work.BourgainPlan.Oscillation.cut_shift_helpers
import Submission.Work.BourgainPlan.Oscillation.one_side_max_gen_via_density
import Submission.Work.BourgainPlan.Oscillation.nbrhd_sup_shell_l2

/-!
# The shifted one-sided cut maximal inequality at the lacunary scales

For `ρ > 1` there is `C` with

`∫⁻_x (⨆_i |∫_{θ ≤ s ρ^{-i}} h θ e(-2πixθ) dθ|)² d# ≤ C² ∫⁻|h|²`

for every `s > 0` and every `h ∈ L²(0,1]`, with `C` independent of `s`.

The aligned family `1_{(0, ρ^{-i}]}` is the case `s = 1` of the same statements; the general shift
is handled by snapping `s` to the lattice (`exists_zpow_le_lt`), writing the shifted cut as the
aligned cut at the snapped radius plus the *gap* `1_{(ρ^{k-i}, s ρ^{-i}]}`, and paying for the gaps
by the square function (`nbrhd_sup_shell_l2`), whose annuli are pairwise disjoint
(`tsum_ioc_zpow_le`, `pairwiseDisjoint_ioc_zpow`).
-/

namespace Work.BourgainPlan.Oscillation

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

open Lacunary

/-! ## The one-sided cut operator -/

/-- The one-sided frequency cut `θ ↦ 1_{θ ≤ c}` applied to `h`, as a function of `x : ℤ`. -/
def cutOne (h : ℝ → ℂ) (c : ℝ) (x : ℤ) : ℂ :=
  ∫ θ, (if θ ≤ c then (1 : ℂ) else 0) * h θ * Echar x θ ∂mu01

/-- The one-sided and the symmetric cut integrals agree, because `mu01` lives on `(0,1]`. -/
lemma cutOne_eq_symm (ρ : ℝ) (h : ℝ → ℂ) (i : ℕ) (x : ℤ) :
    cutOne h (cc ρ i) x
      = ∫ θ, (if |θ| ≤ cc ρ i then (1 : ℂ) else 0) * h θ * Echar x θ ∂mu01 := by
  unfold cutOne
  refine integral_congr_ae ?_
  filter_upwards [cut_indicator_ae ρ i] with θ hθ
  rw [hθ]

/-- Above the full scale `1` the one-sided cut is the whole interval. -/
lemma cutOne_eq_one_of_one_le (h : ℝ → ℂ) {c : ℝ} (hc : 1 ≤ c) (x : ℤ) :
    cutOne h c x = cutOne h 1 x := by
  unfold cutOne
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with θ hθ
  rw [if_pos (le_trans hθ.2 hc), if_pos hθ.2]

/-- The aligned cut at a non-negative lattice exponent is the full interval. -/
lemma cutOne_zpow_of_nonneg (ρ : ℝ) (hρ : 1 < ρ) (h : ℝ → ℂ)
    {j : ℤ} (hj : 0 ≤ j) (x : ℤ) :
    cutOne h (ρ ^ j) x = cutOne h (cc ρ 0) x := by
  have h1 : 1 ≤ ρ ^ j := by
    have := zpow_le_zpow_right₀ hρ.le hj
    simpa using this
  have h2 : cc ρ 0 = (1 : ℝ) := by simp [cc]
  rw [h2]
  exact cutOne_eq_one_of_one_le h h1 x

/-- Every aligned lattice cut `ρ ^ j`, `j : ℤ`, is dominated by the one-sided aligned maximal
function of the statement (over `cc ρ i = ρ ^ (-i)`, `i : ℕ`). -/
lemma cutOne_zpow_le_sup (ρ : ℝ) (hρ : 1 < ρ) (h : ℝ → ℂ) (j : ℤ) (x : ℤ) :
    ‖cutOne h (ρ ^ j) x‖ₑ ≤ ⨆ i : ℕ, ‖cutOne h (cc ρ i) x‖ₑ := by
  by_cases hj : 0 ≤ j
  · rw [cutOne_zpow_of_nonneg ρ hρ h hj x]
    exact le_iSup (fun i : ℕ => ‖cutOne h (cc ρ i) x‖ₑ) 0
  · push Not at hj
    have hje : j = -(((-j).toNat : ℕ) : ℤ) := by
      have h0 : (0 : ℤ) ≤ -j := by omega
      have h1 := Int.toNat_of_nonneg h0
      omega
    rw [hje]
    exact le_iSup (fun i : ℕ => ‖cutOne h (cc ρ i) x‖ₑ) ((-j).toNat)

/-! ## The `mu01`-form of the shell (square-function) estimate -/

/-- `nbrhd_sup_shell_l2` with the interval integrals rewritten as `mu01`-integrals. -/
lemma shell_bound_mu01 {K : ℝ} (hK : 0 ≤ K) (φ : ℕ → ℝ → ℝ)
    (hφm : ∀ t, Measurable (φ t)) (hφ0 : ∀ t θ, 0 ≤ φ t θ)
    (hφsum : ∀ θ N, ∑ t ∈ Finset.range N, φ t θ ^ 2 ≤ K)
    (Q : ℝ → ℂ) (hQ : MemLp Q 2 mu01) :
    ∫⁻ x : ℤ, (⨆ t : ℕ, ‖∫ θ, (φ t θ : ℂ) * Q θ * Echar x θ ∂mu01‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal K * ∫⁻ θ : ℝ, ‖Q θ‖ₑ ^ (2 : ℝ) ∂mu01 := by
  have h := nbrhd_sup_shell_l2 K hK φ hφm hφ0 hφsum Q hQ
  simpa only [mu01, Echar, intervalIntegral_eq_mu01] using h

/-! ## The gap family `1_{(ρ^{k-i}, s ρ^{-i}]}` -/

/-- The gap cut between the aligned radius `ρ ^ (k-i)` and the shifted radius `s ρ ^ (-i)`. -/
def shiftGap (ρ s : ℝ) (k : ℤ) : ℕ → ℝ → ℝ :=
  fun i θ => (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
    - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0)

lemma shiftGap_measurable (ρ s : ℝ) (k : ℤ) (i : ℕ) : Measurable (shiftGap ρ s k i) := by
  show Measurable (fun θ : ℝ =>
    (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
      - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0))
  refine Measurable.sub ?_ ?_
  · exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  · exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const

/-- The aligned radius never exceeds the shifted one. -/
lemma zpow_le_mul_shift (ρ s : ℝ) (k : ℤ) (hρ : 0 < ρ) (hk : ρ ^ k ≤ s) (i : ℕ) :
    ρ ^ (k - (i : ℤ)) ≤ s * ρ ^ (-(i : ℤ)) := by
  have h1 : ρ ^ k * ρ ^ (-(i : ℤ)) ≤ s * ρ ^ (-(i : ℤ)) :=
    mul_le_mul_of_nonneg_right hk (zpow_pos hρ _).le
  rwa [← zpow_add₀ (ne_of_gt hρ)] at h1

/-- The gap cut is non-negative. -/
lemma shiftGap_nonneg (ρ s : ℝ) (k : ℤ) (hρ : 0 < ρ) (hk : ρ ^ k ≤ s) (i : ℕ) (θ : ℝ) :
    0 ≤ shiftGap ρ s k i θ := by
  have hBA := zpow_le_mul_shift ρ s k hρ hk i
  show 0 ≤ (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
    - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0)
  by_cases hθ : θ ≤ ρ ^ (k - (i : ℤ))
  · rw [if_pos (le_trans hθ hBA), if_pos hθ]; norm_num
  · rw [if_neg hθ]
    by_cases hθ' : θ ≤ s * ρ ^ (-(i : ℤ))
    · rw [if_pos hθ']; norm_num
    · rw [if_neg hθ']; norm_num

/-- The gap cut takes only the values `0` and `1`. -/
lemma shiftGap_eq_zero_or_one (ρ s : ℝ) (k : ℤ) (hρ : 0 < ρ) (hk : ρ ^ k ≤ s)
    (i : ℕ) (θ : ℝ) : shiftGap ρ s k i θ = 0 ∨ shiftGap ρ s k i θ = 1 := by
  have hBA := zpow_le_mul_shift ρ s k hρ hk i
  show (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
      - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0) = 0 ∨
    (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
      - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0) = 1
  by_cases hθ : θ ≤ ρ ^ (k - (i : ℤ))
  · left; rw [if_pos (le_trans hθ hBA), if_pos hθ]; norm_num
  · by_cases hθ' : θ ≤ s * ρ ^ (-(i : ℤ))
    · right; rw [if_neg hθ, if_pos hθ']; norm_num
    · left; rw [if_neg hθ, if_neg hθ']; norm_num

/-- Characterization of the gap cut being `1`: the point lies in the gap annulus. -/
lemma shiftGap_eq_one_iff (ρ s : ℝ) (k : ℤ) (hρ : 0 < ρ) (hk : ρ ^ k ≤ s)
    (i : ℕ) (θ : ℝ) :
    shiftGap ρ s k i θ = 1 ↔ ρ ^ (k - (i : ℤ)) < θ ∧ θ ≤ s * ρ ^ (-(i : ℤ)) := by
  have hBA := zpow_le_mul_shift ρ s k hρ hk i
  by_cases hθ : θ ≤ ρ ^ (k - (i : ℤ))
  · have h1 : shiftGap ρ s k i θ = 0 := by
      show (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
        - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0) = 0
      rw [if_pos (le_trans hθ hBA), if_pos hθ]; norm_num
    constructor
    · intro h; rw [h1] at h; norm_num at h
    · intro h; exact absurd hθ (not_le.mpr h.1)
  · by_cases hθ' : θ ≤ s * ρ ^ (-(i : ℤ))
    · have h1 : shiftGap ρ s k i θ = 1 := by
        show (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
          - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0) = 1
        rw [if_neg hθ, if_pos hθ']; norm_num
      exact ⟨fun _ => ⟨not_le.mp hθ, hθ'⟩, fun _ => h1⟩
    · have h1 : shiftGap ρ s k i θ = 0 := by
        show (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℝ) else 0)
          - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℝ) else 0) = 0
        rw [if_neg hθ, if_neg hθ']; norm_num
      constructor
      · intro h; rw [h1] at h; norm_num at h
      · intro h; exact absurd h.2 hθ'

/-- **The gap annuli are disjoint (index form).**  If `θ` lies above the aligned radius of the
scale `a` and below the shifted radius of the scale `b`, then `b ≤ a`. -/
lemma shiftGap_idx_le (ρ s : ℝ) (k : ℤ) (hρ : 1 < ρ) (hks : s < ρ ^ (k + 1))
    (a b : ℕ) {θ : ℝ} (ha : ρ ^ (k - (a : ℤ)) < θ) (hb : θ ≤ s * ρ ^ (-(b : ℤ))) :
    b ≤ a := by
  have hρ0 : 0 < ρ := by linarith
  have hb2 : s * ρ ^ (-(b : ℤ)) < ρ ^ (k + 1 - (b : ℤ)) := by
    have h := mul_lt_mul_of_pos_right hks (zpow_pos hρ0 (-(b : ℤ)))
    rwa [← zpow_add₀ (ne_of_gt hρ0)] at h
  have h2 : ρ ^ (k - (a : ℤ)) < ρ ^ (k + 1 - (b : ℤ)) := lt_trans (lt_of_lt_of_le ha hb) hb2
  have h3 : k - (a : ℤ) < k + 1 - (b : ℤ) := (zpow_lt_zpow_iff_right₀ hρ).mp h2
  omega

/-- **At most one gap is active**, so the squared gap cuts sum to at most `1`. -/
lemma shiftGap_sq_sum_le_one (ρ s : ℝ) (k : ℤ) (hρ : 1 < ρ) (hk : ρ ^ k ≤ s)
    (hks : s < ρ ^ (k + 1)) (θ : ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range N, shiftGap ρ s k t θ ^ 2 ≤ 1 := by
  have hρ0 : 0 < ρ := by linarith
  classical
  set S : Finset ℕ := (Finset.range N).filter (fun t => shiftGap ρ s k t θ ≠ 0) with hS
  have hmem : ∀ t ∈ S, shiftGap ρ s k t θ = 1 := by
    intro t ht
    rw [hS, Finset.mem_filter] at ht
    rcases shiftGap_eq_zero_or_one ρ s k hρ0 hk t θ with h | h
    · exact absurd h ht.2
    · exact h
  have hsub : S ⊆ Finset.range N := by
    intro t ht; rw [hS, Finset.mem_filter] at ht; exact ht.1
  have hzero : ∀ t ∈ Finset.range N, t ∉ S → shiftGap ρ s k t θ ^ 2 = 0 := by
    intro t ht hts
    have h0 : shiftGap ρ s k t θ = 0 := by
      by_contra hne
      exact hts (by rw [hS, Finset.mem_filter]; exact ⟨ht, hne⟩)
    rw [h0]; norm_num
  have hsum : ∑ t ∈ Finset.range N, shiftGap ρ s k t θ ^ 2 = (S.card : ℝ) := by
    rw [← Finset.sum_subset hsub hzero]
    rw [show ∑ t ∈ S, shiftGap ρ s k t θ ^ 2 = ∑ _t ∈ S, (1 : ℝ) from
      Finset.sum_congr rfl (fun t ht => by rw [hmem t ht]; norm_num)]
    simp
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha1 := (shiftGap_eq_one_iff ρ s k hρ0 hk a θ).mp (hmem a ha)
    have hb1 := (shiftGap_eq_one_iff ρ s k hρ0 hk b θ).mp (hmem b hb)
    have hab : b ≤ a := shiftGap_idx_le ρ s k hρ hks a b ha1.1 hb1.2
    have hba : a ≤ b := shiftGap_idx_le ρ s k hρ hks b a hb1.1 ha1.2
    omega
  rw [hsum]
  exact_mod_cast hcard

/-! ## The gap operator and the splitting of the shifted cut -/

/-- The gap operator: the cut `1_{(ρ^{k-i}, s ρ^{-i}]}` applied to `h`. -/
def gapOp (ρ s : ℝ) (k : ℤ) (h : ℝ → ℂ) (i : ℕ) (x : ℤ) : ℂ :=
  ∫ θ, (shiftGap ρ s k i θ : ℂ) * h θ * Echar x θ ∂mu01

/-- **The splitting**: the shifted cut at scale `i` is the aligned cut at `ρ ^ (k-i)` plus the
gap operator. -/
lemma cutOne_split (ρ s : ℝ) (k : ℤ) (h : ℝ → ℂ) (hh : MemLp h 2 mu01)
    (i : ℕ) (x : ℤ) :
    cutOne h (s * ρ ^ (-(i : ℤ))) x
      = cutOne h (ρ ^ (k - (i : ℤ))) x + gapOp ρ s k h i x := by
  have _inst : IsFiniteMeasure mu01 := isFiniteMeasure_mu01
  have hintC : ∀ (c : ℝ), Integrable (fun θ : ℝ =>
      (if θ ≤ c then (1 : ℂ) else 0) * h θ * Echar x θ) mu01 := by
    intro c
    refine Integrable.mono' (hh.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm ?_ ?_
    · refine ((Measurable.ite (measurableSet_le measurable_id measurable_const)
          measurable_const measurable_const).aestronglyMeasurable.mul
        hh.aestronglyMeasurable).mul (continuous_Echar x).measurable.aestronglyMeasurable
    · filter_upwards with θ
      calc ‖(if θ ≤ c then (1 : ℂ) else 0) * h θ * Echar x θ‖
          = ‖(if θ ≤ c then (1 : ℂ) else 0)‖ * ‖h θ‖ * ‖Echar x θ‖ := by
            rw [norm_mul, norm_mul]
        _ = ‖(if θ ≤ c then (1 : ℂ) else 0)‖ * ‖h θ‖ * 1 := by rw [norm_Echar]
        _ ≤ 1 * ‖h θ‖ * 1 := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) zero_le_one
            split <;> simp
        _ = ‖h θ‖ := by ring
  have hcast : ∀ θ : ℝ, (shiftGap ρ s k i θ : ℂ)
      = (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
        - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℂ) else 0) := by
    intro θ
    by_cases hA : θ ≤ s * ρ ^ (-(i : ℤ))
    · by_cases hB : θ ≤ ρ ^ (k - (i : ℤ))
      · simp only [shiftGap, hA, hB, if_true]; norm_num
      · simp only [shiftGap, hA, hB, if_true, if_false]; norm_num
    · by_cases hB : θ ≤ ρ ^ (k - (i : ℤ))
      · simp only [shiftGap, hA, hB, if_true, if_false]; norm_num
      · simp only [shiftGap, hA, hB, if_false]; norm_num
  have hptG : ∀ θ : ℝ, (shiftGap ρ s k i θ : ℂ) * h θ * Echar x θ
      = (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * h θ * Echar x θ
        - (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℂ) else 0) * h θ * Echar x θ := by
    intro θ; rw [hcast θ]; ring
  have hpt : ∀ θ : ℝ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * h θ * Echar x θ
      = (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℂ) else 0) * h θ * Echar x θ
        + (shiftGap ρ s k i θ : ℂ) * h θ * Echar x θ := by
    intro θ; rw [hcast θ]; ring
  have hintG : Integrable (fun θ : ℝ => (shiftGap ρ s k i θ : ℂ) * h θ * Echar x θ) mu01 :=
    Integrable.congr ((hintC (s * ρ ^ (-(i : ℤ)))).sub (hintC (ρ ^ (k - (i : ℤ)))))
      (Filter.Eventually.of_forall (fun θ => (hptG θ).symm))
  calc cutOne h (s * ρ ^ (-(i : ℤ))) x
      = ∫ θ, ((if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℂ) else 0) * h θ * Echar x θ
              + (shiftGap ρ s k i θ : ℂ) * h θ * Echar x θ) ∂mu01 := by
          unfold cutOne
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ θ, (if θ ≤ ρ ^ (k - (i : ℤ)) then (1 : ℂ) else 0) * h θ * Echar x θ ∂mu01)
          + (∫ θ, (shiftGap ρ s k i θ : ℂ) * h θ * Echar x θ ∂mu01) :=
          integral_add (hintC (ρ ^ (k - (i : ℤ)))) hintG
    _ = cutOne h (ρ ^ (k - (i : ℤ))) x + gapOp ρ s k h i x := rfl

/-! ## The main theorem -/

theorem shifted_cut_maximal (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s : ℝ), 0 < s → ∀ (h : ℝ → ℂ),
        MeasureTheory.MemLp h 2 Work.BourgainPlan.Oscillation.Lacunary.mu01 →
        ∫⁻ x : ℤ, (⨆ i : ℕ, ‖∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * h θ
            * Work.BourgainPlan.Oscillation.Lacunary.Echar x θ
              ∂Work.BourgainPlan.Oscillation.Lacunary.mu01‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ)
            ∂Work.BourgainPlan.Oscillation.Lacunary.mu01 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := lacunary_truncated_maximal_l2_gen_via_density ρ hρ
  refine ⟨Real.sqrt (4 * C₀ ^ 2 + 4), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro s hs g hg
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨k, hk_le, hk_lt⟩ := exists_zpow_le_lt ρ hρ s hs
  show (∫⁻ x : ℤ, (⨆ i : ℕ, ‖cutOne g (s * ρ ^ (-(i : ℤ))) x‖ₑ) ^ (2 : ℝ)
      ∂MeasureTheory.Measure.count)
    ≤ ENNReal.ofReal ((Real.sqrt (4 * C₀ ^ 2 + 4)) ^ 2)
        * ∫⁻ θ : ℝ, ‖g θ‖ₑ ^ (2 : ℝ) ∂mu01
  set N : ℝ≥0∞ := ∫⁻ θ : ℝ, ‖g θ‖ₑ ^ (2 : ℝ) ∂mu01 with hN
  -- the aligned maximal bound
  have hMbd : ∫⁻ x : ℤ, (⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count ≤ ENNReal.ofReal (C₀ ^ 2) * N := by
    rw [hN]
    have hc := hC₀ g hg
    have heq : (∫⁻ x : ℤ, (⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        = ∫⁻ x : ℤ, (⨆ i : ℕ, ‖∫ θ, (if |θ| ≤ cc ρ i then (1 : ℂ) else 0) * g θ
            * Echar x θ ∂mu01‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
      refine lintegral_congr (fun x => ?_)
      have hs' : (⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ)
          = ⨆ i : ℕ, ‖∫ θ, (if |θ| ≤ cc ρ i then (1 : ℂ) else 0) * g θ
              * Echar x θ ∂mu01‖ₑ :=
        iSup_congr (fun i => by rw [cutOne_eq_symm ρ g i x])
      rw [hs']
    rw [heq]
    exact hc
  -- the gap (shell) bound
  have hGbd : ∫⁻ x : ℤ, (⨆ i : ℕ, ‖gapOp ρ s k g i x‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count ≤ 1 * N := by
    rw [hN]
    have hsh := shell_bound_mu01 (K := 1) (by norm_num) (shiftGap ρ s k)
      (shiftGap_measurable ρ s k) (shiftGap_nonneg ρ s k hρ0 hk_le)
      (shiftGap_sq_sum_le_one ρ s k hρ hk_le hk_lt) g hg
    simpa only [gapOp, ENNReal.ofReal_one] using hsh
  -- the pointwise splitting
  have hsplit : ∀ x : ℤ, (⨆ i : ℕ, ‖cutOne g (s * ρ ^ (-(i : ℤ))) x‖ₑ)
      ≤ (⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ) + (⨆ i : ℕ, ‖gapOp ρ s k g i x‖ₑ) := by
    intro x
    refine iSup_le (fun i => ?_)
    have hid := cutOne_split ρ s k g hg i x
    calc ‖cutOne g (s * ρ ^ (-(i : ℤ))) x‖ₑ
        = ‖cutOne g (ρ ^ (k - (i : ℤ))) x + gapOp ρ s k g i x‖ₑ := by rw [hid]
      _ ≤ ‖cutOne g (ρ ^ (k - (i : ℤ))) x‖ₑ + ‖gapOp ρ s k g i x‖ₑ := enorm_add_le _ _
      _ ≤ (⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ) + (⨆ i : ℕ, ‖gapOp ρ s k g i x‖ₑ) :=
          add_le_add (cutOne_zpow_le_sup ρ hρ g (k - (i : ℤ)) x)
            (le_iSup (fun j : ℕ => ‖gapOp ρ s k g j x‖ₑ) i)
  -- arithmetic
  have harith : (4 : ℝ≥0∞) * (ENNReal.ofReal (C₀ ^ 2) * N) + 4 * (1 * N)
      = ENNReal.ofReal ((Real.sqrt (4 * C₀ ^ 2 + 4)) ^ 2) * N := by
    have hA : (4 : ℝ≥0∞) * ENNReal.ofReal (C₀ ^ 2) = ENNReal.ofReal (4 * C₀ ^ 2) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hB : (4 : ℝ≥0∞) * 1 = ENNReal.ofReal (4 : ℝ) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num]; simp
    rw [← mul_assoc, ← mul_assoc, hA, hB, ← add_mul,
      ← ENNReal.ofReal_add (by positivity) (by norm_num : (0 : ℝ) ≤ 4),
      Real.sq_sqrt (by positivity)]
  calc (∫⁻ x : ℤ, (⨆ i : ℕ, ‖cutOne g (s * ρ ^ (-(i : ℤ))) x‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count)
      ≤ ∫⁻ x : ℤ, ((⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ)
          + (⨆ i : ℕ, ‖gapOp ρ s k g i x‖ₑ)) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (hsplit x) (by norm_num : (0 : ℝ) ≤ 2))
    _ ≤ ∫⁻ x : ℤ, 4 * (((⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ) ^ (2 : ℝ))
          + ((⨆ i : ℕ, ‖gapOp ρ s k g i x‖ₑ) ^ (2 : ℝ)))
        ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => Lacunary.add_sq_le _ _)
    _ = 4 * (∫⁻ x : ℤ, (⨆ i : ℕ, ‖cutOne g (cc ρ i) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        + 4 * (∫⁻ x : ℤ, (⨆ i : ℕ, ‖gapOp ρ s k g i x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count) := by
        rw [lintegral_const_mul' _ _ (by norm_num),
          lintegral_add_left (measurable_of_countable _), mul_add]
    _ ≤ 4 * (ENNReal.ofReal (C₀ ^ 2) * N) + 4 * (1 * N) :=
        add_le_add (mul_le_mul_of_nonneg_left hMbd (by norm_num))
          (mul_le_mul_of_nonneg_left hGbd (by norm_num))
    _ = ENNReal.ofReal ((Real.sqrt (4 * C₀ ^ 2 + 4)) ^ 2) * N := harith
    _ = ENNReal.ofReal ((Real.sqrt (4 * C₀ ^ 2 + 4)) ^ 2)
        * ∫⁻ θ : ℝ, ‖g θ‖ₑ ^ (2 : ℝ) ∂mu01 := by rw [hN]

end

end Work.BourgainPlan.Oscillation
