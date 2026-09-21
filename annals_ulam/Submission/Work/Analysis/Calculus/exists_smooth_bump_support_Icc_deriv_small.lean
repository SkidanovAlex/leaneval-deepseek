import Mathlib
import Submission.Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds

open scoped ContDiff
open Set

set_option autoImplicit false

namespace Commons.Analysis.Calculus

lemma exists_smooth_bump_support_Icc_deriv_small
    {a b : ℝ} (hab : a < b) (h0 : (0 : ℝ) ∉ Set.Icc a b)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      ContDiff ℝ ∞ h ∧
      (∀ x, 0 ≤ h x) ∧
      Function.support h ⊆ Set.Icc a b ∧
      h 0 = 0 ∧
      (∀ j ≤ k, ∀ x, |iteratedDeriv j h x| ≤ ε) ∧
      h ≠ 0 := by
  classical
  let x₀ : ℝ := (a + b) / 2
  have hx₀_mem : x₀ ∈ Set.Ioo a b := by
    dsimp [x₀]
    constructor <;> linarith
  have hIoo_nhds : Set.Ioo a b ∈ nhds x₀ := Ioo_mem_nhds hx₀_mem.1 hx₀_mem.2
  obtain ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf_x₀⟩ :=
    exists_contDiff_tsupport_subset (s := Set.Ioo a b) (x := x₀) (n := (⊤ : ℕ∞)) hIoo_nhds
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact (hf_range ⟨x, rfl⟩).1
  have hf_supp : Function.support f ⊆ Set.Icc a b := by
    intro x hx
    have hx_ts : x ∈ tsupport f := subset_tsupport f hx
    have hx_ioo : x ∈ Set.Ioo a b := hf_tsupp hx_ts
    exact ⟨le_of_lt hx_ioo.1, le_of_lt hx_ioo.2⟩
  have hf0 : f 0 = 0 := by
    by_contra hf0ne
    have h0supp : (0 : ℝ) ∈ Function.support f := by
      simpa [Function.mem_support] using hf0ne
    exact h0 (hf_supp h0supp)
  have hf_ne : f ≠ 0 := by
    intro hzero
    have : f x₀ = 0 := by rw [hzero]; rfl
    rw [hf_x₀] at this
    norm_num at this
  have hf_bounds :=
    exists_bound_iteratedDeriv_of_hasCompactSupport_smooth hf_smooth hf_cs
  choose C hC_nonneg hC using hf_bounds
  let B : ℝ := ∑ j ∈ Finset.range (k + 1), (C j + 1)
  have hB_pos : 0 < B := by
    dsimp [B]
    apply Finset.sum_pos
    · intro j hj
      have := hC_nonneg j
      linarith
    · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  let δ : ℝ := ε / B
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact div_pos hε hB_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  let h : ℝ → ℝ := δ • f
  have hh_smooth : ContDiff ℝ ∞ h := by
    dsimp [h]
    exact hf_smooth.const_smul δ
  have hh_nonneg : ∀ x, 0 ≤ h x := by
    intro x
    dsimp [h]
    exact mul_nonneg hδ_nonneg (hf_nonneg x)
  have hh_supp : Function.support h ⊆ Set.Icc a b := by
    intro x hx
    apply hf_supp
    dsimp [h] at hx
    intro hfx
    apply hx
    simp [hfx]
  have hh0 : h 0 = 0 := by
    dsimp [h]
    rw [hf0, mul_zero]
  have hh_bounds : ∀ j ≤ k, ∀ x, |iteratedDeriv j h x| ≤ ε := by
    intro j hj x
    have hderiv : iteratedDeriv j h x = δ * iteratedDeriv j f x := by
      dsimp [h]
      rw [iteratedDeriv_const_smul_field, smul_eq_mul]
    rw [hderiv, abs_mul, abs_of_nonneg hδ_nonneg]
    have hCj : |iteratedDeriv j f x| ≤ C j := hC j x
    have hCj_le_B : C j ≤ B := by
      dsimp [B]
      have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
      have hsingle : C j ≤ C j + 1 := by linarith
      have hsum_le : C j + 1 ≤ ∑ i ∈ Finset.range (k + 1), (C i + 1) := by
        exact Finset.single_le_sum (s := Finset.range (k + 1)) (f := fun i => C i + 1)
          (fun i _ => by have := hC_nonneg i; linarith) hmem
      linarith
    calc
      δ * |iteratedDeriv j f x| ≤ δ * C j := mul_le_mul_of_nonneg_left hCj hδ_nonneg
      _ ≤ δ * B := mul_le_mul_of_nonneg_left hCj_le_B hδ_nonneg
      _ = ε := by dsimp [δ]; field_simp [ne_of_gt hB_pos]
  refine ⟨h, hh_smooth, hh_nonneg, hh_supp, hh0, hh_bounds, ?_⟩
  intro hzero
  have : h x₀ = 0 := by rw [hzero]; rfl
  dsimp [h] at this
  rw [hf_x₀, mul_one] at this
  exact hδ_ne this

end Commons.Analysis.Calculus

namespace Commons.Analysis.Calculus

lemma exists_smooth_bump_support_Icc_deriv_small_tau
    (τ : ℝ) (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      ContDiff ℝ ∞ h ∧
      (∀ x, 0 ≤ h x) ∧
      Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ) ∧
      h 0 = 0 ∧
      (∀ j ≤ k, ∀ x, |iteratedDeriv j h x| ≤ ε) ∧
      h ≠ 0 := by
  have ha : (1 - 2 * τ : ℝ) < 1 - τ := by linarith
  have h0 : (0 : ℝ) ∉ Set.Icc (1 - 2 * τ) (1 - τ) := by
    intro hmem
    have hle : 1 - 2 * τ ≤ 0 := hmem.1
    linarith
  exact exists_smooth_bump_support_Icc_deriv_small ha h0 k hε

end Commons.Analysis.Calculus

namespace Commons.Analysis.Calculus

/-- Paper-shaped flat bump: nonzero smooth bump supported in `[c-2δ, c-δ]`, vanishing
on the initial segment `[c-2δ, c-2δ+η)` of its support, with all iterated derivatives
up to `k` bounded by `ε`. -/
lemma exists_smooth_bump_support_Icc_deriv_small_flat
    {c δ η : ℝ} (_hc0 : 0 < c) (_hc1 : c < 1)
    (_hδ0 : 0 < δ) (hδsmall : 2 * δ < c)
    (hη0 : 0 < η) (hηδ : η < δ)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      ContDiffOn ℝ ∞ h Set.univ ∧
      (∀ x, 0 ≤ h x) ∧
      Function.support h ⊆ Set.Icc (c - 2 * δ) (c - δ) ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) ∧
      (∃ η' : ℝ, 0 < η' ∧ ∀ s : ℝ, c - 2 * δ ≤ s → s < c - 2 * δ + η' → h s = 0) ∧
      h 0 = 0 ∧
      (∀ j ≤ k, ∀ x, |iteratedDeriv j h x| ≤ ε) := by
  let a : ℝ := c - 2 * δ + η
  let b : ℝ := c - δ
  have hab : a < b := by
    dsimp [a, b]
    linarith
  have h0 : (0 : ℝ) ∉ Set.Icc a b := by
    intro hmem
    have ha_pos : 0 < a := by
      dsimp [a]
      linarith
    linarith [hmem.1]
  obtain ⟨h, hh_smooth, hh_nonneg, hh_supp, hh0, hh_bounds, hh_ne⟩ :=
    exists_smooth_bump_support_Icc_deriv_small hab h0 k hε
  refine ⟨h, hh_smooth.contDiffOn, hh_nonneg, ?_, ?_, ?_, hh0, hh_bounds⟩
  · intro s hs
    have hs' := hh_supp hs
    constructor <;> dsimp [a, b] at hs' ⊢ <;> linarith [hs'.1, hs'.2, hη0]
  · rcases Function.ne_iff.mp hh_ne with ⟨s, hs⟩
    refine ⟨s, ?_, hs⟩
    by_contra hsnonpos
    have hs_not : s ∉ Function.support h := by
      intro hmem
      have hmem_Icc : s ∈ Set.Icc a b := hh_supp hmem
      have ha_pos : 0 < a := by
        dsimp [a]
        linarith
      linarith [hmem_Icc.1]
    exact hs_not (by simpa [Function.mem_support] using hs)
  · refine ⟨η, hη0, ?_⟩
    intro s hs_left hs_right
    by_contra hne
    have hs_supp : s ∈ Function.support h := by
      simpa [Function.mem_support] using hne
    have hs_Icc : s ∈ Set.Icc a b := hh_supp hs_supp
    have hsa : a ≤ s := hs_Icc.1
    have hlt : s < a := by
      dsimp [a] at hs_right ⊢
      exact hs_right
    linarith

end Commons.Analysis.Calculus
