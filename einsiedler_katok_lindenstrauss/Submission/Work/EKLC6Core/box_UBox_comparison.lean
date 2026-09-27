import Mathlib
import Submission.Work.EKLC6Core.UBoxDef
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLC6Core.uminus_isHoro

/-!
# `EKLC6Core.box_UBox_comparison`

For the contracted horospherical subgroup `U = Uminus t = ⨆_{t i < t j} U_ij` and any radius
`R ≥ 1`:

* `B₁^U ⊆ UBox U R`: every element of `U` whose entries are within `1` of the identity has
  entries bounded by `R`;
* there is `K` such that for every `k ≥ K` the conjugate of the entrywise box of radius `R` is
  trapped in the normalising box,
  `aDiag (k • t) · UBox U R · aDiag (k • t)⁻¹ ⊆ B₁^U`.

Both statements are read off from the entry pattern of `Uminus t` (`uminus_entry_facts`):
the diagonal entries of `u ∈ Uminus t` are `1`, and its off-diagonal entries vanish in the
non-contracted directions (`i ≠ j`, `t j ≤ t i`).  Conjugation by `aDiag s` scales the
`(i,j)`-entry by `e^{s i - s j}` (`boxi_conj_apply`), so for `s = k • t` the only entries that
move are those in the strictly contracted directions `t i < t j`, where they are damped by

`e^{k (t i - t j)} ≤ e^{-α k}`,   `α = min {t j - t i : t i < t j} > 0`  (`gapSet t`),

and `1` on the diagonal.  Hence once `e^{-α k} R ≤ 1` — which holds for all `k ≥ K` as soon as
`K α ≥ log R` (Archimedean) — every entry of the conjugate is within `1` of the identity.

The first inclusion is the same entry pattern with the hypothesis `R ≥ 1`.
-/

open Filter Topology
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Entry arithmetic -/

/-- The scalar multiple `k • t` scales entrywise. -/
private theorem ubox_smul_t_sub (t : Fin 3 → ℝ) (k : ℕ) (i j : Fin 3) :
    ((k : ℝ) • t) i - ((k : ℝ) • t) j = (k : ℝ) * (t i - t j) := by
  simp only [Pi.smul_apply]
  ring

/-! ## The first inclusion: `B₁^U ⊆ UBox U R` -/

/-- The normalising box of `U = Uminus t` is contained in the entrywise box of any radius
`R ≥ 1`: the diagonal entries of `Uminus t` are `1` and the off-diagonal entries of an element
of the normalising box are already bounded by `1`. -/
theorem box1_uminus_subset_UBox (t : Fin 3 → ℝ) {R : ℝ} (hR : 1 ≤ R) :
    Box1 (Uminus t) ⊆ UBox (Uminus t) R := by
  intro g hg
  obtain ⟨hdiag, _⟩ := uminus_entry_facts t hg.1
  refine ⟨hg.1, fun i j => ?_⟩
  rcases eq_or_ne i j with rfl | hij
  · rw [hdiag i, abs_one]
    exact hR
  · have h := hg.2 i j
    rw [Matrix.one_apply_ne hij, sub_zero] at h
    linarith

/-! ## The second inclusion, for all large `k` -/

/-- **The contracted box of radius `R` is trapped in the normalising box.**  For the contracted
horospherical subgroup `Uminus t` there is `K` such that for every `k ≥ K` the conjugate
`aDiag (k • t) · UBox U R · aDiag (k • t)⁻¹` is contained in `B₁^{U}`. -/
theorem eventually_conj_UBox_uminus_subset_Box1 (t : Fin 3 → ℝ) {R : ℝ} (hR : 1 ≤ R) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      conjBy ((k : ℝ) • t) (UBox (Uminus t) R) ⊆ Box1 (Uminus t) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  -- the least positive contraction gap
  let α : ℝ := (gapSet t).min' (gapSet_nonempty t)
  have hαpos : 0 < α := gapSet_pos t (Finset.min'_mem _ _)
  have hαle : ∀ i j : Fin 3, i ≠ j → t i < t j → α ≤ t j - t i :=
    fun i j hij hlt => gapSet_min_le t hij hlt
  -- choose `K` with `e^{-α k} R ≤ 1` for all `k ≥ K`
  obtain ⟨K, hKexp⟩ : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Real.exp (-(α * (k : ℝ))) * R ≤ 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (Real.log R / α)
    refine ⟨N, fun k hk => ?_⟩
    have hNk : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    have hNα : Real.log R ≤ (N : ℝ) * α := (div_le_iff₀ hαpos).mp hN
    have hkα : Real.log R ≤ (k : ℝ) * α :=
      le_trans hNα (mul_le_mul_of_nonneg_right hNk hαpos.le)
    have hexp : Real.exp (-(α * (k : ℝ))) ≤ R⁻¹ := by
      calc Real.exp (-(α * (k : ℝ))) ≤ Real.exp (-(Real.log R)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = R⁻¹ := by rw [Real.exp_neg, Real.exp_log hRpos]
    calc Real.exp (-(α * (k : ℝ))) * R ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_right hexp hRpos.le
      _ = 1 := inv_mul_cancel₀ hRpos.ne'
  refine ⟨K, fun k hk h hh => ?_⟩
  rw [conjBy, Set.mem_image] at hh
  obtain ⟨g, hg, rfl⟩ := hh
  obtain ⟨hdiag, hoff⟩ := uminus_entry_facts t hg.1
  refine ⟨(uminus_isHoro t).1.2.1 ((k : ℝ) • t) g hg.1, fun i j => ?_⟩
  rw [boxi_conj_apply, ubox_smul_t_sub]
  rcases eq_or_ne i j with rfl | hij
  · -- the diagonal entries are fixed
    rw [sub_self, mul_zero, Real.exp_zero, one_mul, hdiag i, Matrix.one_apply_eq, sub_self,
      abs_zero]
    norm_num
  · rw [Matrix.one_apply_ne hij, sub_zero]
    by_cases hlt : t i < t j
    · -- a strictly contracted direction: the entry is damped by `e^{-α k}`
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have hgij : |g i j| ≤ R := hg.2 i j
      have hexp : Real.exp ((k : ℝ) * (t i - t j)) ≤ Real.exp (-(α * (k : ℝ))) := by
        rw [Real.exp_le_exp]
        have h1 : t i - t j ≤ -α := by linarith [hαle i j hij hlt]
        have h2 : (k : ℝ) * (t i - t j) ≤ (k : ℝ) * (-α) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
        have h3 : (k : ℝ) * (-α) = -(α * (k : ℝ)) := by ring
        linarith
      calc Real.exp ((k : ℝ) * (t i - t j)) * |g i j|
          ≤ Real.exp (-(α * (k : ℝ))) * R :=
            mul_le_mul hexp hgij (abs_nonneg _) (Real.exp_pos _).le
        _ ≤ 1 := hKexp k hk
    · -- a non-contracted direction: the entry of `g` vanishes
      have hle : t j ≤ t i := not_lt.mp hlt
      rw [hoff i j hij hle, mul_zero, abs_zero]
      norm_num

/-! ## The comparison -/

theorem box_UBox_comparison (t : Fin 3 → ℝ) {R : ℝ} (hR : 1 ≤ R) :
    (Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t) ⊆
        Work.EKLC6Core.UBox (Work.EKLC6Core.Uminus t) R) ∧
      (∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        Work.EKLC6Core.conjBy (((k : ℝ)) • t) (Work.EKLC6Core.UBox (Work.EKLC6Core.Uminus t) R)
          ⊆ Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t)) :=
  ⟨box1_uminus_subset_UBox t hR, eventually_conj_UBox_uminus_subset_Box1 t hR⟩

end Work.EKLC6Core
