/-
# ZeroFreeTables — HB84Assembly

The assembly of **HB Lemma 8.4** from the four analytic inputs
`HBLemma8_1`, `HBTable2and3`, `HBTable4range`, `HBRepZero84` of `HB8Defs.lean`.

The case analysis is HB's own (his §8, after Lemma 8.3):

* the first conjunct (`λ₁ ≤ 0.2 ⟹ λ₀ ≥ (2 − ε) log(λ₁⁻¹)`) combines
  `HBLemma8_1` (which covers the range `λ₀ ≥ 4e`) with the `4e`-capped form of
  `HBTable2and3` (which covers `λ₀ < 4e`);
* the second conjunct (`λ₀ ≥ max((3/2)log(λ₁⁻¹), 1.294)`, no `ε`) is
  `HBTable2and3` for `λ₁ ≤ 0.4`, `HBTable4range` for `0.4 ≤ λ₁ ≤ 1.294`, and is
  immediate from the minimality of `λ₁` for `λ₁ ≥ 1.294`;
* in both conjuncts the multiplicity clause of `Lam0Bound` is vacuous, by
  `HBRepZero84` (`λ₁ ≥ 1.294` for a repeated zero, incompatible with the range).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.LinnikAreas.exists_minLam_zero
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

private lemma conj_eq_of_im_zero {z : ℂ} (h : z.im = 0) : starRingEnd ℂ z = z := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, h]

/-- **HB Lemma 8.4** from its four ingredients. -/
theorem HBLemma8_4_of_pieces (h81 : HBLemma8_1) (h23 : HBTable2and3) (h4r : HBTable4range)
    (hrz : HBRepZero84) : HBLemma8_4 := by
  intro ε hε
  intro lamS hlamS
  obtain ⟨q1, h1⟩ := h81 ε hε lamS hlamS
  obtain ⟨q2, h2⟩ := h23 ε hε lamS hlamS
  obtain ⟨q3, h3⟩ := h4r
  obtain ⟨q4, h4⟩ := hrz
  refine ⟨max (max q1 q2) (max q3 q4), ?_⟩
  intro q hq hqne χ₁ ρ₁ hwide hsq him0 hSle
  have hq1 : q1 ≤ q := by omega
  have hq2 : q2 ≤ q := by omega
  have hq3 : q3 ≤ q := by omega
  have hq4 : q4 ≤ q := by omega
  have hmin : IsMin1 χ₁ ρ₁ := hwide.1
  have hZ1 : IsZ χ₁ ρ₁ := hmin.1
  have hχ1 : χ₁ ≠ 1 := isZ_ne_one hZ1
  have hconj1 : starRingEnd ℂ ρ₁ = ρ₁ := conj_eq_of_im_zero him0
  have hq2q : 2 ≤ q := by
    by_contra hlt
    have hq1 : q = 1 := by
      have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      omega
    exact hχ1 (DirichletCharacter.level_one' χ₁ hq1)
  have hlam1nn : 0 ≤ lamOf q ρ₁ := Work.LinnikContract.API.isZ_lambda_nonneg hq2q hZ1
  -- the two table inputs, instantiated
  have hT23 := h2 q hq2 χ₁ ρ₁ hwide hsq him0 hSle
  have hT4 := h3 q hq3 χ₁ ρ₁ hwide hsq him0
  have hRZ := h4 q hq4 χ₁ ρ₁ hwide hsq him0
  constructor
  · -- ## first conjunct: `λ₁ ≤ 0.2 ⟹ λ₀ ≥ (2 − ε) log(1/λ₁)`
    intro h5
    have hlam1le : lamOf q ρ₁ ≤ 1 / 5 := by linarith
    -- the multiplicity clause is vacuous
    have hmult : 2 ≤ zeroMult χ₁ ρ₁ → (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ lamOf q ρ₁ := by
      intro hm
      have := hRZ hm
      linarith
    refine lam0Bound_of_parts hmult ?_
    intro ρ hZρ hneρ _
    -- the minimal `λ`-zero `u ≠ ρ₁` of the working region
    have hzmρ : zeroMult χ₁ ρ ≠ 0 := isZ_mult_ne_zero hZρ
    have himρ : |ρ.im| ≤ 1 := isZ_im_le_one hZρ
    obtain ⟨u, hzu, hune, himu, hle_up, hminimal⟩ :=
      Work.LinnikAreas.exists_minLam_zero χ₁ hχ1 ρ₁ ρ 1 hzmρ himρ hneρ
    have hZu : IsZ χ₁ u := ⟨hχ1, hzu, himu⟩
    have hminu : ∀ v : ℂ, IsZ χ₁ v → v ≠ ρ₁ → lamOf q u ≤ lamOf q v := by
      intro v hZv hnev
      by_cases hv : lamOf q v ≤ lamOf q ρ
      · exact hminimal v (isZ_mult_ne_zero hZv) hnev (isZ_im_le_one hZv) hv
      · push_neg at hv
        linarith
    have hgoal : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ lamOf q u := by
      by_cases h4e : 4 * Real.exp 1 ≤ lamOf q u
      · exact h1 q hq1 χ₁ ρ₁ u hwide hsq him0 hZu hune hminu hSle hlam1le h4e
      · push_neg at h4e
        have hle := hT23.1 hlam1le u hZu hune (fun _ => by rw [hconj1]; exact hune)
        by_cases hc4 : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 4 * Real.exp 1
        · have hmin_eq : min (4 * Real.exp 1) ((2 - ε) * Real.log (1 / lamOf q ρ₁))
              = (2 - ε) * Real.log (1 / lamOf q ρ₁) := min_eq_right hc4
          rw [hmin_eq] at hle
          exact hle
        · push_neg at hc4
          have hmin_eq : min (4 * Real.exp 1) ((2 - ε) * Real.log (1 / lamOf q ρ₁))
              = 4 * Real.exp 1 := min_eq_left hc4.le
          rw [hmin_eq] at hle
          linarith
    exact le_trans hgoal hle_up
  · -- ## second conjunct: `λ₀ ≥ max((3/2) log(1/λ₁), 1.294)`
    have hmult : 2 ≤ zeroMult χ₁ ρ₁ →
        max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000) ≤ lamOf q ρ₁ := by
      intro hm
      have h1294 := hRZ hm
      have hlam1pos : 0 < lamOf q ρ₁ := by linarith
      have hinv1 : (1 : ℝ) / lamOf q ρ₁ ≤ 1 := by
        rw [div_le_iff₀ hlam1pos]; linarith
      have hlogneg : Real.log (1 / lamOf q ρ₁) ≤ 0 :=
        Real.log_nonpos (div_nonneg (by norm_num) hlam1pos.le) hinv1
      rw [max_le_iff]
      exact ⟨by nlinarith [hlogneg, hlam1nn], h1294⟩
    refine lam0Bound_of_parts hmult ?_
    intro ρ hZρ hneρ _
    have hle1 : lamOf q ρ₁ ≤ lamOf q ρ := isMin1_lam_le hmin hZρ
    by_cases hcase1 : lamOf q ρ₁ ≤ 2 / 5
    · exact hT23.2 hcase1 ρ hZρ hneρ (fun _ => by rw [hconj1]; exact hneρ)
    · push_neg at hcase1
      by_cases hcase2 : lamOf q ρ₁ ≤ 1294 / 1000
      · exact hT4 hcase1.le hcase2 ρ hZρ hneρ (fun _ => by rw [hconj1]; exact hneρ)
      · push_neg at hcase2
        -- `λ₁ ≥ 1.294`: the maximality gives `λ(ρ) ≥ λ₁ ≥ 1.294 = max(...)`
        have hlam1pos : 0 < lamOf q ρ₁ := by linarith
        have hinv1 : (1 : ℝ) / lamOf q ρ₁ ≤ 1 := by
          rw [div_le_iff₀ hlam1pos]; linarith
        have hlogneg : Real.log (1 / lamOf q ρ₁) ≤ 0 :=
          Real.log_nonpos (div_nonneg (by norm_num) hlam1pos.le) hinv1
        rw [max_le_iff]
        exact ⟨by nlinarith [hlogneg, hle1, hlam1nn], by linarith⟩

end Work.ZeroFreeTables
