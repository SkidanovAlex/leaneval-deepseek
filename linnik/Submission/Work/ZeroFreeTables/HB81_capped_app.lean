import Mathlib
import Submission.Work.ZeroFreeTables.HB81_capped
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.HB81_triangle_local_unif

namespace Work.ZeroFreeTables

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- **Application form of HB's Lemma 8.1** (the "capped" repulsion `λ₀ ≥ (2−ε) log(1/λ₁)`),
in the form consumed by the `χ₁`-window argument: the box in which `ρ₀` is `λ`-minimal is the
*own window* `|Im| ≤ |ρ₀.im| + δ` of `ρ₀` (with the *given* slack `δ ∈ (0,1)`, hence strictly
smaller than `1`), and the log-derivative input `L52Hyp χ₁ (1/8 + εs − εL/4) εL δ` is supplied
as a hypothesis.

This is `Work.ZeroFreeTables.HB81_capped_wide` with the box height `Hb := |ρ₀.im| + δ` chosen
*after* `q`: the §6 triangle `Work.ZeroFreeTables.HB81_triangle_local_unif` has a threshold
independent of the box height, so the dyadic-cover assembly of `HB81_capped_wide` goes through
verbatim with the variable height. -/
theorem HB81_capped_app (δ ec εs εL : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hεs : 0 < εs) (hεL : 0 < εL) (hec : ec = 2 * εs + 3.5 * εL) :
    ∀ ε : ℝ, 0 < ε → 8 * (2 - ε) * ec ≤ ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] (ρ₁ ρ₀ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → ρ₀ ≠ ρ₁ →
    (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ |ρ₀.im| + δ → u ≠ ρ₁ →
      Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) →
    |ρ₀.im| ≤ 10 * Real.log (q : ℝ) →
    Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 5 → 4 * Real.exp 1 ≤ Work.LinnikContract.lamOf q ρ₀ →
    Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamMax q →
    Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + εs - εL / 4) εL δ →
    (2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ Work.LinnikContract.lamOf q ρ₀ := by
  intro ε hε hsmall
  by_cases hε2 : 2 ≤ ε
  · -- `ε ≥ 2`: the right-hand side of the log satisfies `(2-ε) log(1/λ₁) ≤ 0`
    refine ⟨2, ?_⟩
    intro q hq _inst χ₁ _instc ρ₁ ρ₀ hmin hsq him hzm0 hne hmax0 hγ10 h15 h4e hcap H
    have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
    have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
    obtain ⟨-, -, hlam1pos⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq hχ1 hzm1
    have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := by linarith [h4e, Real.exp_pos 1]
    have hLpos : 0 < Real.log (1 / Work.LinnikContract.lamOf q ρ₁) := by
      apply Real.log_pos
      rw [one_div, one_lt_inv₀ hlam1pos]
      linarith [h15]
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le) hlam0pos.le
  · push_neg at hε2
    have hec0 : (0 : ℝ) ≤ ec := by rw [hec]; positivity
    have hsmall4 : 4 * (2 - ε) * ec ≤ ε := by linarith [hsmall]
    obtain ⟨N, hN⟩ := exists_nat_ge (8 / ε)
    set K : ℕ := N + 1 with hKdef
    have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
    have hXK : 4 * (2 - ε) / ε ≤ 4 * Real.exp 1 * 2 ^ K := by
      rw [hKdef]
      have h2 : (N : ℝ) ≤ (2 : ℝ) ^ N :=
        by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := N)))
      have hmono : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (N + 1) :=
        calc (2 : ℝ) ^ N ≤ (2 : ℝ) ^ N * 2 :=
              le_mul_of_one_le_right (by positivity) (by norm_num)
          _ = (2 : ℝ) ^ (N + 1) := by ring
      have h8 : 8 / ε ≤ (2 : ℝ) ^ (N + 1) := by linarith [hN, h2, hmono]
      have h4' : 4 * (2 - ε) / ε ≤ 8 / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        nlinarith [hε2.le]
      have hpos : (0 : ℝ) < 2 ^ (N + 1) := by positivity
      have hle : 8 / ε ≤ 4 * Real.exp 1 * 2 ^ (N + 1) := by nlinarith [h8, hexp1, hpos]
      linarith [h4', hle]
    let xOf : ℕ → ℝ := fun k => 1 / 2 + 1 / (4 * Real.exp 1 * 2 ^ k) + 2 * ec
    have hxOf : ∀ k, 0 < xOf k := fun k => by simp only [xOf]; positivity
    have hTgen : ∀ k : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor]
          (ρ₁ ρ₀ : ℂ) (Hb : ℝ),
          Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
          Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → ρ₀ ≠ ρ₁ →
          (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb → u ≠ ρ₁ →
            Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) →
          |ρ₀.im| + δ ≤ Hb → |ρ₀.im| ≤ 10 * Real.log (q : ℝ) →
          Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 100 →
          Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamMax q →
          Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + εs - εL / 4) εL δ →
          0 ≤ 2 * (∫ t in (0:ℝ)..xOf k,
                Real.exp (Work.LinnikContract.lamOf q ρ₀ * t) * (xOf k - t))
            - 2 * (∫ t in (0:ℝ)..xOf k, Real.exp ((Work.LinnikContract.lamOf q ρ₀
                - Work.LinnikContract.lamOf q ρ₁) * t) * (xOf k - t))
            - xOf k ^ 2 / 2 + (2 * (1 / 8 + εs - εL / 4) + 4 * εL) * xOf k :=
      fun k => HB81_triangle_local_unif (xOf k) (hxOf k) εL hεL δ hδ0 hδ1 (1 / 8 + εs - εL / 4)
    choose qT hqT using hTgen
    refine ⟨max (Finset.sup (Finset.range (K + 1)) qT) 2, ?_⟩
    intro q hq _inst χ₁ _instc ρ₁ ρ₀ hmin hsq him hzm0 hne hmax0 hγ10 h15 h4e hcap H
    have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
    have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
    have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
    obtain ⟨-, -, hlam1pos⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
    by_cases h100 : Work.LinnikContract.lamOf q ρ₁ < 1 / 100
    · have hLam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := by linarith [h4e, Real.exp_pos 1]
      rcases HB81_cover (Work.LinnikContract.lamOf q ρ₀) h4e K with ⟨k, hkK, hk1, hk2⟩ | hKle
      · have hkk : k < K + 1 := by omega
        have hqk : qT k ≤ q := le_trans (Finset.le_sup (Finset.mem_range.mpr hkk))
          (le_trans (le_max_left _ _) hq)
        have h6 := hqT k q hqk χ₁ ρ₁ ρ₀ (|ρ₀.im| + δ) hmin hsq him hzm0 hne hmax0 le_rfl hγ10
          h100.le hcap H
        have hbk := hb81_logBound (x₀ := xOf k) (X := 4 * Real.exp 1 * 2 ^ k)
          (εx := ec) (εc := ec) (C := 2 * (1 / 8 + εs - εL / 4) + 4 * εL)
          (by positivity) hLam0pos hlam1pos hec0 (by simp only [xOf])
          (by rw [hec]; ring) le_rfl h6
        have hk2' : Work.LinnikContract.lamOf q ρ₀ ≤ 2 * (4 * Real.exp 1 * 2 ^ k) := by
          have heq : (4 : ℝ) * Real.exp 1 * 2 ^ (k + 1) = 2 * (4 * Real.exp 1 * 2 ^ k) := by
            rw [pow_succ]; ring
          linarith [hk2, heq]
        exact HB81_cell_arith ε ec hε hε2.le hec0 hsmall4 (4 * Real.exp 1 * 2 ^ k)
          (by have hk' : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
                exact_mod_cast (Nat.one_le_two_pow (n := k))
              nlinarith [hk', Real.exp_pos 1])
          (Work.LinnikContract.lamOf q ρ₀) (Work.LinnikContract.lamOf q ρ₁)
          hk1 hk2' hlam1pos (by simpa only [xOf] using hbk)
      · have hkk : K < K + 1 := by omega
        have hqk : qT K ≤ q := le_trans (Finset.le_sup (Finset.mem_range.mpr hkk))
          (le_trans (le_max_left _ _) hq)
        have h6 := hqT K q hqk χ₁ ρ₁ ρ₀ (|ρ₀.im| + δ) hmin hsq him hzm0 hne hmax0 le_rfl hγ10
          h100.le hcap H
        have hbk := hb81_logBound (x₀ := xOf K) (X := 4 * Real.exp 1 * 2 ^ K)
          (εx := ec) (εc := ec) (C := 2 * (1 / 8 + εs - εL / 4) + 4 * εL)
          (by positivity) hLam0pos hlam1pos hec0 (by simp only [xOf])
          (by rw [hec]; ring) le_rfl h6
        exact HB81_tail_arith ε ec hε hε2.le hec0 hsmall (4 * Real.exp 1 * 2 ^ K)
          (by have hk' : (1 : ℝ) ≤ (2 : ℝ) ^ K := by
                exact_mod_cast (Nat.one_le_two_pow (n := K))
              nlinarith [hk', Real.exp_pos 1])
          hXK (Work.LinnikContract.lamOf q ρ₀) (Work.LinnikContract.lamOf q ρ₁)
          hKle hlam1pos (by simpa only [xOf] using hbk)
    · -- `1/100 ≤ λ₁`: the log is bounded by `5`, while `λ₀ ≥ 4e > 10`
      push_neg at h100
      have hLle : Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ Real.log 100 := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hlam1pos]; linarith [h100]
      have hLnn : 0 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₁) := by
        apply Real.log_nonneg
        rw [one_div, one_le_inv₀ hlam1pos]; linarith [h15]
      have h5 : Real.log 100 ≤ 5 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have he5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
          rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        rw [he5]
        calc (100 : ℝ) ≤ (2.7182818283) ^ 5 := by norm_num
          _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 5
      have h10 : (10 : ℝ) ≤ 4 * Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
      have h1 : (2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ 2 * Real.log 100 := by
        have h2 : (2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁)
            ≤ 2 * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) :=
          mul_le_mul_of_nonneg_right (by linarith [hε]) hLnn
        have h3 : 2 * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ 2 * Real.log 100 :=
          mul_le_mul_of_nonneg_left hLle (by norm_num)
        linarith [h2, h3]
      linarith [h1, h5, h10, h4e]

end

end Work.ZeroFreeTables
