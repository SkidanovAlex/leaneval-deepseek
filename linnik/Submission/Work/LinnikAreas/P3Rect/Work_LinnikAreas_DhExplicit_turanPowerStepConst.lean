import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_Inputs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Reduction
import Submission.Work.LinnikAreas.DhK.turanWeighted
import Submission.Work.LinnikAreas.turanPowerSum
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Work.LinnikAreas.DhK.XiAux

namespace Work.LinnikAreas.DhExplicit

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

noncomputable section

/-- The `kMult`-zero set of `ζ_K` inside a ball is finite. -/
private lemma kMult_finite_ball {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (R : ℝ) :
    ({v : ℂ | DhK.kMult χ v ≠ 0 ∧ ‖v‖ ≤ R} : Set ℂ).Finite := by
  have hΞ : ({v : ℂ | analyticOrderNatAt DhK.Xi v ≠ 0 ∧ ‖v‖ ≤ R} : Set ℂ).Finite := by
    refine (DhK.Xi_divisor_support_finite R).subset ?_
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hmem : v ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv2
    rw [Function.mem_support]
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (DhK.Xi_analyticOnNhd _) hmem]
    exact_mod_cast hv1
  have hL : ({v : ℂ | analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v ≠ 0 ∧
      ‖v‖ ≤ R} : Set ℂ).Finite := by
    have hsupp : (Function.support (fun u : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) R)) u : ℤ))).Finite := by
      simpa [Function.HasFiniteSupport] using
        (Commons.NumberTheory.Linnik.divisor_finiteSupport χ hχ (0 : ℂ) R)
    refine hsupp.subset ?_
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hmem : v ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv2
    rw [Function.mem_support]
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall (0 : ℂ) R) (z := v)
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z) hmem]
    exact_mod_cast hv1
  refine (hΞ.union hL).subset ?_
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  have hdisj : analyticOrderNatAt DhK.Xi v ≠ 0 ∨
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv1 (by simp [DhK.kMult, hcon.1, hcon.2])
  rcases hdisj with h | h
  · exact Or.inl ⟨h, hv2⟩
  · exact Or.inr ⟨h, hv2⟩

/-- `kMult`-zeros have real part at most `1`. -/
private lemma kMult_eq_zero_of_one_lt_re {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {v : ℂ}
    (hv : 1 < v.re) : DhK.kMult χ v = 0 := by
  have h1 : analyticOrderNatAt DhK.Xi v = 0 := by
    by_contra h
    exact DhK.Xi_ne_zero_of_one_lt_re hv (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
  have h2 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v = 0 := by
    by_contra h
    exact Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re χ hv
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
  simp only [DhK.kMult, h1, h2, Nat.add_zero]

/-- `(m²/(c-v)²)^j = m^{2j}·(1/(c-v))^{2j}`, in `ℂ`. -/
private lemma nw_pow_div (m : ℝ) (c v : ℂ) (j : ℕ) :
    (((m : ℂ) / (c - v)) ^ 2) ^ j = ((m ^ (2 * j) : ℝ) : ℂ) * (1 / (c - v)) ^ (2 * j) := by
  rw [← pow_mul, div_pow, one_div, inv_pow, ← Complex.ofReal_pow]
  ring

/-- **Turán step.**  With the Weyl-sum bound (`hweyl`, from `MassBound`) and the differentiated
explicit formula for `ζ_K` at `c ≥ 5` in "exceptional zero removed" form (`hdiff`, from
`ExplFormula`) as hypotheses, the pair of zeros `ρ₀` (real, exceptional) and `ρ` of a real
primitive character `χ` satisfies the Turán power inequality
`(1/36)/(5 - Re ρ)^{2j} ≤ 4j(1 - Re ρ₀)/4^{2j+1}` for some power `1 ≤ j ≤ K·Cw·log N`.

Proof route: this is `Work.LinnikAreas.turan_bound` of `ownRepelNearWindow.lean` (read it as a
template!) with `hule : 1 - u.re ≤ 1/100` replaced by `1 - ρ.re ≤ 1/3` and the final arithmetic
(`turan_arith`) removed; the constants `17, 34, 306` there become `19, 38, 342` (since
`m ≤ 5 - β' ≤ 5 - 2/3 = 13/3`, so `m^2 ≤ 19`).  The conclusion here asks only for the
intermediate inequality `hmain` of that proof, in terms of `ρ.re`. -/
theorem turanPowerStepConst {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ₀ ρ : ℂ) (hN3 : 3 ≤ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hχ2 : χ ^ 2 = 1) (hρ₀im : ρ₀.im = 0)
    (hzρ₀ : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ₀ ≠ 0)
    (hzρ : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0)
    (himρ : |ρ.im| ≤ 1) (hne : ρ ≠ ρ₀)
    (hρ₀le : 1 - ρ₀.re ≤ 1 / 100) (hρle : 1 - ρ.re ≤ 1 / 3)
    {Cw : ℝ} (hCw : 0 < Cw)
    (hweyl : ∀ {c γ' : ℝ}, 2 ≤ c → c ≤ 10 → |γ'| ≤ 1 →
      Summable (fun v : ℂ => (Work.LinnikAreas.DhK.kMult χ v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) ∧
      (∑' v : ℂ, (Work.LinnikAreas.DhK.kMult χ v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2)))
          ≤ Cw * Real.log (N : ℝ))
    (hdiff : ∀ (j : ℕ), 1 ≤ j → ∀ {c γ' : ℝ}, 5 ≤ c →
      Summable (fun v : ℂ => (Work.LinnikAreas.DhK.kMult χ v : ℝ) *
        ((1 / ((c : ℂ) - v) ^ (2 * j)).re
          + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) ∧
      4 * (j : ℝ) * (1 - ρ₀.re) / (c - 1) ^ (2 * j + 1) ≥
        ∑' v : ℂ, (if v = ρ₀ then 0 else (Work.LinnikAreas.DhK.kMult χ v : ℝ)) *
          ((1 / ((c : ℂ) - v) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ 10000 * Cw * Real.log (N : ℝ) ∧
      (1 / 36) / (5 - ρ.re) ^ (2 * j)
        ≤ 4 * (j : ℝ) * (1 - ρ₀.re) / (4 : ℝ) ^ (2 * j + 1) := by
  have hzρ0 : DirichletCharacter.completedLFunction χ ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hzρ
  have hρ_strip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hprim hzρ0
  have hρlt : ρ.re < 1 := hρ_strip.2
  have hfin := kMult_finite_ball χ hχ (20 : ℝ)
  set U : Finset ℂ := hfin.toFinset with hUdef
  have hUmem : ∀ v : ℂ, v ∈ U ↔ (DhK.kMult χ v ≠ 0 ∧ ‖v‖ ≤ 20) := by
    intro v
    rw [hUdef, Set.Finite.mem_toFinset]
    rfl
  have hρk : DhK.kMult χ ρ ≠ 0 := by
    intro h0
    simp only [DhK.kMult] at h0
    exact hzρ (by omega)
  have hρU : ρ ∈ U := by
    refine (hUmem ρ).mpr ⟨hρk, ?_⟩
    have h1 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    have h2 : |ρ.re| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hρ_strip.1], by linarith⟩
    have h3 : |ρ.im| ≤ 1 := by rwa [abs_le] at himρ ⊢
    linarith [h1, h2, h3]
  set β' : ℝ := ρ.re with hβ'def
  set γ' : ℝ := ρ.im with hγ'def
  have hβ'lt : β' < 1 := by rw [hβ'def]; exact hρlt
  have hβ'ge : 1 - 1 / 3 ≤ β' := by rw [hβ'def]; linarith
  have hγ'abs : |γ'| ≤ 1 := by rw [hγ'def]; exact himρ
  set d : ℂ → ℝ := fun v => min ‖((5 : ℂ) - v)‖ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖
    with hddef
  set S : Finset ℂ := U.filter (fun v => v ≠ ρ₀) with hSdef
  have hρS : ρ ∈ S := by
    rw [hSdef, Finset.mem_filter]; exact ⟨hρU, hne⟩
  obtain ⟨v₀, hv₀S, hv₀min⟩ := Finset.exists_min_image S d ⟨ρ, hρS⟩
  obtain ⟨hv₀U, hv₀ne⟩ := Finset.mem_filter.mp hv₀S
  have hv₀k : DhK.kMult χ v₀ ≠ 0 := ((hUmem v₀).mp hv₀U).1
  set m : ℝ := d v₀ with hmdef
  have hmnn : 0 ≤ m := by
    rw [hmdef, hddef]
    exact le_min (norm_nonneg _) (norm_nonneg _)
  have h5v₀ : (5 : ℂ) - v₀ ≠ 0 := by
    intro h0
    have h1 : v₀ = 5 := (sub_eq_zero.mp h0).symm
    have h2 : (1 : ℝ) < v₀.re := by rw [h1]; norm_num
    exact hv₀k (kMult_eq_zero_of_one_lt_re h2)
  have h5γv₀ : (5 : ℂ) + Complex.I * (γ' : ℂ) - v₀ ≠ 0 := by
    intro h0
    have h2 : (1 : ℝ) < v₀.re := by
      have h1 : (5 : ℝ) - v₀.re = 0 := by
        have hc := congrArg Complex.re h0
        rw [show ((5 : ℂ) + Complex.I * (γ' : ℂ) - v₀).re = 5 - v₀.re by simp] at hc
        simpa using hc
      linarith
    exact hv₀k (kMult_eq_zero_of_one_lt_re h2)
  have hmpos : 0 < m := by
    refine lt_of_le_of_ne hmnn (Ne.symm ?_)
    intro h0
    have h1 : d v₀ = 0 := by rw [← hmdef]; exact h0
    rw [hddef, min_eq_iff] at h1
    rcases h1 with h | h
    · exact norm_ne_zero_iff.mpr h5v₀ h.1
    · exact norm_ne_zero_iff.mpr h5γv₀ h.1
  have hm_le_dρ : m ≤ d ρ := by rw [hmdef]; exact hv₀min ρ hρS
  have hρdecomp : ρ = ((β' : ℝ) : ℂ) + Complex.I * ((γ' : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hβ'def, hγ'def]
    · simp [hβ'def, hγ'def]
  have hnorm2 : ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ)‖ = 5 - β' := by
    have h1 : ((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ) = ((5 - β' : ℝ) : ℂ) := by
      rw [hρdecomp]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 5 - β')]
  have hdρ_le : d ρ ≤ 5 - β' := by
    rw [hddef]
    calc min ‖((5 : ℂ) - ρ)‖ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ)‖
        ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ)‖ := min_le_right _ _
      _ = 5 - β' := hnorm2
  have hm_le_5β' : m ≤ 5 - β' := le_trans hm_le_dρ hdρ_le
  have hm_sq_le : m ^ 2 ≤ 19 := by
    have h1 : 5 - β' ≤ 4 + 1 / 3 := by linarith [hβ'ge]
    have h2 : m ^ 2 ≤ (4 + 1 / 3) ^ 2 := pow_le_pow_left₀ hmnn (hm_le_5β'.trans h1) 2
    nlinarith only [h2]
  have hγ6 : ‖((5 : ℂ) + Complex.I * (γ' : ℂ))‖ ≤ 6 := by
    have h1 : ‖((5 : ℂ) + Complex.I * (γ' : ℂ))‖ ≤ ‖((5 : ℂ))‖ + ‖Complex.I * (γ' : ℂ)‖ :=
      norm_add_le _ _
    have h2 : ‖Complex.I * (γ' : ℂ)‖ = |γ'| := by simp
    have h3 : ‖((5 : ℂ))‖ = 5 := by norm_num
    linarith [h1, h2, h3, hγ'abs]
  have hfar : ∀ v : ℂ, 20 < ‖v‖ →
      m ≤ ‖((5 : ℂ) - v)‖ ∧ m ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ := by
    intro v hv
    have hβ'ge4 : 5 - β' ≤ 4 + 1 / 3 := by linarith [hβ'ge]
    have h5n : ‖((5 : ℂ))‖ = 5 := by norm_num
    constructor
    · have h := abs_norm_sub_norm_le v (5 : ℂ)
      rw [h5n, abs_le] at h
      have h1 : ‖v‖ - 5 ≤ ‖((5 : ℂ) - v)‖ := by
        rw [norm_sub_rev]
        linarith [h.2]
      linarith [h1, hm_le_5β', hβ'ge4, hv]
    · have h := abs_norm_sub_norm_le v ((5 : ℂ) + Complex.I * (γ' : ℂ))
      rw [abs_le] at h
      have h1 : ‖v‖ - 6 ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ := by
        rw [norm_sub_rev]
        linarith [h.2, hγ6]
      linarith [h1, hm_le_5β', hβ'ge4, hv]
  -- the weight and the two point families
  set Wt : ℂ → ℝ := fun v => if v = ρ₀ then 0 else (DhK.kMult χ v : ℝ) with hWtdef
  set Z1 : ℂ → ℂ := fun v => if v = ρ₀ ∨ DhK.kMult χ v = 0 then 0
    else ((m : ℂ) / ((5 : ℂ) - v)) ^ 2 with hZ1def
  set Z2 : ℂ → ℂ := fun v => if v = ρ₀ ∨ DhK.kMult χ v = 0 then 0
    else ((m : ℂ) / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v)) ^ 2 with hZ2def
  have hWt_apply : ∀ v : ℂ, Wt v = if v = ρ₀ then 0 else (DhK.kMult χ v : ℝ) := by
    intro v; rw [hWtdef]
  have hZ1_apply : ∀ v : ℂ, Z1 v = if v = ρ₀ ∨ DhK.kMult χ v = 0 then 0
      else ((m : ℂ) / ((5 : ℂ) - v)) ^ 2 := by intro v; rw [hZ1def]
  have hZ2_apply : ∀ v : ℂ, Z2 v = if v = ρ₀ ∨ DhK.kMult χ v = 0 then 0
      else ((m : ℂ) / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v)) ^ 2 := by intro v; rw [hZ2def]
  have hv₀ne' : ¬(v₀ = ρ₀ ∨ DhK.kMult χ v₀ = 0) := by tauto
  have hm_le_dist1 : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult χ v ≠ 0 → m ≤ ‖((5 : ℂ) - v)‖ := by
    intro v hv1 hv2
    by_cases hv : ‖v‖ ≤ 20
    · have hvS : v ∈ S := Finset.mem_filter.mpr ⟨(hUmem v).mpr ⟨hv2, hv⟩, hv1⟩
      exact le_trans (by rw [hmdef]; exact hv₀min v hvS) (min_le_left _ _)
    · push_neg at hv
      exact (hfar v hv).1
  have hm_le_dist2 : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult χ v ≠ 0 →
      m ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ := by
    intro v hv1 hv2
    by_cases hv : ‖v‖ ≤ 20
    · have hvS : v ∈ S := Finset.mem_filter.mpr ⟨(hUmem v).mpr ⟨hv2, hv⟩, hv1⟩
      exact le_trans (by rw [hmdef]; exact hv₀min v hvS) (min_le_right _ _)
    · push_neg at hv
      exact (hfar v hv).2
  have hm_div1_le : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult χ v ≠ 0 → m / ‖((5 : ℂ) - v)‖ ≤ 1 := by
    intro v hv1 hv2
    have hne : (5 : ℂ) - v ≠ 0 := sub_ne_zero.mpr (by
      intro hc; exact hv2 (kMult_eq_zero_of_one_lt_re (by rw [← hc]; norm_num)))
    rw [div_le_one (norm_pos_iff.mpr hne)]
    exact hm_le_dist1 v hv1 hv2
  have hm_div2_le : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult χ v ≠ 0 →
      m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ ≤ 1 := by
    intro v hv1 hv2
    have hne : (5 : ℂ) + Complex.I * (γ' : ℂ) - v ≠ 0 := sub_ne_zero.mpr (by
      intro hc
      have h1 : (5 : ℝ) = v.re := by
        have h3 := congrArg Complex.re hc
        simpa using h3
      exact hv2 (kMult_eq_zero_of_one_lt_re (by linarith)))
    rw [div_le_one (norm_pos_iff.mpr hne)]
    exact hm_le_dist2 v hv1 hv2
  have hZ1_bound : ∀ v : ℂ, ‖Z1 v‖ ≤ (m / ‖((5 : ℂ) - v)‖) ^ 2 := by
    intro v
    rw [hZ1_apply v]
    by_cases h : v = ρ₀ ∨ DhK.kMult χ v = 0
    · rw [if_pos h, norm_zero]; exact sq_nonneg (m / ‖((5 : ℂ) - v)‖)
    · rw [if_neg h]
      rw [norm_pow]
      congr 1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmnn]
  have hZ2_bound : ∀ v : ℂ, ‖Z2 v‖ ≤ (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖) ^ 2 := by
    intro v
    rw [hZ2_apply v]
    by_cases h : v = ρ₀ ∨ DhK.kMult χ v = 0
    · rw [if_pos h, norm_zero]; exact sq_nonneg (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖)
    · rw [if_neg h]
      rw [norm_pow]
      congr 1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmnn]

  have hZ1_norm : ∀ v : ℂ, ‖Z1 v‖ ≤ 1 := by
    intro v
    by_cases hv : v = ρ₀ ∨ DhK.kMult χ v = 0
    · rw [hZ1_apply v, if_pos hv]; simp only [norm_zero]; norm_num
    · push_neg at hv
      refine le_trans (hZ1_bound v) ?_
      exact pow_le_one₀ (by positivity) (hm_div1_le v hv.1 hv.2)
  have hZ2_norm : ∀ v : ℂ, ‖Z2 v‖ ≤ 1 := by
    intro v
    by_cases hv : v = ρ₀ ∨ DhK.kMult χ v = 0
    · rw [hZ2_apply v, if_pos hv]; simp only [norm_zero]; norm_num
    · push_neg at hv
      refine le_trans (hZ2_bound v) ?_
      exact pow_le_one₀ (by positivity) (hm_div2_le v hv.1 hv.2)
  -- the index type and the designated element
  set wfun : ℂ × Bool → ℝ := fun i => Wt i.1 with hwfundef
  set zfun : ℂ × Bool → ℂ := fun i => if i.2 then Z2 i.1 else Z1 i.1 with hzfundef
  have hwfun_apply : ∀ i : ℂ × Bool, wfun i = Wt i.1 := by intro i; rw [hwfundef]
  have hzfun_apply : ∀ i : ℂ × Bool, zfun i = if i.2 then Z2 i.1 else Z1 i.1 := by
    intro i; rw [hzfundef]
  set i₀ : ℂ × Bool := if ‖((5 : ℂ) - v₀)‖ = m then (v₀, false) else (v₀, true) with hi₀def
  have hi₀fst : i₀.1 = v₀ := by
    rw [hi₀def]; split_ifs <;> rfl
  have hwi₀ : 1 ≤ wfun i₀ := by
    rw [hwfun_apply, hi₀fst, hWt_apply, if_neg hv₀ne]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hv₀k
  have hw_nonneg : ∀ i : ℂ × Bool, 0 ≤ wfun i := by
    intro i
    rw [hwfun_apply, hWt_apply]
    by_cases h : i.1 = ρ₀
    · rw [if_pos h]
    · rw [if_neg h]; positivity
  have hz_norm : ∀ i : ℂ × Bool, ‖zfun i‖ ≤ 1 := by
    intro i
    rw [hzfun_apply]
    by_cases h : i.2
    · rw [if_pos h]; exact hZ2_norm i.1
    · rw [if_neg h]; exact hZ1_norm i.1
  have hz_i₀_norm : ‖zfun i₀‖ = 1 := by
    rw [hi₀def]
    have hfalse : ¬ (((false : Bool)) = true) := by decide
    have htrue : (((true : Bool)) = true) := rfl
    split_ifs with hc
    · rw [hzfun_apply]
      rw [if_neg hfalse, hZ1_apply, if_neg hv₀ne']
      rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmnn, hc,
        div_self (ne_of_gt hmpos)]
      norm_num
    · rw [hzfun_apply]
      rw [if_pos htrue, hZ2_apply, if_neg hv₀ne']
      have hmm : m = ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v₀)‖ := by
        have h1 : m = min ‖((5 : ℂ) - v₀)‖ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v₀)‖ := by
          rw [hmdef, hddef]
        rcases min_choice ‖((5 : ℂ) - v₀)‖ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v₀)‖ with h | h
        · exact absurd (h1.trans h).symm hc
        · exact h1.trans h
      rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmnn, ← hmm,
        div_self (ne_of_gt hmpos)]
      norm_num
  have hz_i₀_ne : zfun i₀ ≠ 0 := by
    intro h0
    rw [h0] at hz_i₀_norm
    simp at hz_i₀_norm
  have hmax : ∀ i : ℂ × Bool, ‖zfun i‖ ≤ ‖zfun i₀‖ := by
    intro i; rw [hz_i₀_norm]; exact hz_norm i
  -- the majorant and the summability of the Turán family
  obtain ⟨hWsum, hWbnd⟩ := hweyl (c := 5) (γ' := γ') (by norm_num) (by norm_num) hγ'abs
  set Gmaj : ℂ × Bool → ℝ := fun i => 19 * ((DhK.kMult χ i.1 : ℝ) *
      (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
        + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) with hGmajdef
  have hGmaj_apply : ∀ i : ℂ × Bool, Gmaj i = 19 * ((DhK.kMult χ i.1 : ℝ) *
      (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
        + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) := by intro i; rw [hGmajdef]
  have hGmaj_nonneg : ∀ i : ℂ × Bool, 0 ≤ Gmaj i := by
    intro i; rw [hGmaj_apply i]; positivity
  have hptGmaj : ∀ v : ℂ, Gmaj (v, true) + Gmaj (v, false) = 38 * ((DhK.kMult χ v : ℝ) *
      (1 / ((5 - v.re) ^ 2 + v.im ^ 2) + 1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
    intro v
    simp only [hGmaj_apply, Prod.fst, Prod.snd]
    ring
  have hGmaj_summable : Summable Gmaj := by
    refine (summable_prod_of_nonneg (f := Gmaj) hGmaj_nonneg).mpr ⟨?_, ?_⟩
    · intro v
      exact summable_of_finite_support (Set.toFinite _)
    · have h2 : (fun v : ℂ => ∑' b : Bool, Gmaj (v, b)) = fun v : ℂ => 38 * ((DhK.kMult χ v : ℝ) *
          (1 / ((5 - v.re) ^ 2 + v.im ^ 2) + 1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
        funext v
        rw [tsum_fintype, Fintype.sum_bool, hptGmaj v]
      rw [h2]
      exact hWsum.mul_left 38
  have hGmaj_tsum : (∑' i : ℂ × Bool, Gmaj i) ≤ 38 * (Cw * Real.log (N : ℝ)) := by
    have hsplit : (∑' i : ℂ × Bool, Gmaj i)
        = ∑' v : ℂ, 38 * ((DhK.kMult χ v : ℝ) *
            (1 / ((5 - v.re) ^ 2 + v.im ^ 2) + 1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
      rw [Summable.tsum_prod hGmaj_summable]
      exact tsum_congr (fun v => by rw [tsum_fintype, Fintype.sum_bool, hptGmaj v])
    rw [hsplit, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hWbnd (by norm_num)
  have hden1 : ∀ v : ℂ, ‖((5 : ℂ) - v)‖ ^ 2 = (5 - v.re) ^ 2 + v.im ^ 2 := by
    intro v
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [show ((5 : ℂ) - v).re = 5 - v.re by simp]
    rw [show ((5 : ℂ) - v).im = -v.im by simp]
    ring
  have hden2 : ∀ v : ℂ, ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ ^ 2
      = (5 - v.re) ^ 2 + (v.im - γ') ^ 2 := by
    intro v
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [show ((5 : ℂ) + Complex.I * (γ' : ℂ) - v).re = 5 - v.re by simp]
    rw [show ((5 : ℂ) + Complex.I * (γ' : ℂ) - v).im = γ' - v.im by simp]
    ring
  have hm_sq_ker1 : ∀ v : ℂ, (m / ‖((5 : ℂ) - v)‖) ^ 2 ≤ 19 * (1 / ((5 - v.re) ^ 2 + v.im ^ 2)) := by
    intro v
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ (5 - v.re) ^ 2 + v.im ^ 2 by positivity) with h0 | hd
    · have hzero : ‖((5 : ℂ) - v)‖ = 0 := by
        have h2 : ‖((5 : ℂ) - v)‖ ^ 2 = 0 := by rw [hden1 v, ← h0]
        exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
      rw [hzero, div_zero, ← h0, one_div, inv_zero, mul_zero]
      norm_num
    have h1 : (m / ‖((5 : ℂ) - v)‖) ^ 2 = m ^ 2 / ((5 - v.re) ^ 2 + v.im ^ 2) := by
      rw [div_pow, hden1 v]
    rw [h1, div_le_iff₀ hd]
    calc m ^ 2 ≤ 19 := hm_sq_le
      _ = 19 * (1 / ((5 - v.re) ^ 2 + v.im ^ 2)) * ((5 - v.re) ^ 2 + v.im ^ 2) := by
          rw [one_div, mul_assoc, inv_mul_cancel₀ (ne_of_gt hd), mul_one]
  have hm_sq_ker2 : ∀ v : ℂ, (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖) ^ 2
      ≤ 19 * (1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2)) := by
    intro v
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ (5 - v.re) ^ 2 + (v.im - γ') ^ 2 by positivity) with h0 | hd
    · have hzero : ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ = 0 := by
        have h2 : ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ ^ 2 = 0 := by rw [hden2 v, ← h0]
        exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
      rw [hzero, div_zero, ← h0, one_div, inv_zero, mul_zero]
      norm_num
    have h1 : (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖) ^ 2
        = m ^ 2 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2) := by
      rw [div_pow, hden2 v]
    rw [h1, div_le_iff₀ hd]
    calc m ^ 2 ≤ 19 := hm_sq_le
      _ = 19 * (1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2)) * ((5 - v.re) ^ 2 + (v.im - γ') ^ 2) := by
          rw [one_div, mul_assoc, inv_mul_cancel₀ (ne_of_gt hd), mul_one]
  have hz_le : ∀ i : ℂ × Bool, ‖zfun i‖ ≤ (m / ‖((5 : ℂ) - i.1)‖) ^ 2
      + (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖) ^ 2 := by
    intro i
    rw [hzfun_apply]
    by_cases hb : i.2
    · rw [if_pos hb]
      linarith [hZ2_bound i.1, sq_nonneg (m / ‖((5 : ℂ) - i.1)‖)]
    · rw [if_neg hb]
      linarith [hZ1_bound i.1, sq_nonneg (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖)]
  have hfamily_le : ∀ i : ℂ × Bool, wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖)) ≤ Gmaj i := by
    intro i
    have hcase : wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖)) ≤ wfun i * ‖zfun i‖ := by
      apply mul_le_mul_of_nonneg_left _ (hw_nonneg i)
      rw [hz_i₀_norm, div_le_iff₀ (by positivity : (0:ℝ) < 1 + ‖zfun i‖)]
      nlinarith only [hz_norm i, norm_nonneg (zfun i)]
    refine le_trans hcase ?_
    rw [hwfun_apply, hWt_apply]
    by_cases hρ : i.1 = ρ₀
    · rw [if_pos hρ]; simp only [zero_mul]; exact hGmaj_nonneg i
    · rw [if_neg hρ, hGmaj_apply i]
      have hk : (0 : ℝ) ≤ (DhK.kMult χ i.1 : ℝ) := by positivity
      calc (DhK.kMult χ i.1 : ℝ) * ‖zfun i‖
          ≤ (DhK.kMult χ i.1 : ℝ) * ((m / ‖((5 : ℂ) - i.1)‖) ^ 2
              + (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖) ^ 2) :=
            mul_le_mul_of_nonneg_left (hz_le i) hk
        _ ≤ 19 * ((DhK.kMult χ i.1 : ℝ) *
              (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
                + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) := by
            have hA := hm_sq_ker1 i.1
            have hB := hm_sq_ker2 i.1
            nlinarith only [mul_le_mul_of_nonneg_left hA hk, mul_le_mul_of_nonneg_left hB hk]
  have hsum_family : Summable (fun i : ℂ × Bool =>
      wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖))) := by
    refine Summable.of_nonneg_of_le (f := Gmaj) (g := fun i : ℂ × Bool =>
      wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖))) ?_ ?_ hGmaj_summable
    · intro i; positivity
    · exact hfamily_le
  obtain ⟨j, hj1, hj2, hj3⟩ :=
    DhK.turanWeighted 1 (by norm_num) wfun zfun i₀ hwi₀ hw_nonneg hz_i₀_ne hmax hsum_family
  have hMj : (j : ℝ) ≤ 342 * Cw * Real.log (N : ℝ) := by
    have hMb : (∑' i : ℂ × Bool, wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖)))
        ≤ 38 * (Cw * Real.log (N : ℝ)) :=
      le_trans (Summable.tsum_le_tsum hfamily_le hsum_family hGmaj_summable) hGmaj_tsum
    have h9 : (j : ℝ) ≤ 9 * (38 * (Cw * Real.log (N : ℝ))) := by
      calc (j : ℝ) ≤ (8 + 1) * (∑' i : ℂ × Bool, wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖))) := hj2
        _ ≤ 9 * (38 * (Cw * Real.log (N : ℝ))) := by linarith [hMb]
    linarith only [h9]
  set Sfin : ℝ := ∑' v : ℂ, (if v = ρ₀ then 0 else (DhK.kMult χ v : ℝ)) *
      ((1 / ((5 : ℂ) - v) ^ (2 * j)).re
        + (1 / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re) with hSfindef
  have hwz_le : ∀ i : ℂ × Bool, wfun i * ‖zfun i‖ ≤ Gmaj i := by
    intro i
    have hcase : wfun i * ‖zfun i‖ ≤ Gmaj i := by
      rw [hwfun_apply, hWt_apply]
      by_cases hρ : i.1 = ρ₀
      · rw [if_pos hρ]; simp only [zero_mul]; exact hGmaj_nonneg i
      · rw [if_neg hρ, hGmaj_apply i]
        have hk : (0 : ℝ) ≤ (DhK.kMult χ i.1 : ℝ) := by positivity
        calc (DhK.kMult χ i.1 : ℝ) * ‖zfun i‖
            ≤ (DhK.kMult χ i.1 : ℝ) * ((m / ‖((5 : ℂ) - i.1)‖) ^ 2
                + (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖) ^ 2) :=
              mul_le_mul_of_nonneg_left (hz_le i) hk
          _ ≤ 19 * ((DhK.kMult χ i.1 : ℝ) *
                (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
                  + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) := by
              have hA := hm_sq_ker1 i.1
              have hB := hm_sq_ker2 i.1
              nlinarith only [mul_le_mul_of_nonneg_left hA hk, mul_le_mul_of_nonneg_left hB hk]
    exact hcase
  have hhalf : Summable (fun v : ℂ => Gmaj (v, false) + Gmaj (v, true)) := by
    have hpt : (fun v : ℂ => Gmaj (v, false) + Gmaj (v, true)) = fun v : ℂ => 38 * ((DhK.kMult χ v : ℝ) *
        (1 / ((5 - v.re) ^ 2 + v.im ^ 2) + 1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
      funext v; rw [add_comm, hptGmaj v]
    rw [hpt]
    exact hWsum.mul_left 38
  have hsumm_Gfalse : Summable (fun v : ℂ => Gmaj (v, false)) :=
    Summable.of_nonneg_of_le (fun v => hGmaj_nonneg (v, false))
      (fun v => le_add_of_nonneg_right (hGmaj_nonneg (v, true))) hhalf
  have hsumm_Gtrue : Summable (fun v : ℂ => Gmaj (v, true)) :=
    Summable.of_nonneg_of_le (fun v => hGmaj_nonneg (v, true))
      (fun v => le_add_of_nonneg_left (hGmaj_nonneg (v, false))) hhalf
  have hnorm_half : ∀ (b : Bool) (v : ℂ), ‖wfun (v, b) * (zfun (v, b)) ^ j‖ ≤ Gmaj (v, b) := by
    intro b v
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg (v, b))]
    have h1 : ‖zfun (v, b)‖ ^ j ≤ ‖zfun (v, b)‖ :=
      pow_le_self_one (norm_nonneg _) (hz_norm (v, b)) hj1
    exact le_trans (mul_le_mul_of_nonneg_left h1 (hw_nonneg (v, b))) (hwz_le (v, b))
  have hsumm1 : Summable (fun v : ℂ => wfun (v, false) * (zfun (v, false)) ^ j) :=
    Summable.of_norm_bounded (g := fun v : ℂ => Gmaj (v, false)) hsumm_Gfalse
      (fun v => hnorm_half false v)
  have hsumm2 : Summable (fun v : ℂ => wfun (v, true) * (zfun (v, true)) ^ j) :=
    Summable.of_norm_bounded (g := fun v : ℂ => Gmaj (v, true)) hsumm_Gtrue
      (fun v => hnorm_half true v)
  have hsumm_outer : Summable (fun v : ℂ => ∑' b : Bool, wfun (v, b) * (zfun (v, b)) ^ j) := by
    have hident : (fun v : ℂ => ∑' b : Bool, wfun (v, b) * (zfun (v, b)) ^ j)
        = fun v : ℂ => wfun (v, true) * (zfun (v, true)) ^ j
            + wfun (v, false) * (zfun (v, false)) ^ j := by
      funext v; rw [tsum_fintype, Fintype.sum_bool]
    rw [hident]
    exact hsumm2.add hsumm1
  have hsumm_zj : Summable (fun i : ℂ × Bool => wfun i * (zfun i) ^ j) := by
    refine Summable.of_norm_bounded (g := Gmaj) hGmaj_summable ?_
    intro i
    exact hnorm_half i.2 i.1
  -- the sum identity
  have hxinv : ∀ x : ℂ, 1 / x ^ (2 * j) = (1 / x) ^ (2 * j) := by
    intro x; rw [one_div, one_div, inv_pow]
  have hpointIJ : ∀ v : ℂ, (wfun (v, true) * (zfun (v, true)) ^ j).re
      + (wfun (v, false) * (zfun (v, false)) ^ j).re
      = m ^ (2 * j) * ((if v = ρ₀ then 0 else (DhK.kMult χ v : ℝ)) *
          ((1 / ((5 : ℂ) - v) ^ (2 * j)).re
            + (1 / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) := by
    intro v
    have hw : wfun (v, true) = wfun (v, false) := rfl
    rw [hw]
    by_cases hv : v = ρ₀
    · rw [hv]
      have h1 : wfun (ρ₀, false) = 0 := by rw [hwfun_apply, hWt_apply, if_pos rfl]
      rw [h1, if_pos rfl]
      simp
    · by_cases hk : DhK.kMult χ v = 0
      · have h1 : wfun (v, false) = 0 := by
          rw [hwfun_apply, hWt_apply, if_neg hv, hk]; norm_num
        rw [h1, if_neg hv, hk]
        simp
      · have hne : ¬(v = ρ₀ ∨ DhK.kMult χ v = 0) := by tauto
        have hwt : wfun (v, false) = (DhK.kMult χ v : ℝ) := by
          rw [hwfun_apply, hWt_apply, if_neg hv]
        have hzt : (zfun (v, true)) ^ j
            = ((m ^ (2 * j) : ℝ) : ℂ)
              * (1 / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v)) ^ (2 * j) := by
          rw [hzfun_apply, if_pos rfl, hZ2_apply, if_neg hne,
            nw_pow_div m ((5 : ℂ) + Complex.I * (γ' : ℂ)) v j]
        have hzf : (zfun (v, false)) ^ j
            = ((m ^ (2 * j) : ℝ) : ℂ) * (1 / ((5 : ℂ) - v)) ^ (2 * j) := by
          rw [hzfun_apply, if_neg (by decide : ¬ (((false : Bool)) = true)), hZ1_apply,
            if_neg hne, nw_pow_div m (5 : ℂ) v j]
        rw [hwt, hzt, hzf, if_neg hv]
        simp only [hxinv]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        ring
  have hpointIJ2 : ∀ v : ℂ, (∑' b : Bool, (wfun (v, b) * (zfun (v, b)) ^ j).re)
      = m ^ (2 * j) * ((if v = ρ₀ then 0 else (DhK.kMult χ v : ℝ)) *
          ((1 / ((5 : ℂ) - v) ^ (2 * j)).re
            + (1 / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) := by
    intro v
    rw [tsum_fintype, Fintype.sum_bool, hpointIJ v]
  have hsumId : (∑' i : ℂ × Bool, wfun i * (zfun i) ^ j).re = m ^ (2 * j) * Sfin := by
    rw [Summable.tsum_prod hsumm_zj, Complex.re_tsum hsumm_outer]
    rw [tsum_congr (fun v => (Complex.re_tsum
      (summable_of_finite_support (Set.toFinite _) :
        Summable (fun b : Bool => wfun (v, b) * (zfun (v, b)) ^ j))))]
    rw [tsum_congr hpointIJ2]
    rw [tsum_mul_left, hSfindef]
  -- the bound from the differentiated explicit formula
  obtain ⟨hEsumm2, hEbound⟩ := hdiff j hj1 (c := 5) (γ' := γ') (by norm_num)
  have hS_le : Sfin ≤ 4 * (j : ℝ) * (1 - ρ₀.re) / 4 ^ (2 * j + 1) := by
    rw [hSfindef]
    have h45 : (5 - 1 : ℝ) = 4 := by norm_num
    rw [h45] at hEbound
    exact hEbound
  have h36 : (1 / 36 : ℝ) ≤ m ^ (2 * j) * Sfin := by
    have h := hj3
    rw [hz_i₀_norm, one_pow, mul_one] at h
    rw [hsumId] at h
    norm_num at h
    exact h
  have hmain : (1 / 36) / (5 - β') ^ (2 * j) ≤ 4 * (j : ℝ) * (1 - ρ₀.re) / 4 ^ (2 * j + 1) := by
    have h1 : (1 / 36 : ℝ) ≤ m ^ (2 * j) * (4 * (j : ℝ) * (1 - ρ₀.re) / 4 ^ (2 * j + 1)) :=
      le_trans h36 (mul_le_mul_of_nonneg_left hS_le (by positivity))
    have hmposj : 0 < m ^ (2 * j) := pow_pos hmpos _
    have h2 : (1 / 36) / m ^ (2 * j) ≤ 4 * (j : ℝ) * (1 - ρ₀.re) / 4 ^ (2 * j + 1) := by
      rw [div_le_iff₀ hmposj]
      linarith [h1]
    have h4 : m ^ (2 * j) ≤ (5 - β') ^ (2 * j) := pow_le_pow_left₀ hmnn hm_le_5β' _
    have h5 : (1 / 36) / (5 - β') ^ (2 * j) ≤ (1 / 36) / m ^ (2 * j) :=
      div_le_div_of_nonneg_left (by norm_num) hmposj h4
    linarith [h2, h5]
  refine ⟨j, hj1, ?_, ?_⟩
  · calc (j : ℝ) ≤ 342 * Cw * Real.log (N : ℝ) := hMj
      _ ≤ 10000 * Cw * Real.log (N : ℝ) := by
          have h1 : (342 : ℝ) * Cw ≤ 10000 * Cw :=
            mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt hCw)
          have h2 : 0 ≤ Real.log (N : ℝ) :=
            le_of_lt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
          exact mul_le_mul_of_nonneg_right h1 h2
  · simpa only [hβ'def] using hmain

end

end Work.LinnikAreas.DhExplicit
