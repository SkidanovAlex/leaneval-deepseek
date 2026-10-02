/-
Own file for `Work.LinnikAreas.ownRepelNearWindow`: the *window* half of the same-character
Deuring–Heilbronn repulsion (`λ(u) ≤ log q/100`).

Route (Linnik's Turán power-sum method, as modernised by Kadiri–Ng–Wong, arXiv:1902.08640 §2):
the Turán power-sum theorem (`Work.LinnikAreas.DhK.turanWeighted`) applied to the zeros of
`ζ_K = Ξ·Λ_ψ` (ψ the primitive real character inducing the given χ₀), with weights equal to the
zero multiplicities and the two families of points `z_v = m²/(5-v)²`, `w_v = m²/(5+iγ'-v)²`,
produces a power `j ≤ (8+ε)M` whose power sum is at least `δ`; the delegated differentiated
explicit formula for `ζ_K` (Heath-Brown (6.3) / KNW (2.5)–(2.6)) bounds the same power sum by
`4j(1-β₁)/(c-1)^{2j+1}`.  Together they give `(1-β')𝓛 ≳ log(1/λ(ρ₀))`, where `ρ'` is the zero of
maximal real part with `|Im| ≤ 1`; every other zero has `λ ≥ λ(ρ')`, so the repulsion follows for
the given `u`.  The Weyl sum `M` is bounded by
`(5-1+1/100)²·Σ_v kMult(v)(1/|5-v|² + 1/|5+iγ'-v|²) ≤ 17C_w log q`
(delegated: `ownRepelNW.kMultWeylBound`).
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhK.turanWeighted
import Submission.Work.LinnikAreas.turanPowerSum
import Submission.Work.LinnikAreas.finite_inBox_zeroMult
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_Inputs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_turanPowerIneq
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_zeroSumKMultBound
import Submission.Work.LinnikAreas.DhExplicit.conductor_large_of_lambda_small
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_ownRepelNW_turanPowerStepWeyl
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_explFormula

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The `kMult`-zero set of `ζ_K` inside a ball is finite. -/
private lemma kMult_finite_ball (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (R : ℝ) :
    ({v : ℂ | DhK.kMult ψ v ≠ 0 ∧ ‖v‖ ≤ R} : Set ℂ).Finite := by
  have hΞ : ({v : ℂ | analyticOrderNatAt DhK.Xi v ≠ 0 ∧ ‖v‖ ≤ R} : Set ℂ).Finite := by
    refine (DhK.Xi_divisor_support_finite R).subset ?_
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hmem : v ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv2
    rw [Function.mem_support]
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (DhK.Xi_analyticOnNhd _) hmem]
    exact_mod_cast hv1
  have hL : ({v : ℂ | analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) v ≠ 0 ∧
      ‖v‖ ≤ R} : Set ℂ).Finite := by
    have hsupp : (Function.support (fun u : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ)
          (Metric.closedBall (0 : ℂ) R)) u : ℤ))).Finite := by
      simpa [Function.HasFiniteSupport] using
        (Commons.NumberTheory.Linnik.divisor_finiteSupport ψ hψ (0 : ℂ) R)
    refine hsupp.subset ?_
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hmem : v ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv2
    rw [Function.mem_support]
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (f := DirichletCharacter.completedLFunction ψ)
      (U := Metric.closedBall (0 : ℂ) R) (z := v)
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction hψ).analyticAt z) hmem]
    exact_mod_cast hv1
  refine (hΞ.union hL).subset ?_
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  have hdisj : analyticOrderNatAt DhK.Xi v ≠ 0 ∨
      analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv1 (by simp [DhK.kMult, hcon.1, hcon.2])
  rcases hdisj with h | h
  · exact Or.inl ⟨h, hv2⟩
  · exact Or.inr ⟨h, hv2⟩

/-- The arithmetic core: from the exponential form of the Turán/explicit-formula combination one
gets the logarithmic repulsion. -/
private lemma turan_arith {Cw J0 j β' lam0 lam' L : ℝ} (hCw : 0 < Cw) (hJ0 : 0 < J0)
    (hL : 0 < L) (hj : 1 ≤ j) (hjL : j ≤ J0 * Cw * L) (hlam0 : 0 < lam0) (hb : 0 ≤ 1 - β')
    (hlam' : lam' = (1 - β') * L)
    (hkey : Real.exp (-(2 * j * (1 - β') / 4)) ≤ 36 * j * (lam0 / L)) :
    (1 / (J0 / 2 * Cw)) * (Real.log (1 / lam0) - Real.log (max 1 (36 * J0 * Cw))) ≤ lam' := by
  have hCwne : Cw ≠ 0 := ne_of_gt hCw
  have hJ0pos : 0 < J0 * Cw := by positivity
  have hexp : -(2 * j * (1 - β') / 4) = -(j * (1 - β') / 2) := by ring
  rw [hexp] at hkey
  have hstep : Real.exp (-(J0 * Cw * L * (1 - β') / 2)) ≤ 36 * j * (lam0 / L) := by
    refine le_trans ?_ hkey
    apply Real.exp_le_exp.mpr
    linarith only [mul_le_mul_of_nonneg_right hjL hb]
  have hfacs : 36 * j * (lam0 / L) ≤ 36 * J0 * Cw * lam0 := by
    have hnn : 0 ≤ 36 * (lam0 / L) := by positivity
    have h2a : 36 * j * (lam0 / L) ≤ 36 * (J0 * Cw * L) * (lam0 / L) := by
      linarith only [mul_le_mul_of_nonneg_right hjL hnn]
    have h2b : 36 * (J0 * Cw * L) * (lam0 / L) = 36 * J0 * Cw * lam0 := by
      have hLne : L ≠ 0 := ne_of_gt hL
      field_simp
    linarith only [h2a, h2b.le, h2b.ge]
  have hexp3 : -(J0 * Cw * L * (1 - β') / 2) = -(J0 * Cw / 2) * lam' := by
    rw [hlam']; ring
  have h4 : Real.exp (-(J0 * Cw / 2) * lam') ≤ 36 * J0 * Cw * lam0 := by
    rw [← hexp3]; exact le_trans hstep hfacs
  have h5 : -(J0 * Cw / 2) * lam' ≤ Real.log (36 * J0 * Cw) + Real.log lam0 := by
    have h := Real.log_le_log (Real.exp_pos _) h4
    rw [Real.log_exp, Real.log_mul (by positivity) (ne_of_gt hlam0)] at h
    exact h
  have h6 : (2 / (J0 * Cw)) * (Real.log (1 / lam0) - Real.log (36 * J0 * Cw)) ≤ lam' := by
    have hinv : Real.log (1 / lam0) = -Real.log lam0 := by rw [one_div, Real.log_inv]
    have h7 : (Real.log (1 / lam0) - Real.log (36 * J0 * Cw)) ≤ (J0 * Cw / 2) * lam' := by
      rw [hinv]; linarith only [h5]
    have h11 : (2 / (J0 * Cw)) * ((J0 * Cw / 2) * lam') = lam' := by
      field_simp
    have h12 : 0 ≤ 2 / (J0 * Cw) := by positivity
    calc (2 / (J0 * Cw)) * (Real.log (1 / lam0) - Real.log (36 * J0 * Cw))
        ≤ (2 / (J0 * Cw)) * ((J0 * Cw / 2) * lam') := mul_le_mul_of_nonneg_left h7 h12
      _ = lam' := h11
  have hCf : (1 : ℝ) / (J0 / 2 * Cw) = 2 / (J0 * Cw) := by
    field_simp
  rw [hCf]
  have hmax : Real.log (36 * J0 * Cw) ≤ Real.log (max 1 (36 * J0 * Cw)) :=
    Real.log_le_log (by positivity) (le_max_right _ _)
  have hnn : 0 ≤ 2 / (J0 * Cw) := by positivity
  calc (2 / (J0 * Cw)) * (Real.log (1 / lam0) - Real.log (max 1 (36 * J0 * Cw)))
      ≤ (2 / (J0 * Cw)) * (Real.log (1 / lam0) - Real.log (36 * J0 * Cw)) := by
        apply mul_le_mul_of_nonneg_left _ hnn
        linarith
    _ ≤ lam' := h6

/-- `kMult`-zeros have real part at most `1`. -/
private lemma kMult_eq_zero_of_one_lt_re {ψ : DirichletCharacter ℂ q} {v : ℂ}
    (hv : 1 < v.re) : DhK.kMult ψ v = 0 := by
  have h1 : analyticOrderNatAt DhK.Xi v = 0 := by
    by_contra h
    exact DhK.Xi_ne_zero_of_one_lt_re hv (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
  have h2 : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) v = 0 := by
    by_contra h
    exact Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re ψ hv
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
  simp only [DhK.kMult, h1, h2, Nat.add_zero]

/-- `(m²/(c-v)²)^j = m^{2j}·(1/(c-v))^{2j}`, in `ℂ`. -/
private lemma nw_pow_div (m : ℝ) (c v : ℂ) (j : ℕ) :
    (((m : ℂ) / (c - v)) ^ 2) ^ j = ((m ^ (2 * j) : ℝ) : ℂ) * (1 / (c - v)) ^ (2 * j) := by
  rw [← pow_mul, div_pow, one_div, inv_pow, ← Complex.ofReal_pow]
  ring

/-- **Turán step.**  From the Weyl-sum bound and the differentiated explicit formula for `ζ_K`,
the zero `ρ'` of maximal real part among the zeros of `Λ_ψ` with `|Im| ≤ 1` satisfies the
logarithmic repulsion with absolute constants. -/
private lemma turan_bound (ψ : DirichletCharacter ℂ q) (ρ₀ u : ℂ)
    (L : ℝ) (hLpos : 0 < L)
    (hψ : ψ ≠ 1) (hprim : ψ.IsPrimitive) (hψ2 : ψ ^ 2 = 1) (hρ₀im : ρ₀.im = 0)
    (hzρ₀ : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ₀ ≠ 0)
    (hzu : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u ≠ 0)
    (himu : |u.im| ≤ 1) (hne : u ≠ ρ₀)
    (hρ₀le : 1 - ρ₀.re ≤ 1 / 100) (hule : 1 - u.re ≤ 1 / 100)
    {Cw : ℝ} (hCw : 0 < Cw)
    (hweyl : ∀ {c γ' : ℝ}, 2 ≤ c → c ≤ 10 → |γ'| ≤ 1 →
      Summable (fun v : ℂ => (DhK.kMult ψ v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) ∧
      (∑' v : ℂ, (DhK.kMult ψ v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2)))
          ≤ Cw * L)
    (hdiff : ∀ (j : ℕ), 1 ≤ j → ∀ {c γ' : ℝ}, 5 ≤ c →
      Summable (fun v : ℂ => (DhK.kMult ψ v : ℝ) *
        ((1 / ((c : ℂ) - v) ^ (2 * j)).re
          + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) ∧
      4 * (j : ℝ) * (1 - ρ₀.re) / (c - 1) ^ (2 * j + 1) ≥
        ∑' v : ℂ, (if v = ρ₀ then 0 else (DhK.kMult ψ v : ℝ)) *
          ((1 / ((c : ℂ) - v) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) :
    (1 / (306 / 2 * Cw)) *
      (Real.log (1 / ((1 - ρ₀.re) * L)) - Real.log (max 1 (36 * 306 * Cw)))
      ≤ (1 - u.re) * L := by
  have hzu0 : DirichletCharacter.completedLFunction ψ u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hzu
  have hρ₀0 : DirichletCharacter.completedLFunction ψ ρ₀ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hzρ₀
  have hu_strip := Commons.NumberTheory.Linnik.completedL_zero_strip ψ hψ hprim hzu0
  have hρ₀_strip := Commons.NumberTheory.Linnik.completedL_zero_strip ψ hψ hprim hρ₀0
  have hult : u.re < 1 := hu_strip.2
  have hρ₀lt : ρ₀.re < 1 := hρ₀_strip.2
  have hρ₀decomp : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hρ₀im
  have hfin := kMult_finite_ball ψ hψ (20 : ℝ)
  set U : Finset ℂ := hfin.toFinset with hUdef
  have hUmem : ∀ v : ℂ, v ∈ U ↔ (DhK.kMult ψ v ≠ 0 ∧ ‖v‖ ≤ 20) := by
    intro v
    rw [hUdef, Set.Finite.mem_toFinset]
    rfl
  have hkM_le_one : ∀ v : ℂ, v ∈ U → v.re ≤ 1 := by
    intro v hv
    by_contra hcon
    exact ((hUmem v).mp hv).1 (kMult_eq_zero_of_one_lt_re (not_le.mp hcon))
  have huU : u ∈ U := by
    refine (hUmem u).mpr ⟨?_, ?_⟩
    · intro h0
      simp only [DhK.kMult] at h0
      exact hzu (by omega)
    · have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      have h2 : |u.re| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith only [hu_strip.1], by linarith⟩
      have h3 : |u.im| ≤ 1 := by rwa [abs_le] at himu ⊢
      linarith only [h1, h2, h3]
  have hρ₀U : ρ₀ ∈ U := by
    refine (hUmem ρ₀).mpr ⟨?_, ?_⟩
    · intro h0
      simp only [DhK.kMult] at h0
      exact hzρ₀ (by omega)
    · have h1 : ‖ρ₀‖ ≤ |ρ₀.re| + |ρ₀.im| := Complex.norm_le_abs_re_add_abs_im ρ₀
      have h2 : |ρ₀.re| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith only [hρ₀_strip.1], by linarith⟩
      have h3 : |ρ₀.im| = 0 := by rw [hρ₀im]; norm_num
      linarith only [h1, h2, h3]
  set T : Finset ℂ := U.filter (fun v => |v.im| ≤ 1 ∧
    analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) v ≠ 0 ∧ v ≠ ρ₀) with hTdef
  have huT : u ∈ T := by
    rw [hTdef, Finset.mem_filter]
    exact ⟨huU, himu, hzu, hne⟩
  obtain ⟨ρ', hρ'T, hρ'max⟩ := Finset.exists_max_image T (fun v => v.re) ⟨u, huT⟩
  obtain ⟨hρ'U, hρ'im, hρ'k, hρ'ne⟩ := (Finset.mem_filter.mp hρ'T)
  have hρ'kM : DhK.kMult ψ ρ' ≠ 0 := ((hUmem ρ').mp hρ'U).1
  have hre_le : u.re ≤ ρ'.re := hρ'max u huT
  set β' : ℝ := ρ'.re with hβ'def
  set γ' : ℝ := ρ'.im with hγ'def
  have hβ'lt : β' < 1 := by
    have h0 : DirichletCharacter.completedLFunction ψ (ρ' : ℂ) = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hρ'k
    have := (Commons.NumberTheory.Linnik.completedL_zero_strip ψ hψ hprim h0).2
    rw [hβ'def]; exact this
  have hβ'ge : 1 - 1 / 100 ≤ β' := by linarith only [hule, hre_le]
  have hβ'le1 : β' ≤ 1 := le_of_lt hβ'lt
  have hγ'abs : |γ'| ≤ 1 := hρ'im
  set d : ℂ → ℝ := fun v => min ‖((5 : ℂ) - v)‖ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖
    with hddef
  set S : Finset ℂ := U.filter (fun v => v ≠ ρ₀) with hSdef
  have huS : u ∈ S := by
    rw [hSdef, Finset.mem_filter]; exact ⟨huU, hne⟩
  obtain ⟨v₀, hv₀S, hv₀min⟩ := Finset.exists_min_image S d ⟨u, huS⟩
  obtain ⟨hv₀U, hv₀ne⟩ := Finset.mem_filter.mp hv₀S
  have hv₀k : DhK.kMult ψ v₀ ≠ 0 := ((hUmem v₀).mp hv₀U).1
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
  have hρ'S : ρ' ∈ S := Finset.mem_filter.mpr ⟨hρ'U, hρ'ne⟩
  have hm_le_dρ' : m ≤ d ρ' := by
    rw [hmdef]; exact hv₀min ρ' hρ'S
  have hρ'decomp : ρ' = ((β' : ℝ) : ℂ) + Complex.I * ((γ' : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hβ'def, hγ'def]
    · simp [hβ'def, hγ'def]
  have hnorm2 : ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ')‖ = 5 - β' := by
    have h1 : ((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ') = ((5 - β' : ℝ) : ℂ) := by
      rw [hρ'decomp]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 5 - β')]
  have hdρ'_le : d ρ' ≤ 5 - β' := by
    rw [hddef]
    calc min ‖((5 : ℂ) - ρ')‖ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ')‖
        ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - ρ')‖ := min_le_right _ _
      _ = 5 - β' := hnorm2
  have hm_le_5β' : m ≤ 5 - β' := le_trans hm_le_dρ' hdρ'_le
  have hm_sq_le : m ^ 2 ≤ 17 := by
    have h1 : 5 - β' ≤ 4 + 1 / 100 := by linarith only [hβ'ge]
    have h2 : m ^ 2 ≤ (4 + 1 / 100) ^ 2 := pow_le_pow_left₀ hmnn (le_trans hm_le_5β' h1) 2
    linarith only [h2]
  have hγ6 : ‖((5 : ℂ) + Complex.I * (γ' : ℂ))‖ ≤ 6 := by
    have h1 : ‖((5 : ℂ) + Complex.I * (γ' : ℂ))‖ ≤ ‖((5 : ℂ))‖ + ‖Complex.I * (γ' : ℂ)‖ :=
      norm_add_le _ _
    have h2 : ‖Complex.I * (γ' : ℂ)‖ = |γ'| := by simp
    have h3 : ‖((5 : ℂ))‖ = 5 := by norm_num
    linarith only [h1, h2, h3, hγ'abs]
  have hfar : ∀ v : ℂ, 20 < ‖v‖ →
      m ≤ ‖((5 : ℂ) - v)‖ ∧ m ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ := by
    intro v hv
    have hβ'ge4 : 5 - β' ≤ 4 + 1 / 100 := by linarith only [hβ'ge]
    have h5n : ‖((5 : ℂ))‖ = 5 := by norm_num
    constructor
    · have h := abs_norm_sub_norm_le v (5 : ℂ)
      rw [h5n, abs_le] at h
      have h1 : ‖v‖ - 5 ≤ ‖((5 : ℂ) - v)‖ := by
        rw [norm_sub_rev]
        linarith only [h.2]
      linarith only [h1, hm_le_5β', hβ'ge4, hv]
    · have h := abs_norm_sub_norm_le v ((5 : ℂ) + Complex.I * (γ' : ℂ))
      rw [abs_le] at h
      have h1 : ‖v‖ - 6 ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ := by
        rw [norm_sub_rev]
        linarith only [h.2, hγ6]
      linarith only [h1, hm_le_5β', hβ'ge4, hv]
  -- the weight and the two point families
  set Wt : ℂ → ℝ := fun v => if v = ρ₀ then 0 else (DhK.kMult ψ v : ℝ) with hWtdef
  set Z1 : ℂ → ℂ := fun v => if v = ρ₀ ∨ DhK.kMult ψ v = 0 then 0
    else ((m : ℂ) / ((5 : ℂ) - v)) ^ 2 with hZ1def
  set Z2 : ℂ → ℂ := fun v => if v = ρ₀ ∨ DhK.kMult ψ v = 0 then 0
    else ((m : ℂ) / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v)) ^ 2 with hZ2def
  have hWt_apply : ∀ v : ℂ, Wt v = if v = ρ₀ then 0 else (DhK.kMult ψ v : ℝ) := by
    intro v; rw [hWtdef]
  have hZ1_apply : ∀ v : ℂ, Z1 v = if v = ρ₀ ∨ DhK.kMult ψ v = 0 then 0
      else ((m : ℂ) / ((5 : ℂ) - v)) ^ 2 := by intro v; rw [hZ1def]
  have hZ2_apply : ∀ v : ℂ, Z2 v = if v = ρ₀ ∨ DhK.kMult ψ v = 0 then 0
      else ((m : ℂ) / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v)) ^ 2 := by intro v; rw [hZ2def]
  have hv₀ne' : ¬(v₀ = ρ₀ ∨ DhK.kMult ψ v₀ = 0) := by tauto
  have hm_le_dist1 : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult ψ v ≠ 0 → m ≤ ‖((5 : ℂ) - v)‖ := by
    intro v hv1 hv2
    by_cases hv : ‖v‖ ≤ 20
    · have hvS : v ∈ S := Finset.mem_filter.mpr ⟨(hUmem v).mpr ⟨hv2, hv⟩, hv1⟩
      exact le_trans (by rw [hmdef]; exact hv₀min v hvS) (min_le_left _ _)
    · push_neg at hv
      exact (hfar v hv).1
  have hm_le_dist2 : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult ψ v ≠ 0 →
      m ≤ ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖ := by
    intro v hv1 hv2
    by_cases hv : ‖v‖ ≤ 20
    · have hvS : v ∈ S := Finset.mem_filter.mpr ⟨(hUmem v).mpr ⟨hv2, hv⟩, hv1⟩
      exact le_trans (by rw [hmdef]; exact hv₀min v hvS) (min_le_right _ _)
    · push_neg at hv
      exact (hfar v hv).2
  have hm_div1_le : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult ψ v ≠ 0 → m / ‖((5 : ℂ) - v)‖ ≤ 1 := by
    intro v hv1 hv2
    have hne : (5 : ℂ) - v ≠ 0 := sub_ne_zero.mpr (by
      intro hc; exact hv2 (kMult_eq_zero_of_one_lt_re (by rw [← hc]; norm_num)))
    rw [div_le_one (norm_pos_iff.mpr hne)]
    exact hm_le_dist1 v hv1 hv2
  have hm_div2_le : ∀ v : ℂ, v ≠ ρ₀ → DhK.kMult ψ v ≠ 0 →
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
    by_cases h : v = ρ₀ ∨ DhK.kMult ψ v = 0
    · rw [if_pos h, norm_zero]; exact sq_nonneg (m / ‖((5 : ℂ) - v)‖)
    · rw [if_neg h]
      rw [norm_pow]
      congr 1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmnn]
  have hZ2_bound : ∀ v : ℂ, ‖Z2 v‖ ≤ (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖) ^ 2 := by
    intro v
    rw [hZ2_apply v]
    by_cases h : v = ρ₀ ∨ DhK.kMult ψ v = 0
    · rw [if_pos h, norm_zero]; exact sq_nonneg (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖)
    · rw [if_neg h]
      rw [norm_pow]
      congr 1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmnn]

  have hZ1_norm : ∀ v : ℂ, ‖Z1 v‖ ≤ 1 := by
    intro v
    by_cases hv : v = ρ₀ ∨ DhK.kMult ψ v = 0
    · rw [hZ1_apply v, if_pos hv]; simp only [norm_zero]; norm_num
    · push_neg at hv
      refine le_trans (hZ1_bound v) ?_
      exact pow_le_one₀ (by positivity) (hm_div1_le v hv.1 hv.2)
  have hZ2_norm : ∀ v : ℂ, ‖Z2 v‖ ≤ 1 := by
    intro v
    by_cases hv : v = ρ₀ ∨ DhK.kMult ψ v = 0
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
  set Gmaj : ℂ × Bool → ℝ := fun i => 17 * ((DhK.kMult ψ i.1 : ℝ) *
      (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
        + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) with hGmajdef
  have hGmaj_apply : ∀ i : ℂ × Bool, Gmaj i = 17 * ((DhK.kMult ψ i.1 : ℝ) *
      (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
        + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) := by intro i; rw [hGmajdef]
  have hGmaj_nonneg : ∀ i : ℂ × Bool, 0 ≤ Gmaj i := by
    intro i; rw [hGmaj_apply i]; positivity
  have hptGmaj : ∀ v : ℂ, Gmaj (v, true) + Gmaj (v, false) = 34 * ((DhK.kMult ψ v : ℝ) *
      (1 / ((5 - v.re) ^ 2 + v.im ^ 2) + 1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
    intro v
    simp only [hGmaj_apply, Prod.fst, Prod.snd]
    ring
  have hGmaj_summable : Summable Gmaj := by
    refine (summable_prod_of_nonneg (f := Gmaj) hGmaj_nonneg).mpr ⟨?_, ?_⟩
    · intro v
      exact summable_of_finite_support (Set.toFinite _)
    · have h2 : (fun v : ℂ => ∑' b : Bool, Gmaj (v, b)) = fun v : ℂ => 34 * ((DhK.kMult ψ v : ℝ) *
          (1 / ((5 - v.re) ^ 2 + v.im ^ 2) + 1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
        funext v
        rw [tsum_fintype, Fintype.sum_bool, hptGmaj v]
      rw [h2]
      exact hWsum.mul_left 34
  have hGmaj_tsum : (∑' i : ℂ × Bool, Gmaj i) ≤ 34 * (Cw * L) := by
    have hsplit : (∑' i : ℂ × Bool, Gmaj i)
        = ∑' v : ℂ, 34 * ((DhK.kMult ψ v : ℝ) *
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
  have hm_sq_ker1 : ∀ v : ℂ, (m / ‖((5 : ℂ) - v)‖) ^ 2 ≤ 17 * (1 / ((5 - v.re) ^ 2 + v.im ^ 2)) := by
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
    calc m ^ 2 ≤ 17 := hm_sq_le
      _ = 17 * (1 / ((5 - v.re) ^ 2 + v.im ^ 2)) * ((5 - v.re) ^ 2 + v.im ^ 2) := by
          rw [one_div, mul_assoc, inv_mul_cancel₀ (ne_of_gt hd), mul_one]
  have hm_sq_ker2 : ∀ v : ℂ, (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - v)‖) ^ 2
      ≤ 17 * (1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2)) := by
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
    calc m ^ 2 ≤ 17 := hm_sq_le
      _ = 17 * (1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2)) * ((5 - v.re) ^ 2 + (v.im - γ') ^ 2) := by
          rw [one_div, mul_assoc, inv_mul_cancel₀ (ne_of_gt hd), mul_one]
  have hz_le : ∀ i : ℂ × Bool, ‖zfun i‖ ≤ (m / ‖((5 : ℂ) - i.1)‖) ^ 2
      + (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖) ^ 2 := by
    intro i
    rw [hzfun_apply]
    by_cases hb : i.2
    · rw [if_pos hb]
      linarith only [hZ2_bound i.1, sq_nonneg (m / ‖((5 : ℂ) - i.1)‖)]
    · rw [if_neg hb]
      linarith only [hZ1_bound i.1, sq_nonneg (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖)]
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
      have hk : (0 : ℝ) ≤ (DhK.kMult ψ i.1 : ℝ) := by positivity
      calc (DhK.kMult ψ i.1 : ℝ) * ‖zfun i‖
          ≤ (DhK.kMult ψ i.1 : ℝ) * ((m / ‖((5 : ℂ) - i.1)‖) ^ 2
              + (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖) ^ 2) :=
            mul_le_mul_of_nonneg_left (hz_le i) hk
        _ ≤ 17 * ((DhK.kMult ψ i.1 : ℝ) *
              (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
                + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) := by
            have hA := hm_sq_ker1 i.1
            have hB := hm_sq_ker2 i.1
            nlinarith only [hk, hA, hB]
  have hsum_family : Summable (fun i : ℂ × Bool =>
      wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖))) := by
    refine Summable.of_nonneg_of_le (f := Gmaj) (g := fun i : ℂ × Bool =>
      wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖))) ?_ ?_ hGmaj_summable
    · intro i; positivity
    · exact hfamily_le
  obtain ⟨j, hj1, hj2, hj3⟩ :=
    DhK.turanWeighted 1 (by norm_num) wfun zfun i₀ hwi₀ hw_nonneg hz_i₀_ne hmax hsum_family
  have hMj : (j : ℝ) ≤ 306 * Cw * L := by
    have hMb : (∑' i : ℂ × Bool, wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖)))
        ≤ 34 * (Cw * L) :=
      le_trans (Summable.tsum_le_tsum hfamily_le hsum_family hGmaj_summable) hGmaj_tsum
    have h9 : (j : ℝ) ≤ 9 * (34 * (Cw * L)) := by
      calc (j : ℝ) ≤ (8 + 1) * (∑' i : ℂ × Bool, wfun i * (‖zfun i‖ / (‖zfun i₀‖ + ‖zfun i‖))) := hj2
        _ ≤ 9 * (34 * (Cw * L)) := by linarith only [hMb]
    linarith only [h9]
  -- the sum identity
  set Sfin : ℝ := ∑' v : ℂ, (if v = ρ₀ then 0 else (DhK.kMult ψ v : ℝ)) *
      ((1 / ((5 : ℂ) - v) ^ (2 * j)).re
        + (1 / ((5 : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re) with hSfindef
  have hwz_le : ∀ i : ℂ × Bool, wfun i * ‖zfun i‖ ≤ Gmaj i := by
    intro i
    have hcase : wfun i * ‖zfun i‖ ≤ Gmaj i := by
      rw [hwfun_apply, hWt_apply]
      by_cases hρ : i.1 = ρ₀
      · rw [if_pos hρ]; simp only [zero_mul]; exact hGmaj_nonneg i
      · rw [if_neg hρ, hGmaj_apply i]
        have hk : (0 : ℝ) ≤ (DhK.kMult ψ i.1 : ℝ) := by positivity
        calc (DhK.kMult ψ i.1 : ℝ) * ‖zfun i‖
            ≤ (DhK.kMult ψ i.1 : ℝ) * ((m / ‖((5 : ℂ) - i.1)‖) ^ 2
                + (m / ‖((5 : ℂ) + Complex.I * (γ' : ℂ) - i.1)‖) ^ 2) :=
              mul_le_mul_of_nonneg_left (hz_le i) hk
          _ ≤ 17 * ((DhK.kMult ψ i.1 : ℝ) *
                (1 / ((5 - i.1.re) ^ 2 + i.1.im ^ 2)
                  + 1 / ((5 - i.1.re) ^ 2 + (i.1.im - γ') ^ 2))) := by
              have hA := hm_sq_ker1 i.1
              have hB := hm_sq_ker2 i.1
              nlinarith only [hk, hA, hB]
    exact hcase
  have hhalf : Summable (fun v : ℂ => Gmaj (v, false) + Gmaj (v, true)) := by
    have hpt : (fun v : ℂ => Gmaj (v, false) + Gmaj (v, true)) = fun v : ℂ => 34 * ((DhK.kMult ψ v : ℝ) *
        (1 / ((5 - v.re) ^ 2 + v.im ^ 2) + 1 / ((5 - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
      funext v; rw [add_comm, hptGmaj v]
    rw [hpt]
    exact hWsum.mul_left 34
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
      = m ^ (2 * j) * ((if v = ρ₀ then 0 else (DhK.kMult ψ v : ℝ)) *
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
    · by_cases hk : DhK.kMult ψ v = 0
      · have h1 : wfun (v, false) = 0 := by
          rw [hwfun_apply, hWt_apply, if_neg hv, hk]; norm_num
        rw [h1, if_neg hv, hk]
        simp
      · have hne : ¬(v = ρ₀ ∨ DhK.kMult ψ v = 0) := by tauto
        have hwt : wfun (v, false) = (DhK.kMult ψ v : ℝ) := by
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
      = m ^ (2 * j) * ((if v = ρ₀ then 0 else (DhK.kMult ψ v : ℝ)) *
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
      linarith only [h1]
    have h4 : m ^ (2 * j) ≤ (5 - β') ^ (2 * j) := pow_le_pow_left₀ hmnn hm_le_5β' _
    have h5 : (1 / 36) / (5 - β') ^ (2 * j) ≤ (1 / 36) / m ^ (2 * j) :=
      div_le_div_of_nonneg_left (by norm_num) hmposj h4
    linarith only [h2, h5]
  -- the exponential form fits `turan_arith`
  have hkey : Real.exp (-(2 * (j : ℝ) * (1 - β') / 4))
      ≤ 36 * (j : ℝ) * (((1 - ρ₀.re) * L) / L) := by
    rw [show (((1 - ρ₀.re) * L) / L) = (1 - ρ₀.re) by
      field_simp]
    have h5b : 0 < 5 - β' := by linarith
    have hA : (1 / 36) * 4 ^ (2 * j + 1) ≤ 4 * (j : ℝ) * (1 - ρ₀.re) * (5 - β') ^ (2 * j) := by
      have hpos : 0 < (5 - β') ^ (2 * j) := pow_pos h5b _
      have h2 := (div_le_div_iff₀ hpos (pow_pos (by norm_num : (0 : ℝ) < 4) _)).mp hmain
      linarith only [h2]
    have hB : (4 / (5 - β')) ^ (2 * j) ≤ 36 * (j : ℝ) * (1 - ρ₀.re) := by
      rw [div_pow, div_le_iff₀ (pow_pos h5b _)]
      have h4 : (4 : ℝ) ^ (2 * j) ≤ 36 * (j : ℝ) * (1 - ρ₀.re) * (5 - β') ^ (2 * j) := by
        have hpow : (4 : ℝ) ^ (2 * j + 1) = 4 * 4 ^ (2 * j) := by rw [pow_succ']
        linarith only [hA, hpow]
      linarith only [h4]
    have hlog : Real.log ((5 - β') / 4) ≤ (1 - β') / 4 := by
      have h1 : (5 - β') / 4 = 1 + (1 - β') / 4 := by ring
      rw [h1]
      have ht : 0 < 1 + (1 - β') / 4 := by linarith
      have h2 := Real.log_le_sub_one_of_pos ht
      linarith
    have hexp_le : Real.exp (-(2 * (j : ℝ) * (1 - β') / 4)) ≤ (4 / (5 - β')) ^ (2 * j) := by
      have hy : 0 < 4 / (5 - β') := by positivity
      have h4 : -(2 * (j : ℝ) * (1 - β') / 4) ≤ 2 * (j : ℝ) * Real.log (4 / (5 - β')) := by
        have hlogarg : Real.log (4 / (5 - β')) = -Real.log ((5 - β') / 4) := by
          have h1 : ((5 - β') / 4 : ℝ)⁻¹ = 4 / (5 - β') := inv_div _ _
          rw [← h1, Real.log_inv]
        rw [hlogarg]
        linarith only [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) j)]
      calc Real.exp (-(2 * (j : ℝ) * (1 - β') / 4))
          ≤ Real.exp (2 * (j : ℝ) * Real.log (4 / (5 - β'))) := Real.exp_le_exp.mpr h4
        _ = (4 / (5 - β')) ^ (2 * j) := by
          rw [show 2 * (j : ℝ) * Real.log (4 / (5 - β'))
              = Real.log (4 / (5 - β')) * ((2 * j : ℕ) : ℝ) by push_cast; ring]
          rw [Real.exp_mul, Real.rpow_natCast, Real.exp_log hy]
    exact le_trans hexp_le hB
  have hlam'bd : (1 - β') * L ≤ (1 - u.re) * L :=
    mul_le_mul_of_nonneg_right (by linarith only [hre_le]) hLpos.le
  have hmain2 := turan_arith (Cw := Cw) (J0 := 306) (j := (j : ℝ)) (β' := β')
    (lam0 := (1 - ρ₀.re) * L) (lam' := (1 - β') * L)
    hCw (by norm_num) hLpos (by exact_mod_cast hj1) hMj (by positivity) (by linarith) rfl hkey
  linarith only [hmain2, hlam'bd]

/-! ## The final repulsion theorem

With the Turán route assembled (`DhExplicit.turanPowerIneq`, whose three inputs `MassBound`,
`ExplFormula` and `ConductorLarge` are all available), the remaining step is arithmetic: the power
inequality `(1/36)/(5 - Re ρ)^{2j} ≤ 4j(1 - Re ρ₀)/4^{2j+1}` with `j ≤ κ log q` combines with the
minimality of `ρ₀` (`IsMin1`) into the logarithmic repulsion. -/

/-- The exponential form of the Turán power inequality: from
`(1/36)/(5-β')^{2j} ≤ 4j(1-β₀)/4^{2j+1}` (with `β' ≤ 1`) one gets
`exp(-(2j(1-β')/4)) ≤ 36j(1-β₀)`, the hypothesis of `turan_arith`. -/
private lemma hkey_of_power {j : ℕ} {β' β₀ : ℝ} (hβ' : β' ≤ 1)
    (h : (1 / 36 : ℝ) / (5 - β') ^ (2 * j) ≤ 4 * (j : ℝ) * (1 - β₀) / 4 ^ (2 * j + 1)) :
    Real.exp (-(2 * (j : ℝ) * (1 - β') / 4)) ≤ 36 * (j : ℝ) * (1 - β₀) := by
  have h5b : 0 < 5 - β' := by linarith
  have hA : (1 / 36) * 4 ^ (2 * j + 1) ≤ 4 * (j : ℝ) * (1 - β₀) * (5 - β') ^ (2 * j) := by
    have hpos : 0 < (5 - β') ^ (2 * j) := pow_pos h5b _
    have h2 := (div_le_div_iff₀ hpos (pow_pos (by norm_num : (0 : ℝ) < 4) _)).mp h
    linarith only [h2]
  have hB : (4 / (5 - β')) ^ (2 * j) ≤ 36 * (j : ℝ) * (1 - β₀) := by
    rw [div_pow, div_le_iff₀ (pow_pos h5b _)]
    have h4 : (4 : ℝ) ^ (2 * j) ≤ 36 * (j : ℝ) * (1 - β₀) * (5 - β') ^ (2 * j) := by
      have hpow : (4 : ℝ) ^ (2 * j + 1) = 4 * 4 ^ (2 * j) := by rw [pow_succ']
      linarith only [hA, hpow]
    linarith only [h4]
  have hlog : Real.log ((5 - β') / 4) ≤ (1 - β') / 4 := by
    have h1 : (5 - β') / 4 = 1 + (1 - β') / 4 := by ring
    rw [h1]
    have ht : 0 < 1 + (1 - β') / 4 := by linarith
    have h2 := Real.log_le_sub_one_of_pos ht
    linarith
  have hexp_le : Real.exp (-(2 * (j : ℝ) * (1 - β') / 4)) ≤ (4 / (5 - β')) ^ (2 * j) := by
    have hy : 0 < 4 / (5 - β') := by positivity
    have h4 : -(2 * (j : ℝ) * (1 - β') / 4) ≤ 2 * (j : ℝ) * Real.log (4 / (5 - β')) := by
      have hlogarg : Real.log (4 / (5 - β')) = -Real.log ((5 - β') / 4) := by
        have h1 : ((5 - β') / 4 : ℝ)⁻¹ = 4 / (5 - β') := inv_div _ _
        rw [← h1, Real.log_inv]
      rw [hlogarg]
      linarith only [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) j)]
    calc Real.exp (-(2 * (j : ℝ) * (1 - β') / 4))
        ≤ Real.exp (2 * (j : ℝ) * Real.log (4 / (5 - β'))) := Real.exp_le_exp.mpr h4
      _ = (4 / (5 - β')) ^ (2 * j) := by
        rw [show 2 * (j : ℝ) * Real.log (4 / (5 - β'))
            = Real.log (4 / (5 - β')) * ((2 * j : ℕ) : ℝ) by push_cast; ring]
        rw [Real.exp_mul, Real.rpow_natCast, Real.exp_log hy]
  exact le_trans hexp_le hB

/-- **The window repulsion, given the differentiated explicit formula.** -/
private lemma ownRepel_aux (hExpl : Work.LinnikAreas.DhExplicit.ExplFormula) :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
      Work.LinnikContract.lamOf q u ≤ (1 / 100) * Real.log (q : ℝ) →
      c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨κ, hκpos, qT, hT⟩ :=
    Work.LinnikAreas.DhExplicit.turanPowerIneq
      Work.LinnikAreas.ownRepelNW.massBound_of_zeroSumKMultBound hExpl
      Work.LinnikAreas.DhExplicit.conductor_large_of_lambda_small
  set Λ : ℝ := max 2 (36 * κ) with hΛdef
  have hΛ2 : 2 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := by linarith
  have hlogΛpos : 0 < Real.log Λ := Real.log_pos (by linarith)
  set cE : ℝ := 2 / κ with hcEdef
  have hcEpos : 0 < cE := by rw [hcEdef]; positivity
  set c : ℝ := min (cE / 2) (1 / (2 * Λ ^ 2 * Real.log Λ)) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]; exact lt_min (by positivity) (by positivity)
  have hcle : c ≤ cE / 2 := by rw [hcdef]; exact min_le_left _ _
  have hcle2 : c ≤ 1 / (2 * Λ ^ 2 * Real.log Λ) := by rw [hcdef]; exact min_le_right _ _
  refine ⟨c, hcpos, max qT 16, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him0 h100 u hzu himu hne hule
  haveI : NeZero q := hqne
  have hqT : qT ≤ q := le_trans (le_max_left _ _) hq
  have hq16 : 16 ≤ q := le_trans (le_max_right _ _) hq
  have hq3 : 3 ≤ q := by omega
  have hlogq1 : 1 ≤ Real.log (q : ℝ) := by
    have hM : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have h2 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith only [Real.exp_one_lt_d9]
    exact le_trans h2 (Real.log_le_log (by norm_num) hM)
  have hlogqpos : 0 < Real.log (q : ℝ) := lt_of_lt_of_le zero_lt_one hlogq1
  have hχ0ne : χ₀ ≠ 1 := hmin.1.1
  have hzρ0 : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin.1.2.1
  haveI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  have hstrip0 := DhK.zeroMult_strip χ₀ hχ0ne hzρ0
  have hρ0lt : ρ₀.re < 1 := hstrip0.2
  have hstripu := DhK.zeroMult_strip χ₀ hχ0ne hzu
  have hult : u.re < 1 := hstripu.2
  have hpos0 : 0 < (1 - ρ₀.re) * Real.log (q : ℝ) :=
    mul_pos (by linarith) hlogqpos
  have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := hpos0
  set T : ℝ := Real.log (1 / ((1 - ρ₀.re) * Real.log (q : ℝ))) with hTdef
  have hinv100 : (100 : ℝ) ≤ 1 / ((1 - ρ₀.re) * Real.log (q : ℝ)) := by
    rw [le_div_iff₀ hpos0]
    have h := h100
    rw [Work.LinnikContract.lamOf] at h
    linarith
  have hTge : Real.log 100 ≤ T := by
    rw [hTdef]
    exact Real.log_le_log (by norm_num) hinv100
  have hT4 : (4 : ℝ) ≤ T := by
    have h : (4 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have he : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [he]
      calc (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_d9) 4
        _ ≤ 100 := by norm_num
    linarith
  -- the Turán power inequality at the given zero `u`
  have hu3 : Work.LinnikContract.lamOf q u ≤ (1 / 3) * Real.log (q : ℝ) := by
    rw [Work.LinnikContract.lamOf] at hule ⊢
    linarith only [hule, hlogqpos]
  obtain ⟨j, hj1, hjle, hpow⟩ := hT q hqT χ₀ ρ₀ u hmin hsq him0 h100 hzu hne himu hu3
  have hden : 4 + Work.LinnikContract.lamOf q u / Real.log (q : ℝ) = 5 - u.re := by
    rw [Work.LinnikContract.lamOf, mul_div_cancel_right₀ _ (ne_of_gt hlogqpos)]
    ring
  rw [hden] at hpow
  have hkey : Real.exp (-(2 * (j : ℝ) * (1 - u.re) / 4)) ≤ 36 * (j : ℝ) * (1 - ρ₀.re) :=
    hkey_of_power (by linarith) hpow
  have hjL : (j : ℝ) ≤ 1 * κ * Real.log (q : ℝ) := by simpa using hjle
  have hu1 : 0 ≤ 1 - u.re := by linarith
  have hkey' : Real.exp (-(2 * (j : ℝ) * (1 - u.re) / 4))
      ≤ 36 * (j : ℝ) * (((1 - ρ₀.re) * Real.log (q : ℝ)) / Real.log (q : ℝ)) := by
    rw [mul_div_cancel_right₀ _ (ne_of_gt hlogqpos)]
    exact hkey
  have hmain := turan_arith (Cw := κ) (J0 := 1) (j := (j : ℝ)) (β' := u.re)
    (lam0 := (1 - ρ₀.re) * Real.log (q : ℝ)) (lam' := (1 - u.re) * Real.log (q : ℝ))
    hκpos (by norm_num) hlogqpos (by exact_mod_cast hj1) hjL hpos0 hu1 rfl hkey'
  have hmaxeq : max 1 (36 * (1 : ℝ) * κ) = max 1 (36 * κ) := by ring_nf
  rw [hmaxeq] at hmain
  have hcoef : (1 : ℝ) / (1 / 2 * κ) = cE := by rw [hcEdef]; field_simp
  rw [hcoef] at hmain
  rw [← hTdef] at hmain
  -- `hmain : cE * (T - log (max 1 (36κ))) ≤ λ(u)`
  have hlamu : Work.LinnikContract.lamOf q u = (1 - u.re) * Real.log (q : ℝ) := rfl
  have hmaxle : Real.log (max 1 (36 * κ)) ≤ Real.log Λ := by
    refine Real.log_le_log (by positivity) ?_
    rw [hΛdef]
    exact max_le_max (by norm_num) le_rfl
  have hgoal : c * T ≤ Work.LinnikContract.lamOf q u := by
    rw [hlamu]
    by_cases hcase : 2 * Real.log (max 1 (36 * κ)) ≤ T
    · have h1 : cE * (T - Real.log (max 1 (36 * κ))) ≥ cE * (T / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcEpos)
        linarith
      have h2 : c * T ≤ cE * (T / 2) := by
        have h3 : c * T ≤ (cE / 2) * T := mul_le_mul_of_nonneg_right hcle (by linarith)
        have h4 : (cE / 2) * T = cE * (T / 2) := by ring
        linarith only [h3, h4.le, h4.ge]
      linarith only [hmain, h1, h2]
    · push_neg at hcase
      -- `T` is bounded above, so `λ(ρ₀) = exp (-T) > 1/Λ²`
      have hTb : T < 2 * Real.log Λ := lt_of_lt_of_le hcase (by linarith only [hmaxle])
      have hlam0T : Work.LinnikContract.lamOf q ρ₀ = Real.exp (-T) := by
        rw [Work.LinnikContract.lamOf]
        have hthis : Real.exp T = 1 / ((1 - ρ₀.re) * Real.log (q : ℝ)) := by
          rw [hTdef, Real.exp_log (by positivity : (0:ℝ) < 1 / ((1 - ρ₀.re) * Real.log (q : ℝ)))]
        have h2 : Real.exp (-T) = 1 / Real.exp T := by rw [Real.exp_neg, one_div]
        rw [h2, hthis]
        field_simp
      have hminimal : Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u :=
        hmin.2 χ₀ u ⟨hχ0ne, hzu, himu⟩
      have hbig : 1 / Λ ^ 2 < Work.LinnikContract.lamOf q u := by
        have h2 : Real.exp (-(2 * Real.log Λ)) = 1 / Λ ^ 2 := by
          rw [Real.exp_neg]
          have h3 : Real.exp (2 * Real.log Λ) = Λ ^ 2 := by
            rw [show (2 : ℝ) * Real.log Λ = ((2 : ℕ) : ℝ) * Real.log Λ by norm_num,
              Real.exp_nat_mul, Real.exp_log hΛpos]
          rw [h3, one_div]
        have h4 : Real.exp (-(2 * Real.log Λ)) < Real.exp (-T) := Real.exp_lt_exp.mpr (by linarith)
        rw [h2] at h4
        rw [← hlam0T] at h4
        linarith only [h4, hminimal]
      have hct : c * T ≤ 1 / Λ ^ 2 := by
        have h3 : c * T ≤ c * (2 * Real.log Λ) := mul_le_mul_of_nonneg_left hTb.le hcpos.le
        have h4 : c * (2 * Real.log Λ) ≤ 1 / Λ ^ 2 := by
          have h6 : 0 < 2 * Λ ^ 2 * Real.log Λ := by positivity
          calc c * (2 * Real.log Λ) ≤ (1 / (2 * Λ ^ 2 * Real.log Λ)) * (2 * Real.log Λ) :=
                mul_le_mul_of_nonneg_right hcle2 (by linarith only [hlogΛpos])
            _ = 1 / Λ ^ 2 := by
                field_simp
        linarith only [h3, h4]
      linarith only [hbig, hct, hlamu]
  exact hgoal

/-- **The window half of the same-character Deuring–Heilbronn repulsion** (Heath-Brown (1992),
Principle 1 / the Turán power-sum route of Kadiri–Ng–Wong arXiv:1902.08640 §2).

`ownRepel_aux` above reduces the statement to the differentiated explicit formula; here it is
supplied by `DhExplicit.explFormula_of_diffExplicitIneq` applied to the specialised form
`ownRepelNW.diffExplicitIneq`. -/
theorem ownRepelNearWindow : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
      Work.LinnikContract.lamOf q u ≤ (1 / 100) * Real.log (q : ℝ) →
      c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u :=
  ownRepel_aux Work.LinnikAreas.DhExplicit.explFormula
