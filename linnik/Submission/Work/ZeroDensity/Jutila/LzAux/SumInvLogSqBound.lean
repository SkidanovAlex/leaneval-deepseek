import Mathlib

namespace Work.ZeroDensity.Jutila.LzAux

open MeasureTheory intervalIntegral

/-- Helper: `d/dx log(Q/x) = -1/x` for `Q > 0`, `x > 0`. -/
private lemma hasDerivAt_log_div {Q x : ℝ} (hQ : 0 < Q) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (Q / y)) (-(1 / x)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hQx : Q / x ≠ 0 := div_ne_zero (ne_of_gt hQ) hx0
  have h1 : HasDerivAt (fun y : ℝ => Q / y) (-(Q / x ^ 2)) x := by
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x^2)⁻¹) x := hasDerivAt_inv hx0
    have h2 := hinv.const_mul Q
    have hval : Q * (-(x^2)⁻¹) = -(Q / x ^ 2) := by ring
    have h3 : HasDerivAt (fun y : ℝ => Q / y) (Q * (-(x^2)⁻¹)) x := by
      simpa [div_eq_mul_inv] using h2
    rwa [hval] at h3
  have h4 := h1.log hQx
  have hval2 : (-(Q / x ^ 2)) / (Q / x) = -(1 / x) := by field_simp
  rwa [hval2] at h4

/-- Helper: the derivative of the pointwise product `x ↦ x · (1 + log²(Q/x))` is
`(log(Q/x) - 1)²`, via the chain and product rules. -/
private lemma hasDerivAt_g {Q : ℝ} (hQ : 0 < Q) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (id * fun y : ℝ => 1 + (Real.log (Q / y)) ^ 2)
      ((Real.log (Q / x) - 1) ^ 2) x := by
  have hlog := hasDerivAt_log_div hQ hx
  have hsum1 : HasDerivAt (fun y : ℝ => (Real.log (Q / y)) ^ 2)
      (2 * (Real.log (Q / x)) ^ (2 - 1) * (-(1 / x))) x := hlog.pow 2
  have hsum : HasDerivAt (fun y : ℝ => 1 + (Real.log (Q / y)) ^ 2)
      (0 + 2 * (Real.log (Q / x)) ^ (2 - 1) * (-(1 / x))) x := by
    simpa using hsum1.const_add 1
  have hprod := (hasDerivAt_id x).mul hsum
  have hgoal : (1 : ℝ) * (1 + (Real.log (Q / x)) ^ 2)
      + id x * (0 + 2 * (Real.log (Q / x)) ^ (2 - 1) * (-(1 / x)))
      = (Real.log (Q / x) - 1) ^ 2 := by
    simp only [id_eq]; field_simp; ring
  rw [hgoal] at hprod
  exact hprod

/-- Helper: the real function `x ↦ 1/(x (1 + log²(Q/x)))` is antitone on `[1,Q]` for `Q ≥ 1`.
Its denominator `x(1+log²(Q/x))` has nonnegative derivative `(log(Q/x)-1)²`, hence is monotone,
and `[1,Q] ∋ x ↦ Q/x ≥ 0` maps into `(1,∞)`; inverting a monotone positive function is antitone. -/
lemma antitone_invOneAddLogSq (Q : ℝ) (hQ : 1 ≤ Q) :
    AntitoneOn (fun x : ℝ => 1 / (x * (1 + (Real.log (Q / x)) ^ 2))) (Set.Icc 1 Q) := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hxne : ∀ x ∈ Set.Icc 1 Q, x ≠ 0 := fun x hx =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
  have hne : ∀ x ∈ Set.Icc 1 Q, Q / x ≠ 0 := fun x hx =>
    div_ne_zero (ne_of_gt hQpos) (hxne x hx)
  have hlogcont : ContinuousOn (fun x : ℝ => Real.log (Q / x)) (Set.Icc 1 Q) :=
    ContinuousOn.log (ContinuousOn.div continuousOn_const continuousOn_id hxne) hne
  have hmono' : MonotoneOn (id * fun y : ℝ => 1 + (Real.log (Q / y)) ^ 2) (Set.Icc 1 Q) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 1 Q)
    · exact continuousOn_id.mul (continuousOn_const.add (hlogcont.pow 2))
    · intro x hx
      rw [interior_Icc] at hx
      have hxpos : 0 < x := lt_trans zero_lt_one hx.1
      exact (hasDerivAt_g hQpos hxpos).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxpos : 0 < x := lt_trans zero_lt_one hx.1
      rw [(hasDerivAt_g hQpos hxpos).deriv]
      exact sq_nonneg _
  have hmono : MonotoneOn (fun x : ℝ => x * (1 + (Real.log (Q / x)) ^ 2)) (Set.Icc 1 Q) := by
    have heq : (fun x : ℝ => x * (1 + (Real.log (Q / x)) ^ 2))
        = (id * fun y : ℝ => 1 + (Real.log (Q / y)) ^ 2) := by
      funext x; simp [Pi.mul_apply]
    rw [heq]; exact hmono'
  have hmap : Set.MapsTo (fun x : ℝ => x * (1 + (Real.log (Q / x)) ^ 2))
      (Set.Icc 1 Q) (Set.Ioi 0) := by
    intro x hx
    rw [Set.mem_Ioi]
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have hsq : 0 ≤ (Real.log (Q / x)) ^ 2 := sq_nonneg _
    nlinarith
  have hcomp : AntitoneOn
      ((fun y : ℝ => y⁻¹) ∘ fun x : ℝ => x * (1 + (Real.log (Q / x)) ^ 2))
      (Set.Icc 1 Q) :=
    AntitoneOn.comp_MonotoneOn inv_antitoneOn_Ioi hmono hmap
  convert hcomp using 1
  ext x
  simp [Function.comp, one_div]

/-- Helper: `∫_1^Q 1/(x (1 + log²(Q/x))) dx ≤ 2` for `Q ≥ 1`; the antiderivative
`-arctan(log(Q/x))` gives the value `arctan(log Q) < π/2 < 2`. -/
lemma integral_invOneAddLogSq_le (Q : ℝ) (hQ : 1 ≤ Q) :
    ∫ x in (1 : ℝ)..Q, 1 / (x * (1 + (Real.log (Q / x)) ^ 2)) ≤ 2 := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  set F : ℝ → ℝ := -(fun x : ℝ => Real.arctan (Real.log (Q / x))) with hF
  have hxne : ∀ x ∈ Set.Icc (1 : ℝ) Q, x ≠ 0 := fun x hx =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
  have hne : ∀ x ∈ Set.Icc (1 : ℝ) Q, Q / x ≠ 0 := fun x hx =>
    div_ne_zero (ne_of_gt hQpos) (hxne x hx)
  have hlogcont : ContinuousOn (fun x : ℝ => Real.log (Q / x)) (Set.Icc (1 : ℝ) Q) :=
    ContinuousOn.log (ContinuousOn.div continuousOn_const continuousOn_id hxne) hne
  have hcontF : ContinuousOn F (Set.Icc (1 : ℝ) Q) := by
    rw [hF]
    exact (Real.continuous_arctan.comp_continuousOn hlogcont).neg
  have hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) Q,
      HasDerivAt F (1 / (x * (1 + (Real.log (Q / x)) ^ 2))) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx.1
    have hlog := hasDerivAt_log_div hQpos hxpos
    have harctan : HasDerivAt (fun y : ℝ => Real.arctan (Real.log (Q / y)))
        (1 / (1 + (Real.log (Q / x)) ^ 2) * (-(1 / x))) x := hlog.arctan
    have hneg := harctan.neg
    have hgoal : -(1 / (1 + (Real.log (Q / x)) ^ 2) * (-(1 / x)))
        = 1 / (x * (1 + (Real.log (Q / x)) ^ 2)) := by
      field_simp
    rw [hgoal] at hneg
    rw [hF]
    exact hneg
  have hcontH : ContinuousOn (fun x : ℝ => 1 / (x * (1 + (Real.log (Q / x)) ^ 2)))
      (Set.Icc (1 : ℝ) Q) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul (continuousOn_const.add (hlogcont.pow 2))
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      exact ne_of_gt (by positivity)
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (x * (1 + (Real.log (Q / x)) ^ 2)))
      volume (1 : ℝ) Q :=
    ContinuousOn.intervalIntegrable_of_Icc hQ hcontH
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (1 : ℝ)) (b := Q) (f := F)
    (f' := fun x : ℝ => 1 / (x * (1 + (Real.log (Q / x)) ^ 2))) hQ hcontF hderiv hint
  rw [hftc]
  have hFQ : F Q = 0 := by
    simp only [hF, Pi.neg_apply, div_self (ne_of_gt hQpos), Real.log_one, Real.arctan_zero,
      neg_zero]
  have hF1 : F 1 = -Real.arctan (Real.log Q) := by
    simp only [hF, Pi.neg_apply, div_one]
  rw [hFQ, hF1]
  have hlt := Real.arctan_lt_pi_div_two (Real.log Q)
  have hpi : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
  linarith

/-- The dyadic-type bound `Σ_{q ≤ Q} (1/q)·1/(1 + (log(Q/q))²) ≤ C`, uniformly in `Q ≥ 1`.
Proved by splitting `[1,Q]` into the blocks `(⌊Q/2^{j+1}⌋, ⌊Q/2^j⌋]`; on the `j`-th block `log(Q/q) ≥ j log 2` and `Σ 1/q ≤ log 2`, so the block contributes `≤ log 2/(1+(j log 2)²)` and `Σ_j` converges. -/
theorem SumInvLogSqBound : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q →
    ∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * (1/(1 + (Real.log ((Q:ℝ)/(q:ℝ)))^2)) ≤ C := by
  refine ⟨3, by norm_num, ?_⟩
  intro Q hQ
  set H : ℝ → ℝ := fun x => 1 / (x * (1 + (Real.log ((Q:ℝ) / x)) ^ 2)) with hH
  have hQR : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hanti : AntitoneOn H (Set.Icc 1 (Q:ℝ)) := by
    rw [hH]; exact antitone_invOneAddLogSq (Q:ℝ) hQR
  have hcongr : ∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * (1/(1 + (Real.log ((Q:ℝ)/(q:ℝ)))^2))
      = ∑ q ∈ Finset.Icc 1 Q, H (q:ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    simp only [hH]
    rw [one_div, one_div, one_div, mul_inv]
  rw [hcongr]
  have hIcc : Finset.Icc 1 Q = insert 1 (Finset.Ico 2 (Q+1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  have hsum : ∑ q ∈ Finset.Icc 1 Q, H (q:ℝ)
      = H 1 + ∑ i ∈ Finset.Ico 1 Q, H (((i+1:ℕ)):ℝ) := by
    rw [hIcc, Finset.sum_insert (by simp)]
    congr 1
    · push_cast; rfl
    · rw [← Finset.sum_Ico_add' (fun k : ℕ => H (k:ℝ)) 1 Q 1]
  rw [hsum]
  have hH1 : H 1 ≤ 1 := by
    simp only [hH, div_one, one_mul]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (Real.log (Q:ℝ))]
  have hint : ∑ i ∈ Finset.Ico 1 Q, H (((i+1:ℕ)):ℝ) ≤ ∫ x in (1:ℝ)..(Q:ℝ), H x := by
    have hanti' : AntitoneOn H (Set.Icc ((1:ℕ):ℝ) ((Q:ℕ):ℝ)) := by simpa using hanti
    have h := AntitoneOn.sum_le_integral_Ico (a := 1) (b := Q) (f := H) hQ hanti'
    simpa using h
  have hintb : ∫ x in (1:ℝ)..(Q:ℝ), H x ≤ 2 := by
    rw [hH]; exact integral_invOneAddLogSq_le (Q:ℝ) hQR
  linarith

end Work.ZeroDensity.Jutila.LzAux
