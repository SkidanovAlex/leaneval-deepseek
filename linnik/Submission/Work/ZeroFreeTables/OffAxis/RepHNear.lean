/-
# ZeroFreeTables/OffAxis/RepHNear

`Work.ZeroFreeTables.Rep9.nearSumDoubleH`: the **aligned double zero** contributes `2·P₃(1)` to
the near sum at the point `σ + i·Im ρ₁` (`σ = 1 + a/log q`), for the height-`H` numbering
`IsMinWideAt H W χ₁ ρ₁` with room `H + 2 ≤ W`.

This is the height-parametric form of the first conjunct of `Rep9.nearSum_bounds`; the proof is
that of `Submission/Work/ZeroFreeTables/Rep9/nearSum_bounds.lean` (lines 299–420), with
`IsMin1WideAt 10` + `IsZ` replaced by `IsMinWideAt H W`, the window bound `|u.im| ≤ 10` of the
near summands replaced by `|u.im| ≤ W` (from `|u.im| ≤ |s.im| + δ ≤ H + 1 < H + 2 ≤ W`), and
`0 ≤ λ(ρ₁)` derived from `zeroMult χ₁ ρ₁ ≠ 0` instead of from `IsZ`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.ZeroFreeTables.Rep9.nearSum_bounds
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.LinnikAreas.boxMaxZero

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Rep9

open Work.ZeroFreeTables Work.LinnikContract

/-! ## A copy of a private helper of `Rep9.nearSum_bounds` -/

private lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
  exact hχ h2.symm

/-! ## The near summands at height `H` -/

private lemma sub_mul_log_eq {q : ℕ} [NeZero q] {a : ℝ} (hq : 2 ≤ q) {s u : ℂ}
    (hs : s.re = 1 + a / Real.log (q : ℝ)) :
    (s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ) =
      ((a + Work.LinnikContract.lamOf q u : ℝ) : ℂ)
        + ((Real.log (q : ℝ) * (s.im - u.im) : ℝ) : ℂ) * Complex.I := by
  have hL : Real.log (q : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < q)))
  have h1 : ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)).re
      = a + Work.LinnikContract.lamOf q u := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_im, zero_mul]
    rw [Work.LinnikContract.lamOf, hs]
    field_simp
    ring
  have h2 : ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)).im
      = Real.log (q : ℝ) * (s.im - u.im) := by
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  apply Complex.ext
  · rw [h1]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
    ring
  · rw [h2]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    ring

/-- HB (4.11) in the shape needed by the near sum: if `Re s = 1 + a/log q`, `0 < a + λ₁` and
`λ₁ ≤ λ(u)` then `Re P₃((a+λ₁)/((s-u)·log q)) ≥ 0`. -/
private lemma P3_sub_mul_log_nonneg {q : ℕ} [NeZero q] {a lam : ℝ} {s u : ℂ} (hq : 2 ≤ q)
    (hs : s.re = 1 + a / Real.log (q : ℝ)) (hα : 0 < a + lam)
    (hβ : a + lam ≤ a + Work.LinnikContract.lamOf q u) :
    0 ≤ (Work.ZeroFreeTables.P3
      (((a : ℂ) + ((lam : ℝ) : ℂ))
        / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re := by
  rw [sub_mul_log_eq hq hs]
  have hnum : ((a : ℂ) + ((lam : ℝ) : ℂ)) = (((a + lam : ℝ)) : ℂ) := by push_cast; ring
  rw [hnum]
  exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) (a + Work.LinnikContract.lamOf q u)
    (Real.log (q : ℝ) * (s.im - u.im)) hα hβ

/-- The divisor of the completed `L`-function at level `q`, computed as the vanishing order
(and `0` outside the ball on which the divisor is taken). -/

private lemma pdiv_eq_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s u : ℂ) :
    Work.ZeroFreeTables.pdiv q χ s u
      = if u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
          then (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) else 0 := by
  rw [Work.ZeroFreeTables.pdiv]
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
  · rw [if_pos hu]
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hu]
    simp only [analyticOrderNatAt]
    cases h : analyticOrderAt (DirichletCharacter.completedLFunction χ) u with
    | top => simp
    | coe n => simp
  · rw [if_neg hu, MeromorphicOn.divisor_def]
    simp [hu]

/-- **Every summand of the near sum is non-negative.**  This is HB's §9 step "drop the far
zeros": a near zero `u` (within `δ < 1` of `1 + i·Im s`) has `λ(u) ≥ λ₁` by the wide minimality
of `ρ₁` — so its multiplicity is a genuine `zeroMult` zero (`pdiv` counts the complete
`L`-function at the level `q`, `zeroMult` that of the primitive character) — whence
`Re P₃(α/((s-u)𝓛)) ≥ 0` by HB (4.11). -/

private lemma nearSum_term_nonneg_H {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    {H W a δ : ℝ} (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁)
    (hW : H + 2 ≤ W) (hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁)
    (ha : 0 < a) (hδ1 : δ < 1)
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {s u : ℂ} (hγ : |s.im| ≤ H)
    (hs : s.re = 1 + a / Real.log (q : ℝ)) :
    0 ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) *
      (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
        then (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁) / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        else 0) := by
  by_cases hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hnear]
    by_cases hdiv : Work.ZeroFreeTables.pdiv q ψ s u = 0
    · rw [hdiv]; simp
    · have hre : |1 - u.re| ≤ δ := by
        have h1 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by simp
        rw [← h1]
        exact le_trans (Complex.abs_re_le_norm _) hnear
      have him : |s.im - u.im| ≤ δ := by
        have h1 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
        rw [← h1]
        exact le_trans (Complex.abs_im_le_norm _) hnear
      have hu0 : 0 < u.re := by
        have h2 := abs_le.mp hre
        linarith [h2.1, hδ1]
      have huW : |u.im| ≤ W := by
        have h2 := abs_le.mp him
        have h3 := abs_le.mp hγ
        rw [abs_le]
        constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, hδ1, hW]
      have hball : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
        by_contra hb
        exact hdiv (by rw [pdiv_eq_order ψ hψ s u, if_neg hb])
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u ≠ 0 := by
        intro h0
        exact hdiv (by rw [pdiv_eq_order ψ hψ s u, if_pos hball, h0]; rfl)
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        zeroMult_ne_zero_of_completedLFunction_eq_zero ψ hψ hu0
          (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have hlam : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
        hmin.2.2.2 ψ u hψ hzm huW
      have hdivnn : (0 : ℝ) ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) := by
        rw [pdiv_eq_order ψ hψ s u, if_pos hball]
        positivity
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁)
            / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re :=
        P3_sub_mul_log_nonneg hq hs (by linarith) (by linarith)
      exact mul_nonneg hdivnn hP3
  · rw [if_neg hnear]
    simp


theorem nearSumDoubleH {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) {H W a δ : ℝ}
    (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁)
    (hW : H + 2 ≤ W) (hmult : 2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁)
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδL : Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ) :
    (2 : ℝ) * Work.ZeroFreeTables.P3R 1 ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q:ℝ)) χ₁
        ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a
        (Work.LinnikContract.lamOf q ρ₁) δ := by
  have hχ₁ : χ₁ ≠ 1 := hmin.1
  have hγ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := by
    have hre : ρ₁.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hmin.2.1
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
    rw [Work.LinnikContract.lamOf]
    exact mul_nonneg (by linarith) hlog
  -- `ρ₁` lies in the open critical strip
  have hstrip : 0 < ρ₁.re ∧ ρ₁.re < 1 := by
    haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    refine Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter
      (primitiveCharacter_ne_one hχ₁)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) ?_
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by
      simpa only [Work.LinnikContract.zeroMult] using hmin.2.1)
  -- ### the double zero `ρ₁` contributes `2*P3R 1`
  set s : ℂ := (((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I
    with hsdef
  have hsr : s.re = 1 + a / Real.log (q : ℝ) := by
    rw [hsdef]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hsi : s.im = ρ₁.im := by
    rw [hsdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  set f : ℂ → ℝ := fun u => ((Work.ZeroFreeTables.pdiv q χ₁ s u : ℤ) : ℝ) *
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
      (Work.ZeroFreeTables.P3
        ((a + Work.LinnikContract.lamOf q ρ₁)
          / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
      else 0) with hfdef
  have hterm_nonneg : ∀ u : ℂ, 0 ≤ f u := by
    intro u
    simp only [hfdef]
    exact nearSum_term_nonneg_H χ₁ ρ₁ hq hmin hW hlamnn ha hδ1 hχ₁
      (by rw [hsi]; exact hγ) hsr
  have hfinDiv : Function.HasFiniteSupport (Work.ZeroFreeTables.pdiv q χ₁ s) := by
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ₁).analyticAt z
    have hd : Function.HasFiniteSupport (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u) := by
      simpa only [Function.HasFiniteSupport] using
        (MeromorphicOn.divisor_support_finite_of_subset
          (f := DirichletCharacter.completedLFunction χ₁)
          (U := Metric.closedBall (0 : ℂ) (|s.im| + 2))
          (V := Metric.closedBall (0 : ℂ) (|s.im| + 2))
          hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _))
    exact hd
  have hfin : Function.HasFiniteSupport f := hfinDiv.subset (fun u hu => by
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by simp only [hfdef, h0]; simp))
  -- `ρ₁` lies in the ball and in the near window
  have hρ1ball : ρ₁ ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, hsi]
    calc ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
      _ ≤ 1 + |ρ₁.im| := by
          have h1 : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hstrip.1]; linarith [hstrip.2]
          linarith
      _ ≤ |ρ₁.im| + 2 := by linarith [abs_nonneg ρ₁.im]
  have hif : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
    have hz : (1 : ℂ) + (s.im : ℂ) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hsi]
    rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hstrip.2])]
    have h1 : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) := by
      have hLne : Real.log (q : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < q)))
      rw [Work.LinnikContract.lamOf]
      simp [hLne]
    rw [h1]; exact hδL
  have hdivρ1 : (2 : ℤ) ≤ Work.ZeroFreeTables.pdiv q χ₁ s ρ₁ := by
    rw [pdiv_eq_order χ₁ hχ₁ s ρ₁, if_pos hρ1ball,
      ← zeroMult_eq_analyticOrderNatAt_of_re_pos_of_re_lt_one χ₁ hχ₁ hstrip.1 hstrip.2]
    exact_mod_cast hmult
  have harg : ((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
      / ((s - ρ₁) * ((Real.log (q : ℝ) : ℝ) : ℂ)) = 1 := by
    have hnum : ((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
        = ((a + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) := by push_cast; ring
    have h1 : (s - ρ₁) * ((Real.log (q : ℝ) : ℝ) : ℂ)
        = ((a + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) := by
      rw [sub_mul_log_eq hq hsr]
      have h2 : s.im - ρ₁.im = 0 := by rw [hsi]; ring
      rw [h2]; simp
    rw [hnum, h1]
    exact div_self (by
      have hpos : (0 : ℝ) < a + Work.LinnikContract.lamOf q ρ₁ := by linarith
      exact_mod_cast ne_of_gt hpos)
  have hP3one : (Work.ZeroFreeTables.P3 1).re = Work.ZeroFreeTables.P3R 1 := by
    norm_num [Work.ZeroFreeTables.P3, Work.ZeroFreeTables.P3R]
  have hterm : (2 : ℝ) * Work.ZeroFreeTables.P3R 1 ≤ f ρ₁ := by
    simp only [hfdef, if_pos hif, harg, hP3one]
    have h2 : (2 : ℝ) ≤ ((Work.ZeroFreeTables.pdiv q χ₁ s ρ₁ : ℤ) : ℝ) := by
      exact_mod_cast hdivρ1
    have h3 : 0 < Work.ZeroFreeTables.P3R 1 := by
      norm_num [Work.ZeroFreeTables.P3R]
    nlinarith
  have hmem : ρ₁ ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset hfin, Function.mem_support]
    have h3 : 0 < Work.ZeroFreeTables.P3R 1 := by norm_num [Work.ZeroFreeTables.P3R]
    intro h0
    have h' := hterm
    rw [h0] at h'
    nlinarith
  have hsingle : f ρ₁ ≤ ∑ u ∈ hfin.toFinset, f u :=
    Finset.single_le_sum (fun u _ => hterm_nonneg u) hmem
  have hPNS : Work.ZeroFreeTables.P3NearSumL q (Real.log (q : ℝ)) χ₁ s a
      (Work.LinnikContract.lamOf q ρ₁) δ = ∑ᶠ u : ℂ, f u := by
    rw [Work.ZeroFreeTables.P3NearSumL]
  rw [hPNS, finsum_eq_sum f hfin]
  exact le_trans hterm hsingle

end Work.ZeroFreeTables.Rep9
