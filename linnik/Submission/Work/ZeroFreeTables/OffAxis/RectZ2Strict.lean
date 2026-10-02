/-
# ZeroFreeTables/OffAxis/RectZ2Strict

**The off-axis `Z2` clause at rectangle height `L`, strict form**: a *real* character
`χ₁` (`χ₁² = 1`) whose non-real zero `ρ₁` is `λ`-minimal in the rectangle `|Im| ≤ L`
(with room `10L`, i.e. `Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁`) satisfies `λ₁ > 0.56`.

This is the strict companion of `Work.ZeroFreeTables.OffAxis.RectC_Z2` (`0.56 ≤ λ₁`);
both are proved by the *same* Heath-Brown §9 computation:

* the Chebyshev expansion (9.15) `(3+10cos θ)²(9+10cos θ)²
  = 14379 + 24480cos θ + 14900cos 2θ + 6000cos 3θ + 1250cos 4θ` evaluated at the unit
  point `χ₁(n)n^{-iγ₁}` gives, at `β₁ = Re ρ₁`,
  `0 ≤ 14379 K(β₁,χ₀) + 24480 K(β₁+iγ₁,χ₁) + 14900 K(β₁+2iγ₁,χ₀) + 6000 K(β₁+3iγ₁,χ₁)
        + 1250 K(β₁+4iγ₁,χ₀)`;
* for `χ₁² = 1` the *even* shifts carry the principal character, and off-axis
  (`|γ₁| > 1`) they sit at height `≥ 2`, so (HB Lemma 5.3) their main term is bounded by
  the decay of the Laplace transform of `f`; they are dropped, leaving HB's order-5
  inequality with `N = 24480 + 6000 = 30480` in place of `46630`:
  `14379 F(-λ₁) - 24480 F(0) + 30480 f(0)(1/8+ε) ≥ 0`;
* finally HB's Lemma 7.5 applied to the Lemma 7.1 test function with `θ = arctan 2`,
  `λ = 14/25` turns this into a numerical contradiction for `λ₁ ≤ 14/25`.

The only difference from `RectC_Z2` is in the last step: the contradiction is run against
the **non-strict** assumption `λ₁ ≤ 14/25`, not `λ₁ < 14/25`.  Every use of `λ₁ < 14/25` in
the argument in fact only needs `λ₁ ≤ 14/25` (monotonicity of `∫ e^{λt} f(t) dt` and
`λ₁ ≤ 1`), so the same contradiction yields the strict conclusion `λ₁ > 0.56`.

A downstream consumer needs a *strict* bound (to open the Table 15 interval `(0.56, 0.58)`
for the real character `χ₁`).  The shifted principal-character bound used below is
`Work.ZeroFreeTables.OffAxis.KsumPrincipalShift`
(`Submission/Work/ZeroFreeTables/OffAxis/KsumPrincipalShift.lean`), the `sorry`-free form of
HB Lemma 5.3 at a shifted point: the version in `OffAxis/Ksum_principal_shift.lean` rests on
the two `sorry` stubs `OffAxis.error_absorb` and `OffAxis.Ksum_eq_re_tsum`, which that module
instead proves in full.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.HB94.HB94Aux
import Submission.Work.ZeroFreeTables.HB94.L52supply_pow
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.lemma5_3
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg
import Submission.Work.ZeroFreeTables.testFn7_1
import Submission.Work.ZeroFreeTables.P9F.arctan_bounds
import Submission.Work.ZeroFreeTables.HB95plus.Main
import Submission.Work.ZeroFreeTables.OffAxis.tf71Fc_decay_strip
import Submission.Work.ZeroFreeTables.OffAxis.KsumPrincipalShift



namespace Work.ZeroFreeTables.OffAxis

set_option maxHeartbeats 4000000

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-! ## Bookkeeping lemmas -/

/-- A zero lying in the `δ`-window of the point `s` lies at height at most `|Im s| + 1`. -/
private lemma abs_im_le_of_window {s u : ℂ} {δ : ℝ} (hδ : δ < 1)
    (h : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) : |u.im| ≤ |s.im| + 1 := by
  have h3 := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
  have h3b : (((1 : ℂ) + (s.im : ℂ) * Complex.I - u)).im = s.im - u.im := by simp
  rw [h3b, abs_sub_comm] at h3
  have h4 : |u.im| ≤ |u.im - s.im| + |s.im| := by
    calc |u.im| = |(u.im - s.im) + s.im| := by ring_nf
      _ ≤ |u.im - s.im| + |s.im| := abs_add_le _ _
  linarith [le_trans h3 h, h4, hδ]

/-- The support of a meromorphic divisor is contained in its domain. -/
private lemma mem_ball_of_divisor_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (h : MeromorphicOn.divisor f U u ≠ 0) : u ∈ U := by
  by_contra hu
  exact h (by rw [MeromorphicOn.divisor_def]; simp [hu])

/-- The divisor of the completed `L`-function detects the zeros counted by `zeroMult`. -/
private lemma zeroMult_ne_zero_of_divisor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {R : ℝ} {u : ℂ}
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0) :
    Work.LinnikContract.zeroMult χ u ≠ 0 := by
  have hu : u ∈ Metric.closedBall (0 : ℂ) R := mem_ball_of_divisor_ne_zero hdiv
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction
      (HB94.primitive_ne_one_aux χ hχ)).analyticAt z
  have hcast : (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) u =
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  intro h0
  apply hdiv
  rw [hcast]
  have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u = 0 := by
    have h := h0
    simpa only [Work.LinnikContract.zeroMult] using h
  rw [hnat]
  norm_num

/-- **The window condition.**  For a `λ`-minimal zero `ρ₁` of `χ₁` in the rectangle `|Im| ≤ L`
(`IsRectMin L χ₁ ρ₁`) and a point `s` of height at most `3L`, every zero `u` of `χ₁` in the
`δ`-window of `s` has `u.re ≤ 1 - λ₁/log q`. -/
private lemma window_le_of_rectMin {q : ℕ} [NeZero q] {L : ℝ} (hL : 1 ≤ L)
    {χ₁ : DirichletCharacter ℂ q} [NeZero χ₁.conductor] {ρ₁ : ℂ} (hR : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁)
    {δ : ℝ} (hδ1 : δ < 1) {s u : ℂ} (hsL : |s.im| ≤ 3 * L)
    (hlogq : 0 < Real.log q)
    (hzm : Work.LinnikContract.zeroMult χ₁ u ≠ 0)
    (hwin : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    u.re ≤ 1 - Work.LinnikContract.lamOf q ρ₁ / Real.log q := by
  have him := abs_im_le_of_window hδ1 hwin
  have h10 : |u.im| ≤ 10 * L := by
    have h1 : |u.im| ≤ 3 * L + 1 := by linarith
    nlinarith
  have hmin := hR.2 χ₁ u ⟨hR.1.1, hzm, h10⟩
  rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at hmin
  have h4 : 1 - ρ₁.re ≤ 1 - u.re := (mul_le_mul_iff_left₀ hlogq).mp hmin
  have h5 : Work.LinnikContract.lamOf q ρ₁ / Real.log q = 1 - ρ₁.re := by
    rw [Work.LinnikContract.lamOf, mul_div_cancel_right₀ _ (ne_of_gt hlogq)]
  linarith [h4, h5]

/-- The window condition in the shape consumed by the `K`-sum lemmas, for a point `s` with
`s.re = ρ₁.re` and `|s.im| ≤ 3L`. -/
private lemma window_condition {q : ℕ} [NeZero q] {L : ℝ} (hL : 1 ≤ L)
    {χ₁ : DirichletCharacter ℂ q} [NeZero χ₁.conductor] {ρ₁ : ℂ}
    (hR : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁)
    (hχ1 : χ₁ ≠ 1) {δ : ℝ} (hδ1 : δ < 1) {s : ℂ} (hsL : |s.im| ≤ 3 * L)
    (hlogq : 0 < Real.log q) (hsre : s.re = ρ₁.re) :
    ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
  intro u hdiv hwin
  have hzm := zeroMult_ne_zero_of_divisor χ₁ hχ1 hdiv
  have h := window_le_of_rectMin hL hR hδ1 hsL hlogq hzm hwin
  have h5 : Work.LinnikContract.lamOf q ρ₁ / Real.log q = 1 - ρ₁.re := by
    rw [Work.LinnikContract.lamOf, mul_div_cancel_right₀ _ (ne_of_gt hlogq)]
  rw [hsre]
  linarith


/-! ## The main theorem -/

theorem RectZ2Strict : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| → χ₁ ^ 2 = 1 →
      (56:ℝ)/100 < Work.LinnikContract.lamOf q ρ₁ := by
  intro L hL
  -- ## the test function of HB Lemma 7.1 with `θ = arctan 2`, `λ = 14/25`
  have hθbounds := Work.ZeroFreeTables.P9F.arctan_of_inv_bounds 2 (by norm_num) 3 (110/100)
    (111/100) (by norm_num) (by norm_num)
  set θ : ℝ := Real.arctan 2 with hθdef
  have hθ_ge : (110:ℝ)/100 ≤ θ := by rw [hθdef]; exact hθbounds.1
  have hθ_le : θ ≤ (111:ℝ)/100 := by rw [hθdef]; exact hθbounds.2
  have hθ0 : 0 < θ := by linarith
  have hθ1 : θ < Real.pi / 2 := by rw [hθdef]; exact Real.arctan_lt_pi_div_two 2
  have htan : Real.tan θ = 2 := by rw [hθdef]; exact Real.tan_arctan 2
  set lam0 : ℝ := 14/25 with hlam0def
  have hlam0pos : 0 < lam0 := by rw [hlam0def]; norm_num
  set f : ℝ → ℝ := tf71f θ lam0 with hfdef
  set x₀ : ℝ := 2 * tf71γ θ lam0 with hx₀def
  have hγpos : 0 < tf71γ θ lam0 := tf71γ_pos hθ0 hθ1 hlam0pos
  have hx₀pos : 0 < x₀ := by rw [hx₀def]; exact tf71_twoγ_pos hθ0 hθ1 hlam0pos
  have hx₀nn : 0 ≤ x₀ := hx₀pos.le
  -- ## the values of `f` and of its Laplace transform
  have hf0val : f 0 = (14:ℝ)/5 * ((7:ℝ)/2 * θ - 3) := by
    rw [hfdef, tf71f_at_zero hθ0 hθ1 hlam0pos, htan, hlam0def]
    norm_num
    ring
  have hf0pos : 0 < f 0 := by rw [hf0val]; linarith
  have hfnn : ∀ t : ℝ, 0 ≤ f t := by
    intro t; rw [hfdef]; exact tf71f_nonneg θ lam0 hθ0 hθ1 hlam0pos t
  have hF0int : (∫ t in (0:ℝ)..x₀, f t) = 10 * (1 - θ/2)^2 := by
    rw [hfdef, hx₀def, tf71f_intervalIntegral θ lam0 hθ0 hθ1 hlam0pos, htan]
    norm_num
    ring
  have hFnegint : (∫ t in (0:ℝ)..x₀, Real.exp (lam0 * t) * f t) = 11 - (15:ℝ)/2 * θ := by
    have hpt : ∀ t : ℝ, Complex.exp (-((((-lam0 : ℝ)) : ℂ) * (t:ℂ))) * ((f t : ℝ):ℂ)
        = ((Real.exp (lam0 * t) * f t : ℝ) : ℂ) := by
      intro t
      have harg : -((((-lam0 : ℝ)) : ℂ) * (t:ℂ)) = ((lam0 * t : ℝ) : ℂ) := by push_cast; ring
      rw [harg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    have hcomplex : (∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((-lam0 : ℝ)) : ℂ) * (t:ℂ))) * ((f t : ℝ):ℂ))
        = ((∫ t in (0:ℝ)..x₀, Real.exp (lam0 * t) * f t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal (f := fun t => Real.exp (lam0 * t) * f t)]
      apply intervalIntegral.integral_congr
      intro t _
      exact hpt t
    have h1 : (tf71Fc θ lam0 ((-lam0 : ℝ) : ℂ)).re = 11 - (15:ℝ)/2 * θ := by
      rw [tf71Fc_neglam_re θ lam0 hθ0 hθ1 hlam0pos, htan]
      norm_num
      ring
    have h2 : tf71Fc θ lam0 ((-lam0 : ℝ) : ℂ)
        = (∫ t in (0:ℝ)..x₀,
            Complex.exp (-((((-lam0 : ℝ)) : ℂ) * (t:ℂ))) * ((f t : ℝ):ℂ)) := by
      simp only [tf71Fc, hx₀def, hfdef]
    rw [h2, hcomplex] at h1
    simpa using h1
  -- ## the analytic inputs
  obtain ⟨B, hB0, hBnd⟩ := tf71f_bound θ lam0 hγpos
  obtain ⟨δ, hδ0, hδ1, qS60, hS60⟩ := Work.ZeroFreeTables.HB94.L52supply_pow
  obtain ⟨Cdec, hCdecpos, hdec⟩ := tf71Fc_decay_strip θ lam0 hθ0 hθ1 hlam0pos
  have hcont : ContinuousOn f (Set.Ici 0) := by rw [hfdef]; exact tf71f_cont θ lam0
  have hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0 := by
    intro t ht
    rw [hfdef]
    refine tf71f_supp hθ0 hθ1 hlam0pos t ?_
    rwa [hx₀def] at ht
  have hdiff : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀) := by
    rw [hfdef, hx₀def]; exact tf71f_diff θ lam0 hγpos
  have hBnd' : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0:ℝ) (2 * tf71γ θ lam0) := by rwa [hx₀def] at ht
    have hgoal : iteratedDeriv 2 f t = iteratedDeriv 2 (tf71f θ lam0) t := by rw [hfdef]
    rw [hgoal]
    exact hBnd t ht'
  have hFc : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ)).re := by
    intro z hz
    have h := tf71Fc_re_nonneg θ lam0 hθ0 hθ1 hlam0pos z hz
    have h2 : tf71Fc θ lam0 z = ∫ t in (0:ℝ)..x₀,
        Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ) := by
      simp only [tf71Fc, hx₀def, hfdef]
    rwa [h2] at h
  have hdec' : ∀ z : ℂ, -(1:ℝ) ≤ z.re → 1 ≤ |z.im| →
      ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ)‖ ≤ Cdec / |z.im| := by
    intro z h1 h2
    have h := hdec z h1 h2
    have h3 : tf71Fc θ lam0 z = ∫ t in (0:ℝ)..x₀,
        Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ) := by
      simp only [tf71Fc, hx₀def, hfdef]
    rwa [h3] at h
  obtain ⟨qP, hP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le x₀ B hx₀pos hB0 hcont hsupp
    hdiff hBnd' (ε := 1/1000) (by norm_num) hf0pos
  obtain ⟨qS, hS⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi x₀ B (1/8) hx₀pos hB0
    hcont hsupp hdiff hBnd' hf0pos hFc (ε := 1/1000000) (by norm_num) hδ0 hδ1
  obtain ⟨qT, hT⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi x₀ B (1/8) hx₀pos hB0
    hcont hsupp hdiff hBnd' hf0pos hFc (ε := 1/1000000) (by norm_num) hδ0 hδ1
  obtain ⟨qSh, hSh⟩ := KsumPrincipalShift x₀ B Cdec hx₀pos hB0 hCdecpos.le hcont hsupp hdiff
    hBnd' hf0pos hdec' (ε := 1/1000) (by norm_num)
  -- ## the threshold
  set Lreq : ℝ := max (4*L) (max 2 (max (14/(25*δ) + 1) (16150*Cdec/495 + 1))) with hLreqdef
  refine ⟨max (max (max qS60 qP) (max qS qT)) (max qSh (Nat.ceil (Real.exp Lreq) + 10)), ?_⟩
  intro q hq hqne χ₁ ρ₁ hR hIm hsq
  haveI : NeZero q := hqne
  -- ## unpacking the thresholds
  have hqS60 : qS60 ≤ q := by
    have h1 : qS60 ≤ max qS60 qP := le_max_left qS60 qP
    have h2 : max qS60 qP ≤ max (max qS60 qP) (max qS qT) :=
      le_max_left (max qS60 qP) (max qS qT)
    have h3 : max (max qS60 qP) (max qS qT)
        ≤ max (max (max qS60 qP) (max qS qT)) (max qSh (Nat.ceil (Real.exp Lreq) + 10)) :=
      le_max_left _ _
    exact le_trans (le_trans (le_trans h1 h2) h3) hq
  have hqP : qP ≤ q := by
    have h1 : qP ≤ max qS60 qP := le_max_right qS60 qP
    have h2 : max qS60 qP ≤ max (max qS60 qP) (max qS qT) :=
      le_max_left (max qS60 qP) (max qS qT)
    have h3 : max (max qS60 qP) (max qS qT)
        ≤ max (max (max qS60 qP) (max qS qT)) (max qSh (Nat.ceil (Real.exp Lreq) + 10)) :=
      le_max_left _ _
    exact le_trans (le_trans (le_trans h1 h2) h3) hq
  have hqS : qS ≤ q := by
    have h1 : qS ≤ max qS qT := le_max_left qS qT
    have h2 : max qS qT ≤ max (max qS60 qP) (max qS qT) :=
      le_max_right (max qS60 qP) (max qS qT)
    have h3 : max (max qS60 qP) (max qS qT)
        ≤ max (max (max qS60 qP) (max qS qT)) (max qSh (Nat.ceil (Real.exp Lreq) + 10)) :=
      le_max_left _ _
    exact le_trans (le_trans (le_trans h1 h2) h3) hq
  have hqT : qT ≤ q := by
    have h1 : qT ≤ max qS qT := le_max_right qS qT
    have h2 : max qS qT ≤ max (max qS60 qP) (max qS qT) :=
      le_max_right (max qS60 qP) (max qS qT)
    have h3 : max (max qS60 qP) (max qS qT)
        ≤ max (max (max qS60 qP) (max qS qT)) (max qSh (Nat.ceil (Real.exp Lreq) + 10)) :=
      le_max_left _ _
    exact le_trans (le_trans (le_trans h1 h2) h3) hq
  have hqSh : qSh ≤ q := by
    have h1 : qSh ≤ max qSh (Nat.ceil (Real.exp Lreq) + 10) :=
      le_max_left qSh (Nat.ceil (Real.exp Lreq) + 10)
    exact le_trans (le_trans h1 (le_max_right _ _)) hq
  have hqceil : Nat.ceil (Real.exp Lreq) + 10 ≤ q := by
    have h1 : Nat.ceil (Real.exp Lreq) + 10
        ≤ max qSh (Nat.ceil (Real.exp Lreq) + 10) :=
      le_max_right qSh (Nat.ceil (Real.exp Lreq) + 10)
    exact le_trans (le_trans h1 (le_max_right _ _)) hq
  have hq10 : 10 ≤ q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hexp_le : Real.exp Lreq ≤ (q : ℝ) := by
    have h1 : Real.exp Lreq ≤ (Nat.ceil (Real.exp Lreq) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp Lreq) + 10 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hqceil
    push_cast at h2
    linarith
  have hLreq_le : Lreq ≤ Real.log q := by
    rw [← Real.log_exp Lreq]
    exact Real.log_le_log (Real.exp_pos Lreq) hexp_le
  have h4L : 4*L ≤ Real.log q := by
    have h : 4*L ≤ Lreq := by rw [hLreqdef]; exact le_max_left _ _
    exact le_trans h hLreq_le
  have h2le : (2:ℝ) ≤ Real.log q := by
    have h : (2:ℝ) ≤ Lreq := by
      rw [hLreqdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans h hLreq_le
  have hδLg : 14/(25*δ) + 1 ≤ Real.log q := by
    have h : 14/(25*δ) + 1 ≤ Lreq := by
      rw [hLreqdef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    exact le_trans h hLreq_le
  have hCLg : 16150*Cdec/495 + 1 ≤ Real.log q := by
    have h : 16150*Cdec/495 + 1 ≤ Lreq := by
      rw [hLreqdef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    exact le_trans h hLreq_le
  -- ## the contradiction
  by_contra hcon
  push_neg at hcon
  have hχ1 : χ₁ ≠ 1 := hR.1.1
  have hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hR.1.2.1
  have hγL : |ρ₁.im| ≤ L := hR.1.2.2
  have hγ1 : 1 < |ρ₁.im| := hIm
  haveI hc1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hstrip : 0 < ρ₁.re ∧ ρ₁.re < 1 := by
    have hzero : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ₁ = 0 := by
      refine apply_eq_zero_of_analyticOrderNatAt_ne_zero ?_
      show Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0
      exact hzm
    exact Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter
      (Work.ZeroFreeTables.HB94.primitive_ne_one_aux χ₁ hχ1)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hzero
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := by
    rw [Work.LinnikContract.lamOf]
    exact mul_nonneg (by linarith [hstrip.2]) hlogq.le
  have hlam1le : Work.LinnikContract.lamOf q ρ₁ ≤ 14/25 := by linarith [hcon]
  have hlamval : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log q := by
    rw [Work.LinnikContract.lamOf, mul_div_cancel_right₀ _ (ne_of_gt hlogq)]
  have hsqrtge : (14:ℝ)/25 ≤ Real.sqrt (Real.log (Real.log q)) := by
    have h3 : Real.log 2 ≤ Real.log (Real.log q) := Real.log_le_log (by norm_num) h2le
    have h4 : ((14:ℝ)/25)^2 ≤ Real.log 2 := by
      have h5 := Real.log_two_gt_d9
      norm_num
      linarith
    have h6 : ((14:ℝ)/25)^2 ≤ Real.log (Real.log q) := by linarith
    calc (14:ℝ)/25 = Real.sqrt (((14:ℝ)/25)^2) :=
          (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (14:ℝ)/25)).symm
      _ ≤ Real.sqrt (Real.log (Real.log q)) := Real.sqrt_le_sqrt h6
  have hβre : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log q)) / Real.log q := by
    have h2 : |ρ₁.re - 1| = 1 - ρ₁.re := by
      have h3 : 0 ≤ 1 - ρ₁.re := by linarith [hstrip.2]
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h2, hlamval]
    exact div_le_div_of_nonneg_right (le_trans hlam1le hsqrtge) hlogq.le
  have hslo : 1 - Real.sqrt (Real.log (Real.log q)) / Real.log q ≤ ρ₁.re := by
    have h1 : -|ρ₁.re - 1| ≤ ρ₁.re - 1 := neg_abs_le _
    linarith [hβre, h1]
  have hχ60 : χ₁ ^ 60 = 1 := by
    rw [show (60:ℕ) = 2 * 30 by norm_num, pow_mul, hsq, one_pow]
  have hL52 : Commons.NumberTheory.Linnik.L52Hyp χ₁ ((1:ℝ)/8) (1/1000000) δ :=
    hS60 q hqS60 χ₁ hχ1 hχ60
  have hpow3 : χ₁ ^ 3 = χ₁ := by
    rw [show (3:ℕ) = 2 + 1 by norm_num, pow_add, hsq, one_mul, pow_one]
  have hpow4 : χ₁ ^ 4 = (1 : DirichletCharacter ℂ q) := by
    rw [show (4:ℕ) = 2 * 2 by norm_num, pow_mul, hsq, one_pow]
  -- ## (k = 0) the unshifted principal term
  have hb0 : Ksum q f (Real.log q)
      ((ρ₁.re : ℂ) + ((((0:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 0)
      ≤ Real.log q * (∫ t in (0:ℝ)..x₀,
          Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
        + f 0 * (1/1000) * Real.log q := by
    have hpt : ((ρ₁.re : ℂ) + ((((0:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) = (ρ₁.re : ℂ) := by simp
    have hpw : χ₁ ^ 0 = (1 : DirichletCharacter ℂ q) := by simp
    rw [hpt, hpw]
    have h := hP (q := q) hqP (β := ρ₁.re) (lam := Work.LinnikContract.lamOf q ρ₁)
      (by rw [Work.LinnikContract.lamOf]; ring) hβre
    rw [← Work.ZeroFreeTables.HB94.Ksum_def_aux] at h
    exact h
  -- ## (k = 1) the `χ₁`-term retaining the zero `ρ₁`
  have hb1 : Ksum q f (Real.log q)
      ((ρ₁.re : ℂ) + ((((1:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 1)
      ≤ -(Real.log q) * (10 * (1 - θ/2)^2) + f 0 * (1/8 + 1/1000000) * Real.log q := by
    have hpt : ((ρ₁.re : ℂ) + ((((1:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) = ρ₁ := by
      rw [one_mul]; exact Complex.re_add_im ρ₁
    have hpw : χ₁ ^ 1 = χ₁ := by simp
    rw [hpt, hpw]
    have hdiv1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₁.im| + 2))) ρ₁ ≠ 0 := by
      have hmem : ρ₁ ∈ Metric.closedBall (0:ℂ) (|ρ₁.im| + 2) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have hre : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hstrip.1]; exact hstrip.2.le
        calc ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
          _ ≤ |ρ₁.im| + 1 := by linarith
          _ ≤ |ρ₁.im| + 2 := by linarith
      exact Work.ZeroFreeTables.HB94.divisor_ne_zero_of_zeroMult_aux χ₁ hχ1 hmem hzm
    have hwin1 : ‖(1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
      have h1 : (1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hstrip.2])]
      rw [hlamval, div_le_iff₀ hlogq]
      have h2 : δ * (14/(25*δ) + 1) ≤ δ * Real.log q := mul_le_mul_of_nonneg_left hδLg hδ0.le
      have h3 : δ * (14/(25*δ) + 1) = 14/25 + δ := by field_simp
      linarith [h2, h3, hδ0]
    have hsL1 : |ρ₁.im| ≤ 3 * L := by linarith [hγL]
    have hzw := window_condition hL hR hχ1 hδ1 (s := ρ₁) hsL1 hlogq rfl
    have hsim1 : |ρ₁.im| ≤ 10 * Real.log q := by linarith [hγL, h4L]
    have h := hS (q := q) hqS χ₁ hχ1 (s := ρ₁) (ρ := ρ₁) hβre hsim1 hslo hL52 hdiv1 hwin1 hzw
    rw [← Work.ZeroFreeTables.HB94.Ksum_def_aux] at h
    have hF0c : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((ρ₁ - ρ₁) * (Real.log q) * (t:ℂ)))) * ((f t : ℝ):ℂ)).re
        = 10 * (1 - θ/2)^2 := by
      have h1 : ∀ t : ℝ,
          Complex.exp (-(((ρ₁ - ρ₁) * (Real.log q) * (t:ℂ)))) * ((f t : ℝ):ℂ)
            = ((f t : ℝ):ℂ) := by
        intro t; rw [sub_self, zero_mul, zero_mul, neg_zero, Complex.exp_zero, one_mul]
      rw [intervalIntegral.integral_congr (fun t _ => h1 t),
        intervalIntegral.integral_ofReal, Complex.ofReal_re]
      exact hF0int
    rw [hF0c] at h
    exact h
  -- ## (k = 2) the shifted principal term
  have hb2 : Ksum q f (Real.log q)
      ((ρ₁.re : ℂ) + ((((2:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 2)
      ≤ f 0 * (1/1000) * Real.log q + Cdec := by
    rw [hsq]
    have hτabs : |(2:ℝ) * ρ₁.im| ≤ Real.log q := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith [hγL, h4L]
    have hτ1 : 1 ≤ |(2:ℝ) * ρ₁.im| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith [hγ1]
    have hlam_le : Real.log q * (1 - ρ₁.re) ≤ 1 := by
      rw [show Real.log q * (1 - ρ₁.re) = Work.LinnikContract.lamOf q ρ₁ by
        rw [Work.LinnikContract.lamOf]; ring]
      linarith [hlam1le]
    exact hSh (q := q) hqSh (β := ρ₁.re) (τ := (2:ℝ) * ρ₁.im) hβre hlam_le hτabs hτ1
  -- ## (k = 3) the `χ₁`-term with an empty window
  have hb3 : Ksum q f (Real.log q)
      ((ρ₁.re : ℂ) + ((((3:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 3)
      ≤ f 0 * (1/8 + 1/1000000) * Real.log q := by
    rw [hpow3]
    set s3 : ℂ := (ρ₁.re : ℂ) + ((((3:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I with hs3def
    have hs3re : s3.re = ρ₁.re := by rw [hs3def]; simp
    have hs3im : s3.im = 3 * ρ₁.im := by rw [hs3def]; simp
    have hsL3 : |s3.im| ≤ 3 * L := by
      rw [hs3im, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
      linarith [hγL]
    have hsim3 : |s3.im| ≤ 10 * Real.log q := by
      have h1 : |s3.im| ≤ 3 * L := hsL3
      linarith [h4L]
    have hzw := window_condition hL hR hχ1 hδ1 (s := s3) hsL3 hlogq hs3re
    have h := hT (q := q) hqT χ₁ hχ1 (s := s3) (by rw [hs3re]; exact hβre)
      (by rw [hs3im] at hsim3 ⊢; exact hsim3) (by rw [hs3re]; exact hslo) hL52 hzw
    rw [← Work.ZeroFreeTables.HB94.Ksum_def_aux] at h
    exact h
  -- ## (k = 4) the shifted principal term
  have hb4 : Ksum q f (Real.log q)
      ((ρ₁.re : ℂ) + ((((4:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 4)
      ≤ f 0 * (1/1000) * Real.log q + Cdec := by
    rw [hpow4]
    have hτabs : |(4:ℝ) * ρ₁.im| ≤ Real.log q := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
      linarith [hγL, h4L]
    have hτ1 : 1 ≤ |(4:ℝ) * ρ₁.im| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
      linarith [hγ1]
    have hlam_le : Real.log q * (1 - ρ₁.re) ≤ 1 := by
      rw [show Real.log q * (1 - ρ₁.re) = Work.LinnikContract.lamOf q ρ₁ by
        rw [Work.LinnikContract.lamOf]; ring]
      linarith [hlam1le]
    exact hSh (q := q) hqSh (β := ρ₁.re) (τ := (4:ℝ) * ρ₁.im) hβre hlam_le hτabs hτ1
  -- ## the (9.16) combination
  have hcomb := Work.ZeroFreeTables.ksum_trigPoly_nonneg (q := q) (f := f) hfnn
    (x₀ := x₀) (L := Real.log q) (β := ρ₁.re) (γ := ρ₁.im) hlogq hx₀nn hsupp
    (c := Work.ZeroFreeTables.c95) (d := 4) Work.ZeroFreeTables.c95_hP χ₁
  have hexp : (∑ k ∈ Finset.range 5, Work.ZeroFreeTables.c95 k *
        Ksum q f (Real.log q) ((ρ₁.re : ℂ) + (((k:ℝ) * ρ₁.im : ℝ) : ℂ) * Complex.I) (χ₁ ^ k))
      = 14379 * Ksum q f (Real.log q)
          ((ρ₁.re : ℂ) + ((((0:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 0)
        + 24480 * Ksum q f (Real.log q)
          ((ρ₁.re : ℂ) + ((((1:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 1)
        + 14900 * Ksum q f (Real.log q)
          ((ρ₁.re : ℂ) + ((((2:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 2)
        + 6000 * Ksum q f (Real.log q)
          ((ρ₁.re : ℂ) + ((((3:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 3)
        + 1250 * Ksum q f (Real.log q)
          ((ρ₁.re : ℂ) + ((((4:ℝ) * ρ₁.im : ℝ)) : ℂ) * Complex.I) (χ₁ ^ 4) := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Work.ZeroFreeTables.c95]
  have hK0 := mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 14379)
  have hK1 := mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 24480)
  have hK2 := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 14900)
  have hK3 := mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 6000)
  have hK4 := mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 1250)
  have hcomb' : 0 ≤ ∑ k ∈ Finset.range 5, Work.ZeroFreeTables.c95 k *
      Ksum q f (Real.log q) ((ρ₁.re : ℂ) + (((k:ℝ) * ρ₁.im : ℝ) : ℂ) * Complex.I) (χ₁ ^ k) := by
    simpa only [Complex.ofReal_mul] using hcomb
  have hsum1 : (∑ k ∈ Finset.range 5, Work.ZeroFreeTables.c95 k *
        Ksum q f (Real.log q) ((ρ₁.re : ℂ) + (((k:ℝ) * ρ₁.im : ℝ) : ℂ) * Complex.I) (χ₁ ^ k))
      ≤ 14379 * (Real.log q * (∫ t in (0:ℝ)..x₀,
            Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
          + f 0 * (1/1000) * Real.log q)
        + 24480 * (-(Real.log q) * (10 * (1 - θ/2)^2) + f 0 * (1/8 + 1/1000000) * Real.log q)
        + 14900 * (f 0 * (1/1000) * Real.log q + Cdec)
        + 6000 * (f 0 * (1/8 + 1/1000000) * Real.log q)
        + 1250 * (f 0 * (1/1000) * Real.log q + Cdec) := by
    rw [hexp]
    linarith [hK0, hK1, hK2, hK3, hK4]
  -- ## the monotonicity of the principal term and the numeric core
  have hA_le : (∫ t in (0:ℝ)..x₀, Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
      ≤ (∫ t in (0:ℝ)..x₀, Real.exp (lam0 * t) * f t) := by
    have hint1 : IntervalIntegrable
        (fun t : ℝ => Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t) MeasureTheory.volume
        (0:ℝ) x₀ :=
      ContinuousOn.intervalIntegrable_of_Icc hx₀nn
        (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
          (hcont.mono (fun t ht => ht.1)))
    have hint2 : IntervalIntegrable (fun t : ℝ => Real.exp (lam0 * t) * f t) MeasureTheory.volume
        (0:ℝ) x₀ :=
      ContinuousOn.intervalIntegrable_of_Icc hx₀nn
        (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
          (hcont.mono (fun t ht => ht.1)))
    exact intervalIntegral.integral_mono_on hx₀nn hint1 hint2
      (fun t ht => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlam1le ht.1)) (hfnn t))
  have hA_le' : (∫ t in (0:ℝ)..x₀, Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
      ≤ 11 - (15:ℝ)/2 * θ := le_trans hA_le hFnegint.le
  have hPhi : 14379 * (11 - (15:ℝ)/2 * θ) - 24480 * (10 * (1 - θ/2)^2)
      + 30480 * f 0 * (1/8 + 1/1000000) + 30529 * f 0 * (1/1000) ≤ -495 := by
    rw [hf0val]
    have h1 : 14379 * (11 - (15:ℝ)/2 * θ) - 24480 * (10 * (1 - θ/2)^2)
        + 30480 * ((14:ℝ)/5 * ((7:ℝ)/2 * θ - 3)) * (1/8 + 1/1000000)
        + 30529 * ((14:ℝ)/5 * ((7:ℝ)/2 * θ - 3)) * (1/1000)
        ≤ 14379 * (11 - (15:ℝ)/2 * ((111:ℝ)/100)) - 24480 * (10 * (1 - ((111:ℝ)/100)/2)^2)
        + 30480 * ((14:ℝ)/5 * ((7:ℝ)/2 * ((111:ℝ)/100) - 3)) * (1/8 + 1/1000000)
        + 30529 * ((14:ℝ)/5 * ((7:ℝ)/2 * ((111:ℝ)/100) - 3)) * (1/1000) := by
      nlinarith only [hθ_ge, hθ_le, sq_nonneg (θ - 111/100),
        mul_nonneg (sub_nonneg.mpr hθ_ge) (sub_nonneg.mpr hθ_le)]
    have h2 : 14379 * (11 - (15:ℝ)/2 * ((111:ℝ)/100)) - 24480 * (10 * (1 - ((111:ℝ)/100)/2)^2)
        + 30480 * ((14:ℝ)/5 * ((7:ℝ)/2 * ((111:ℝ)/100) - 3)) * (1/8 + 1/1000000)
        + 30529 * ((14:ℝ)/5 * ((7:ℝ)/2 * ((111:ℝ)/100) - 3)) * (1/1000) ≤ -495 := by norm_num
    linarith [h1, h2]
  have hcombine : 14379 * (Real.log q * (∫ t in (0:ℝ)..x₀,
          Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
        + f 0 * (1/1000) * Real.log q)
      + 24480 * (-(Real.log q) * (10 * (1 - θ/2)^2) + f 0 * (1/8 + 1/1000000) * Real.log q)
      + 14900 * (f 0 * (1/1000) * Real.log q + Cdec)
      + 6000 * (f 0 * (1/8 + 1/1000000) * Real.log q)
      + 1250 * (f 0 * (1/1000) * Real.log q + Cdec)
      = Real.log q * (14379 * (∫ t in (0:ℝ)..x₀,
            Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
          - 24480 * (10 * (1 - θ/2)^2) + 30480 * f 0 * (1/8 + 1/1000000)
          + 30529 * f 0 * (1/1000)) + 16150 * Cdec := by ring
  have hX : 14379 * (∫ t in (0:ℝ)..x₀, Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
        - 24480 * (10 * (1 - θ/2)^2) + 30480 * f 0 * (1/8 + 1/1000000) + 30529 * f 0 * (1/1000)
      ≤ 14379 * (11 - (15:ℝ)/2 * θ) - 24480 * (10 * (1 - θ/2)^2)
        + 30480 * f 0 * (1/8 + 1/1000000) + 30529 * f 0 * (1/1000) := by
    linarith only [hA_le']
  have hstep1 : 0 ≤ Real.log q * (14379 * (∫ t in (0:ℝ)..x₀,
          Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
        - 24480 * (10 * (1 - θ/2)^2) + 30480 * f 0 * (1/8 + 1/1000000) + 30529 * f 0 * (1/1000))
      + 16150 * Cdec := by
    rw [← hcombine]
    exact le_trans hcomb' hsum1
  have hstep2 : Real.log q * (14379 * (∫ t in (0:ℝ)..x₀,
          Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
        - 24480 * (10 * (1 - θ/2)^2) + 30480 * f 0 * (1/8 + 1/1000000) + 30529 * f 0 * (1/1000))
      + 16150 * Cdec
      ≤ Real.log q * (14379 * (11 - (15:ℝ)/2 * θ) - 24480 * (10 * (1 - θ/2)^2)
        + 30480 * f 0 * (1/8 + 1/1000000) + 30529 * f 0 * (1/1000)) + 16150 * Cdec :=
    add_le_add (mul_le_mul_of_nonneg_left hX hlogq.le) le_rfl
  have hstep3 : Real.log q * (14379 * (11 - (15:ℝ)/2 * θ) - 24480 * (10 * (1 - θ/2)^2)
        + 30480 * f 0 * (1/8 + 1/1000000) + 30529 * f 0 * (1/1000)) + 16150 * Cdec
      ≤ Real.log q * (-495) + 16150 * Cdec :=
    add_le_add (mul_le_mul_of_nonneg_left hPhi hlogq.le) le_rfl
  have hfin : 0 ≤ Real.log q * (-495) + 16150 * Cdec := le_trans hstep1 (le_trans hstep2 hstep3)
  have hthr : 16150 * Cdec < 495 * Real.log q := by linarith only [hCLg]
  linarith

end

end Work.ZeroFreeTables.OffAxis
