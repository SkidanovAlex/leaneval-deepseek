/-
# `OffAxis/RectRepCaseCNear`

The **case C near branch** of the repeated-zero `P₃` engine at rectangle height `H`
(HB §9, `χ₁² = 1`, `ρ₁` a multiple zero, `ρ̄₁` inside the near window of `1 + i·Im ρ₁`):
the two aligned zeros `ρ₁`, `ρ̄₁` contribute `2·P₃(1) + 2·Re P₃(α/(α + 2iγ𝓛))`
(`α = a + λ₁`, `γ = Im ρ₁`, `𝓛 = log q`) to the near sum `P3NearSumL`.

This is the height-`H` form of `Rep9.caseC_near` (`IsMin1WideAt 10 χ₁ ρ₁` replaced by
`IsMinWideAt H W χ₁ ρ₁` with room `3H + 1 ≤ W`).  The only place where the height enters is the
window bound on the near summands: a zero `u` in the window `‖1 + i·Im s - u‖ ≤ δ < 1` of the
point `s = σ + i·Im ρ₁` has `|Im u| ≤ |Im ρ₁| + δ < H + 1 ≤ 3H + 1 ≤ W`, so the wide minimality
of `ρ₁` at height `W` applies to it (`|Im ρ₁| ≤ H` is part of `IsMinWideAt`, hence `H ≥ 0`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.Rep9.nearSum_bounds
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.LinnikAreas.boxMaxZero

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-! ## The summand of `P3NearSumL` -/

/-- The `u`-summand of `P3NearSumL`: the divisor value times the windowed `Re P₃`. -/
private def nearTerm (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (a lam L δ : ℝ) (u : ℂ) : ℝ :=
  ((Work.ZeroFreeTables.pdiv q χ s u : ℤ) : ℝ) *
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      then (Work.ZeroFreeTables.P3 ((a + lam) / ((s - u) * (L : ℂ)))).re else 0)

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

/-- The imprimitive bridge in the form used here: for a non-principal `χ` and a point `u` of the
open critical strip the divisor of the completed `L`-function at level `q` is the multiplicity
`zeroMult χ u`. -/
private theorem pdiv_eq_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1)
    (huR : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)) :
    Work.ZeroFreeTables.pdiv q χ s u = (Work.LinnikContract.zeroMult χ u : ℤ) := by
  rw [pdiv_eq_order χ hχ s u, if_pos huR,
    ← Work.ZeroFreeTables.Rep9.zeroMult_eq_analyticOrderNatAt_of_re_pos_of_re_lt_one
      χ hχ hu0 hu1]

/-- **Every summand of the near sum is non-negative.**  This is HB's §9 step "drop the far
zeros": a near zero `u` (within `δ < 1` of `1 + i·Im s`) has `λ(u) ≥ λ₁` by the minimality of
`ρ₁` — so its multiplicity is a genuine `zeroMult` zero (`pdiv` counts the complete `L`-function
at the level `q`, `zeroMult` that of the primitive character) — whence
`Re P₃(α/((s-u)𝓛)) ≥ 0` by HB (4.11). -/
private theorem nearTerm_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    {a lam L δ : ℝ} (hL : 0 < L) (hχ : χ ≠ 1) (hα : 0 < a + lam) (hδ1 : δ < 1)
    (hsre : s.re = 1 + a / L)
    (hmin : ∀ v : ℂ, Work.LinnikContract.zeroMult χ v ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → lam ≤ (1 - v.re) * L)
    (u : ℂ) : 0 ≤ nearTerm q χ s a lam L δ u := by
  unfold nearTerm
  by_cases hwin : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hwin]
    by_cases hdiv : Work.ZeroFreeTables.pdiv q χ s u = 0
    · rw [hdiv]; simp
    · have hre : |1 - u.re| ≤ δ := by
        have h1 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by simp
        rw [← h1]
        exact le_trans (Complex.abs_re_le_norm _) hwin
      have hu0 : 0 < u.re := by
        have h2 := (abs_le.mp hre).2
        linarith
      have huR : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
        by_contra hb
        exact hdiv (by rw [pdiv_eq_order χ hχ s u, if_neg hb])
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
        intro h0
        exact hdiv (by rw [pdiv_eq_order χ hχ s u, if_pos huR, h0]; rfl)
      have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 :=
        Work.ZeroFreeTables.Rep9.zeroMult_ne_zero_of_completedLFunction_eq_zero χ hχ hu0
          (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have hβ : ((s - u) * (L : ℂ)).re = a + (1 - u.re) * L := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.sub_re, hsre]
        have hLne : L ≠ 0 := ne_of_gt hL
        field_simp
        ring
      have hge : a + lam ≤ ((s - u) * (L : ℂ)).re := by
        rw [hβ]; linarith [hmin u hzm hwin]
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3 ((a + lam) / ((s - u) * (L : ℂ)))).re := by
        have harg : (s - u) * (L : ℂ) = ((((s - u) * (L : ℂ)).re : ℝ) : ℂ)
            + ((((s - u) * (L : ℂ)).im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im _).symm
        rw [harg, ← Complex.ofReal_add a lam]
        exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) ((s - u) * (L : ℂ)).re
          ((s - u) * (L : ℂ)).im hα hge
      have hdivnn : (0 : ℝ) ≤ ((Work.ZeroFreeTables.pdiv q χ s u : ℤ) : ℝ) := by
        rw [pdiv_eq_order χ hχ s u, if_pos huR]
        positivity
      exact mul_nonneg hdivnn hP3
  · rw [if_neg hwin, mul_zero]

/-- **The sum over a finite set of near points is at most `P3NearSumL`**, all of whose summands
are non-negative. -/
private theorem finset_sum_le_P3NearSumL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) {a lam L δ : ℝ}
    (hfin : Function.HasFiniteSupport (Work.ZeroFreeTables.pdiv q χ s))
    (hnn : ∀ u : ℂ, 0 ≤ nearTerm q χ s a lam L δ u) (F : Finset ℂ) :
    ∑ u ∈ F, nearTerm q χ s a lam L δ u
      ≤ Work.ZeroFreeTables.P3NearSumL q L χ s a lam δ := by
  have hsupp : Function.HasFiniteSupport (nearTerm q χ s a lam L δ) :=
    hfin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by unfold nearTerm; rw [h0]; simp))
  have hsumm : Summable (nearTerm q χ s a lam L δ) := by
    apply summable_of_ne_finset_zero (s := hfin.toFinset)
    intro u hu
    have hp0 : Work.ZeroFreeTables.pdiv q χ s u = 0 := by
      by_contra hp
      exact hu ((Set.Finite.mem_toFinset hfin).mpr (by simpa [Function.mem_support] using hp))
    unfold nearTerm
    rw [hp0]
    simp
  have htsum : Work.ZeroFreeTables.P3NearSumL q L χ s a lam δ
      = ∑' u : ℂ, nearTerm q χ s a lam L δ u := by
    rw [Work.ZeroFreeTables.P3NearSumL]
    exact (tsum_eq_finsum hsupp).symm
  rw [htsum]
  exact hsumm.sum_le_tsum F (fun v _ => hnn v)

/-! ## The main statement -/

theorem RectRepCaseCNear {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) {H W : ℝ},
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ → 3 * H + 1 ≤ W →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ →
      ‖(1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ →
      (2 : ℝ) * Work.ZeroFreeTables.P3R 1
        + 2 * (Work.ZeroFreeTables.P3
            (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
              / (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
                  + ((2 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I))).re
        ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q:ℝ)) χ₁
            ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a
            (Work.LinnikContract.lamOf q ρ₁) δ := by
  refine ⟨2, ?_⟩
  intro q hq2 _inst χ₁ ρ₁ H W hmin hW hmult hsq hγ hδL hnearc
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hχ1 : χ₁ ≠ 1 := hmin.1
  have hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := by
    rintro h0
    rw [h0] at hmult
    omega
  have himH : |ρ₁.im| ≤ H := hmin.2.2.1
  have hHnn : 0 ≤ H := le_trans (abs_nonneg _) himH
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  set lam : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlamdef
  have hlam : lam = (1 - ρ₁.re) * L := by
    rw [hlamdef, Work.LinnikContract.lamOf, ← hLdef]
  have hre1 : ρ₁.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hzm
  have hlamnn : 0 ≤ lam := by
    rw [hlamdef]; exact IsMinWideAt.lam_nonneg hmin
  have hα : 0 < a + lam := by linarith
  have hdec : ((1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁)
      = (((1 - ρ₁.re : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  have hre_abs : |1 - ρ₁.re| ≤ δ := by
    have h := Complex.abs_re_le_norm
      ((1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁)
    have h2 : (((1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁)).re
        = 1 - ρ₁.re := by rw [hdec]; simp
    rw [h2] at h
    exact h.trans hnearc
  have him_abs : 2 * |ρ₁.im| ≤ δ := by
    have h := Complex.abs_im_le_norm
      ((1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁)
    have h2 : (((1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁)).im
        = 2 * ρ₁.im := by rw [hdec]; simp
    rw [h2] at h
    have h3 : |2 * ρ₁.im| = 2 * |ρ₁.im| := by rw [abs_mul]; norm_num
    rw [h3] at h
    exact h.trans hnearc
  have hrepos : 0 < ρ₁.re := by
    have hlt : 1 - ρ₁.re ≤ δ := (abs_le.mp hre_abs).2
    linarith
  have hne : ρ₁ ≠ (starRingEnd ℂ) ρ₁ := by
    intro h
    apply hγ
    have hh := congrArg Complex.im h
    rw [Complex.conj_im] at hh
    linarith
  set s : ℂ := ((1 + a / L : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I with hsdef
  have hsim : s.im = ρ₁.im := by simp [hsdef]
  have hsre : s.re = 1 + a / L := by simp [hsdef]
  have hmlt : (2 : ℝ) ≤ ((Work.LinnikContract.zeroMult χ₁ ρ₁ : ℤ) : ℝ) := by
    have h : (2 : ℤ) ≤ (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℤ) := by exact_mod_cast hmult
    exact_mod_cast h
  have hball : ∀ v : ℂ, ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ →
      v ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have h3 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 1 + |s.im| := by
      calc ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖
          ≤ ‖(1 : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 1 + |s.im| := by simp
    calc ‖v‖ ≤ ‖v - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖
            + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by
          have hh := norm_add_le (v - ((1 : ℂ) + (s.im : ℂ) * Complex.I))
            ((1 : ℂ) + (s.im : ℂ) * Complex.I)
          simpa using hh
      _ = ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖
            + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by rw [norm_sub_rev]
      _ ≤ δ + (1 + |s.im|) := by linarith
      _ ≤ |s.im| + 2 := by linarith [le_of_lt hδ1]
  have hwin_im : ∀ v : ℂ, ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → |v.im| ≤ W := by
    intro v hv
    have h1 : |s.im - v.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - v)
      have h2 : (((1 : ℂ) + (s.im : ℂ) * Complex.I - v)).im = s.im - v.im := by simp
      rw [h2] at h
      exact h.trans hv
    have h2 : |v.im| ≤ |s.im| + |s.im - v.im| := by
      calc |v.im| = |s.im - (s.im - v.im)| := by congr 1; ring
        _ ≤ |s.im| + |s.im - v.im| := abs_sub _ _
    rw [hsim] at h1 h2
    have h3 : |v.im| ≤ H + δ := by linarith
    have h4 : |v.im| < H + 1 := by linarith
    linarith
  have hwin_min : ∀ v : ℂ, Work.LinnikContract.zeroMult χ₁ v ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → lam ≤ (1 - v.re) * L := by
    intro v hzv hv
    have h := hmin.2.2.2 χ₁ v hχ1 hzv (hwin_im v hv)
    rw [← hlamdef, Work.LinnikContract.lamOf, ← hLdef] at h
    exact h
  have hfinDiv : (Function.support (fun u : ℂ => Work.ZeroFreeTables.pdiv q χ₁ s u)).Finite := by
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ1).analyticAt z
    have h := MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ₁)
      (U := Metric.closedBall (0 : ℂ) (|s.im| + 2))
      (V := Metric.closedBall (0 : ℂ) (|s.im| + 2))
      hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _)
    simpa [Function.HasFiniteSupport, Work.ZeroFreeTables.pdiv] using h
  have hnn : ∀ u : ℂ, 0 ≤ nearTerm q χ₁ s a lam L δ u := fun u =>
    nearTerm_nonneg χ₁ hLpos hχ1 hα hδ1 hsre hwin_min u
  have hnorm_ofReal : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by simp
  have hwinρ : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
    have h1 : (1 : ℂ) + (s.im : ℂ) * Complex.I - ρ₁ = (((1 - ρ₁.re : ℝ)) : ℂ) := by
      rw [hsim]
      apply Complex.ext <;> simp <;> ring
    rw [h1, hnorm_ofReal]
    exact hre_abs
  have hwinρc : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ := by
    rw [hsim]
    exact hnearc
  have hsρ : s - ρ₁ = (((1 + a / L - ρ₁.re : ℝ)) : ℂ) := by
    rw [hsdef]
    apply Complex.ext <;> simp <;> ring
  have hreal : (1 + a / L - ρ₁.re) * L = a + lam := by
    rw [hlam]
    field_simp
    ring
  have hargρ : (s - ρ₁) * (L : ℂ) = ((a : ℂ) + (lam : ℂ)) := by
    rw [hsρ, ← Complex.ofReal_mul, hreal, Complex.ofReal_add]
  have hFρ : (2 : ℝ) * Work.ZeroFreeTables.P3R 1 ≤ nearTerm q χ₁ s a lam L δ ρ₁ := by
    unfold nearTerm
    rw [if_pos hwinρ]
    have hpdiv : Work.ZeroFreeTables.pdiv q χ₁ s ρ₁
        = (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℤ) :=
      pdiv_eq_zeroMult χ₁ hχ1 hrepos hre1 (hball _ hwinρ)
    rw [hpdiv]
    have harg : ((a : ℂ) + (lam : ℂ)) / ((s - ρ₁) * (L : ℂ)) = 1 := by
      rw [hargρ]
      refine div_self ?_
      rw [← Complex.ofReal_add]
      exact_mod_cast ne_of_gt hα
    rw [harg]
    have hP3one : (Work.ZeroFreeTables.P3 (1 : ℂ)).re = Work.ZeroFreeTables.P3R 1 := by
      simp only [Work.ZeroFreeTables.P3, Work.ZeroFreeTables.P3R]
      norm_num
    rw [hP3one]
    have hP3Rnn : 0 ≤ Work.ZeroFreeTables.P3R 1 := by
      simp only [Work.ZeroFreeTables.P3R]
      norm_num
    exact mul_le_mul_of_nonneg_right hmlt hP3Rnn
  have hFρc : 2 * (Work.ZeroFreeTables.P3
        (((a : ℂ) + (lam : ℂ)) / (((a : ℂ) + (lam : ℂ))
          + (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I))).re
      ≤ nearTerm q χ₁ s a lam L δ ((starRingEnd ℂ) ρ₁) := by
    unfold nearTerm
    rw [if_pos hwinρc]
    have hrepos_c : 0 < ((starRingEnd ℂ) ρ₁).re := by simpa using hrepos
    have hre1_c : ((starRingEnd ℂ) ρ₁).re < 1 := by simpa using hre1
    have hpdiv : Work.ZeroFreeTables.pdiv q χ₁ s ((starRingEnd ℂ) ρ₁)
        = (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℤ) := by
      rw [pdiv_eq_zeroMult χ₁ hχ1 hrepos_c hre1_c (hball _ hwinρc),
        Work.A7.zeroMult_conj_sq_one χ₁ hsq ρ₁]
    rw [hpdiv]
    have hsc : s - (starRingEnd ℂ) ρ₁
        = (((1 + a / L - ρ₁.re : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I := by
      rw [hsdef]
      apply Complex.ext <;> simp <;> ring
    have hargc : (s - (starRingEnd ℂ) ρ₁) * (L : ℂ)
        = ((a : ℂ) + (lam : ℂ)) + (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I := by
      have h1 : (((1 + a / L - ρ₁.re : ℝ)) : ℂ) * (L : ℂ) = ((a : ℂ) + (lam : ℂ)) := by
        rw [← Complex.ofReal_mul, hreal, Complex.ofReal_add]
      have h2 : ((((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I) * (L : ℂ)
          = (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I := by
        rw [mul_assoc, mul_comm Complex.I ((L : ℝ) : ℂ), ← mul_assoc, ← Complex.ofReal_mul]
      rw [hsc, add_mul, h1, h2]
    rw [hargc]
    have hP3nn : 0 ≤ (Work.ZeroFreeTables.P3
        (((a : ℂ) + (lam : ℂ)) / (((a : ℂ) + (lam : ℂ))
          + (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I))).re := by
      rw [← Complex.ofReal_add a lam]
      exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) (a + lam) (2 * ρ₁.im * L) hα le_rfl
    exact mul_le_mul_of_nonneg_right hmlt hP3nn
  have hsum_ge : nearTerm q χ₁ s a lam L δ ρ₁ + nearTerm q χ₁ s a lam L δ ((starRingEnd ℂ) ρ₁)
      ≤ Work.ZeroFreeTables.P3NearSumL q L χ₁ s a lam δ := by
    have h1 := finset_sum_le_P3NearSumL χ₁ s hfinDiv hnn ({ρ₁, (starRingEnd ℂ) ρ₁} : Finset ℂ)
    rwa [Finset.sum_pair hne] at h1
  linarith [hFρ, hFρc, hsum_ge]

end Work.ZeroFreeTables.OffAxis
