import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.API
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroFreeTables.Rep9

open DirichletCharacter Complex
open scoped Classical BigOperators Topology
noncomputable section

/-! ## The divisor of the level-`q` completed `L`-function on the right half-plane -/

/-- The divisor of an analytic function on a set is the vanishing order. -/
private lemma divisor_eq_order {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  simp only [analyticOrderNatAt]
  cases h : analyticOrderAt f z with
  | top => simp
  | coe n => simp

private theorem zeroMult_eq_order_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {u : ℂ} (hu : 0 < u.re) :
    Work.LinnikContract.zeroMult χ u
      = analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u := by
  classical
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : DirichletCharacter ℂ χ.conductor, ψ = χ.primitiveCharacter :=
    ⟨χ.primitiveCharacter, rfl⟩
  have hψne : ψ ≠ 1 := by
    intro h
    exact hχ (by
      have h1 := χ.changeLevel_primitiveCharacter
      rw [← hψdef] at h1
      rw [h] at h1
      rw [DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h1
      exact h1.symm)
  have hNne : χ.conductor ≠ 1 := fun h => hψne (DirichletCharacter.level_one' ψ h)
  have hval : χ (-1) = ψ (-1) := by
    have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := χ) (a := -1)
      (show IsCoprime (-1 : ℤ) (q : ℤ) from ⟨-1, 0, by ring⟩)
    rw [← hψdef] at h
    simpa using h.symm
  have hpar : χ.Even ↔ ψ.Even := by
    rw [DirichletCharacter.Even, DirichletCharacter.Even, hval]
  have hgf : DirichletCharacter.gammaFactor χ = DirichletCharacter.gammaFactor ψ := by
    funext z
    rw [DirichletCharacter.gammaFactor, DirichletCharacter.gammaFactor]
    by_cases h : χ.Even
    · rw [if_pos h, if_pos (hpar.mp h)]
    · rw [if_neg h, if_neg (fun h2 => h (hpar.mpr h2))]
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ → ℂ, P = fun z : ℂ =>
      ∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-z)) := ⟨_, rfl⟩
  have hLχ : ∀ z : ℂ, DirichletCharacter.LFunction χ z
      = DirichletCharacter.LFunction ψ z * P z := by
    intro z
    have h1 := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level ψ (s := z) (Or.inl hψne)
    rw [hψdef] at h1
    rw [χ.changeLevel_primitiveCharacter] at h1
    rw [h1, ← hψdef, hPdef]
  have hloc : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 u]
      fun z => DirichletCharacter.completedLFunction ψ z * P z := by
    filter_upwards [Metric.ball_mem_nhds u hu] with z hz
    have hzre : 0 < z.re := by
      have h1 : |z.re - u.re| ≤ ‖z - u‖ := by
        simpa using Complex.abs_re_le_norm (z - u)
      have h2 : ‖z - u‖ < u.re := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have h3 : -‖z - u‖ ≤ z.re - u.re := neg_le_of_abs_le h1
      linarith
    have hgzne : DirichletCharacter.gammaFactor ψ z ≠ 0 := by
      rcases ψ.even_or_odd with he | ho
      · rw [he.gammaFactor_def]
        exact Complex.Gammaℝ_ne_zero_of_re_pos hzre
      · rw [ho.gammaFactor_def]
        have h2 : 0 < (z + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
        exact Complex.Gammaℝ_ne_zero_of_re_pos h2
    have hgz : DirichletCharacter.gammaFactor χ z ≠ 0 := by rw [hgf]; exact hgzne
    have e1 : DirichletCharacter.completedLFunction χ z
        = DirichletCharacter.gammaFactor χ z * DirichletCharacter.LFunction χ z := by
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr (by
        intro hq1
        exact hχ (DirichletCharacter.level_one' χ hq1)))
      rw [h, mul_div_cancel₀ _ hgz]
    have e2 : DirichletCharacter.completedLFunction ψ z
        = DirichletCharacter.gammaFactor ψ z * DirichletCharacter.LFunction ψ z := by
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ z (Or.inr hNne)
      rw [h, mul_div_cancel₀ _ hgzne]
    rw [e1, e2, hLχ z, hgf]
    ring
  have hP0 : analyticOrderAt P u = 0 := by
    refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
    rw [hPdef, Finset.prod_ne_zero_iff]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hnorm : ‖ψ p * (p : ℂ) ^ (-u)‖ < 1 := by
      have h1 : ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-u.re) := by
        simpa using Complex.norm_natCast_cpow_of_pos hpp.pos (-u)
      calc ‖ψ p * (p : ℂ) ^ (-u)‖
          ≤ ‖ψ p‖ * ‖(p : ℂ) ^ (-u)‖ := norm_mul_le _ _
        _ ≤ 1 * ((p : ℝ) ^ (-u.re)) := by
            rw [h1]
            exact mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)
        _ < 1 := by
            rw [one_mul, Real.rpow_neg hpos.le]
            exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by exact_mod_cast hpp.one_lt) hu)
    intro h0
    have h1 : ψ p * (p : ℂ) ^ (-u) = 1 := (sub_eq_zero.mp h0).symm
    rw [h1, norm_one] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  have hanaψ : AnalyticAt ℂ (DirichletCharacter.completedLFunction ψ) u :=
    (DirichletCharacter.differentiable_completedLFunction hψne).analyticAt u
  have hanaP : AnalyticAt ℂ P u := by
    have hmain : AnalyticAt ℂ
        (∏ p ∈ q.primeFactors, fun z : ℂ => 1 - ψ p * (p : ℂ) ^ (-z)) u := by
      refine Finset.analyticAt_prod _ (fun p hp => ?_)
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp0 : (p : ℂ) ≠ 0 := by
        have h1 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        exact_mod_cast ne_of_gt h1
      have hcpow : (fun z : ℂ => 1 - ψ p * (p : ℂ) ^ (-z))
          = fun z : ℂ => 1 - ψ p * Complex.exp (Complex.log (p : ℂ) * (-z)) := by
        funext z
        rw [Complex.cpow_def_of_ne_zero hp0]
      rw [hcpow]
      have hexp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (Complex.log (p : ℂ) * (-z))) u :=
        (analyticAt_const.mul (analyticAt_id.neg)).cexp
      exact analyticAt_const.sub (analyticAt_const.mul hexp)
    rw [hPdef]
    refine hmain.congr ?_
    filter_upwards with z
    simp only [Finset.prod_apply]
  have hord : analyticOrderAt (DirichletCharacter.completedLFunction χ) u
      = analyticOrderAt (DirichletCharacter.completedLFunction ψ) u + analyticOrderAt P u := by
    rw [analyticOrderAt_congr hloc]
    have hsm : (fun z => DirichletCharacter.completedLFunction ψ z * P z)
        = DirichletCharacter.completedLFunction ψ • P := by
      funext z
      show DirichletCharacter.completedLFunction ψ z * P z
        = DirichletCharacter.completedLFunction ψ z • P z
      rw [smul_eq_mul]
    rw [hsm, analyticOrderAt_smul hanaψ hanaP]
  have hmain2 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u
      = analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u := by
    simp only [analyticOrderNatAt]
    rw [hord, hP0, add_zero]
  have hzm : Work.LinnikContract.zeroMult χ u
      = analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u := by
    rw [Work.LinnikContract.zeroMult, ← hψdef]
  rw [hzm, hmain2]

private theorem pdiv_eq_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s u : ℂ} (hu : 0 < u.re) (huR : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)) :
    Work.ZeroFreeTables.pdiv q χ s u = (Work.LinnikContract.zeroMult χ u : ℤ) := by
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  rw [Work.ZeroFreeTables.pdiv, divisor_eq_order hAn huR,
    ← zeroMult_eq_order_of_re_pos χ hχ hu]

/-! ## The summand of `P3NearSumL` -/

/-- The `u`-summand of `P3NearSumL`: the divisor value times the windowed `Re P₃`. -/
private def nearTerm (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (a lam L δ : ℝ) (u : ℂ) : ℝ :=
  ((Work.ZeroFreeTables.pdiv q χ s u : ℤ) : ℝ) *
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      then (Work.ZeroFreeTables.P3 ((a + lam) / ((s - u) * (L : ℂ)))).re else 0)

private theorem P3NearSumL_eq_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    {a lam L δ : ℝ} (hsupp : Function.HasFiniteSupport (nearTerm q χ s a lam L δ)) :
    Work.ZeroFreeTables.P3NearSumL q L χ s a lam δ
      = ∑' u : ℂ, nearTerm q χ s a lam L δ u := by
  rw [Work.ZeroFreeTables.P3NearSumL]
  exact (tsum_eq_finsum hsupp).symm

/-- Every summand is non-negative. -/
private theorem nearTerm_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    {L a lam δ : ℝ} (hL : 0 < L) (hχ : χ ≠ 1) (hα : 0 < a + lam) (hsre : s.re = 1 + a / L)
    (hball : ∀ v : ℂ, ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ →
      v ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2))
    (hrepos : ∀ v : ℂ, ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → 0 < v.re)
    (hmin : ∀ v : ℂ, Work.LinnikContract.zeroMult χ v ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → lam ≤ (1 - v.re) * L)
    (u : ℂ) : 0 ≤ nearTerm q χ s a lam L δ u := by
  unfold nearTerm
  by_cases hwin : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hwin]
    have hpdiv : Work.ZeroFreeTables.pdiv q χ s u = (Work.LinnikContract.zeroMult χ u : ℤ) :=
      pdiv_eq_zeroMult χ hχ (hrepos u hwin) (hball u hwin)
    rw [hpdiv]
    by_cases hz : Work.LinnikContract.zeroMult χ u = 0
    · simp [hz]
    · have hβ : ((s - u) * (L : ℂ)).re = a + (1 - u.re) * L := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.sub_re, hsre]
        have hLne : L ≠ 0 := ne_of_gt hL
        field_simp
        ring
      have hge : a + lam ≤ ((s - u) * (L : ℂ)).re := by
        rw [hβ]; linarith [hmin u hz hwin]
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3 ((a + lam) / ((s - u) * (L : ℂ)))).re := by
        have harg : (s - u) * (L : ℂ) = ((((s - u) * (L : ℂ)).re : ℝ) : ℂ)
            + ((((s - u) * (L : ℂ)).im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im _).symm
        rw [harg, ← Complex.ofReal_add a lam]
        exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) ((s - u) * (L : ℂ)).re
          ((s - u) * (L : ℂ)).im hα hge
      have hz0 : (0 : ℝ) ≤ ((Work.LinnikContract.zeroMult χ u : ℤ) : ℝ) := by
        exact_mod_cast Int.natCast_nonneg (Work.LinnikContract.zeroMult χ u)
      exact mul_nonneg hz0 hP3
  · rw [if_neg hwin, mul_zero]

/-! ## The main statement -/

theorem caseC_near {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁ →
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
  intro q hq2 _ χ₁ ρ₁ hmin hZ hmult hsq hγ hδL hnearc
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  obtain ⟨hχ1, hzm, him1⟩ := hZ
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  set lam : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlamdef
  have hlam : lam = (1 - ρ₁.re) * L := by
    rw [hlamdef, Work.LinnikContract.lamOf, ← hLdef]
  have hre1 : ρ₁.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hzm
  have hlamnn : 0 ≤ lam := by rw [hlam]; exact mul_nonneg (by linarith) (le_of_lt hLpos)
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
  have hwin_re : ∀ v : ℂ, ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → 0 < v.re := by
    intro v hv
    have h1 : |1 - v.re| ≤ δ := by
      have h := Complex.abs_re_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - v)
      have h2 : (((1 : ℂ) + (s.im : ℂ) * Complex.I - v)).re = 1 - v.re := by simp
      rw [h2] at h
      exact h.trans hv
    have hlt : 1 - v.re ≤ δ := (abs_le.mp h1).2
    linarith
  have hwin_im : ∀ v : ℂ, ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → |v.im| ≤ 10 := by
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
    have h3 : |ρ₁.im| ≤ 1 := him1
    linarith [le_of_lt hδ1]
  have hwin_min : ∀ v : ℂ, Work.LinnikContract.zeroMult χ₁ v ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ → lam ≤ (1 - v.re) * L := by
    intro v hzv hv
    have h := hmin.2 χ₁ v hχ1 hzv (hwin_im v hv)
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
  have hsupp : Function.HasFiniteSupport (nearTerm q χ₁ s a lam L δ) := by
    rw [Function.HasFiniteSupport]
    refine hfinDiv.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by
      unfold nearTerm
      rw [h0]
      simp)
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
      pdiv_eq_zeroMult χ₁ hχ1 hrepos (hball _ hwinρ)
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
    have hpdiv : Work.ZeroFreeTables.pdiv q χ₁ s ((starRingEnd ℂ) ρ₁)
        = (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℤ) := by
      rw [pdiv_eq_zeroMult χ₁ hχ1 hrepos_c (hball _ hwinρc),
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
  have hsumm : Summable (nearTerm q χ₁ s a lam L δ) := by
    apply summable_of_ne_finset_zero (s := hfinDiv.toFinset)
    intro u hu
    have hp0 : Work.ZeroFreeTables.pdiv q χ₁ s u = 0 := by
      by_contra hp
      exact hu ((Set.Finite.mem_toFinset hfinDiv).mpr (by simpa [Function.mem_support] using hp))
    unfold nearTerm
    rw [hp0]
    simp
  have hFsum := P3NearSumL_eq_tsum χ₁ s hsupp
  have hsum_ge : nearTerm q χ₁ s a lam L δ ρ₁ + nearTerm q χ₁ s a lam L δ ((starRingEnd ℂ) ρ₁)
      ≤ ∑' u : ℂ, nearTerm q χ₁ s a lam L δ u := by
    have h1 := hsumm.sum_le_tsum ({ρ₁, (starRingEnd ℂ) ρ₁} : Finset ℂ)
      (fun v _ => nearTerm_nonneg χ₁ hLpos hχ1 hα hsre hball hwin_re hwin_min v)
    rwa [Finset.sum_pair hne] at h1
  rw [hFsum]
  linarith

end

end Work.ZeroFreeTables.Rep9
