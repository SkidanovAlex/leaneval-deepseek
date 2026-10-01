import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip

namespace Work.ZeroFreeTables.Rep9

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

/-! ## Auxiliary facts about the completed `L`-function at the level of an imprimitive
character.

`Work.LinnikContract.zeroMult χ ρ` is the vanishing order of the completed `L`-function of the
*primitive* character inducing `χ`, whereas `Work.ZeroFreeTables.pdiv` uses the completed
`L`-function of `χ` itself.  On the open right half-plane the two differ by the entire,
non-vanishing Euler-factor correction `∏_{p ∣ q} (1 - ψ(p)p^{-s})` (`p^{-s}` has modulus `≠ 1`
there), so the vanishing orders agree. -/

/-- The archimedean Gamma factor of a Dirichlet character is non-zero on the open right
half-plane. -/
private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hz
  · rw [hO.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- The primitive character inducing a non-principal character is non-principal. -/
private lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
  exact hχ h2.symm

/-- The `changeLevel` Euler-factor correction `∏_{p ∣ q} (1 - ψ(p)p^{-s})` does not vanish on the
open right half-plane. -/
private lemma eulerCorr_ne_zero {q N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {u : ℂ}
    (hu : 0 < u.re) :
    (∏ p ∈ q.primeFactors, (1 - ψ (p : ZMod N) * (p : ℂ) ^ (-u))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  intro h0
  have hone : ψ (p : ZMod N) * (p : ℂ) ^ (-u) = 1 := (sub_eq_zero.mp h0).symm
  have hnorm : ‖ψ (p : ZMod N) * (p : ℂ) ^ (-u)‖ < 1 := by
    have h1 : ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-u.re) := by
      have := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-u)
      simpa using this
    calc ‖ψ (p : ZMod N) * (p : ℂ) ^ (-u)‖
        ≤ ‖ψ (p : ZMod N)‖ * ‖(p : ℂ) ^ (-u)‖ := norm_mul_le _ _
      _ ≤ 1 * (p : ℝ) ^ (-u.re) := by
            rw [h1]
            exact mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)
      _ < 1 := by
            rw [one_mul, Real.rpow_neg (le_of_lt hpos)]
            exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp1 hu)
  rw [hone, norm_one] at hnorm
  exact absurd hnorm (lt_irrefl 1)

/-- **The imprimitive bridge, order form.**  For a non-principal `χ` mod `q` and a point `u` of
the critical strip, the vanishing order of the completed `L`-function of `χ` (at the level `q`) is
the multiplicity `zeroMult χ u` of `u` as a zero of the completed `L`-function of the primitive
character inducing `χ`. -/
theorem zeroMult_eq_analyticOrderNatAt_of_re_pos_of_re_lt_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    Work.LinnikContract.zeroMult χ u =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hψ
  have hψne : ψ ≠ 1 := by
    intro h1
    have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [← hψ, h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
    exact hχ h2.symm
  set F : ℂ → ℂ := fun s => ∏ p ∈ q.primeFactors,
      (1 - ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) with hF
  have hF_diff : Differentiable ℂ F := by
    intro z
    rw [hF]
    exact DifferentiableAt.fun_finsetProd (fun p hp => by
      have hp' : NeZero p := ⟨(Nat.pos_of_mem_primeFactors hp).ne'⟩
      fun_prop)
  have hF_an : ∀ z : ℂ, AnalyticAt ℂ F z := fun z => hF_diff.analyticAt z
  have hFne : F u ≠ 0 := by rw [hF]; exact eulerCorr_ne_zero ψ hu0
  have hχeq : DirichletCharacter.changeLevel χ.conductor_dvd_level ψ = χ := by
    rw [hψ, DirichletCharacter.changeLevel_primitiveCharacter]
  have hLfac : DirichletCharacter.LFunction χ = DirichletCharacter.LFunction ψ * F := by
    funext s
    rw [Pi.mul_apply, hF]
    have h := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level ψ (Or.inl hψne) (s := s)
    rw [hχeq] at h
    exact h
  have hL_an : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.LFunction ψ) z :=
    fun z => (DirichletCharacter.differentiable_LFunction hψne).analyticAt z
  have hord : analyticOrderNatAt (DirichletCharacter.LFunction χ) u
      = analyticOrderNatAt (DirichletCharacter.LFunction ψ) u := by
    have h1 : analyticOrderAt (DirichletCharacter.LFunction χ) u
        = analyticOrderAt (DirichletCharacter.LFunction ψ) u := by
      rw [hLfac, analyticOrderAt_mul (hL_an u) (hF_an u),
        analyticOrderAt_eq_zero.mpr (Or.inr hFne), add_zero]
    simpa [analyticOrderNatAt] using congrArg ENat.toNat h1
  calc Work.LinnikContract.zeroMult χ u
      = analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u := by
          simp only [Work.LinnikContract.zeroMult, ← hψ]
    _ = analyticOrderNatAt (DirichletCharacter.LFunction ψ) u :=
          (Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
            ψ hψne hu0 hu1).symm
    _ = analyticOrderNatAt (DirichletCharacter.LFunction χ) u := hord.symm
    _ = analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u :=
          Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
            χ hχ hu0 hu1

/-- **The imprimitive bridge, non-vanishing form.**  On the open right half-plane, a zero of the
completed `L`-function of `χ` (at the level of `χ`) is a zero counted by `zeroMult`. -/
theorem zeroMult_ne_zero_of_completedLFunction_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {u : ℂ} (hu : 0 < u.re)
    (hΛ : DirichletCharacter.completedLFunction χ u = 0) :
    Work.LinnikContract.zeroMult χ u ≠ 0 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hψ
  have hψne : ψ ≠ 1 := by
    intro h1
    have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [← hψ, h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
    exact hχ h2.symm
  have hu0 : u ≠ 0 := fun h0 => by rw [h0] at hu; simp at hu
  -- `L(·,χ)` vanishes at `u`
  have hLχ : DirichletCharacter.LFunction χ u = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hu0), hΛ, zero_div]
  -- hence so does `L(·,ψ)`, the correction product being non-zero
  have hLψ : DirichletCharacter.LFunction ψ u = 0 := by
    have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level ψ (Or.inl hψne)
      (s := u)
    rw [DirichletCharacter.changeLevel_primitiveCharacter χ, hLχ] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (eulerCorr_ne_zero ψ hu)
  -- and therefore `Λ(·,ψ)`
  have hΛψ : DirichletCharacter.completedLFunction ψ u = 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ u (Or.inl hu0)
    rw [hLψ] at h
    rcases (div_eq_zero_iff.mp h.symm) with h' | h'
    · exact h'
    · exact absurd h' (gammaFactor_ne_zero_of_re_pos ψ hu)
  have hψ_an : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.completedLFunction ψ) z :=
    fun z => (DirichletCharacter.differentiable_completedLFunction hψne).analyticAt z
  have hΛψ_ne : DirichletCharacter.completedLFunction ψ ≠ 0 := by
    intro h0
    have h2 : DirichletCharacter.LFunction ψ (2 : ℂ) = 0 := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ 2 (Or.inl (by norm_num)),
        show DirichletCharacter.completedLFunction ψ (2 : ℂ) = 0 from by rw [h0]; rfl,
        zero_div]
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψne) (s := (2 : ℂ))
      (by norm_num)) h2
  have hfin : analyticOrderAt (DirichletCharacter.completedLFunction ψ) u ≠ ⊤ :=
    fun htop => hΛψ_ne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u hψ_an).mp htop)
  have hne0 : analyticOrderAt (DirichletCharacter.completedLFunction ψ) u ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hψ_an u, hΛψ⟩
  have hgoal : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u ≠ 0 := by
    intro hc
    have hcast := Nat.cast_analyticOrderNatAt
      (f := DirichletCharacter.completedLFunction ψ) (z₀ := u) hfin
    rw [hc, Nat.cast_zero] at hcast
    exact hne0 hcast.symm
  simpa only [Work.LinnikContract.zeroMult, ← hψ] using hgoal


/-- `(s - u)·log q = (a + λ(u)) + i·log q·(Im s - Im u)` when `Re s = 1 + a/log q`. -/
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
private lemma nearSum_term_nonneg {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    {a δ : ℝ} (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁)
    (hZ : Work.LinnikContract.IsZ χ₁ ρ₁) (ha : 0 < a) (hδ1 : δ < 1)
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {s u : ℂ} (hγ : |s.im| ≤ 8)
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
      have hu10 : |u.im| ≤ 10 := by
        have h2 := abs_le.mp him
        have h3 := abs_le.mp hγ
        rw [abs_le]
        constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, hδ1]
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
        hmin.2 ψ u hψ hzm hu10
      have hdivnn : (0 : ℝ) ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) := by
        rw [pdiv_eq_order ψ hψ s u, if_pos hball]
        positivity
      have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
        Work.LinnikContract.API.isZ_lambda_nonneg hq hZ
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁)
            / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re :=
        P3_sub_mul_log_nonneg hq hs (by linarith) (by linarith)
      exact mul_nonneg hdivnn hP3
  · rw [if_neg hnear]
    simp

theorem nearSum_bounds {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) {a δ γ' : ℝ}
    (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁) (hZ : Work.LinnikContract.IsZ χ₁ ρ₁)
    (hmult : 2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁)
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδL : Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ) :
    (2 : ℝ) * Work.ZeroFreeTables.P3R 1 ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q:ℝ)) χ₁
        ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a
        (Work.LinnikContract.lamOf q ρ₁) δ ∧
    (∀ (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → |γ'| ≤ 8 →
      0 ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q:ℝ)) ψ
        ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((γ' : ℝ) : ℂ) * Complex.I) a
        (Work.LinnikContract.lamOf q ρ₁) δ) := by
  have hχ₁ : χ₁ ≠ 1 := hZ.1
  have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq hZ
  -- `ρ₁` lies in the open critical strip
  have hstrip : 0 < ρ₁.re ∧ ρ₁.re < 1 := by
    haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    refine Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter
      (primitiveCharacter_ne_one hχ₁)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) ?_
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by
      simpa only [Work.LinnikContract.zeroMult] using hZ.2.1)
  constructor
  · -- ### the first conjunct: the double zero `ρ₁` contributes `2·P₃(1)`
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
      exact nearSum_term_nonneg χ₁ ρ₁ hq hmin hZ ha hδ1 hχ₁
        (by rw [hsi]; linarith [hZ.2.2]) hsr
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
        _ ≤ 1 + 1 := by
            have h1 : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hstrip.1]; linarith [hstrip.2]
            linarith [h1, hZ.2.2]
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
  · -- ### the second conjunct: every near-summand is non-negative
    intro ψ hψ hγ'
    have hsr' : ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((γ' : ℝ) : ℂ) * Complex.I).re
        = 1 + a / Real.log (q : ℝ) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have hγ8 : |((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((γ' : ℝ) : ℂ)
        * Complex.I).im| ≤ 8 := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      exact hγ'
    rw [Work.ZeroFreeTables.P3NearSumL]
    refine finsum_nonneg (fun u => ?_)
    exact nearSum_term_nonneg χ₁ ρ₁ hq hmin hZ ha hδ1 hψ hγ8 hsr'

end

end Work.ZeroFreeTables.Rep9
