/-
# ZeroFreeTables/XY/NebenfallOrd2V

The order-2 `Nebenfall` inequality of Xylouris's `λ'`-estimate (his Lemma 4.2 / (4.14) at
`k = 1`), in the height-restricted form needed here: the second zero `u` of a **real**
character `χ₁` is allowed only at heights `|Im u| ≤ 5`.

  `0 ≤ (3/2)(F(-λ₁) - F(λ_u - λ₁)) - 2F(0) + f(0)/2 + 2·sup G(λ₁) + sup H(λ₁) + 1/4`.

Why the height restriction: the eight evaluation points of the underlying pointwise identity
`0 ≤ χ₀(n)(1 + Re{χ₁(n)n^{-iγ'}})(1 + Re{χ₁(n)n^{-iγ₁}})²` sit at the heights
`0, γ', γ₁, γ₁ ∓ γ', 2γ₁, 2γ₁ ∓ γ'` and the HB-Lemma-5.2 windows have radius `δ < 1`, so every
*window* zero has `|Im| ≤ 2|γ₁| + |γ'| + δ ≤ 2 + 5 + δ < 10`; the frozen minimality
`IsMin1WideAt 10` therefore applies to every window zero, which is exactly what the retention
argument needs.  With `|u.im| ≤ 10` (the sibling statement `XY.NebenfallOrd2`, which is FALSE)
the windows reach `12 + δ > 10`.

Files: `XY.KsumEightNonneg` (the eight-term positivity, proved), `XY.KsumWindowKeepFinsetV`
(HB Lemma 5.2 with retained `Finset`, proved), `XY.KsumPrincipalComplex`,
`Commons.NumberTheory.Linnik.Ksum_principal_le` (principal terms), `XY.LamPrimeSup`,
`XY.LamPrimeFVal` (final numerics).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.TestFn_F_nonneg
import Submission.Work.ZeroFreeTables.XY.LamPrimeDefs
import Submission.Work.ZeroFreeTables.XY.KsumEightNonneg
import Submission.Work.ZeroFreeTables.XY.KsumWindowKeepFinsetV
import Submission.Work.ZeroFreeTables.XY.KsumPrincipalComplex
import Submission.Work.ZeroFreeTables.XY.LamPrimeSup
import Submission.Work.ZeroFreeTables.XY.LamPrimeFVal
import Submission.Work.ZeroFreeTables.XY.FMethodOrd2
import Submission.Work.ZeroFreeTables.XY.L52HypEighthDelta
import Submission.Work.ZeroFreeTables.HBRepZeroStrict
import Submission.Work.A7.zeroMult_conj_sq_one

open DirichletCharacter Complex
set_option maxHeartbeats 4000000

open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

open Work.LinnikContract
open MeasureTheory

/-- `10 ≤ log q` for `q ≥ 10^6`. -/
theorem log_ge_ten {q : ℕ} (hq : 10^6 ≤ q) : 10 ≤ Real.log (q:ℝ) := by
  have h1 : Real.log ((10:ℝ)^6) ≤ Real.log (q:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hlog10 : (2:ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have h2 : Real.log ((10:ℝ)^6) = 6 * Real.log 10 := by
    rw [Real.log_pow]; norm_num
  rw [h2] at h1
  linarith

/-- `1 ≤ log (log q)` for `q ≥ 10^6`. -/
theorem loglog_ge_one {q : ℕ} (hq : 10^6 ≤ q) : 1 ≤ Real.log (Real.log (q:ℝ)) := by
  have hL10 : 10 ≤ Real.log (q:ℝ) := log_ge_ten hq
  have hLpos : 0 < Real.log (q:ℝ) := by linarith
  rw [Real.le_log_iff_exp_le hLpos]
  linarith [Real.exp_one_lt_three]

/-- **Principal-character `K`-sum at the real point `β₁ = 1 - λ₁/L`**: from HB Lemma 5.3
(`Ksum_principal_le`) in the shape used by the `Nebenfall` (the loss is `f(0)·ε·L`). -/
theorem nebenfall_principal_real (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (lam₁ : ℝ), 0 ≤ lam₁ → lam₁ ≤ 1 →
      Kxy0 q xyT.f (Real.log (q : ℝ)) (1 - lam₁ / Real.log (q : ℝ)) 0
        ≤ Real.log (q : ℝ) * xyF (-lam₁) + xyT.f 0 * ε * Real.log (q : ℝ) := by
  obtain ⟨B, hB0, hBnd⟩ := xyT.f_bound
  obtain ⟨qP, hP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le xyT.x₀ B xyT.x₀_pos hB0
    xyT.f_cont xyT.f_supp xyT.f_diff hBnd hε xyT.f0_pos
  refine ⟨max qP (10^6), ?_⟩
  intro q hq hqne lam₁ hlam0 hlam1
  haveI : NeZero q := hqne
  have hqP : qP ≤ q := le_trans (le_max_left _ _) hq
  have hqbig : 10^6 ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hL10 : 10 ≤ Real.log (q:ℝ) := log_ge_ten hqbig
  have hL1 : 1 ≤ Real.log (q:ℝ) := by linarith
  have hloglog1 : 1 ≤ Real.log (Real.log (q:ℝ)) := loglog_ge_one hqbig
  have hsqrtlog : 1 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hreg : |(1 - lam₁ / Real.log (q:ℝ)) - 1| ≤
      Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h1 : (1 - lam₁ / Real.log (q:ℝ)) - 1 = -(lam₁ / Real.log (q:ℝ)) := by ring
    rw [h1, abs_neg, abs_of_nonneg (by positivity)]
    calc lam₁ / Real.log (q:ℝ) ≤ 1 / Real.log (q:ℝ) :=
          div_le_div_of_nonneg_right hlam1 hLpos.le
      _ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
          div_le_div_of_nonneg_right hsqrtlog hLpos.le
  have hlam : lam₁ = Real.log (q:ℝ) * (1 - (1 - lam₁ / Real.log (q:ℝ))) := by
    field_simp; ring
  have h := hP hqP (β := 1 - lam₁ / Real.log (q:ℝ)) (lam := lam₁) hlam hreg
  rw [Kxy0_eq_tsum_flat]
  have hint : (∫ t in (0:ℝ)..xyT.x₀, Real.exp (lam₁ * t) * xyT.f t) = xyF (-lam₁) := by
    rw [xyF, TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun u _ => by ring_nf)
  rw [hint] at h
  linarith [h]

/-- **Principal-character `K`-sum at the complex point `β₁ + iη`**: from HB Lemma 5.3 in the
complex-height form (`XY.KsumPrincipalComplex`). -/
theorem nebenfall_principal_complex (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (lam₁ η : ℝ), 0 ≤ lam₁ → lam₁ ≤ 1 →
      |η| ≤ 10 →
      Kxy0 q xyT.f (Real.log (q : ℝ)) (1 - lam₁ / Real.log (q : ℝ)) η
        ≤ Real.log (q : ℝ) * xyRe (-lam₁) (η * Real.log (q : ℝ))
            + xyT.f 0 * ε * Real.log (q : ℝ) := by
  obtain ⟨B, hB0, hBnd⟩ := xyT.f_bound
  obtain ⟨qC, hC⟩ := KsumPrincipalComplex xyT.x₀ B xyT.x₀_pos hB0
    xyT.f_cont xyT.f_supp xyT.f_diff hBnd hε xyT.f0_pos
  refine ⟨max qC (10^6), ?_⟩
  intro q hq hqne lam₁ η hlam0 hlam1 hη
  haveI : NeZero q := hqne
  have hqC : qC ≤ q := le_trans (le_max_left _ _) hq
  have hqbig : 10^6 ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hL10 : 10 ≤ Real.log (q:ℝ) := log_ge_ten hqbig
  have hL1 : 1 ≤ Real.log (q:ℝ) := by linarith
  have hloglog1 : 1 ≤ Real.log (Real.log (q:ℝ)) := loglog_ge_one hqbig
  have hsqrtlog : 1 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hreg : |(1 - lam₁ / Real.log (q:ℝ)) - 1| ≤
      Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h1 : (1 - lam₁ / Real.log (q:ℝ)) - 1 = -(lam₁ / Real.log (q:ℝ)) := by ring
    rw [h1, abs_neg, abs_of_nonneg (by positivity)]
    calc lam₁ / Real.log (q:ℝ) ≤ 1 / Real.log (q:ℝ) :=
          div_le_div_of_nonneg_right hlam1 hLpos.le
      _ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
          div_le_div_of_nonneg_right hsqrtlog hLpos.le
  have hηL : |η| ≤ Real.log (q:ℝ) := le_trans hη hL10
  have h := hC hqC (σ := 1 - lam₁ / Real.log (q:ℝ)) (τ := η) hreg hηL
  rw [Kxy0_eq_tsum']
  have hint : (∫ t in (0:ℝ)..xyT.x₀,
      Real.cos (η * Real.log (q:ℝ) * t) *
        (Real.exp (-(((1 - lam₁ / Real.log (q:ℝ)) - 1) * Real.log (q:ℝ) * t)) * xyT.f t))
      = xyRe (-lam₁) (η * Real.log (q:ℝ)) := by
    rw [xyT_x0, xyRe_eq_integral (-lam₁) (η * Real.log (q:ℝ))]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    have hexp : ((1 - lam₁ / Real.log (q:ℝ)) - 1) * Real.log (q:ℝ) = -lam₁ := by
      field_simp; ring
    rw [hexp]
  rw [hint] at h
  linarith [h]


/-! ## The four `χ₁`-terms of the `Nebenfall`

HB Lemma 5.2 in the retention form `KsumWindowKeepFinsetV`, applied at the four points
`β₁ + i·Im u`, `β₁ + iρ₁.im`, `β₁ + i(2ρ₁.im ∓ u.im)` with the retained zeros
`{u, ρ₁, ρ̄₁}`, `{ρ₁, ρ̄₁}`, `{ρ₁}`, `{ρ₁}`. -/

theorem nebenfall_chi :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ u : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      zeroMult χ₁ u ≠ 0 → |u.im| ≤ 5 → u ≠ ρ₁ → u ≠ starRingEnd ℂ ρ₁ →
      0 ≤ lamOf q ρ₁ → lamOf q u ≤ 1 → lamOf q ρ₁ ≤ 628 / 1000 →
      (Kxy xyT.f (Real.log (q:ℝ)) (1 - lamOf q ρ₁ / Real.log (q:ℝ)) u.im χ₁ ≤
        -(Real.log (q:ℝ)) * (xyF (lamOf q u - lamOf q ρ₁)
          + xyRe 0 ((u.im - ρ₁.im) * Real.log (q:ℝ))
          + xyRe 0 ((u.im + ρ₁.im) * Real.log (q:ℝ)))
        + xyT.f 0 * (1/8 + 1/1000) * Real.log (q:ℝ))
      ∧ (Kxy xyT.f (Real.log (q:ℝ)) (1 - lamOf q ρ₁ / Real.log (q:ℝ)) ρ₁.im χ₁ ≤
        -(Real.log (q:ℝ)) * (xyF 0 + xyRe 0 (2 * ρ₁.im * Real.log (q:ℝ)))
        + xyT.f 0 * (1/8 + 1/1000) * Real.log (q:ℝ))
      ∧ (Kxy xyT.f (Real.log (q:ℝ)) (1 - lamOf q ρ₁ / Real.log (q:ℝ)) (2 * ρ₁.im - u.im) χ₁ ≤
        -(Real.log (q:ℝ)) * (xyRe 0 ((ρ₁.im - u.im) * Real.log (q:ℝ)))
        + xyT.f 0 * (1/8 + 1/1000) * Real.log (q:ℝ))
      ∧ (Kxy xyT.f (Real.log (q:ℝ)) (1 - lamOf q ρ₁ / Real.log (q:ℝ)) (2 * ρ₁.im + u.im) χ₁ ≤
        -(Real.log (q:ℝ)) * (xyRe 0 ((ρ₁.im + u.im) * Real.log (q:ℝ)))
        + xyT.f 0 * (1/8 + 1/1000) * Real.log (q:ℝ)) := by
  obtain ⟨B, hB0, hBnd⟩ := xyT.f_bound
  obtain ⟨δ, hδ0, hδ1, qL, hL52⟩ := L52HypEighth_fixedDelta
  obtain ⟨qR, hR⟩ := HBRepZeroStrict
  obtain ⟨qW, hW⟩ := KsumWindowKeepFinsetV xyT.x₀ B (1/8) xyT.x₀_pos hB0
      xyT.f_cont xyT.f_supp xyT.f_diff hBnd xyT.f0_pos
      (fun z hz => by rw [← xyT.Fc_spec z]; exact xyT.Fc_re_nonneg z hz)
      (ε := 1/1000) (by norm_num) hδ0 hδ1
  refine ⟨max (max (max (max (max qL qR) qW) (max (Nat.ceil (Real.exp (1/δ)) + 1) (10^6))) 4) 2, ?_⟩
  intro q hq hqne χ₁ ρ₁ u hmw hsq him hzu huim hu1 hu2 hlam0 hlamu hlam628
  haveI : NeZero q := hqne
  simp only [max_le_iff] at hq
  have hqL : qL ≤ q := by omega
  have hqR : qR ≤ q := by omega
  have hqW : qW ≤ q := by omega
  have hqδ : Nat.ceil (Real.exp (1/δ)) + 1 ≤ q := by omega
  have hqbig : 10^6 ≤ q := by omega
  have hq4 : 4 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  -- ===== basic consequences of the hypotheses =====
  have hchi1ne : χ₁ ≠ 1 := hmw.1.1.1
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := hmw.1.1.2.1
  have hg1 : |ρ₁.im| ≤ 1 := hmw.1.1.2.2
  have hsq' : χ₁ * χ₁ = 1 := by rw [← pow_two]; exact hsq
  have hmin : ∀ w : ℂ, zeroMult χ₁ w ≠ 0 → |w.im| ≤ 10 → lamOf q ρ₁ ≤ lamOf q w :=
    fun w hzw hw => hmw.2 χ₁ w hchi1ne hzw hw
  set L : ℝ := Real.log (q:ℝ) with hLdef
  set β : ℝ := 1 - lamOf q ρ₁ / L with hbetaDef
  set γ : ℝ := u.im with hgammaDef
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hq1
  have hL10 : 10 ≤ L := by rw [hLdef]; exact log_ge_ten hqbig
  have hL1 : 1 ≤ L := by linarith
  have hloglog1 : 1 ≤ Real.log L := by rw [hLdef]; exact loglog_ge_one hqbig
  have hsqrtlog : 1 ≤ Real.sqrt (Real.log L) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hδL : 1 / δ ≤ L := by
    have hexp1 : 0 < Real.exp (1/δ) := Real.exp_pos _
    have h1 : Real.exp (1/δ) ≤ (q:ℝ) := by
      have h2 : (Nat.ceil (Real.exp (1/δ)) : ℝ) ≤ (q:ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (Real.exp (1/δ)) ≤ q)
      linarith [Nat.le_ceil (Real.exp (1/δ)), h2]
    have h3 : 1/δ ≤ Real.log (q:ℝ) := by
      have h4 := Real.log_le_log hexp1 h1
      rwa [Real.log_exp] at h4
    exact h3
  have hlamEq : ∀ w : ℂ, lamOf q w = (1 - w.re) * L := by intro w; rw [lamOf, ← hLdef]
  have hlam1u : lamOf q ρ₁ ≤ lamOf q u := hmin u hzu (by linarith [huim])
  have hure_le : u.re ≤ β := by
    have h1 : lamOf q ρ₁ ≤ (1 - u.re) * L := by rw [← hlamEq u]; exact hlam1u
    have h2 : lamOf q ρ₁ / L ≤ 1 - u.re := by rw [div_le_iff₀ hLpos]; linarith
    rw [hbetaDef]; linarith
  have hρre : ρ₁.re = β := by
    rw [hbetaDef, hlamEq ρ₁]; field_simp; ring
  have hcρre : ((starRingEnd ℂ) ρ₁).re = β := by rw [Complex.conj_re]; exact hρre
  have hcρim : ((starRingEnd ℂ) ρ₁).im = -ρ₁.im := Complex.conj_im ρ₁
  -- the violating zero lies in the working strip: `|λ_u - λ₁| ≤ 1` and `0 ≤ λ_u`
  have hlamu0 : 0 ≤ lamOf q u := le_trans hlam0 hlam1u
  have hurs : (β - u.re) * L = lamOf q u - lamOf q ρ₁ := by
    rw [hbetaDef, hlamEq u, hlamEq ρ₁]; field_simp; ring
  have hρrs : (β - ρ₁.re) * L = 0 := by rw [hρre]; ring
  have hcρrs : (β - ((starRingEnd ℂ) ρ₁).re) * L = 0 := by rw [hcρre]; ring
  -- simplicity of the two known zeros
  have hsimple : zeroMult χ₁ ρ₁ = 1 := by
    by_contra hne
    have hm2 : 2 ≤ zeroMult χ₁ ρ₁ := by omega
    have hnr : ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) := fun h => him h.2
    have hgt := hR q hqR χ₁ ρ₁ hmw hnr hm2
    linarith
  have hsimplec : zeroMult χ₁ ((starRingEnd ℂ) ρ₁) = 1 := by
    rw [Work.A7.zeroMult_conj_sq_one χ₁ hsq ρ₁]; exact hsimple
  have hcρzm : zeroMult χ₁ ((starRingEnd ℂ) ρ₁) ≠ 0 := by rw [hsimplec]; norm_num
  -- the analytic input
  haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hprim_ne : χ₁.primitiveCharacter ≠ 1 := by
    intro h
    refine hchi1ne ?_
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h]
    exact DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level
  have hanal : ∀ R : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun R z _ => (DirichletCharacter.differentiable_completedLFunction hprim_ne).analyticAt z
  -- norms of the three zeros (they lie well inside every admissible ball)
  have hnorm_ρ : ‖ρ₁‖ ≤ 2 := by
    have hre1 : ρ₁.re ≤ 1 := by
      have h := hlam0; rw [hlamEq ρ₁] at h; nlinarith [hLpos, h]
    have hre0 : 0 ≤ ρ₁.re := by
      have h : lamOf q ρ₁ ≤ 1 := le_trans hlam628 (by norm_num)
      rw [hlamEq ρ₁] at h; nlinarith [hLpos, h]
    have h2 : ‖ρ₁‖ ^ 2 ≤ 4 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hb := abs_le.mp hg1
      nlinarith [sq_abs ρ₁.re, sq_abs ρ₁.im, sq_nonneg ρ₁.re, sq_nonneg ρ₁.im]
    nlinarith [norm_nonneg ρ₁]
  have hnorm_cρ : ‖(starRingEnd ℂ) ρ₁‖ ≤ 2 := by simpa using hnorm_ρ
  have hnorm_u : ‖u‖ ≤ |γ| + 2 := by
    have hre1 : u.re ≤ 1 := by
      rw [hlamEq u] at hlamu0; nlinarith [hLpos, hlamu0]
    have hre0 : 0 ≤ u.re := by
      rw [hlamEq u] at hlamu; nlinarith [hLpos]
    have h1 : |u.re| ≤ 1 := abs_le.mpr ⟨by linarith, hre1⟩
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ 1 + |γ| := by rw [hgammaDef]; linarith
      _ = |γ| + 2 - 1 := by ring
      _ ≤ |γ| + 2 := by linarith
  -- ===== generic tools =====
  have hsre : ∀ h : ℝ, (((β:ℂ) + (h:ℂ) * Complex.I)).re = β := by
    intro h; simp [Complex.add_re, Complex.mul_re]
  have hsim : ∀ h : ℝ, (((β:ℂ) + (h:ℂ) * Complex.I)).im = h := by
    intro h; simp [Complex.add_im, Complex.mul_im]
  have hreg1 : |β - 1| ≤ Real.sqrt (Real.log L) / L := by
    have h1 : β - 1 = -(lamOf q ρ₁ / L) := by rw [hbetaDef]; ring
    rw [h1, abs_neg, abs_of_nonneg (by positivity)]
    calc lamOf q ρ₁ / L ≤ 1 / L := div_le_div_of_nonneg_right (by linarith) hLpos.le
      _ ≤ Real.sqrt (Real.log L) / L := div_le_div_of_nonneg_right hsqrtlog hLpos.le
  have hreg2 : 1 - Real.sqrt (Real.log L) / L ≤ β := by
    have h3 : 1 / L ≤ Real.sqrt (Real.log L) / L :=
      div_le_div_of_nonneg_right hsqrtlog hLpos.le
    have h4 : lamOf q ρ₁ / L ≤ 1 / L :=
      div_le_div_of_nonneg_right (by linarith) hLpos.le
    rw [hbetaDef]; linarith
  have hH : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/8) (1/2000) δ :=
    hL52 q hqL χ₁ hchi1ne hsq' (1/2000) (by norm_num) (by norm_num)
  have hdivc : ∀ (R : ℝ) (w : ℂ), zeroMult χ₁ w ≠ 0 → ‖w‖ ≤ R →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 R)) w ≠ 0 := by
    intro R w hzw hw
    have hmem : w ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hw
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal R) hmem]
    have h : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) w ≠ 0 := by
      simpa only [Work.LinnikContract.zeroMult] using hzw
    exact_mod_cast h
  have hdiv1 : ∀ R : ℝ, 2 ≤ R →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 R)) ρ₁ = 1 := by
    intro R hR
    have hmem : ρ₁ ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal R) hmem]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) ρ₁ = 1 := by
      simpa only [Work.LinnikContract.zeroMult] using hsimple
    rw [h1]; norm_num
  have hdiv1c : ∀ R : ℝ, 2 ≤ R →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 R)) ((starRingEnd ℂ) ρ₁) = 1 := by
    intro R hR
    have hmem : (starRingEnd ℂ) ρ₁ ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      refine le_trans ?_ hR
      simpa using hnorm_cρ
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal R) hmem]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        ((starRingEnd ℂ) ρ₁) = 1 := by
      simpa only [Work.LinnikContract.zeroMult] using hsimplec
    rw [h1]; norm_num
  -- no zero of `χ₁` with `λ < λ₁` lies in a Lemma-5.2 window of a point of height `≤ 9`
  have hno_gen : ∀ h : ℝ, |h| ≤ 9 → ∀ w : ℂ,
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|h| + 2))) w ≠ 0 →
      ‖(1:ℂ) + (h:ℂ) * Complex.I - w‖ ≤ δ → β < w.re → False := by
    intro h hh w hdw hwin hlt
    have hmem : w ∈ Metric.closedBall 0 (|h| + 2) := by
      by_contra hnot
      refine hdw ?_
      have hnot' : ¬ (MeromorphicOn (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|h| + 2)) ∧ w ∈ Metric.closedBall 0 (|h| + 2)) :=
        fun hc => hnot hc.2
      rw [MeromorphicOn.divisor_def, if_neg hnot']
    have hzw : zeroMult χ₁ w ≠ 0 := by
      have hcast : ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          w : ℕ) : ℤ) ≠ 0 := by
        rw [← Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal _) hmem]
        exact hdw
      intro h0
      have h1 : ((zeroMult χ₁ w : ℕ) : ℤ) = 0 := by rw [h0]; rfl
      have h2 : ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          w : ℕ) : ℤ) = 0 := by
        simpa only [Work.LinnikContract.zeroMult] using h1
      exact hcast h2
    have hwim : |w.im| ≤ 10 := by
      have h1 : |h - w.im| ≤ δ := by
        have h2 : |((1:ℂ) + (h:ℂ) * Complex.I - w).im| ≤ δ :=
          le_trans (Complex.abs_im_le_norm _) hwin
        have h3 : ((1:ℂ) + (h:ℂ) * Complex.I - w).im = h - w.im := by
          simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
        rwa [h3] at h2
      have h4 : |w.im| ≤ |h| + |h - w.im| := by
        calc |w.im| = |h - (h - w.im)| := by ring_nf
          _ ≤ |h| + |h - w.im| := abs_sub _ _
      linarith [hδ1]
    have hminw : lamOf q ρ₁ ≤ lamOf q w := hmin w hzw hwim
    rw [hlamEq] at hminw
    have h2 : w.re ≤ ρ₁.re := by
      have h4 : (1 - ρ₁.re) * L ≤ (1 - w.re) * L := hminw
      have h5 : (1 - ρ₁.re) ≤ (1 - w.re) := le_of_mul_le_mul_right h4 hLpos
      linarith
    rw [hρre] at h2
    linarith
  have hScard : ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ).card ≤ 10 := by
    have h2 : ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ).card ≤ 2 :=
      le_trans (Finset.card_insert_le ρ₁ ({starRingEnd ℂ ρ₁} : Finset ℂ)) (by simp)
    have h3 : ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ).card ≤
        ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ).card + 1 :=
      Finset.card_insert_le u ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ)
    omega
  have hρcne : ρ₁ ≠ starRingEnd ℂ ρ₁ := by
    intro h
    have h1 : ρ₁.im = -ρ₁.im := by
      have h2 := congrArg Complex.im h
      rw [Complex.conj_im] at h2
      exact h2
    have h3 : ρ₁.im = 0 := by linarith
    exact him h3
  -- ===== the generic point bound =====
  have hstep : ∀ (h : ℝ) (A : Finset ℂ), |h| ≤ 9 →
      (∀ w ∈ A, w = u ∨ w = ρ₁ ∨ w = starRingEnd ℂ ρ₁) →
      (∀ w ∈ A, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|h| + 2))) w ≠ 0) →
      (∀ w ∈ A, w.re ≤ β) →
      (∀ w ∈ A, |((((β:ℂ) + (h:ℂ) * Complex.I) - w) * ((L:ℝ):ℂ)).re| ≤ 1) →
      (∀ w ∈ A, ¬ (‖(1:ℂ) + (h:ℂ) * Complex.I - w‖ ≤ δ) →
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|h| + 2))) w) ≤ 10) →
      Kxy xyT.f L β h χ₁ ≤
        -(L) * (∑ w ∈ A, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
            (Metric.closedBall 0 (|h| + 2))) w : ℤ) : ℝ) *
          (∫ t in (0:ℝ)..xyT.x₀,
            Complex.exp (-((((β:ℂ) + (h:ℂ) * Complex.I) - w) * ((L:ℝ):ℂ) * (t:ℂ))) *
              ((xyT.f t : ℝ) : ℂ)).re)
        + xyT.f 0 * (1/8 + 1/1000) * L := by
    intro h A hh hmem hdiv hre hri hord
    have hrd : |(((β:ℂ) + (h:ℂ) * Complex.I)).re - 1| ≤
        Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
      rw [hsre h, ← hLdef]; exact hreg1
    have himh : |(((β:ℂ) + (h:ℂ) * Complex.I)).im| ≤ 10 * Real.log (q:ℝ) := by
      rw [hsim h, ← hLdef]
      have : |h| ≤ 10 * L := by nlinarith [hL10]
      linarith
    have hs1 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤
        (((β:ℂ) + (h:ℂ) * Complex.I)).re := by
      rw [hsre h, ← hLdef]; exact hreg2
    have hcard : A.card ≤ 10 := by
      have hsub : A ⊆ ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ) := by
        intro w hw
        rcases hmem w hw with h' | h' | h'
        · rw [h']; simp
        · rw [h']; simp
        · rw [h']; simp
      exact le_trans (Finset.card_le_card hsub) hScard
    set s : ℂ := (β:ℂ) + (h:ℂ) * Complex.I with hsdef
    have hnoA : ∀ w : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) w ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - w‖ ≤ δ → s.re < w.re → False := by
      intro w hdw hwin hlt
      have h1 : s.im = h := by rw [hsdef]; exact hsim h
      have h2 : s.re = β := by rw [hsdef]; exact hsre h
      rw [h1] at hdw hwin
      rw [h2] at hlt
      exact hno_gen h hh w hdw hwin hlt
    have hH' : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/8) (1/1000/2) δ := by
      simpa only [show ((1:ℝ)/1000/2) = 1/2000 by norm_num] using hH
    have hsre' : s.re = β := by rw [hsdef]; exact hsre h
    have hsim' : s.im = h := by rw [hsdef]; exact hsim h
    have hdiv' : ∀ w ∈ A, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) w ≠ 0 := by
      intro w hw; rw [hsim']; exact hdiv w hw
    have hre' : ∀ w ∈ A, w.re ≤ s.re := by
      intro w hw; rw [hsre']; exact hre w hw
    have hord' : ∀ w ∈ A, ¬ (‖(1:ℂ) + (s.im : ℂ) * Complex.I - w‖ ≤ δ) →
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) w) ≤ 10 := by
      intro w hw hnw
      rw [hsim'] at hnw ⊢
      exact hord w hw hnw
    have hmain := hW hqW χ₁ hchi1ne (s := s) hrd himh hs1 hH' hnoA A hcard hdiv' hre' hri hord'
    rw [hsim'] at hmain
    rw [← hLdef] at hmain
    rw [Kxy_eq_tsum]
    exact hmain
  -- ===== point 1: `s = β + iγ`, retaining `{u, ρ₁, ρ̄₁}` =====
  have hγ9 : |γ| ≤ 9 := by rw [hgammaDef]; linarith [huim]
  have hu_win : ‖(1:ℂ) + (γ:ℂ) * Complex.I - u‖ ≤ δ := by
    have h1 : (1:ℂ) + (γ:ℂ) * Complex.I - u = ((1 - u.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, hgammaDef]
    rw [h1, Complex.norm_def, Complex.normSq_ofReal,
      show (1 - u.re) * (1 - u.re) = (1 - u.re)^2 by ring, Real.sqrt_sq_eq_abs]
    have h2 : 0 ≤ 1 - u.re := by
      rw [hlamEq u] at hlamu0; nlinarith [hLpos]
    rw [abs_of_nonneg h2]
    have h3 : 1 - u.re = lamOf q u / L := by rw [hlamEq u]; field_simp
    rw [h3]
    calc lamOf q u / L ≤ 1 / L := div_le_div_of_nonneg_right hlamu hLpos.le
      _ ≤ δ := by
        rw [div_le_iff₀ hLpos]
        have h4 : (1:ℝ) ≤ L * δ := (div_le_iff₀ hδ0).mp hδL
        linarith
  have hA1ord : ∀ w ∈ ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
      ¬ (‖(1:ℂ) + (γ:ℂ) * Complex.I - w‖ ≤ δ) →
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|γ| + 2))) w) ≤ 10 := by
    intro w hw hnw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h' | h'
    · exact absurd (h' ▸ hu_win) hnw
    · rw [h'] at *
      rw [hdiv1 (|γ| + 2) (by linarith [abs_nonneg γ])]; norm_num
    · rw [h'] at *
      rw [hdiv1c (|γ| + 2) (by linarith [abs_nonneg γ])]; norm_num
  have hA1div : ∀ w ∈ ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|γ| + 2))) w ≠ 0 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h' | h'
    · rw [h'] at *
      exact hdivc (|γ| + 2) u hzu hnorm_u
    · rw [h'] at *
      exact hdivc (|γ| + 2) ρ₁ hzm1 (le_trans hnorm_ρ (by linarith [abs_nonneg γ]))
    · rw [h'] at *
      exact hdivc (|γ| + 2) ((starRingEnd ℂ) ρ₁) hcρzm
        (le_trans hnorm_cρ (by linarith [abs_nonneg γ]))
  have hA1re : ∀ w ∈ ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ), w.re ≤ β := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h' | h'
    · rw [h'] at *
      exact hure_le
    · rw [h'] at *
      exact le_of_eq hρre
    · rw [h'] at *
      exact le_of_eq hcρre
  have hA1ri : ∀ w ∈ ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
      |((((β:ℂ) + (γ:ℂ) * Complex.I) - w) * ((L:ℝ):ℂ)).re| ≤ 1 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h' | h'
    · rw [h'] at *
      rw [fmo2_mul_re, hsre γ]
      have h2 : (β - u.re) * L = lamOf q u - lamOf q ρ₁ := hurs
      rw [h2, abs_le]
      constructor <;> linarith
    · rw [h'] at *
      rw [fmo2_mul_re, hsre γ, hρre]; ring_nf
      rw [abs_zero]; norm_num
    · rw [h'] at *
      rw [fmo2_mul_re, hsre γ, hcρre]; ring_nf
      rw [abs_zero]; norm_num
  have h1 := hstep γ ({u, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ) hγ9
    (by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with h' | h' | h' <;> [exact Or.inl h'; exact Or.inr (Or.inl h'); exact Or.inr (Or.inr h')])
    hA1div hA1re hA1ri hA1ord
  -- convert the retained sum at point 1
  have hk1 : (∫ t in (0:ℝ)..xyT.x₀,
      Complex.exp (-((((β:ℂ) + (γ:ℂ) * Complex.I) - u) * ((L:ℝ):ℂ) * (t:ℂ))) *
        ((xyT.f t : ℝ) : ℂ)).re = xyF (lamOf q u - lamOf q ρ₁) := by
    rw [fmo2_integral_re ((((β:ℂ) + (γ:ℂ) * Complex.I) - u) * ((L:ℝ):ℂ))]
    have hre : ((((β:ℂ) + (γ:ℂ) * Complex.I) - u) * ((L:ℝ):ℂ)).re = lamOf q u - lamOf q ρ₁ := by
      rw [fmo2_mul_re, hsre γ, hurs]
    have him : ((((β:ℂ) + (γ:ℂ) * Complex.I) - u) * ((L:ℝ):ℂ)).im = 0 := by
      rw [fmo2_mul_im, hsim γ]; rw [hgammaDef]; ring
    rw [hre, him, xyRe_zero_right]
  have hk2 : (∫ t in (0:ℝ)..xyT.x₀,
      Complex.exp (-((((β:ℂ) + (γ:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ) * (t:ℂ))) *
        ((xyT.f t : ℝ) : ℂ)).re = xyRe 0 ((γ - ρ₁.im) * L) := by
    rw [fmo2_integral_re ((((β:ℂ) + (γ:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ))]
    have hre : ((((β:ℂ) + (γ:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).re = 0 := by
      rw [fmo2_mul_re, hsre γ, hρre]; ring
    have him : ((((β:ℂ) + (γ:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).im = (γ - ρ₁.im) * L := by
      rw [fmo2_mul_im, hsim γ]
    rw [hre, him]
  have hk3 : (∫ t in (0:ℝ)..xyT.x₀,
      Complex.exp (-((((β:ℂ) + (γ:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ) * (t:ℂ))) *
        ((xyT.f t : ℝ) : ℂ)).re = xyRe 0 ((γ + ρ₁.im) * L) := by
    rw [fmo2_integral_re ((((β:ℂ) + (γ:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ))]
    have hre : ((((β:ℂ) + (γ:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ)).re = 0 := by
      rw [fmo2_mul_re, hsre γ, hcρre]; ring
    have him : ((((β:ℂ) + (γ:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ)).im
        = (γ + ρ₁.im) * L := by
      rw [fmo2_mul_im, hsim γ, hcρim]; ring
    rw [hre, him]
  have hord1 : (1:ℝ) ≤
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|γ| + 2))) u : ℤ) : ℝ) := by
    have hnn : (0:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|γ| + 2))) u :=
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hanal _) u
    have hne : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|γ| + 2))) u ≠ 0 := hA1div u (by simp)
    have h1 : (1:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|γ| + 2))) u := by omega
    exact_mod_cast h1
  have hFnn : 0 ≤ xyF (lamOf q u - lamOf q ρ₁) := Work.ZeroFreeTables.TestFn_F_nonneg xyT _
  rw [Finset.sum_insert (by simp [hu1, hu2]), Finset.sum_insert (by simp [hρcne]),
    Finset.sum_singleton, hk1, hk2, hk3, hdiv1 (|γ| + 2) (by linarith [abs_nonneg γ]),
    hdiv1c (|γ| + 2) (by linarith [abs_nonneg γ])] at h1
  have h1' : Kxy xyT.f L β γ χ₁ ≤
      -(L) * (xyF (lamOf q u - lamOf q ρ₁) + xyRe 0 ((γ - ρ₁.im) * L) + xyRe 0 ((γ + ρ₁.im) * L))
      + xyT.f 0 * (1/8 + 1/1000) * L := by
    refine le_trans h1 ?_
    have : xyF (lamOf q u - lamOf q ρ₁) + xyRe 0 ((γ - ρ₁.im) * L) + xyRe 0 ((γ + ρ₁.im) * L)
        ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
            (Metric.closedBall 0 (|γ| + 2))) u : ℤ) : ℝ) * xyF (lamOf q u - lamOf q ρ₁)
          + 1 * xyRe 0 ((γ - ρ₁.im) * L) + 1 * xyRe 0 ((γ + ρ₁.im) * L) := by
      nlinarith [hord1, hFnn]
    nlinarith [this, hLpos]
  -- ===== point 2: `s = β + iρ₁.im`, retaining `{ρ₁, ρ̄₁}` =====
  have hA2ord : ∀ w ∈ ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
      ¬ (‖(1:ℂ) + (ρ₁.im:ℂ) * Complex.I - w‖ ≤ δ) →
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₁.im| + 2))) w) ≤ 10 := by
    intro w hw hnw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h'
    · rw [h'] at *
      rw [hdiv1 (|ρ₁.im| + 2) (by linarith [abs_nonneg ρ₁.im])]; norm_num
    · rw [h'] at *
      rw [hdiv1c (|ρ₁.im| + 2) (by linarith [abs_nonneg ρ₁.im])]; norm_num
  have hA2div : ∀ w ∈ ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₁.im| + 2))) w ≠ 0 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h'
    · rw [h'] at *
      exact hdivc (|ρ₁.im| + 2) ρ₁ hzm1 (le_trans hnorm_ρ (by linarith [abs_nonneg ρ₁.im]))
    · rw [h'] at *
      exact hdivc (|ρ₁.im| + 2) ((starRingEnd ℂ) ρ₁) hcρzm
        (le_trans hnorm_cρ (by linarith [abs_nonneg ρ₁.im]))
  have hA2re : ∀ w ∈ ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ), w.re ≤ β := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h'
    · rw [h'] at *
      exact le_of_eq hρre
    · rw [h'] at *
      exact le_of_eq hcρre
  have hA2ri : ∀ w ∈ ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
      |((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - w) * ((L:ℝ):ℂ)).re| ≤ 1 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h' | h'
    · rw [h'] at *
      rw [fmo2_mul_re, hsre ρ₁.im, hρre]; ring_nf; rw [abs_zero]; norm_num
    · rw [h'] at *
      rw [fmo2_mul_re, hsre ρ₁.im, hcρre]; ring_nf; rw [abs_zero]; norm_num
  have h2 := hstep ρ₁.im ({ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ) (by linarith [abs_le.mp hg1])
    (by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with h' | h' <;> [exact Or.inr (Or.inl h'); exact Or.inr (Or.inr h')])
    hA2div hA2re hA2ri hA2ord
  have hk4 : (∫ t in (0:ℝ)..xyT.x₀,
      Complex.exp (-((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ) * (t:ℂ))) *
        ((xyT.f t : ℝ) : ℂ)).re = xyF 0 := by
    rw [fmo2_integral_re ((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ))]
    have hre : ((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).re = 0 := by
      rw [fmo2_mul_re, hsre ρ₁.im, hρre]; ring
    have him : ((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).im = 0 := by
      rw [fmo2_mul_im, hsim ρ₁.im]; ring
    rw [hre, him, xyRe_zero_right]
  have hk5 : (∫ t in (0:ℝ)..xyT.x₀,
      Complex.exp (-((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ) * (t:ℂ))) *
        ((xyT.f t : ℝ) : ℂ)).re = xyRe 0 (2 * ρ₁.im * L) := by
    rw [fmo2_integral_re ((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ))]
    have hre : ((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ)).re = 0 := by
      rw [fmo2_mul_re, hsre ρ₁.im, hcρre]; ring
    have him : ((((β:ℂ) + (ρ₁.im:ℂ) * Complex.I) - (starRingEnd ℂ ρ₁)) * ((L:ℝ):ℂ)).im
        = 2 * ρ₁.im * L := by
      rw [fmo2_mul_im, hsim ρ₁.im, hcρim]; ring
    rw [hre, him]
  rw [Finset.sum_insert (by simp [hρcne]), Finset.sum_singleton, hk4, hk5,
    hdiv1 (|ρ₁.im| + 2) (by linarith [abs_nonneg ρ₁.im]),
    hdiv1c (|ρ₁.im| + 2) (by linarith [abs_nonneg ρ₁.im])] at h2
  -- ===== points 3 and 4: `s = β + i(2ρ₁.im ∓ u.im)`, retaining `{ρ₁}` =====
  have h3 : Kxy xyT.f L β (2 * ρ₁.im - u.im) χ₁ ≤
      -(L) * (xyRe 0 ((ρ₁.im - u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L := by
    have hstep3 := hstep (2 * ρ₁.im - u.im) ({ρ₁} : Finset ℂ)
      (by have h1 := abs_le.mp hg1; have h2 := abs_le.mp huim
          rw [abs_le]; constructor <;> linarith)
      (by intro w hw; simp only [Finset.mem_singleton] at hw; exact Or.inr (Or.inl hw))
      (by intro w hw
          simp only [Finset.mem_singleton] at hw
          rw [hw] at *
          exact hdivc (|2 * ρ₁.im - u.im| + 2) ρ₁ hzm1
            (le_trans hnorm_ρ (by linarith [abs_nonneg (2 * ρ₁.im - u.im)])))
      (by intro w hw; simp only [Finset.mem_singleton] at hw; rw [hw] at *; exact le_of_eq hρre)
      (by intro w hw
          simp only [Finset.mem_singleton] at hw
          rw [hw] at *
          rw [fmo2_mul_re, hsre (2 * ρ₁.im - u.im), hρre]; ring_nf
          rw [abs_zero]; norm_num)
      (by intro w hw hnw
          simp only [Finset.mem_singleton] at hw
          rw [hw] at *
          rw [hdiv1 (|2 * ρ₁.im - u.im| + 2) (by linarith [abs_nonneg (2 * ρ₁.im - u.im)])]
          norm_num)
    have hk6 : (∫ t in (0:ℝ)..xyT.x₀,
        Complex.exp (-((((β:ℂ) + (((2 * ρ₁.im - u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ) * (t:ℂ))) *
          ((xyT.f t : ℝ) : ℂ)).re = xyRe 0 ((ρ₁.im - u.im) * L) := by
      rw [fmo2_integral_re ((((β:ℂ) + (((2 * ρ₁.im - u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ))]
      have hre : ((((β:ℂ) + (((2 * ρ₁.im - u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).re = 0 := by
        rw [fmo2_mul_re, hsre (2 * ρ₁.im - u.im), hρre]; ring
      have him : ((((β:ℂ) + (((2 * ρ₁.im - u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).im
          = (ρ₁.im - u.im) * L := by
        rw [fmo2_mul_im, hsim (2 * ρ₁.im - u.im)]; ring
      rw [hre, him]
    rw [Finset.sum_singleton, hk6, hdiv1 (|2 * ρ₁.im - u.im| + 2)
      (by linarith [abs_nonneg (2 * ρ₁.im - u.im)])] at hstep3
    simpa using hstep3
  have h4 : Kxy xyT.f L β (2 * ρ₁.im + u.im) χ₁ ≤
      -(L) * (xyRe 0 ((ρ₁.im + u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L := by
    have hstep4 := hstep (2 * ρ₁.im + u.im) ({ρ₁} : Finset ℂ)
      (by have h1 := abs_le.mp hg1; have h2 := abs_le.mp huim
          rw [abs_le]; constructor <;> linarith)
      (by intro w hw; simp only [Finset.mem_singleton] at hw; exact Or.inr (Or.inl hw))
      (by intro w hw
          simp only [Finset.mem_singleton] at hw
          rw [hw] at *
          exact hdivc (|2 * ρ₁.im + u.im| + 2) ρ₁ hzm1
            (le_trans hnorm_ρ (by linarith [abs_nonneg (2 * ρ₁.im + u.im)])))
      (by intro w hw; simp only [Finset.mem_singleton] at hw; rw [hw] at *; exact le_of_eq hρre)
      (by intro w hw
          simp only [Finset.mem_singleton] at hw
          rw [hw] at *
          rw [fmo2_mul_re, hsre (2 * ρ₁.im + u.im), hρre]; ring_nf
          rw [abs_zero]; norm_num)
      (by intro w hw hnw
          simp only [Finset.mem_singleton] at hw
          rw [hw] at *
          rw [hdiv1 (|2 * ρ₁.im + u.im| + 2) (by linarith [abs_nonneg (2 * ρ₁.im + u.im)])]
          norm_num)
    have hk7 : (∫ t in (0:ℝ)..xyT.x₀,
        Complex.exp (-((((β:ℂ) + (((2 * ρ₁.im + u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ) * (t:ℂ))) *
          ((xyT.f t : ℝ) : ℂ)).re = xyRe 0 ((ρ₁.im + u.im) * L) := by
      rw [fmo2_integral_re ((((β:ℂ) + (((2 * ρ₁.im + u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ))]
      have hre : ((((β:ℂ) + (((2 * ρ₁.im + u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).re = 0 := by
        rw [fmo2_mul_re, hsre (2 * ρ₁.im + u.im), hρre]; ring
      have him : ((((β:ℂ) + (((2 * ρ₁.im + u.im) : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L:ℝ):ℂ)).im
          = (ρ₁.im + u.im) * L := by
        rw [fmo2_mul_im, hsim (2 * ρ₁.im + u.im)]; ring
      rw [hre, him]
    rw [Finset.sum_singleton, hk7, hdiv1 (|2 * ρ₁.im + u.im| + 2)
      (by linarith [abs_nonneg (2 * ρ₁.im + u.im)])] at hstep4
    simpa using hstep4
  -- rewrite all four in terms of `Real.log q` and reassemble
  have h2' : Kxy xyT.f L β ρ₁.im χ₁ ≤
      -(L) * (xyF 0 + xyRe 0 (2 * ρ₁.im * L)) + xyT.f 0 * (1/8 + 1/1000) * L := by
    simpa only [Int.cast_one, one_mul] using h2
  exact ⟨h1', h2', h3, h4⟩


/-- **The order-2 `Nebenfall` inequality** (Xylouris's Lemma 4.2 for `ord χ₁ = 2`, `k = 1`),
height-restricted to `|Im u| ≤ 5`. -/
theorem NebenfallOrd2V :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ u : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      zeroMult χ₁ u ≠ 0 → |u.im| ≤ 5 → u ≠ ρ₁ → u ≠ starRingEnd ℂ ρ₁ →
      0 ≤ lamOf q ρ₁ → lamOf q u ≤ 1 → lamOf q ρ₁ ≤ 628 / 1000 →
      0 ≤ 3 / 2 * (xyF (-(lamOf q ρ₁)) - xyF (lamOf q u - lamOf q ρ₁))
            - 2 * xyF 0 + (xyT.f 0) / 2
            + 2 * sSup (Set.range (fun t : ℝ => Gfun 1 (lamOf q ρ₁) t))
            + sSup (Set.range (fun t : ℝ => Hfun 1 (lamOf q ρ₁) t))
            + 1 / 4 := by
  obtain ⟨qP, hP⟩ := nebenfall_principal_real (1/1000) (by norm_num)
  obtain ⟨qC, hC⟩ := nebenfall_principal_complex (1/1000) (by norm_num)
  obtain ⟨qX, hX⟩ := nebenfall_chi
  refine ⟨max 2 (max qX (max qP qC)), ?_⟩
  intro q hq hqne χ₁ ρ₁ u hmw hsq him hzu huim hu1 hu2 hlam0 hlamu hlam628
  haveI : NeZero q := hqne
  simp only [max_le_iff] at hq
  have hqX : qX ≤ q := by omega
  have hqP : qP ≤ q := by omega
  have hqC : qC ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  set L : ℝ := Real.log (q:ℝ) with hLdef
  set β : ℝ := 1 - lamOf q ρ₁ / L with hbetaDef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hq1
  have hg1 : |ρ₁.im| ≤ 1 := hmw.1.1.2.2
  -- the eight-term positivity at `β₁ = 1 - λ₁/L`
  have h8 := KsumEightNonneg (f := xyT.f) xyT.f_nonneg (x₀ := xyT.x₀) (L := Real.log (q:ℝ))
    (β := 1 - lamOf q ρ₁ / Real.log (q:ℝ)) (γ := u.im) (γ₁ := ρ₁.im)
    (Real.log_pos hq1) (le_of_lt xyT.x₀_pos) xyT.f_supp χ₁ hsq
  simp only [Kxy_one_eq_Kxy0] at h8
  rw [← hLdef, ← hbetaDef] at h8
  -- the four principal terms
  have b0 : Kxy0 q xyT.f L β 0 ≤ L * xyF (-(lamOf q ρ₁)) + xyT.f 0 * (1/1000) * L := by
    have h := hP q hqP (lamOf q ρ₁) hlam0 (by linarith)
    rw [← hLdef, ← hbetaDef] at h
    exact h
  have b2 : Kxy0 q xyT.f L β (ρ₁.im - u.im) ≤
      L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im - u.im) * L) + xyT.f 0 * (1/1000) * L := by
    have h := hC q hqC (lamOf q ρ₁) (ρ₁.im - u.im) hlam0 (by linarith)
      (by rw [abs_le]; constructor <;> linarith [abs_le.mp huim, abs_le.mp hg1])
    rw [← hLdef, ← hbetaDef] at h
    exact h
  have b4 : Kxy0 q xyT.f L β (ρ₁.im + u.im) ≤
      L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im + u.im) * L) + xyT.f 0 * (1/1000) * L := by
    have h := hC q hqC (lamOf q ρ₁) (ρ₁.im + u.im) hlam0 (by linarith)
      (by rw [abs_le]; constructor <;> linarith [abs_le.mp huim, abs_le.mp hg1])
    rw [← hLdef, ← hbetaDef] at h
    exact h
  have b6 : Kxy0 q xyT.f L β (2 * ρ₁.im) ≤
      L * xyRe (-(lamOf q ρ₁)) (2 * ρ₁.im * L) + xyT.f 0 * (1/1000) * L := by
    have h := hC q hqC (lamOf q ρ₁) (2 * ρ₁.im) hlam0 (by linarith)
      (by rw [abs_le]; constructor <;> linarith [abs_le.mp hg1])
    rw [← hLdef, ← hbetaDef] at h
    exact h
  -- the four `χ₁` terms
  have b1 : Kxy xyT.f L β u.im χ₁ ≤
      -(L * (xyF (lamOf q u - lamOf q ρ₁) + xyRe 0 ((ρ₁.im - u.im) * L)
        + xyRe 0 ((ρ₁.im + u.im) * L))) + xyT.f 0 * (1/8 + 1/1000) * L := by
    have h := (hX q hqX χ₁ ρ₁ u hmw hsq him hzu huim hu1 hu2 hlam0 hlamu hlam628).1
    rw [← hLdef, ← hbetaDef] at h
    have hev1 : xyRe 0 ((u.im - ρ₁.im) * L) = xyRe 0 ((ρ₁.im - u.im) * L) := by
      have h1 : (u.im - ρ₁.im) * L = -((ρ₁.im - u.im) * L) := by ring
      rw [h1, xyRe_neg]
    have hev2 : xyRe 0 ((u.im + ρ₁.im) * L) = xyRe 0 ((ρ₁.im + u.im) * L) := by
      congr 1; ring
    rw [hev1, hev2] at h
    simpa only [neg_mul] using h
  have b3 : Kxy xyT.f L β ρ₁.im χ₁ ≤
      -(L * (xyF 0 + xyRe 0 (2 * ρ₁.im * L))) + xyT.f 0 * (1/8 + 1/1000) * L := by
    have h := (hX q hqX χ₁ ρ₁ u hmw hsq him hzu huim hu1 hu2 hlam0 hlamu hlam628).2.1
    rw [← hLdef, ← hbetaDef] at h
    simpa only [neg_mul] using h
  have b5 : Kxy xyT.f L β (2 * ρ₁.im - u.im) χ₁ ≤
      -(L * xyRe 0 ((ρ₁.im - u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L := by
    have h := (hX q hqX χ₁ ρ₁ u hmw hsq him hzu huim hu1 hu2 hlam0 hlamu hlam628).2.2.1
    rw [← hLdef, ← hbetaDef] at h
    simpa only [neg_mul] using h
  have b7 : Kxy xyT.f L β (2 * ρ₁.im + u.im) χ₁ ≤
      -(L * xyRe 0 ((ρ₁.im + u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L := by
    have h := (hX q hqX χ₁ ρ₁ u hmw hsq him hzu huim hu1 hu2 hlam0 hlamu hlam628).2.2.2
    rw [← hLdef, ← hbetaDef] at h
    simpa only [neg_mul] using h
  -- weighted combination
  have w0 := mul_le_mul_of_nonneg_left b0 (by norm_num : (0:ℝ) ≤ 3/2)
  have w1 := mul_le_mul_of_nonneg_left b1 (by norm_num : (0:ℝ) ≤ 3/2)
  have w2 := b2
  have w3 := mul_le_mul_of_nonneg_left b3 (by norm_num : (0:ℝ) ≤ 2)
  have w4 := b4
  have w5 := mul_le_mul_of_nonneg_left b5 (by norm_num : (0:ℝ) ≤ 1/4)
  have w6 := mul_le_mul_of_nonneg_left b6 (by norm_num : (0:ℝ) ≤ 1/2)
  have w7 := mul_le_mul_of_nonneg_left b7 (by norm_num : (0:ℝ) ≤ 1/4)
  have hsum2 : 0 ≤
      (3/2) * (L * xyF (-(lamOf q ρ₁)) + xyT.f 0 * (1/1000) * L)
      + (3/2) * (-(L * (xyF (lamOf q u - lamOf q ρ₁) + xyRe 0 ((ρ₁.im - u.im) * L)
            + xyRe 0 ((ρ₁.im + u.im) * L))) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im - u.im) * L) + xyT.f 0 * (1/1000) * L)
      + 2 * (-(L * (xyF 0 + xyRe 0 (2 * ρ₁.im * L))) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im + u.im) * L) + xyT.f 0 * (1/1000) * L)
      + (1/4) * (-(L * xyRe 0 ((ρ₁.im - u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (1/2) * (L * xyRe (-(lamOf q ρ₁)) (2 * ρ₁.im * L) + xyT.f 0 * (1/1000) * L)
      + (1/4) * (-(L * xyRe 0 ((ρ₁.im + u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L) := by
    linarith [h8, w0, w1, w2, w3, w4, w5, w6, w7]
  have hdiv : 0 ≤ ((3/2) * (L * xyF (-(lamOf q ρ₁)) + xyT.f 0 * (1/1000) * L)
      + (3/2) * (-(L * (xyF (lamOf q u - lamOf q ρ₁) + xyRe 0 ((ρ₁.im - u.im) * L)
            + xyRe 0 ((ρ₁.im + u.im) * L))) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im - u.im) * L) + xyT.f 0 * (1/1000) * L)
      + 2 * (-(L * (xyF 0 + xyRe 0 (2 * ρ₁.im * L))) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im + u.im) * L) + xyT.f 0 * (1/1000) * L)
      + (1/4) * (-(L * xyRe 0 ((ρ₁.im - u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (1/2) * (L * xyRe (-(lamOf q ρ₁)) (2 * ρ₁.im * L) + xyT.f 0 * (1/1000) * L)
      + (1/4) * (-(L * xyRe 0 ((ρ₁.im + u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L)) / L :=
    div_nonneg hsum2 hLpos.le
  have hkey : ((3/2) * (L * xyF (-(lamOf q ρ₁)) + xyT.f 0 * (1/1000) * L)
      + (3/2) * (-(L * (xyF (lamOf q u - lamOf q ρ₁) + xyRe 0 ((ρ₁.im - u.im) * L)
            + xyRe 0 ((ρ₁.im + u.im) * L))) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im - u.im) * L) + xyT.f 0 * (1/1000) * L)
      + 2 * (-(L * (xyF 0 + xyRe 0 (2 * ρ₁.im * L))) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (L * xyRe (-(lamOf q ρ₁)) ((ρ₁.im + u.im) * L) + xyT.f 0 * (1/1000) * L)
      + (1/4) * (-(L * xyRe 0 ((ρ₁.im - u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L)
      + (1/2) * (L * xyRe (-(lamOf q ρ₁)) (2 * ρ₁.im * L) + xyT.f 0 * (1/1000) * L)
      + (1/4) * (-(L * xyRe 0 ((ρ₁.im + u.im) * L)) + xyT.f 0 * (1/8 + 1/1000) * L)) / L
      = 3/2 * (xyF (-(lamOf q ρ₁)) - xyF (lamOf q u - lamOf q ρ₁)) - 2 * xyF 0 + (xyT.f 0)/2
        + (xyRe (-(lamOf q ρ₁)) ((ρ₁.im - u.im) * L)
            - (7/4) * xyRe 0 ((ρ₁.im - u.im) * L))
        + (xyRe (-(lamOf q ρ₁)) ((ρ₁.im + u.im) * L)
            - (7/4) * xyRe 0 ((ρ₁.im + u.im) * L))
        + ((1/2) * xyRe (-(lamOf q ρ₁)) (2 * ρ₁.im * L) - 2 * xyRe 0 (2 * ρ₁.im * L))
        + 8 * (xyT.f 0 * (1/1000)) := by
    field_simp
    ring_nf
  rw [hkey] at hdiv
  -- the suprema
  set SG : ℝ := sSup (Set.range (fun t : ℝ => Gfun 1 (lamOf q ρ₁) t)) with hSG
  set SH : ℝ := sSup (Set.range (fun t : ℝ => Hfun 1 (lamOf q ρ₁) t)) with hSH
  have hSGbd : BddAbove (Set.range (fun t : ℝ => Gfun 1 (lamOf q ρ₁) t)) :=
    ⟨1/25, by rintro x ⟨t, rfl⟩; exact LamPrimeSup.1 (lamOf q ρ₁) hlam0 hlam628 t⟩
  have hSHbd : BddAbove (Set.range (fun t : ℝ => Hfun 1 (lamOf q ρ₁) t)) :=
    ⟨1/25, by rintro x ⟨t, rfl⟩; exact LamPrimeSup.2 (lamOf q ρ₁) hlam0 hlam628 t⟩
  have hG1 : Gfun 1 (lamOf q ρ₁) ((ρ₁.im - u.im) * L) ≤ SG := le_csSup hSGbd ⟨_, rfl⟩
  have hG2 : Gfun 1 (lamOf q ρ₁) ((ρ₁.im + u.im) * L) ≤ SG := le_csSup hSGbd ⟨_, rfl⟩
  have hH : Hfun 1 (lamOf q ρ₁) (2 * ρ₁.im * L) ≤ SH := le_csSup hSHbd ⟨_, rfl⟩
  have hG1' : xyRe (-(lamOf q ρ₁)) ((ρ₁.im - u.im) * L)
      - (7/4) * xyRe 0 ((ρ₁.im - u.im) * L) ≤ SG := by
    have h := hG1; rw [Gfun] at h; linarith
  have hG2' : xyRe (-(lamOf q ρ₁)) ((ρ₁.im + u.im) * L)
      - (7/4) * xyRe 0 ((ρ₁.im + u.im) * L) ≤ SG := by
    have h := hG2; rw [Gfun] at h; linarith
  have hH' : (1/2) * xyRe (-(lamOf q ρ₁)) (2 * ρ₁.im * L)
      - 2 * xyRe 0 (2 * ρ₁.im * L) ≤ SH := by
    have h := hH; rw [Hfun] at h; linarith
  have herr : 8 * (xyT.f 0 * (1/1000)) ≤ 1/4 := by
    rw [xyT_f_zero]; norm_num
  linarith [hdiv, hG1', hG2', hH', herr]

end Work.ZeroFreeTables.XY
