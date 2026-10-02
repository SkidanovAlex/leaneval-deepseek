import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.L52SupplyGen
import Submission.Work.ZeroFreeTables.Ksum_positivity_three
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Facts
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.ZeroFreeTables.OffAxis.offAxis_identify
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
import Submission.Work.ZeroFreeTables.tf72f_gap_mono
import Submission.Work.ZeroFreeTables.OffAxis.error_absorb
import Submission.Work.OffAxis.Rect10_3EndgameClean
import Submission.Work.OffAxis.MomentStep103
import Submission.Work.OffAxis.TF72Num103a
import Submission.Work.OffAxis.TF72Num103b
import Submission.Work.ZeroFreeTables.OffAxis.Ksum_eq_re_tsum

namespace Work.OffAxis

open DirichletCharacter Complex
open Work.ZeroFreeTables
open scoped Classical BigOperators
open scoped Interval
open MeasureTheory

noncomputable section

open Work.LinnikContract

/-- Conjugating a zero pair: `(χ,ρ) ↦ (χ⁻¹, conj ρ)` preserves `IsZAt`. -/
theorem IsZAt_inv_conj {q : ℕ} [NeZero q] {H : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.ZeroFreeTables.IsZAt H χ ρ) :
    Work.ZeroFreeTables.IsZAt H χ⁻¹ (starRingEnd ℂ ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1
    exact h.1 (inv_eq_one.mp h1)
  · rw [Work.A7.zeroMult_conj_inv χ ρ]
    exact h.2.1
  · simpa [Complex.conj_im, abs_neg] using h.2.2

/-- For a real zero `ρ₁` of `χ₁`, the conjugated pair `(χ₁⁻¹, ρ₁)` is again a rectangle
minimiser. -/
theorem IsRectMin_inv {q : ℕ} [NeZero q] {H : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : Work.ZeroFreeTables.IsRectMin H χ₁ ρ₁) (him : ρ₁.im = 0) :
    Work.ZeroFreeTables.IsRectMin H χ₁⁻¹ ρ₁ := by
  have hconj : starRingEnd ℂ ρ₁ = ρ₁ := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, him]
  refine ⟨⟨?_, ?_, h.1.2.2⟩, fun χ u hu => h.2 χ u hu⟩
  · intro h1
    exact h.1.1 (inv_eq_one.mp h1)
  · have h2 := Work.A7.zeroMult_conj_inv χ₁ ρ₁
    rw [hconj] at h2
    rw [h2]
    exact h.1.2.1

/-- `λ` is invariant under conjugation of the zero. -/
theorem lamOf_star {q : ℕ} (ρ : ℂ) :
    lamOf q (starRingEnd ℂ ρ) = lamOf q ρ :=
  Work.ZeroFreeTables.OffAxis.lamOf_conj q ρ

/-- The Laplace transform of a real test function takes conjugate values at conjugate
arguments. -/
theorem TestFn_Fc_conj (T : TestFn) (z : ℂ) :
    T.Fc (starRingEnd ℂ z) = starRingEnd ℂ (T.Fc z) := by
  have hpt : ∀ t : ℝ, Complex.exp (-((starRingEnd ℂ z) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)
      = starRingEnd ℂ (Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)) := by
    intro t
    have h1 : starRingEnd ℂ (-(z * (t : ℂ))) = -((starRingEnd ℂ z) * (t : ℂ)) := by
      rw [map_neg, map_mul, starRingEnd_apply, starRingEnd_apply,
        Complex.star_def, Complex.conj_ofReal]
    calc Complex.exp (-((starRingEnd ℂ z) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)
        = Complex.exp (starRingEnd ℂ (-(z * (t : ℂ)))) * ((T.f t : ℝ) : ℂ) := by rw [h1]
      _ = starRingEnd ℂ (Complex.exp (-(z * (t : ℂ)))) * ((T.f t : ℝ) : ℂ) := by
            rw [starRingEnd_apply, Complex.star_def, Complex.exp_conj]
      _ = starRingEnd ℂ (Complex.exp (-(z * (t : ℂ)))) * starRingEnd ℂ ((T.f t : ℝ) : ℂ) := by
            rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
      _ = starRingEnd ℂ (Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)) := by rw [map_mul]
  rw [TestFn.Fc_spec, TestFn.Fc_spec]
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.intervalIntegral_conj]

/-- `Re F` is even in the imaginary argument: `Re F(i m) = Re F(-i m)`. -/
theorem TestFn_Fc_I_re_neg (T : TestFn) (m : ℝ) :
    (T.Fc (((-m : ℝ) : ℂ) * Complex.I)).re = (T.Fc (((m : ℝ) : ℂ) * Complex.I)).re := by
  have h := TestFn_Fc_conj T (((m : ℝ) : ℂ) * Complex.I)
  have h1 : starRingEnd ℂ (((m : ℝ) : ℂ) * Complex.I) = (((-m : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
    simp [Complex.conj_I]
  rw [h1] at h
  rw [h]
  rw [starRingEnd_apply, Complex.star_def]
  exact Complex.conj_re _

/-- The shift identity for the principal-character point: `(β + iτ - 1)·log q = -λ + i τ log q`
when `β = 1 - λ/log q`. -/
theorem sub_one_mul_log {q : ℕ} {β τ lam : ℝ} (hL : Real.log (q : ℝ) ≠ 0)
    (hβ : β = 1 - lam / Real.log (q : ℝ)) :
    (((β : ℂ) + (τ : ℂ) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ))
      = (((-lam : ℝ) : ℂ) + ((τ * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have h1 : (((β : ℂ) + (τ : ℂ) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ))
      = ((((β - 1) * Real.log (q : ℝ) : ℝ)) : ℂ)
          + (((τ * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1]
  have h2 : (β - 1) * Real.log (q : ℝ) = -lam := by
    rw [hβ]
    field_simp
    ring
  rw [h2]


/-- `F(-x)` as an integral with the positive exponential. -/
theorem TestFn_F_neg_eq_integral' (T : Work.ZeroFreeTables.TestFn) (x : ℝ) :
    T.F (-x) = ∫ t in (0:ℝ)..T.x₀, Real.exp (x * t) * T.f t := by
  rw [TestFn_F_eq_integral T (-x)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [neg_mul, neg_neg]

/-- `⌈exp M⌉ + 1 ≤ q` implies `M ≤ log q`. -/
theorem ceil_exp_le_log {M : ℝ} {q : ℕ} (hq : Nat.ceil (Real.exp M) + 1 ≤ q) :
    M ≤ Real.log (q : ℝ) := by
  have h1 : Real.exp M ≤ (Nat.ceil (Real.exp M) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp M) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : Real.exp M ≤ (q : ℝ) := by linarith
  calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos M) h3

/-- In a group, `x ^ 2 = 1` forces `x⁻¹ = x`. -/
theorem inv_eq_self_of_sq_eq_one' {G : Type*} [Group G] {x : G} (h : x ^ 2 = 1) : x⁻¹ = x := by
  have h2 : x * x = 1 := by rwa [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h2

/-- `λ(ρ) ≥ 0` for a zero of a non-principal character. -/
theorem lamOf_nonneg_of_zeroMult_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 ≤ lamOf q ρ := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  rw [lamOf]
  refine mul_nonneg ?_ hlog
  have h := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm
  linarith

/-- The argument of the extracted zero term: `(s - ρ)·log q = λ(ρ) - λ`. -/
theorem sub_mul_log_eq_aux {q : ℕ} {β γ lam lam₁ : ℝ} {ρ : ℂ}
    (hlog : Real.log (q : ℝ) ≠ 0) (hβ : β = 1 - lam₁ / Real.log (q : ℝ))
    (hρre : ρ.re = 1 - lam / Real.log (q : ℝ)) (hργ : ρ.im = γ) :
    ((β : ℂ) + (γ : ℂ) * Complex.I - ρ) * (Real.log (q : ℝ) : ℂ) = ((lam - lam₁ : ℝ) : ℂ) := by
  have h1 : ((β : ℂ) + (γ : ℂ) * Complex.I - ρ)
      = ((((lam - lam₁) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
    apply Complex.ext
    · have hre : (((β : ℂ) + (γ : ℂ) * Complex.I - ρ).re) = β - ρ.re := by simp
      rw [Complex.ofReal_re, hre, hβ, hρre]
      field_simp
      ring
    · have him : (((β : ℂ) + (γ : ℂ) * Complex.I - ρ).im) = γ - ρ.im := by simp
      rw [Complex.ofReal_im, him, hργ]
      ring
  rw [h1, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_cancel₀ _ hlog]

/-- A zero of a non-principal Dirichlet `L`-function lies in the critical strip. -/
theorem zeroMult_abs_re_le_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {ρ : ℂ} (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) : |ρ.re| ≤ 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hzero : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa [Work.LinnikContract.zeroMult] using hzm)
  obtain ⟨h1, h2⟩ :=
    Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter hψne
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) ρ hzero
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩


/-- **HB Lemma 5.3 at a shifted point, with the main term kept.**  For a `C²`-function `f`
supported in `[0,x₀]` with `f 0 > 0` and every `ε > 0` there is `q₀` such that for `q ≥ q₀`
and every `s` with `|s.re - 1| ≤ √(log log q)/log q`, `|s.im| ≤ log q`, the principal-character
`K`-sum satisfies

`K(s) ≤ log q · Re ∫₀^{x₀} e^{-((s-1)log q)t} f(t)dt + f(0)·ε·log q`.

(Adapted from `Ksum_principal_shift`, which continues by bounding the main term by a constant;
here the main term is kept, since the `F`-method needs it.) -/
theorem principalShiftMain_aux (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0))
      (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      (ε : ℝ) (hε : 0 < ε) (hf0 : 0 < f 0),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → ∀ (s : ℂ),
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ Real.log (q : ℝ) →
        Work.ZeroFreeTables.Ksum q f (Real.log (q : ℝ)) s (1 : DirichletCharacter ℂ q)
          ≤ Real.log (q : ℝ) *
              (∫ t in (0:ℝ)..x₀,
                Complex.exp (-(((s - 1) * ((Real.log (q : ℝ) : ℂ)) * (t : ℂ))))
                  * ((f t : ℝ) : ℂ)).re
            + f 0 * ε * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd ε hε hf0
  obtain ⟨C, hCpos, hCbd⟩ :=
    Commons.NumberTheory.Linnik.lemma5_3 x₀ B hx₀ hB hcont hsupp hf2 hBnd
  obtain ⟨q₁, hq₁⟩ := Work.ZeroFreeTables.OffAxis.error_absorb C (f 0) ε hCpos hf0 hε
  refine ⟨max q₁ 8, ?_⟩
  intro q hqNe hqq s hsre hsim
  have hq₁q : q₁ ≤ q := le_trans (le_max_left _ _) hqq
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hqq
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hL2 : 2 ≤ L := by
    rw [hLdef]
    have h1 : Real.log 8 ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq8)
    have h3 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h3] at h1
    have h4 : (2:ℝ) < 3 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hLpos : 0 < L := by linarith
  have herr : C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) ≤ f 0 * ε * L := by
    rw [hLdef]; exact hq₁ q hq₁q
  let M : ℂ := ∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - 1) * L) * (t:ℂ))) * ((f t : ℝ):ℂ)
  let cterm : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
      ((f (Real.log n / L) : ℝ) : ℂ)
  have hKsum : Work.ZeroFreeTables.Ksum q f L s (1 : DirichletCharacter ℂ q)
      = (∑' n : ℕ, cterm n).re := by
    rw [Work.ZeroFreeTables.OffAxis.Ksum_eq_re_tsum hLpos q hsupp s (1 : DirichletCharacter ℂ q)]
  have hbound : ‖(∑' n, cterm n) - ((L:ℝ):ℂ) * M‖
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) := by
    have h := hCbd (q := q) (L := L) hL2 s ?_ ?_
    · simpa only [cterm, M] using h
    · have : Real.sqrt (Real.log L) / L
          = Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by rw [hLdef]
      rw [this]; exact hsre
    · rw [hLdef]; exact hsim
  have hmain : (((L:ℝ):ℂ) * M).re
      = L * (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - 1) * L) * (t:ℂ))) * ((f t : ℝ):ℂ)).re := by
    rw [Complex.mul_re]
    simp [M]
  have herr_le : ((∑' n, cterm n) - ((L:ℝ):ℂ) * M).re
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) :=
    le_trans (Complex.re_le_norm _) hbound
  rw [hKsum]
  have hsplit : (∑' n, cterm n).re
      = (((L:ℝ):ℂ) * M).re + ((∑' n, cterm n) - ((L:ℝ):ℂ) * M).re := by
    rw [Complex.sub_re]; ring
  rw [hsplit, hmain]
  linarith [herr_le, herr]

/-! ## The `F`-method ledger in the `χ₁χ₂χ₃ = χ₀` (F2) case

Heath-Brown's §10 F-method, run at rectangle height `H` in the case that the triple product
`χ₁χ₂χ₃` is principal and `ρ₁` is a **real** zero of `χ₁` with `χ₁² ≠ 1`.  Compared with the `F1`
ledger (no principal triple) the only new ingredient is the treatment of the principal character
`χ₀ = χ₁χ₂χ₃`, which appears with weight `1/4` at the point `β + i(γ₁+γ₂+γ₃)` (and, when
`χ₃² = 1` or `χ₂² = 1`, at a second point as well).  Each such term is paid for either

* by the `λ₂`-window `B` (`Re F(-a+im) ≤ f(0)/6` for `|m| ≥ 200`) applied to the explicit shifted
  principal bound `hP`, when the shift `|τ|·log q` is large, or
* by the *companion pair* term with character `χ₂χ₃ = χ₁⁻¹` at the *same* point, whose own window
  extraction supplies `-L·Re F(i·τ·log q)`: the two bounds then reduce, via HB (10.8)
  (`A`: `Re F(-a+im) - 2 Re F(im) ≤ f(0)/6`), to the generic slack `f(0)(1/6+ε)L`, when the shift
  is small enough that the companion window `‖λ₁/L + iτ‖ ≤ δ` is available.

In all cases the total slack is exactly HB's `f(0)(7/6 + 8ε)L`, giving (10.6). -/
set_option maxHeartbeats 4000000 in
theorem rect103Engine (T : Work.ZeroFreeTables.TestFn) (ε' : ℝ) (hε' : 0 < ε')
    (hP : ∃ qP : ℕ, ∀ q : ℕ, qP ≤ q → ∀ [NeZero q] (s : ℂ),
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ Real.log (q : ℝ) →
        Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) s (1 : DirichletCharacter ℂ q)
          ≤ Real.log (q : ℝ) *
              (∫ t in (0:ℝ)..T.x₀,
                Complex.exp (-(((s - 1) * ((Real.log (q : ℝ) : ℂ)) * (t : ℂ))))
                  * ((T.f t : ℝ) : ℂ)).re
            + T.f 0 * ε' * Real.log (q : ℝ))
    (hA : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 →
        (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re
          - 2 * (T.Fc ((m : ℂ) * Complex.I)).re ≤ T.f 0 / 6)
    (hB : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
        (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 / 6) :
    ∀ H : ℝ, 1 ≤ H → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin H χ₁ ρ₁ → ρ₁.im = 0 → χ₁ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.IsZAt H χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt H χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt H χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        lamOf q ρ₂ ≤ lamOf q u) →
      (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt H χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        χ ≠ χ₂ → χ ≠ χ₂⁻¹ → lamOf q ρ₃ ≤ lamOf q u) →
      lamOf q ρ₂ ≤ lamOf q ρ₃ →
      lamOf q ρ₃ ≤ 6/7 →
      χ₁ * χ₂ * χ₃ = 1 →
      T.F (-(lamOf q ρ₁)) - T.F 0 - T.F (lamOf q ρ₂ - lamOf q ρ₁)
        - T.F (lamOf q ρ₃ - lamOf q ρ₁) + T.f 0 * (7/6 + 8 * ε') ≥ 0 := by
  intro H hH1
  obtain ⟨δ, hδ0, hδ1, qL52, hL52⟩ :=
    Work.ZeroFreeTables.OffAxis.L52SupplyGen ε' hε'
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
    intro z hz
    rw [← T.Fc_spec]
    exact T.Fc_re_nonneg z hz
  obtain ⟨qAs, hAs⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qSs, hSs⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qPs, hPs⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le T.x₀ B T.x₀_pos hB0
    (f := T.f) T.f_cont T.f_supp T.f_diff hBnd hε' T.f0_pos
  obtain ⟨qPsh, hPsh⟩ := hP
  refine ⟨max (max (max (max qL52 qAs) (max qSs qPs)) qPsh)
      (Nat.ceil (Real.exp (max (max (3 * H) (12 / (7 * δ)))
        (max (Real.exp (((6 : ℝ) / 7) ^ 2)) (400 / δ)))) + 1), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him0 hsq1 hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hmin2 hmin3 hlam23 hlam3 hprod
  have hqL52 : qL52 ≤ q := by omega
  have hqAs : qAs ≤ q := by omega
  have hqSs : qSs ≤ q := by omega
  have hqPs : qPs ≤ q := by omega
  have hqPsh : qPsh ≤ q := by omega
  have hexpq : Nat.ceil (Real.exp (max (max (3 * H) (12 / (7 * δ)))
      (max (Real.exp (((6 : ℝ) / 7) ^ 2)) (400 / δ)))) + 1 ≤ q := by omega
  have hMle : max (max (3 * H) (12 / (7 * δ)))
      (max (Real.exp (((6 : ℝ) / 7) ^ 2)) (400 / δ)) ≤ Real.log (q : ℝ) :=
    ceil_exp_le_log hexpq
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have h3H : 3 * H ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMle
  have h12δ : 12 / (7 * δ) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMle
  have hexp2 : Real.exp (((6 : ℝ) / 7) ^ 2) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMle
  have h400δ : 400 / δ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMle
  have hL1 : 1 ≤ L := by
    have h0 : (1:ℝ) ≤ Real.exp (((6 : ℝ) / 7) ^ 2) := Real.one_le_exp (by norm_num)
    linarith
  have hloglog : ((6 : ℝ) / 7) ^ 2 ≤ Real.log (Real.log (q : ℝ)) := by
    calc ((6 : ℝ) / 7) ^ 2 = Real.log (Real.exp (((6 : ℝ) / 7) ^ 2)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (q : ℝ)) :=
          Real.log_le_log (Real.exp_pos _) (by rw [← hLdef]; exact hexp2)
  have hloglog0 : 0 ≤ Real.log (Real.log (q : ℝ)) := le_trans (by norm_num) hloglog
  have hsqrt : (6 : ℝ) / 7 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    rw [Real.le_sqrt (by norm_num) hloglog0]
    exact hloglog
  have hlogq : 0 < Real.log (q : ℝ) := by
    have h1 : (1:ℝ) < Real.exp (((6 : ℝ) / 7) ^ 2) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith [hexp2, h1]
  have hδhalf : (6 : ℝ) / 7 / L ≤ δ / 2 := by
    rw [div_le_iff₀ hlogq]
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * δ)).mp h12δ
    linarith only [h]
  set lam₁ : ℝ := lamOf q ρ₁ with hlam₁
  set lam₂ : ℝ := lamOf q ρ₂ with hlam₂
  set lam₃ : ℝ := lamOf q ρ₃ with hlam₃
  set γ₁ : ℝ := ρ₁.im with hγ₁
  set γ₂ : ℝ := ρ₂.im with hγ₂
  set γ₃ : ℝ := ρ₃.im with hγ₃
  set β : ℝ := 1 - lam₁ / L with hβ
  have hl1nn : 0 ≤ lam₁ := by
    rw [hlam₁]; exact lamOf_nonneg_of_zeroMult_aux hR.1.2.1
  have hl2nn : 0 ≤ lam₂ := by
    rw [hlam₂]; exact lamOf_nonneg_of_zeroMult_aux hZ2.2.1
  have hl3nn : 0 ≤ lam₃ := by
    rw [hlam₃]; exact lamOf_nonneg_of_zeroMult_aux hZ3.2.1
  have hl12 : lam₁ ≤ lam₂ := by
    rw [hlam₁, hlam₂]
    exact hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, le_trans hZ2.2.2 (by linarith [hH1])⟩
  have hl13 : lam₁ ≤ lam₃ := le_trans hl12 hlam23
  have hl16 : lam₁ ≤ 6 / 7 := le_trans hl13 hlam3
  have hγ1z : γ₁ = 0 := by rw [hγ₁]; exact him0
  have him0' : ρ₁.im = 0 := by rw [← hγ₁]; exact him0
  have hγ2L : |γ₂| ≤ H := by rw [hγ₂]; exact hZ2.2.2
  have hγ3L : |γ₃| ≤ H := by rw [hγ₃]; exact hZ3.2.2
  have hβ1 : |β - 1| = lam₁ / L := by
    rw [hβ, show 1 - lam₁ / L - 1 = -(lam₁ / L) by ring, abs_neg,
      abs_of_nonneg (div_nonneg hl1nn hlogq.le)]
  have hdivle : lam₁ / L ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / L :=
    div_le_div_of_nonneg_right (le_trans hl16 hsqrt) hlogq.le
  have hρ1re : ρ₁.re = β := by
    rw [hβ, hlam₁, lamOf]
    field_simp
    ring
  -- the range conditions at a point `β + iγ`
  have hrange : ∀ (γ : ℝ), |γ| ≤ 3 * H →
      |(((β : ℂ) + (γ : ℂ) * Complex.I).re - 1)| ≤
          Real.sqrt (Real.log (Real.log (q : ℝ))) / L ∧
      |(((β : ℂ) + (γ : ℂ) * Complex.I).im)| ≤ 10 * L ∧
      1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / L ≤
        ((β : ℂ) + (γ : ℂ) * Complex.I).re := by
    intro γ hγ
    have hre : ((β : ℂ) + (γ : ℂ) * Complex.I).re = β := by simp
    have him : ((β : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hre, hβ1]; exact hdivle
    · rw [him]; linarith [hγ, h3H]
    · rw [hre, hβ]; linarith [hdivle]
  -- the window condition, from the rectangle minimality of `ρ₁`
  have hwin : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → ∀ s : ℂ,
      s.re = β → |s.im| ≤ 3 * H →
      ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
    intro χ _instc hχ s hs hsim u hdiv hwu
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 :=
      Work.ZeroFreeTables.OffAxis.zeroMult_ne_zero_of_divisor χ hχ hdiv
    have him1 : |s.im - u.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
      have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
      rw [h'] at h
      exact le_trans h hwu
    have him2 : |u.im| ≤ |s.im| + δ := by
      calc |u.im| = |s.im - (s.im - u.im)| := by congr 1; ring
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
        _ ≤ |s.im| + δ := by linarith
    have him3 : |u.im| ≤ 10 * H := by linarith [hsim, him2, hδ1, hH1]
    have hZ : Work.ZeroFreeTables.IsZAt (10 * H) χ u := ⟨hχ, hzm, him3⟩
    have hle : lamOf q ρ₁ ≤ lamOf q u := hR.2 χ u hZ
    rw [← hlam₁, lamOf] at hle
    rw [hs, hβ]
    have h2 : lam₁ / L ≤ 1 - u.re := by
      rw [div_le_iff₀ hlogq]
      linarith
    linarith
  -- conductor instances
  haveI hc1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI hc2 : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  haveI hc3 : NeZero χ₃.conductor := ⟨χ₃.conductor_ne_zero⟩
  haveI hc12 : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI hc1i2 : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  haveI hc13 : NeZero (χ₁ * χ₃).conductor := ⟨(χ₁ * χ₃).conductor_ne_zero⟩
  haveI hc1i3 : NeZero (χ₁ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc23 : NeZero (χ₂ * χ₃).conductor := ⟨(χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc2i3 : NeZero (χ₂ * χ₃⁻¹).conductor := ⟨(χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc123 : NeZero (χ₁ * χ₂ * χ₃).conductor := ⟨(χ₁ * χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc12i3 : NeZero (χ₁ * χ₂ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc1i23 : NeZero (χ₁ * χ₂⁻¹ * χ₃).conductor := ⟨(χ₁ * χ₂⁻¹ * χ₃).conductor_ne_zero⟩
  haveI hc123i : NeZero (χ₁⁻¹ * χ₂ * χ₃).conductor := ⟨(χ₁⁻¹ * χ₂ * χ₃).conductor_ne_zero⟩
  -- non-principality of the auxiliary characters
  have hp12 : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply hne2i
    calc χ₂ = χ₁⁻¹ * (χ₁ * χ₂) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * 1 := by rw [h]
      _ = χ₁⁻¹ := mul_one _
  have hp1i2 : χ₁ * χ₂⁻¹ ≠ 1 := by
    intro h
    apply hne21
    have h2 : χ₂⁻¹ = χ₁⁻¹ := by
      calc χ₂⁻¹ = χ₁⁻¹ * (χ₁ * χ₂⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₁⁻¹ * 1 := by rw [h]
        _ = χ₁⁻¹ := mul_one _
    calc χ₂ = (χ₂⁻¹)⁻¹ := (inv_inv χ₂).symm
      _ = (χ₁⁻¹)⁻¹ := by rw [h2]
      _ = χ₁ := inv_inv χ₁
  have hp13 : χ₁ * χ₃ ≠ 1 := by
    intro h
    apply hne3i
    calc χ₃ = χ₁⁻¹ * (χ₁ * χ₃) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * 1 := by rw [h]
      _ = χ₁⁻¹ := mul_one _
  have hp1i3 : χ₁ * χ₃⁻¹ ≠ 1 := by
    intro h
    apply hne31
    have h2 : χ₃⁻¹ = χ₁⁻¹ := by
      calc χ₃⁻¹ = χ₁⁻¹ * (χ₁ * χ₃⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₁⁻¹ * 1 := by rw [h]
        _ = χ₁⁻¹ := mul_one _
    calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
      _ = (χ₁⁻¹)⁻¹ := by rw [h2]
      _ = χ₁ := inv_inv χ₁
  have hp23 : χ₂ * χ₃ ≠ 1 := by
    intro h
    apply hne3ii
    calc χ₃ = χ₂⁻¹ * (χ₂ * χ₃) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₂⁻¹ * 1 := by rw [h]
      _ = χ₂⁻¹ := mul_one _
  have hp2i3 : χ₂ * χ₃⁻¹ ≠ 1 := by
    intro h
    apply hne32
    have h2 : χ₃⁻¹ = χ₂⁻¹ := by
      calc χ₃⁻¹ = χ₂⁻¹ * (χ₂ * χ₃⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₂⁻¹ * 1 := by rw [h]
        _ = χ₂⁻¹ := mul_one _
    calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
      _ = (χ₂⁻¹)⁻¹ := by rw [h2]
      _ = χ₂ := inv_inv χ₂
  have hχ12 : χ₁ * χ₂ = χ₃⁻¹ := by
    have h2 : (χ₁ * χ₂) * χ₃ = 1 := hprod
    calc χ₁ * χ₂ = (χ₁ * χ₂) * χ₃ * χ₃⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = 1 * χ₃⁻¹ := by rw [h2]
      _ = χ₃⁻¹ := one_mul _
  have hχ23 : χ₂ * χ₃ = χ₁⁻¹ := by
    have h2 : χ₁ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact hprod
    calc χ₂ * χ₃ = χ₁⁻¹ * (χ₁ * (χ₂ * χ₃)) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * 1 := by rw [h2]
      _ = χ₁⁻¹ := mul_one _
  have hχ13 : χ₁ * χ₃ = χ₂⁻¹ := by
    have h2 : χ₂ * (χ₁ * χ₃) = 1 := by
      calc χ₂ * (χ₁ * χ₃) = χ₁ * χ₂ * χ₃ := by ac_rfl
        _ = 1 := hprod
    calc χ₁ * χ₃ = χ₂⁻¹ * (χ₂ * (χ₁ * χ₃)) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₂⁻¹ * 1 := by rw [h2]
      _ = χ₂⁻¹ := mul_one _
  have ht12i3 : χ₃ ^ 2 ≠ 1 → χ₁ * χ₂ * χ₃⁻¹ ≠ 1 := by
    intro h3 h
    apply h3
    have h4 : χ₃⁻¹ * χ₃⁻¹ = 1 := by rw [hχ12] at h; exact h
    have h5 : χ₃⁻¹ = χ₃ := by
      have h6 : χ₃ * (χ₃⁻¹ * χ₃⁻¹) = χ₃ := by rw [h4, mul_one]
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h6
    calc χ₃ ^ 2 = χ₃ * χ₃ := pow_two χ₃
      _ = χ₃ * χ₃⁻¹ := by rw [h5]
      _ = 1 := mul_inv_cancel χ₃
  have ht1i23 : χ₂ ^ 2 ≠ 1 → χ₁ * χ₂⁻¹ * χ₃ ≠ 1 := by
    intro h2 h
    apply h2
    have h4 : χ₂⁻¹ * χ₂⁻¹ = 1 := by
      have h8 : χ₁ * χ₂⁻¹ * χ₃ = (χ₁ * χ₃) * χ₂⁻¹ := by ac_rfl
      rw [h8, hχ13] at h
      exact h
    have h5' : χ₂⁻¹ = χ₂ := by
      have h6 : χ₂ * (χ₂⁻¹ * χ₂⁻¹) = χ₂ := by rw [h4, mul_one]
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h6
    calc χ₂ ^ 2 = χ₂ * χ₂ := pow_two χ₂
      _ = χ₂ * χ₂⁻¹ := by rw [h5']
      _ = 1 := mul_inv_cancel χ₂
  have ht123i : χ₁⁻¹ * χ₂ * χ₃ ≠ 1 := by
    intro h
    apply hsq1
    have h1 : χ₁⁻¹ * χ₁⁻¹ = 1 := by
      have h2 : χ₁⁻¹ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact h
      rwa [hχ23] at h2
    have h4 : χ₁⁻¹ = χ₁ := by
      have h6 : χ₁ * (χ₁⁻¹ * χ₁⁻¹) = χ₁ := by rw [h1, mul_one]
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h6
    calc χ₁ ^ 2 = χ₁ * χ₁ := pow_two χ₁
      _ = χ₁ * χ₁⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel χ₁
  -- `ρ₁` is a zero of `χ₁⁻¹` (it is real)
  have hρ1inv : Work.LinnikContract.zeroMult χ₁⁻¹ ρ₁ ≠ 0 := by
    have h2 := Work.A7.zeroMult_conj_inv χ₁ ρ₁
    have hconj : starRingEnd ℂ ρ₁ = ρ₁ := by
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im]
      exact him0'
    rw [hconj] at h2
    rw [h2]
    exact hR.1.2.1
  -- ==================== the point bounds ====================
  have hbP : Work.ZeroFreeTables.Ksum q T.f L (β : ℂ) 1
      ≤ L * T.F (-lam₁) + T.f 0 * ε' * L := by
    have h := hPs (q := q) hqPs (β := β) (lam := lam₁) ?_ ?_
    · have hFint : T.F (-lam₁) = ∫ t in (0:ℝ)..T.x₀, Real.exp (lam₁ * t) * T.f t := by
        rw [TestFn_F_eq_integral]
        apply intervalIntegral.integral_congr
        intro t _
        simp only [neg_mul, neg_neg]
      rw [hFint]
      exact h
    · rw [hβ, hlam₁]; field_simp; ring
    · rw [hβ1]; exact hdivle
  have hsingle : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H → ∀ (ρ : ℂ) (lam : ℝ),
      ρ.im = γ → lam = lamOf q ρ → lam ≤ 6 / 7 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ -L * T.F (lam - lam₁) + T.f 0 * (1/6 + ε') * L := by
    intro χ _instc hχ γ hγ ρ lam hργ hlam hlam67 hzm
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hmem : ρ ∈ Metric.closedBall (0:ℂ) (|γ| + 2) := by
      have h := Work.ZeroFreeTables.mem_closedBall_of_absre_le_one_v2
        (zeroMult_abs_re_le_one hχ hzm)
      rwa [hργ] at h
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (γ : ℂ) * Complex.I).im| + 2))) ρ ≠ 0 := by
      have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [him]
      exact Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult χ hχ hmem hzm
    have hwinρ : ‖(1:ℂ) + ((((β : ℂ) + (γ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ‖ ≤ δ := by
      have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [him, ← hργ]
      have h1 : (1:ℂ) + (ρ.im : ℂ) * Complex.I - ρ = ((1 - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
      have hre : ρ.re = 1 - lam / L := by
        rw [hlam, lamOf]; field_simp; ring
      have hval : 1 - ρ.re = lam / L := by rw [hre]; ring
      have hlamnn : 0 ≤ lam := by
        rw [hlam]; exact lamOf_nonneg_of_zeroMult_aux hzm
      rw [abs_of_nonneg (by rw [hval]; exact div_nonneg hlamnn hlogq.le), hval]
      exact le_trans (le_trans (div_le_div_of_nonneg_right hlam67 hlogq.le) hδhalf)
        (by linarith [hδ0])
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β := by simp
    have h := hSs (q := q) hqSs χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ) hdiv hwinρ
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]; exact hγ))
    have hint : (∫ t in (0:ℝ)..T.x₀,
          Complex.exp (-(((((β : ℂ) + (γ : ℂ) * Complex.I)) - ρ) * (L : ℂ) * (t:ℂ))) *
            ((T.f t : ℝ) : ℂ)).re = T.F (lam - lam₁) := by
      rw [← T.Fc_spec]
      rw [sub_mul_log_eq_aux (q := q) (β := β) (γ := γ) (lam := lam)
        (lam₁ := lam₁) (ρ := ρ) hlogq.ne' hβ ?_ hργ]
      · rfl
      · rw [hlam, lamOf]; field_simp; ring
    rw [hint] at h
    exact h
  have hbS1 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₁ : ℂ) * Complex.I) χ₁
      ≤ -L * T.F 0 + T.f 0 * (1/6 + ε') * L := by
    have h := hsingle χ₁ hR.1.1 γ₁ (by rw [hγ1z, abs_zero]; linarith [hH1])
      ρ₁ lam₁ (by rw [hγ₁])
      hlam₁ hl16 hR.1.2.1
    simpa only [sub_self] using h
  have hbS2 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₂ : ℂ) * Complex.I) χ₂
      ≤ -L * T.F (lam₂ - lam₁) + T.f 0 * (1/6 + ε') * L :=
    hsingle χ₂ hZ2.1 γ₂ (by rw [hγ₂]; linarith [hγ2L, hH1]) ρ₂ lam₂ (by rw [hγ₂]) hlam₂
      (le_trans hlam23 hlam3) hZ2.2.1
  have hbS3 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₃ : ℂ) * Complex.I) χ₃
      ≤ -L * T.F (lam₃ - lam₁) + T.f 0 * (1/6 + ε') * L :=
    hsingle χ₃ hZ3.1 γ₃ (by rw [hγ₃]; linarith [hγ3L, hH1]) ρ₃ lam₃ (by rw [hγ₃]) hlam₃
      hlam3 hZ3.2.1
  have hself : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ T.f 0 * (1/6 + ε') * L := by
    intro χ _instc hχ γ hγ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β := by simp
    exact hAs (q := q) hqAs χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ)
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]; exact hγ))
  -- the generic pair bounds
  have hbP12 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₂) hp12 (γ₁ + γ₂) (by
      calc |γ₁ + γ₂| ≤ |γ₁| + |γ₂| := abs_add_le _ _
        _ = |γ₂| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ2L, hH1])
    simpa only [ofReal_add] using h
  have hbPi12 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₂⁻¹) hp1i2 (γ₁ - γ₂) (by
      calc |γ₁ - γ₂| ≤ |γ₁| + |γ₂| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₂)
        _ = |γ₂| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ2L, hH1])
    simpa only [ofReal_sub] using h
  have hbP13 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₃) hp13 (γ₁ + γ₃) (by
      calc |γ₁ + γ₃| ≤ |γ₁| + |γ₃| := abs_add_le _ _
        _ = |γ₃| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ3L, hH1])
    simpa only [ofReal_add] using h
  have hbPi13 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₃⁻¹) hp1i3 (γ₁ - γ₃) (by
      calc |γ₁ - γ₃| ≤ |γ₁| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₃)
        _ = |γ₃| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ3L, hH1])
    simpa only [ofReal_sub] using h
  have hbP23g : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₂ * χ₃) hp23 (γ₂ + γ₃) (by
      calc |γ₂ + γ₃| ≤ |γ₂| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * H := by linarith [hγ2L, hγ3L, hH1])
    simpa only [ofReal_add] using h
  have hbPi23g : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₂ * χ₃⁻¹) hp2i3 (γ₂ - γ₃) (by
      calc |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
        _ ≤ 3 * H := by linarith [hγ2L, hγ3L, hH1])
    simpa only [ofReal_sub] using h
  -- a single-point bound with the zero `ρ₁` (a zero of `χ₁⁻¹`, since it is real), at the point
  -- `β + iτ`: this is the window extraction that pays for a principal triple.
  have hsingleρ₁ : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 →
      Work.LinnikContract.zeroMult ψ ρ₁ ≠ 0 → ∀ (τ : ℝ), |τ| ≤ δ / 2 →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (τ : ℂ) * Complex.I) ψ
        ≤ -L * (T.Fc (((τ * L : ℝ)) * Complex.I)).re + T.f 0 * (1/6 + ε') * L := by
    intro ψ _instc hψ hzm τ hτ
    have hτ3 : |τ| ≤ 3 * H := by linarith [hτ, hδ1, hH1]
    obtain ⟨hr1, hr2, hr3⟩ := hrange τ hτ3
    have hmem : ρ₁ ∈ Metric.closedBall (0:ℂ) (|τ| + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : |ρ₁.re| ≤ 1 :=
        zeroMult_abs_re_le_one hψ hzm
      have h2 : ‖ρ₁‖ = |ρ₁.re| := by
        have h3 : Complex.normSq ρ₁ = ρ₁.re ^ 2 := by
          rw [Complex.normSq_apply, him0']
          ring
        have h4 : ‖ρ₁‖ ^ 2 = ρ₁.re ^ 2 := by rw [← Complex.normSq_eq_norm_sq, h3]
        calc ‖ρ₁‖ = Real.sqrt (‖ρ₁‖ ^ 2) := (Real.sqrt_sq (norm_nonneg ρ₁)).symm
          _ = Real.sqrt (ρ₁.re ^ 2) := by rw [h4]
          _ = |ρ₁.re| := Real.sqrt_sq_eq_abs _
      rw [h2]
      linarith [h1, abs_nonneg τ]
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (τ : ℂ) * Complex.I).im| + 2))) ρ₁ ≠ 0 := by
      have him : (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ := by simp
      rw [him]
      exact Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult ψ hψ hmem hzm
    have hwinρ : ‖(1:ℂ) + ((((β : ℂ) + (τ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
      have him : (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ := by simp
      have h1 : (1:ℂ) + (τ : ℂ) * Complex.I - ρ₁
          = ((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
        have h2 : (1:ℂ) - ρ₁ = ((lam₁ / L : ℝ) : ℂ) := by
          apply Complex.ext
          · simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
            rw [hρ1re, hβ]; ring
          · simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.zero_im]
            rw [him0']
            ring
        calc (1:ℂ) + (τ : ℂ) * Complex.I - ρ₁ = ((1:ℂ) - ρ₁) + (τ : ℂ) * Complex.I := by ring
          _ = ((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by rw [h2]
      rw [him, h1]
      have h6 : lam₁ / L ≤ δ / 2 :=
        le_trans (div_le_div_of_nonneg_right hl16 hlogq.le) hδhalf
      have h4 : Complex.normSq (((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
          = (lam₁ / L) ^ 2 + τ ^ 2 := by
        rw [Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          sub_zero, add_zero]
        ring
      have h6b : (lam₁ / L) ^ 2 ≤ (δ / 2) ^ 2 := by
        have h6c : 0 ≤ lam₁ / L := div_nonneg hl1nn hlogq.le
        exact pow_le_pow_left₀ h6c h6 2
      have hτ2 : τ ^ 2 ≤ (δ / 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg τ) hτ 2
      have h5 : ((lam₁ / L) ^ 2 + τ ^ 2) ≤ δ ^ 2 := by
        have hd : (δ / 2) ^ 2 = δ ^ 2 / 4 := by ring
        linarith only [h6b, hτ2, hd, sq_nonneg δ]
      have h7 : ‖((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 ≤ δ ^ 2 := by
        rw [Complex.sq_norm, h4]
        exact h5
      nlinarith only [norm_nonneg (((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I), hδ0, h7]
    have hsre : (((β : ℂ) + (τ : ℂ) * Complex.I).re) = β := by simp
    have h := hSs (q := q) hqSs ψ hψ hr1 hr2 hr3 (hL52 q hqL52 ψ hψ) hdiv hwinρ
      (hwin ψ hψ ((β : ℂ) + (τ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]; exact hτ3))
    have hz : (((β : ℂ) + (τ : ℂ) * Complex.I) - ρ₁) * (L : ℂ)
        = (((τ * L : ℝ)) : ℂ) * Complex.I := by
      have hβL : ((β : ℂ) - ρ₁) * (L : ℂ) = 0 := by
        have hb2 : (β : ℂ) - ρ₁ = 0 := by
          apply Complex.ext
          · simp only [Complex.sub_re, Complex.ofReal_re]
            exact sub_eq_zero.mpr hρ1re.symm
          · simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im]
            rw [him0']
            ring
        rw [hb2, zero_mul]
      rw [show ((β : ℂ) + (τ : ℂ) * Complex.I) - ρ₁ = ((β : ℂ) - ρ₁) + (τ : ℂ) * Complex.I
        from by ring, add_mul, hβL, zero_add]
      push_cast
      ring
    rw [hz] at h
    rw [← T.Fc_spec] at h
    exact h
  -- the companion pair `(2,3)+`
  have hbP23s : |γ₂ + γ₃| ≤ δ / 2 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ -L * (T.Fc ((((γ₂ + γ₃) * L : ℝ)) * Complex.I)).re + T.f 0 * (1/6 + ε') * L := by
    intro hsh
    have h := hsingleρ₁ (χ₂ * χ₃) hp23 (by rw [hχ23]; exact hρ1inv) (γ₂ + γ₃) hsh
    simpa only [ofReal_add] using h
  -- the companion pair `(2,3)-` (available when its character is `χ₁⁻¹`)
  have hbPi23s : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) ρ₁ ≠ 0 → |γ₂ - γ₃| ≤ δ / 2 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
      ≤ -L * (T.Fc ((((γ₂ - γ₃) * L : ℝ)) * Complex.I)).re + T.f 0 * (1/6 + ε') * L := by
    intro hz hsh
    have h := hsingleρ₁ (χ₂ * χ₃⁻¹) hp2i3 hz (γ₂ - γ₃) hsh
    simpa only [ofReal_sub] using h
  -- the principal triple `(1)`: character `χ₁χ₂χ₃ = 1`, from the shifted principal bound
  have hbT123 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃)
      ≤ L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
        + T.f 0 * ε' * L := by
    have hm1 : ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I).re = β := by simp
    have hm2 : ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I).im = γ₂ + γ₃ := by simp
    have hs := hPsh (q := q) hqPsh ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I)
      (by rw [hm1, hβ1]; exact hdivle)
      (by rw [hm2]
          have h23 : |γ₂ + γ₃| ≤ 2 * H := by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L]
          linarith [h23, h3H])
    rw [show ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I - 1) * ((L : ℂ))
        = (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I) from
        sub_one_mul_log hlogq.ne' hβ] at hs
    rw [← T.Fc_spec] at hs
    have hpt : ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I := by
      rw [hγ1z]; push_cast; ring
    rw [hprod, hpt]
    exact hs
  -- the principal triple `(2)`: character `χ₁χ₂χ₃⁻¹ = 1` when `χ₃² = 1`
  have hbT12i3 : χ₃ ^ 2 = 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
      ≤ L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
        + T.f 0 * ε' * L := by
    intro h3
    have hchar : χ₁ * χ₂ * χ₃⁻¹ = 1 := by
      have h4 : χ₃⁻¹ * χ₃⁻¹ = (χ₃ ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
      rw [hχ12, h4, h3, inv_one]
    have hm1 : ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I).re = β := by simp
    have hm2 : ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I).im = γ₂ - γ₃ := by simp
    have hs := hPsh (q := q) hqPsh ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I)
      (by rw [hm1, hβ1]; exact hdivle)
      (by rw [hm2]
          have h23 : |γ₂ - γ₃| ≤ 2 * H := by
            have h2' : |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by
              simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
            linarith [h2', hγ2L, hγ3L]
          have h23' : |γ₃ - γ₂| ≤ 2 * H := by
            rw [show γ₃ - γ₂ = -(γ₂ - γ₃) by ring, abs_neg]
            exact h23
          linarith [h23', h3H, hH1])
    rw [show ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I - 1) * ((L : ℂ))
        = (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I) from
        sub_one_mul_log hlogq.ne' hβ] at hs
    rw [← T.Fc_spec] at hs
    have hpt : ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I := by
      rw [hγ1z]; push_cast; ring
    rw [hchar, hpt]
    exact hs
  -- the principal triple `(3)`: character `χ₁χ₂⁻¹χ₃ = 1` when `χ₂² = 1`
  have hbT1i23 : χ₂ ^ 2 = 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
      ≤ L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I)).re
        + T.f 0 * ε' * L := by
    intro h2
    have hchar : χ₁ * χ₂⁻¹ * χ₃ = 1 := by
      have hχ₁₃ : χ₁ * χ₃ = χ₂⁻¹ := by
        have h6 : χ₂ * (χ₁ * χ₃) = 1 := by
          rw [← mul_assoc, mul_comm χ₂ χ₁]; exact hprod
        exact eq_inv_of_mul_eq_one_right h6
      have h7 : χ₁ * χ₂⁻¹ * χ₃ = χ₂⁻¹ * χ₂⁻¹ := by rw [← hχ₁₃]; ac_rfl
      have h4 : χ₂⁻¹ * χ₂⁻¹ = (χ₂ ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
      rw [h7, h4, h2, inv_one]
    have hm1 : ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I).re = β := by simp
    have hm2 : ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I).im = γ₃ - γ₂ := by simp
    have hs := hPsh (q := q) hqPsh ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I)
      (by rw [hm1, hβ1]; exact hdivle)
      (by rw [hm2]
          have h23 : |γ₂ - γ₃| ≤ 2 * H := by
            have h2' : |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by
              simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
            linarith [h2', hγ2L, hγ3L]
          have h23' : |γ₃ - γ₂| ≤ 2 * H := by
            rw [show γ₃ - γ₂ = -(γ₂ - γ₃) by ring, abs_neg]
            exact h23
          linarith [h23', h3H, hH1])
    rw [show ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I - 1) * ((L : ℂ))
        = (((-lam₁ : ℝ) : ℂ) + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I) from
        sub_one_mul_log hlogq.ne' hβ] at hs
    rw [← T.Fc_spec] at hs
    have hpt : ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I := by
      rw [hγ1z]; push_cast; ring
    rw [hchar, hpt]
    exact hs
  -- the generic triple bounds
  have hbT12i3g : χ₃ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    intro h3
    have h := hself (χ₁ * χ₂ * χ₃⁻¹) (ht12i3 h3) (γ₁ + γ₂ - γ₃) (by
      calc |γ₁ + γ₂ - γ₃| ≤ |γ₁ + γ₂| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le (γ₁ + γ₂) (-γ₃)
        _ ≤ 3 * H := by
            have h12 : |γ₂| ≤ H := hγ2L
            rw [hγ1z] at *
            simp only [abs_zero, zero_add] at *
            linarith [h12, hH1])
    simpa only [ofReal_sub, ofReal_add] using h
  have hbT1i23g : χ₂ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    intro h2
    have h := hself (χ₁ * χ₂⁻¹ * χ₃) (ht1i23 h2) (γ₁ - γ₂ + γ₃) (by
      calc |γ₁ - γ₂ + γ₃| ≤ |γ₁ - γ₂| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * H := by
            have h12 : |γ₂| ≤ H := hγ2L
            rw [hγ1z] at *
            simp only [abs_zero, zero_sub, abs_neg] at *
            linarith [h12, hH1])
    simpa only [ofReal_sub, ofReal_add] using h
  have hbTi123 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁⁻¹ * χ₂ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁⁻¹ * χ₂ * χ₃) ht123i (-γ₁ + γ₂ + γ₃) (by
      have h23 : |γ₂ + γ₃| ≤ 2 * H := by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L]
      have h1 : |-γ₁| = |γ₁| := abs_neg γ₁
      calc |-γ₁ + γ₂ + γ₃| = |(-γ₁) + (γ₂ + γ₃)| := by ring
        _ ≤ |(-γ₁)| + |γ₂ + γ₃| := abs_add_le _ _
        _ ≤ 3 * H := by rw [h1, hγ1z, abs_zero, zero_add]; linarith [h23, hH1])
    simpa only [ofReal_neg, ofReal_add] using h
  -- ==================== the case analysis ====================
  have hpos := Work.ZeroFreeTables.Ksum_positivity_three (f := T.f) (fun t => T.f_nonneg t)
    (x₀ := T.x₀) (L := L) (β := β) (γ₁ := γ₁) (γ₂ := γ₂) (γ₃ := γ₃)
    T.x₀_pos hlogq T.f_supp χ₁ χ₂ χ₃
  have hbigOf : ∀ τ : ℝ, δ / 2 < |τ| → 200 ≤ |τ * L| := by
    intro τ hτ
    rw [abs_mul, abs_of_pos hlogq]
    have h1 : δ / 2 * L ≤ |τ| * L := mul_le_mul_of_nonneg_right hτ.le hlogq.le
    have h2 : 200 ≤ δ / 2 * L := by
      have h3 := (div_le_iff₀ hδ0).mp h400δ
      linarith
    linarith
  have h2not : χ₃ ^ 2 = 1 → χ₂ ^ 2 ≠ 1 := by
    intro h3r h2r
    apply hsq1
    have h6 : χ₁ = χ₂ * χ₃ := by
      calc χ₁ = (χ₁⁻¹)⁻¹ := (inv_inv χ₁).symm
        _ = (χ₂ * χ₃)⁻¹ := by rw [← hχ23]
        _ = χ₂ * χ₃ := by
              rw [mul_inv_rev, inv_eq_self_of_sq_eq_one' h2r,
                inv_eq_self_of_sq_eq_one' h3r, mul_comm χ₃ χ₂]
    calc χ₁ ^ 2 = (χ₂ * χ₃) ^ 2 := by rw [h6]
      _ = χ₂ ^ 2 * χ₃ ^ 2 := by rw [mul_pow]
      _ = 1 := by rw [h2r, h3r, one_mul]
  have h3not : χ₂ ^ 2 = 1 → χ₃ ^ 2 ≠ 1 := by
    intro h2r h3r
    exact (h2not h3r) h2r
  -- group bounds: principal triple + its companion pair
  have hgroupRing : (1/4) * (L * (T.f 0 / 6)) + (1/4) * (T.f 0 * ε' * L)
      + (1/2) * (T.f 0 * (1/6 + ε') * L) = (3/4) * (T.f 0 * (1/6 + ε') * L) := by ring
  have hg1 : (1/4) * Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃)
      + (1/2) * Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ (3/4) * (T.f 0 * (1/6 + ε') * L) := by
    by_cases hs1 : |γ₂ + γ₃| ≤ δ / 2
    · have hA1 := hA lam₁ ((γ₂ + γ₃) * L) hl1nn hl16
      have hmul : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          - 2 * (L * (T.Fc ((((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re)
          ≤ L * (T.f 0 / 6) := by
        have h := mul_le_mul_of_nonneg_left hA1 hlogq.le
        linarith only [h]
      linarith [hbT123, hbP23s hs1, hmul, hgroupRing]
    · have hbig := hbigOf (γ₂ + γ₃) (lt_of_not_ge hs1)
      have hB1 := hB lam₁ ((γ₂ + γ₃) * L) hl1nn hl16 hbig
      have hB1L : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          ≤ L * (T.f 0 / 6) := mul_le_mul_of_nonneg_left hB1 hlogq.le
      linarith [hbT123, hB1L, hbP23g, hgroupRing]
  simp only [Work.ZeroFreeTables.Ksum] at hbP hbS1 hbS2 hbS3 hbP12 hbPi12 hbP13 hbPi13 hbP23g hbPi23g hbT123 hbT12i3 hbT1i23 hbT12i3g hbT1i23g hbTi123 hbP23s hg1
  have hmainRing : 7 * (T.f 0 * (1/6 + ε') * L) + T.f 0 * ε' * L
      = T.f 0 * (7/6 + 8 * ε') * L := by ring
  have hmain : 0 ≤ L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁))
      + T.f 0 * (7/6 + 8 * ε') * L := by
    by_cases h3r : χ₃ ^ 2 = 1
    · have h2c : χ₂ ^ 2 ≠ 1 := h2not h3r
      have hcharPi : χ₂ * χ₃⁻¹ = χ₁⁻¹ := by
        rw [inv_eq_self_of_sq_eq_one' h3r]
        exact hχ23
      have hzPi : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) ρ₁ ≠ 0 := by
        rw [hcharPi]; exact hρ1inv
      have hg2 : (1/4) * Work.ZeroFreeTables.Ksum q T.f L
            ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
          + (1/2) * Work.ZeroFreeTables.Ksum q T.f L
            ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
          ≤ (3/4) * (T.f 0 * (1/6 + ε') * L) := by
        simp only [Work.ZeroFreeTables.Ksum]
        by_cases hs2 : |γ₂ - γ₃| ≤ δ / 2
        · have hA1 := hA lam₁ ((γ₂ - γ₃) * L) hl1nn hl16
          have hmul : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
              - 2 * (L * (T.Fc ((((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re)
              ≤ L * (T.f 0 / 6) := by
            have h := mul_le_mul_of_nonneg_left hA1 hlogq.le
            linarith only [h]
          have hb2 := hbPi23s hzPi hs2
          simp only [Work.ZeroFreeTables.Ksum] at hb2
          linarith only [hbT12i3 h3r, hb2, hmul, hgroupRing]
        · have hbig := hbigOf (γ₂ - γ₃) (lt_of_not_ge hs2)
          have hB1 := hB lam₁ ((γ₂ - γ₃) * L) hl1nn hl16 hbig
          have hB1L : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
              ≤ L * (T.f 0 / 6) := mul_le_mul_of_nonneg_left hB1 hlogq.le
          linarith [hbT12i3 h3r, hbPi23g, hB1L, hgroupRing]
      simp only [Work.ZeroFreeTables.Ksum] at hg2
      linarith [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hg1, hg2,
        hbT1i23g h2c, hbTi123, hmainRing]
    · by_cases h2r : χ₂ ^ 2 = 1
      · have hcharPi : χ₂ * χ₃⁻¹ = χ₁ := by
          have hχ₃inv : χ₃⁻¹ = χ₁ * χ₂ := by
            have h : χ₃ = χ₂⁻¹ * χ₁⁻¹ := by
              calc χ₃ = χ₂⁻¹ * (χ₂ * χ₃) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
                _ = χ₂⁻¹ * χ₁⁻¹ := by rw [hχ23]
            calc χ₃⁻¹ = (χ₂⁻¹ * χ₁⁻¹)⁻¹ := by rw [h]
              _ = χ₁ * χ₂ := by rw [mul_inv_rev, inv_inv, inv_inv]
          rw [hχ₃inv]
          calc χ₂ * (χ₁ * χ₂) = χ₁ * (χ₂ * χ₂) := by ac_rfl
            _ = χ₁ * χ₂ ^ 2 := by rw [pow_two]
            _ = χ₁ * 1 := by rw [h2r]
            _ = χ₁ := mul_one χ₁
        have hzPi : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) ρ₁ ≠ 0 := by
          rw [hcharPi]; exact hR.1.2.1
        have hg3 : (1/4) * Work.ZeroFreeTables.Ksum q T.f L
              ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
            + (1/2) * Work.ZeroFreeTables.Ksum q T.f L
              ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
            ≤ (3/4) * (T.f 0 * (1/6 + ε') * L) := by
          simp only [Work.ZeroFreeTables.Ksum]
          have heven : (T.Fc (((-lam₁ : ℝ) : ℂ)
                + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I)).re
              = (T.Fc (((-lam₁ : ℝ) : ℂ)
                + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re := by
            have h := TestFn_Fc_conj T
              (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)
            have h1 : starRingEnd ℂ (((-lam₁ : ℝ) : ℂ)
                  + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)
                = (((-lam₁ : ℝ) : ℂ) + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I) := by
              rw [map_add, map_mul, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
                starRingEnd_apply, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
              push_cast
              ring
            rw [h1] at h
            rw [h, starRingEnd_apply, Complex.star_def]
            exact Complex.conj_re _
          by_cases hs2 : |γ₂ - γ₃| ≤ δ / 2
          · have hA1 := hA lam₁ ((γ₂ - γ₃) * L) hl1nn hl16
            have hmul : L * (T.Fc (((-lam₁ : ℝ) : ℂ)
                  + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
                - 2 * (L * (T.Fc ((((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re)
                ≤ L * (T.f 0 / 6) := by
              have h := mul_le_mul_of_nonneg_left hA1 hlogq.le
              linarith only [h]
            have hb2 := hbPi23s hzPi hs2
            simp only [Work.ZeroFreeTables.Ksum] at hb2
            have heven' := congrArg (HMul.hMul L) heven
            linarith only [hbT1i23 h2r, heven', hb2, hmul, hgroupRing]
          · have hbig := hbigOf (γ₂ - γ₃) (lt_of_not_ge hs2)
            have hbig' : 200 ≤ |(γ₃ - γ₂) * L| := by
              rw [show (γ₃ - γ₂) * L = -((γ₂ - γ₃) * L) by ring, abs_neg]
              exact hbig
            have hB1 := hB lam₁ ((γ₃ - γ₂) * L) hl1nn hl16 hbig'
            have hB1L : L * (T.Fc (((-lam₁ : ℝ) : ℂ)
                  + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I)).re
                ≤ L * (T.f 0 / 6) := mul_le_mul_of_nonneg_left hB1 hlogq.le
            linarith [hbT1i23 h2r, hbPi23g, hB1L, hgroupRing]
        simp only [Work.ZeroFreeTables.Ksum] at hg3
        linarith [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hg1, hg3,
          hbT12i3g (h3not h2r), hbTi123, hmainRing]
      · linarith [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hg1,
          hbPi23g, hbT12i3g h3r, hbT1i23g h2r, hbTi123, hmainRing]
  have hX : 0 ≤ T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
      + T.f 0 * (7/6 + 8 * ε') := by
    by_contra hneg
    push_neg at hneg
    have h2 : L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) < 0 := mul_neg_of_pos_of_neg hlogq hneg
    have h3 : L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) = L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁)
          - T.F (lam₃ - lam₁)) + T.f 0 * (7/6 + 8 * ε') * L := by ring
    linarith [hmain, h2, h3]
  rw [hlam₁, hlam₂, hlam₃] at hX
  exact hX

/-- **HB Lemma 10.3 at rectangle height `L` in the F2 case, `χ₁` complex and `ρ₁` real** —
the requested statement. -/
theorem Rect10_3RealF2Complex : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ρ₁.im = 0 → χ₁ ^ 2 ≠ 1 →
    Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
    χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u) →
    Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
    Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε →
    (χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ = χ₃ ∨ χ₁ * χ₃ = χ₂ ∨ χ₂ * χ₃ = χ₁) →
    6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε H hH
  set ε' : ℝ := min (ε / 1000000) (1 / 1000000) with hε'def
  have hε' : 0 < ε' := by
    rw [hε'def]; exact lt_min (by positivity) (by norm_num)
  have hε'1 : ε' ≤ ε / 1000000 := by rw [hε'def]; exact min_le_left _ _
  have hε'2 : ε' ≤ 1 / 1000000 := by rw [hε'def]; exact min_le_right _ _
  let T : Work.ZeroFreeTables.TestFn :=
    Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)
  have hTx₀ : T.x₀ = 7/3 := by
    rw [show T.x₀ = (2:ℝ) / ((6:ℝ)/7) from rfl]
    norm_num
  have hTf : T.f = Work.ZeroFreeTables.tf72f ((6:ℝ)/7) := rfl
  have hTFc : T.Fc = Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) := rfl
  have hTf0 : T.f 0 = 32/35 := by
    rw [hTf, Work.ZeroFreeTables.tf72f_at_zero ((6:ℝ)/7) (by norm_num)]
    norm_num
  have hTF0 : T.F 0 = 8/9 := by
    show (T.Fc ((0:ℝ):ℂ)).re = 8/9
    rw [hTFc]
    exact Work.ZeroFreeTables.tf72Fc_zero_re ((6:ℝ)/7) (by norm_num)
  have hTF6 : T.F (-(6/7)) = 8/5 := by
    show (T.Fc (((-((6:ℝ)/7) : ℝ)) : ℂ)).re = 8/5
    rw [hTFc]
    exact Work.ZeroFreeTables.tf72Fc_neglam_re ((6:ℝ)/7) (by norm_num)
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hA : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 →
      (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re
        - 2 * (T.Fc ((m : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a m ha ha2
    rw [hTFc, hTf0]
    have h := Work.OffAxis.TF72Num103a a m ha ha2
    linarith
  have hB : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
      (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a m ha ha2 hm
    rw [hTFc, hTf0]
    have h := Work.OffAxis.TF72Num103b a m ha ha2 hm
    have h315 : (16:ℝ)/315 ≤ 16/105 := by norm_num
    linarith [(abs_le.mp h).2]
  have hP : ∃ qP : ℕ, ∀ q : ℕ, qP ≤ q → ∀ [NeZero q] (s : ℂ),
      |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
      |s.im| ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) s (1 : DirichletCharacter ℂ q)
        ≤ Real.log (q : ℝ) *
            (∫ t in (0:ℝ)..T.x₀,
              Complex.exp (-(((s - 1) * ((Real.log (q : ℝ) : ℂ)) * (t : ℂ))))
                * ((T.f t : ℝ) : ℂ)).re
          + T.f 0 * ε' * Real.log (q : ℝ) := by
    obtain ⟨q₀, hq₀⟩ := principalShiftMain_aux T.x₀ B T.x₀_pos hB0
      T.f_cont T.f_supp T.f_diff hBnd ε' hε' T.f0_pos
    exact ⟨q₀, fun q hq _ s hs1 hs2 => hq₀ hq s hs1 hs2⟩
  obtain ⟨qeng, hqeng⟩ := rect103Engine T ε' hε' hP hA hB H hH
  -- the endgame
  have hs0 : 0 ≤ 8 * ε' * T.f 0 := by positivity
  have hse : 8 * ε' * T.f 0 ≤ ε / 10000 := by
    rw [hTf0]
    have h1 : ε' * 8 * (32/35) ≤ (ε / 1000000) * 8 * (32/35) := by
      linarith only [hε'1, hε]
    linarith only [hε'1, hε, hε']
  have hs83 : 8 * ε' * T.f 0 < 83/9000 := by
    rw [hTf0]
    linarith only [hε'2, hε']
  have hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + 8 * ε' * T.f 0 →
        l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
    intro l h0 hl hineq
    have e1 : T.F (-(6/7)) = ∫ t in (0:ℝ)..(7/3),
        Real.exp ((6/7:ℝ)*t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [← hTx₀, TestFn_F_neg_eq_integral', hTf]
    have e2 : T.F (-l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (l*t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [← hTx₀, TestFn_F_neg_eq_integral', hTf]
    have e3 : T.F 0 = ∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [← hTx₀, TestFn_F_eq_integral T 0, hTf]
      simp
    have e4 : T.F (6/7 - l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (-((6/7-l)*t)) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [← hTx₀, TestFn_F_eq_integral T (6/7 - l), hTf]
    rw [e1, e2, e3, e4] at hineq
    exact Work.OffAxis.MomentStep103 ε (8 * ε' * T.f 0) hε hs0 hse l h0 hl hineq
  refine ⟨qeng, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him0 hsq1 hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hmin2 hmin3 hlam23 hlam3 hcases
  have hqeng' : qeng ≤ q := by omega
  have hl1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    lamOf_nonneg_of_zeroMult_aux hR.1.2.1
  have hl13 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₃ :=
    hR.2 χ₃ ρ₃ ⟨hZ3.1, hZ3.2.1, le_trans hZ3.2.2 (by linarith [hH])⟩
  have hl36 : Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 := by linarith [hlam3, hε]
  have heng := fun (χ₁' χ₂' χ₃' : DirichletCharacter ℂ q) (ρ₁' ρ₂' ρ₃' : ℂ)
      (hR' : Work.ZeroFreeTables.IsRectMin H χ₁' ρ₁') (him : ρ₁'.im = 0)
      (hsq : χ₁' ^ 2 ≠ 1) (hZ2' : Work.ZeroFreeTables.IsZAt H χ₂' ρ₂')
      (hZ3' : Work.ZeroFreeTables.IsZAt H χ₃' ρ₃')
      (hn21 : χ₂' ≠ χ₁') (hn2i : χ₂' ≠ χ₁'⁻¹) (hn31 : χ₃' ≠ χ₁') (hn3i : χ₃' ≠ χ₁'⁻¹)
      (hn32 : χ₃' ≠ χ₂') (hn3ii : χ₃' ≠ χ₂'⁻¹)
      (hm2 : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt H χ u →
        χ ≠ χ₁' → χ ≠ χ₁'⁻¹ → Work.LinnikContract.lamOf q ρ₂' ≤ Work.LinnikContract.lamOf q u)
      (hm3 : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt H χ u →
        χ ≠ χ₁' → χ ≠ χ₁'⁻¹ → χ ≠ χ₂' → χ ≠ χ₂'⁻¹ →
          Work.LinnikContract.lamOf q ρ₃' ≤ Work.LinnikContract.lamOf q u)
      (hl23 : Work.LinnikContract.lamOf q ρ₂' ≤ Work.LinnikContract.lamOf q ρ₃')
      (hl3' : Work.LinnikContract.lamOf q ρ₃' ≤ 6/7 - ε)
      (hprod : χ₁' * χ₂' * χ₃' = 1) =>
      hqeng q hqeng' χ₁' χ₂' χ₃' ρ₁' ρ₂' ρ₃' hR' him hsq hZ2' hZ3' hn21 hn2i hn31 hn3i
        hn32 hn3ii hm2 hm3 hl23 (by linarith [hl3', hε]) hprod
  have h106 : T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0
      - T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
      - T.F (Work.LinnikContract.lamOf q ρ₃ - Work.LinnikContract.lamOf q ρ₁)
      + T.f 0 * (7/6 + 8 * ε') ≥ 0 := by
    rcases hcases with h123 | h12 | h13 | h23
    · exact heng χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him0 hsq1 hZ2 hZ3 hne21 hne2i hne31 hne3i hne32
        hne3ii hmin2 hmin3 hlam23 hlam3 h123
    · -- `χ₁χ₂ = χ₃`: conjugate the third pair
      have hne3i' : χ₃⁻¹ ≠ χ₁ := fun hh => hne3i (by
        calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
          _ = χ₁⁻¹ := by rw [hh])
      have hne31' : χ₃⁻¹ ≠ χ₁⁻¹ := fun hh => hne31 (by
        calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
          _ = (χ₁⁻¹)⁻¹ := by rw [hh]
          _ = χ₁ := inv_inv χ₁)
      have hne3ii' : χ₃⁻¹ ≠ χ₂ := fun hh => hne3ii (by
        calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
          _ = χ₂⁻¹ := by rw [hh])
      have hne32' : χ₃⁻¹ ≠ χ₂⁻¹ := fun hh => hne32 (by
        calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
          _ = (χ₂⁻¹)⁻¹ := by rw [hh]
          _ = χ₂ := inv_inv χ₂)
      have h := heng χ₁ χ₂ χ₃⁻¹ ρ₁ ρ₂ (starRingEnd ℂ ρ₃) hR him0 hsq1 hZ2
        (IsZAt_inv_conj hZ3) hne21 hne2i hne3i' hne31' hne3ii' hne32'
        (fun χ u hu h1 h2 => hmin2 χ u hu h1 h2)
        (fun χ u hu h1 h2 h3 h4 => by
          rw [lamOf_star]; exact hmin3 χ u hu h1 h2 h3 h4)
        (by rw [lamOf_star]; exact hlam23) (by rw [lamOf_star]; exact hlam3)
        (by rw [h12, mul_inv_cancel])
      simpa only [lamOf_star] using h
    · -- `χ₁χ₃ = χ₂`: conjugate the second pair
      have hne2i' : χ₂⁻¹ ≠ χ₁ := fun hh => hne2i (by
        calc χ₂ = (χ₂⁻¹)⁻¹ := (inv_inv χ₂).symm
          _ = χ₁⁻¹ := by rw [hh])
      have hne21' : χ₂⁻¹ ≠ χ₁⁻¹ := fun hh => hne21 (by
        calc χ₂ = (χ₂⁻¹)⁻¹ := (inv_inv χ₂).symm
          _ = (χ₁⁻¹)⁻¹ := by rw [hh]
          _ = χ₁ := inv_inv χ₁)
      have hne32' : χ₃ ≠ χ₂⁻¹ := hne3ii
      have hne3ii' : χ₃ ≠ (χ₂⁻¹)⁻¹ := fun hh => hne32 (by
        calc χ₃ = (χ₂⁻¹)⁻¹ := hh
          _ = χ₂ := inv_inv χ₂)
      have hprod' : χ₁ * χ₂⁻¹ * χ₃ = 1 := by
        have h7 : χ₁ * χ₂⁻¹ * χ₃ = (χ₁ * χ₃) * χ₂⁻¹ := by ac_rfl
        rw [h7, h13, mul_inv_cancel]
      have h := heng χ₁ χ₂⁻¹ χ₃ ρ₁ (starRingEnd ℂ ρ₂) ρ₃ hR him0 hsq1
        (IsZAt_inv_conj hZ2) hZ3 hne2i' hne21' hne31 hne3i hne32' hne3ii'
        (fun χ u hu h1 h2 => by rw [lamOf_star]; exact hmin2 χ u hu h1 h2)
        (fun χ u hu h1 h2 h3 h4 =>
          hmin3 χ u hu h1 h2 (fun hh => h4 (by rw [hh, inv_inv])) h3)
        (by rw [lamOf_star]; exact hlam23) hlam3 hprod'
      simpa only [lamOf_star] using h
    · -- `χ₂χ₃ = χ₁`: conjugate the first pair
      have hsq' : χ₁⁻¹ ^ 2 ≠ 1 := by
        intro hh
        apply hsq1
        calc χ₁ ^ 2 = (χ₁⁻¹ ^ 2)⁻¹ := by rw [inv_pow, inv_inv]
          _ = 1⁻¹ := by rw [hh]
          _ = 1 := inv_one
      have hne21' : χ₂ ≠ χ₁⁻¹⁻¹ := fun hh => hne21 (by rw [hh, inv_inv])
      have hne31' : χ₃ ≠ χ₁⁻¹⁻¹ := fun hh => hne31 (by rw [hh, inv_inv])
      have hprod' : χ₁⁻¹ * χ₂ * χ₃ = 1 := by
        rw [mul_assoc, h23, inv_mul_cancel]
      exact heng χ₁⁻¹ χ₂ χ₃ ρ₁ ρ₂ ρ₃ (IsRectMin_inv hR him0) him0 hsq' hZ2 hZ3
        hne2i hne21' hne3i hne31' hne32 hne3ii
        (fun χ u hu h1 h2 => hmin2 χ u hu (fun hh => h2 (by rw [hh, inv_inv])) h1)
        (fun χ u hu h1 h2 h3 h4 =>
          hmin3 χ u hu (fun hh => h2 (by rw [hh, inv_inv])) h1 h3 h4)
        hlam23 hlam3 hprod'
  have hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-(6/7)) := by
    rw [hTf0, hTF0, hTF6]; norm_num
  exact Work.OffAxis.rect10_3_endgame_clean T ε' ε (8 * ε' * T.f 0)
    (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₂)
    (Work.LinnikContract.lamOf q ρ₃) hε hTx₀ hTf hTF0 hTF6
    hL75 hs0 hse (le_refl _) hs83 hmom
    (fun l h0 hle => by
      have h := Work.OffAxis.tf72f_refute_quant_clean T hTx₀ hTf hTF0 hTF6 l h0 hle
      linarith [h]) h106 hl1nn hl13 hlam23 hl36

end

end Work.OffAxis
