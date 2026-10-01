/-
# ZeroFreeTables — HBRepZero84_proof

**`Work.ZeroFreeTables.HBRepZero84`**: if the exceptional real zero `ρ₁` of a real character `χ₁`
mod `q` is *multiple* (`2 ≤ zeroMult χ₁ ρ₁`) then `λ₁ ≥ 1.294` for all large `q`.  This is the
repeated-zero case of Heath-Brown's §6/§8 analysis (Lemma 8.2, whose sharp constant is `2.427`),
used in `HB84Assembly` to make the multiplicity clause of `Lam0Bound` vacuous.

Route.  For a test function `f` satisfying HB's Conditions 1–2, write
`F(z) = ∫₀^{x₀} e^{-zt} f(t) dt`, `λ₁ = (1-β₁) log q`.  Three ingredients, all proved in the
workspace, give the repeated-zero inequality

  `0 ≤ 2F(-λ₁) - 4F(0) + f(0)(2c + 3ε)`:                              (`hb6RepeatedWindow`)

* the §6 positivity `K(β₁,χ₀) + K(β₁,χ₁) + K(β₁+iγ,χ₁) + K(β₁+iγ,χ₀) ≥ 0`
  (`Ksum_positivity_real`) at `γ = 0`, so that the two `χ₁`-sums coincide;
* the bound `K(β₁,χ₁) ≤ -L·(window sum) + f(0)(c+ε)L` (`lemma5_2_of_logDeriv_bound_phi_imprim`)
  together with the *multiplicity* of the window sum at `β₁` (`winSum_two_mul`: the window carries
  the zero `β₁` twice), and `K(β₁,χ₀) ≤ L·F(-λ₁) + f(0)εL` (`Ksum_principal_le_complex`);
* HB Lemma 3.1/Lemma 5.2 for real characters with the window radius `δ` fixed in advance
  (`l52HypRealFixed`).

With the triangle test function `f(t) = max (x₀ - t) 0` of support `x₀ = 10/13` (Condition 2 is
`triangle_hFnn`; `F(0) = x₀²/2`, `f(0) = x₀`, and `F(-13/10) = (e - 2)·100/169` by
`integral_exp_mul_sub`) and `ε = 1/1000`, `c = 1/6 + 10⁻⁶`, the inequality reads

  `0 ≤ 2·(e-2)·100/169 - 4·50/169 + (10/13)(1/3 + 2·10⁻⁶ + 3/1000) ≈ -0.075 < 0`

whenever `λ₁ ≤ 13/10`: contradiction.  Hence `λ₁ > 1.294`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.winSumTwoMul
import Submission.Work.ZeroFreeTables.l52HypRealFixed
import Submission.Work.NumberTheory.Linnik.scratch_l64
import Submission.Work.LinnikAreas.triangle_hFnn
import Submission.Work.LinnikAreas.DhRepel.integral_exp_mul_sub
import Submission.Work.LinnikAreas.DhRepel.integral_mul_max_sub_eq
import Submission.Work.LinnikAreas.DhRepel.integral_sub_self
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

open DirichletCharacter Complex Metric Filter
open scoped BigOperators

namespace Work.ZeroFreeTables

theorem hb6RepeatedWindow {x₀ B c ε δ : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ : ℝ} (hβ₁le : β₁ ≤ 1)
        (hpt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hwin : 2 * (∫ t in (0:ℝ)..x₀, f t) ≤
            Commons.NumberTheory.Linnik.winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β₁ : ℂ))
        (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
          - 4 * (∫ t in (0:ℝ)..x₀, f t)
          + f 0 * (2 * c + 3 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn
  obtain ⟨q₀p, hq₀p⟩ := (Commons.NumberTheory.Linnik.Ksum_principal_le_complex x₀ B hx₀ hB)
    hcont hsupp hf2 hBnd (by positivity : (0:ℝ) < ε/2) hf0
  obtain ⟨q₀χ, hq₀χ⟩ := (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨max (max q₀p q₀χ) 6, ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ hβ₁le hpt hwin H
  have hqp : q₀p ≤ q := by omega
  have hqχ : q₀χ ≤ q := by omega
  have hlogq : (0 : ℝ) < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := le_of_lt hlogq
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < q))]
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 3 ≤ q)
    linarith [Real.exp_one_lt_three]
  have Hraw : ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
      (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
        ≤ (c + ε/4) * Real.log (q : ℝ) := H
  have hram : |β₁ - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    simpa only [abs_sub_comm] using hpt
  have hlo : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ β₁ := by
    have h : 1 - β₁ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := (abs_le.mp hpt).2
    linarith
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hintF : ∀ z : ℂ, IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)) MeasureTheory.volume (0:ℝ) x₀ := by
    intro z
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx₀.le]
    have h1 : Continuous (fun t : ℝ => Complex.exp (-(z * (t : ℂ)))) :=
      Complex.continuous_exp.comp (((continuous_const : Continuous fun _ : ℝ => z).mul
        Complex.continuous_ofReal).neg)
    have h2 : ContinuousOn (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Icc 0 x₀) :=
      Complex.continuous_ofReal.comp_continuousOn (hcont.mono Set.Icc_subset_Ici_self)
    exact h1.continuousOn.mul h2
  -- (6.13) bound for the χ-term at `s = β₁`, using the L52 hypothesis
  have hbχ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re) * f (Real.log n / Real.log (q : ℝ)))
      ≤ -(Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + ε) * Real.log (q : ℝ) := by
    have h := hq₀χ hqχ χ hχ Hraw (β₁ : ℂ)
      (by simp only [Complex.ofReal_re]; exact hram)
      (by simp only [Complex.ofReal_im, abs_zero]; linarith [hlogq])
      (by simp only [Complex.ofReal_re]; exact hlo)
    have h2 : -(Real.log (q : ℝ)) *
          (Commons.NumberTheory.Linnik.winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β₁ : ℂ))
        ≤ -(Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t)) :=
      mul_le_mul_of_nonpos_left hwin (by linarith)
    rw [Commons.NumberTheory.Linnik.winSum] at h2
    linarith only [h, h2]
  -- (6.9) bound for the principal term at `s = β₁`
  have hAeq : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β₁ : ℂ)) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      = (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t) := by
    rw [Commons.NumberTheory.Linnik.re_laplace_eq (hintF (((β₁ : ℂ) - 1) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : (((β₁ : ℂ) - 1)).im = 0 := by simp
    have hr : (((β₁ : ℂ) - 1)).re = β₁ - 1 := by simp
    rw [Commons.NumberTheory.Linnik.re_mul_log ((β₁ : ℂ) - 1) q,
      Commons.NumberTheory.Linnik.im_mul_log ((β₁ : ℂ) - 1) q, hr, ha]
    simp only [zero_mul, Real.cos_zero, mul_one]
    congr 1
    ring
  have hp : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀,
          Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
        + f 0 * (ε/2) * Real.log (q : ℝ) := by
    have h := hq₀p hqp (β := β₁) (γ := 0) hram (by simp only [abs_zero]; exact hLnn)
    have h' : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
        ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β₁ : ℂ)) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
              ((f t : ℝ) : ℂ)).re + f 0 * (ε/2) * Real.log (q : ℝ) := by
      simpa using h
    rw [hAeq] at h'
    exact h'
  -- positivity (6.11) at `β₁`, `γ = 0`
  have hpos := Commons.NumberTheory.Linnik.Ksum_positivity_real (q := q) (f := f) (β := β₁) (γ := 0)
    hfnn hx₀ hlogq hsupp χ hreal
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hpos
  have h0 : 0 ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re) * f (Real.log n / Real.log (q : ℝ))) := by
    linarith only [hpos]
  have hcomb : 0 ≤ (Real.log (q : ℝ)) *
      ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (c + 3 * ε/2)) := by
    have hfac : (Real.log (q : ℝ)) *
        ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
          - 2 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 3 * ε/2))
        = (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
          + f 0 * (ε/2) * Real.log (q : ℝ)
          + (-(Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
              + f 0 * (c + ε) * Real.log (q : ℝ)) := by ring
    rw [hfac]
    linarith only [h0, hp, hbχ]
  have hres := (mul_nonneg_iff_of_pos_left hlogq).mp hcomb
  linarith only [hres]

/-! ## The triangle test function -/

theorem tent_contDiffOn (X : ℝ) : ContDiffOn ℝ 2 (fun t : ℝ => max (X - t) 0) (Set.Ioo 0 X) := by
  have h1 : ContDiffOn ℝ 2 (fun t : ℝ => X - t) (Set.Ioo 0 X) := by fun_prop
  refine h1.congr ?_
  intro t ht
  rw [Set.mem_Ioo] at ht
  exact max_eq_left (by linarith [ht.2])

theorem tent_iteratedDeriv_two (X t : ℝ) (ht : t ∈ Set.Ioo 0 X) :
    iteratedDeriv 2 (fun s : ℝ => max (X - s) 0) t = 0 := by
  have hs : Set.Ioo (0:ℝ) X ∈ nhds t := IsOpen.mem_nhds isOpen_Ioo ht
  have hev : (fun s : ℝ => max (X - s) 0) =ᶠ[nhds t] (fun s : ℝ => X - s) := by
    filter_upwards [hs] with s hs'
    rw [Set.mem_Ioo] at hs'
    exact max_eq_left (by linarith [hs'.2])
  have hlin : iteratedDeriv 2 (fun s : ℝ => X - s) t = 0 := by
    rw [show (fun s : ℝ => X - s) = (fun s : ℝ => X + (-(id s))) from rfl,
      iteratedDeriv_const_add (f := fun s : ℝ => -(id s)) (c := X) (show (0:ℕ) < 2 by norm_num)]
    rw [iteratedDeriv_fun_neg, iteratedDeriv_id]
    norm_num
  rw [hev.iteratedDeriv_eq]
  exact hlin

open Work.LinnikContract in
theorem HBRepZero84_proof : Work.ZeroFreeTables.HBRepZero84 := by
  obtain ⟨δ₀, hδ₀0, hδ₀1, Q₀, hQ₀⟩ := l52HypRealFixed
  -- the triangle test function of support `X = 10/13`
  set X : ℝ := 10/13 with hXdef
  have hXpos : 0 < X := by norm_num [hXdef]
  have hX13 : X = 10/13 := hXdef
  obtain ⟨Q₁, hQ₁⟩ := hb6RepeatedWindow (x₀ := X) (B := 0) (c := 1/6 + 1/1000000)
    (ε := 1/1000) (δ := δ₀) hXpos le_rfl (by norm_num) hδ₀0 hδ₀1
    (by fun_prop)
    (fun t ht => max_eq_right (by linarith))
    (tent_contDiffOn X)
    (fun t ht => by rw [tent_iteratedDeriv_two X t ht]; simp)
    (by
      have h : max (X - 0) 0 = X := by
        rw [max_eq_left (by linarith [hXpos])]
        ring
      rw [h]; exact hXpos)
    (fun t => le_max_right _ _)
    (fun z hz => Work.LinnikAreas.triangle_hFnn hXpos z hz)
  -- the numerical data of the triangle
  have hF0val : (∫ t in (0:ℝ)..X, max (X - t) 0) = X^2/2 := by
    have h := Work.LinnikAreas.DhRepel.integral_mul_max_sub_eq (fun _ : ℝ => (1:ℝ)) X hXpos.le
    have h2 : (∫ t in (0:ℝ)..X, (1:ℝ) * (X - t)) = X^2/2 := by
      simpa using Work.LinnikAreas.DhRepel.integral_sub_self X
    simpa using h.trans h2
  have hFlamval : (∫ t in (0:ℝ)..X, Real.exp ((13/10) * t) * max (X - t) 0)
      = (Real.exp 1 - 2) * 100/169 := by
    have h1 := Work.LinnikAreas.DhRepel.integral_mul_max_sub_eq
      (fun t : ℝ => Real.exp ((13/10) * t)) X hXpos.le
    rw [h1, hX13]
    rw [Work.LinnikAreas.DhRepel.integral_exp_mul_sub (13/10) (10/13) (by norm_num) (by norm_num)]
    have h2 : (13:ℝ)/10 * (10/13) = 1 := by norm_num
    rw [h2]
    field_simp
    ring
  obtain ⟨Qbig, hQbig⟩ : ∃ Qbig : ℕ, ∀ q : ℕ, Qbig ≤ q → Q₀ ≤ q ∧ Q₁ ≤ q ∧
      3 ≤ q ∧ max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3) ≤ Real.log (q:ℝ) := by
    refine ⟨max (max Q₀ Q₁) (max 6 (Nat.ceil (Real.exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3))) + 3)), ?_⟩
    intro q hq
    have h1 : Q₀ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
    have h2 : Q₁ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
    have h3 : 3 ≤ q := by
      have h36 : 6 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
      omega
    refine ⟨h1, h2, h3, ?_⟩
    have hceil : Nat.ceil (Real.exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3))) + 3 ≤ q :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
    have hexp_le : Real.exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3)) ≤ (q:ℝ) := by
      have h4 : Real.exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3))
          ≤ (Nat.ceil (Real.exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3))) : ℝ) := Nat.le_ceil _
      have h5 : ((Nat.ceil (Real.exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3))) : ℕ) : ℝ) ≤ (q:ℝ) := by
        have : Nat.ceil (Real.exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3))) ≤ q := by omega
        exact_mod_cast this
      linarith
    rw [← Real.log_exp (max ((1294:ℝ)/(1000*δ₀)) (Real.exp 3))]
    exact Real.log_le_log (Real.exp_pos _) hexp_le
  refine ⟨Qbig, ?_⟩
  intro q hq hqne χ₁ ρ₁ hwide hsq him hmult
  obtain ⟨hqQ₀, hqQ₁, hq3, hqlog⟩ := hQbig q hq
  have hmin : IsMin1 χ₁ ρ₁ := hwide.1
  have hZ : IsZ χ₁ ρ₁ := hmin.1
  have hχ1 : χ₁ ≠ 1 := hZ.1
  have hzm : zeroMult χ₁ ρ₁ ≠ 0 := hZ.2.1
  have hlogq : (0:ℝ) < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  haveI : NeZero χ₁.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₁⟩
  have hχ' : χ₁.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ1
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h]
    exact DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level
  have hstrip : 0 < ρ₁.re ∧ ρ₁.re < 1 := by
    have hz0 : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ₁ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
    exact Commons.NumberTheory.DirichletCharacter.zerosInStrip χ₁.primitiveCharacter hχ'
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) ρ₁ hz0
  set β₁ : ℝ := ρ₁.re with hβ₁def
  have hβ₁01 : 0 < β₁ ∧ β₁ < 1 := hstrip
  have hρ₁ : ρ₁ = (β₁ : ℂ) := by
    apply Complex.ext
    · simp [β₁]
    · simpa [β₁] using him
  have hlamEq : lamOf q ρ₁ = (1 - β₁) * Real.log (q:ℝ) := by
    rw [hρ₁, lamOf]; simp
  by_contra hcon
  push_neg at hcon
  have hlt1 : (1 - β₁) * Real.log (q:ℝ) < 1294/1000 := by rw [← hlamEq]; exact hcon
  have hβ₁δ : 1 - β₁ ≤ δ₀ := by
    have h2 : 1 - β₁ < (1294/1000) / Real.log (q:ℝ) := (lt_div_iff₀ hlogq).mpr hlt1
    have h3 : (1294/1000) / Real.log (q:ℝ) ≤ δ₀ := by
      rw [div_le_iff₀ hlogq]
      have h4 : (1294:ℝ)/(1000*δ₀) * δ₀ = 1294/1000 := by field_simp
      have h5 : (1294:ℝ)/(1000*δ₀) ≤ Real.log (q:ℝ) := le_trans (le_max_left _ _) hqlog
      nlinarith [h5, hδ₀0, h4]
    linarith
  have hpt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h2 : 1 - β₁ ≤ (1294/1000) / Real.log (q:ℝ) := le_of_lt ((lt_div_iff₀ hlogq).mpr hlt1)
    have hsqrt3' : (1294:ℝ)/1000 ≤ Real.sqrt 3 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1294/1000)]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hexp3 : Real.exp 3 ≤ Real.log (q:ℝ) := le_trans (le_max_right _ _) hqlog
    have hloglog : 3 ≤ Real.log (Real.log (q:ℝ)) := by
      have := Real.log_le_log (Real.exp_pos 3) hexp3
      rwa [Real.log_exp] at this
    have hsq : (1294:ℝ)/1000 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) :=
      le_trans hsqrt3' (Real.sqrt_le_sqrt hloglog)
    have hdiv : (1294/1000) / Real.log (q:ℝ) ≤
        Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right hsq (le_of_lt hlogq)
    rw [abs_of_nonneg (by linarith [hβ₁01.2])]
    linarith
  have hmem2 : (β₁ : ℂ) ∈ Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    simp only [Complex.ofReal_im, abs_zero, zero_add]
    exact ⟨by linarith [hβ₁01.1], by linarith [hβ₁01.2]⟩
  have hcoeff : (2 : ℤ) ≤ MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2)) (β₁ : ℂ) := by
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
    have hcast := Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem2
    rw [hcast, ← hρ₁]
    have : (2:ℤ) ≤ ((zeroMult χ₁ ρ₁ : ℕ) : ℤ) := by exact_mod_cast hmult
    simpa [zeroMult] using this
  have hwinβ : ‖(1:ℂ) - (β₁ : ℂ)‖ ≤ δ₀ := by
    have h1 : (1:ℂ) - (β₁ : ℂ) = ((1 - β₁ : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hβ₁01.2])]
    exact hβ₁δ
  have hzeroW : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) - u‖ ≤ δ₀ → u.re ≤ β₁ := by
    intro u hdiv hw
    have hu_mem : u ∈ Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2) :=
      Commons.Analysis.Complex.divisor_mem_of_ne_zero hdiv
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
    have hzmult : zeroMult χ₁ u ≠ 0 := by
      have hcast := Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu_mem
      have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) u ≠ 0 := by
        intro h0
        exact hdiv (by rw [hcast, h0]; rfl)
      simpa [zeroMult] using hnat
    have himu : |u.im| ≤ 10 := by
      have h1 : |(1 - u).im| ≤ ‖(1:ℂ) - u‖ := Complex.abs_im_le_norm (1 - u)
      have h2 : (1 - u).im = -u.im := by simp
      rw [h2, abs_neg] at h1
      linarith [h1, hw, hδ₀1]
    have hle := hwide.2 χ₁ u hχ1 hzmult himu
    have hle' : (1 - β₁) * Real.log (q:ℝ) ≤ (1 - u.re) * Real.log (q:ℝ) := by
      have h := hle
      rw [hlamEq, lamOf] at h
      exact h
    have h2 : 1 - β₁ ≤ 1 - u.re := (mul_le_mul_iff_of_pos_right hlogq).mp hle'
    linarith
  have hwin : 2 * (∫ t in (0:ℝ)..X, max (X - t) 0) ≤
      Commons.NumberTheory.Linnik.winSum χ₁.primitiveCharacter (fun t => max (X - t) 0) X (Real.log (q:ℝ)) δ₀ (β₁:ℂ) :=
    winSumTwoMul χ₁.primitiveCharacter hχ' (le_of_lt hlogq) hδ₀1
      (fun z hz => Work.LinnikAreas.triangle_hFnn hXpos z hz) hwinβ hcoeff hzeroW
  have hsq' : χ₁ * χ₁ = 1 := by rw [← pow_two]; exact hsq
  have hH : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/6 + 1/1000000) (1/1000) δ₀ :=
    hQ₀ q hqQ₀ χ₁ hχ1 hsq (1/1000) (by norm_num) (by norm_num)
  have hR := hQ₁ hqQ₁ χ₁ hχ1 hsq' (le_of_lt hβ₁01.2) hpt hwin hH
  -- monotonicity of the Laplace transform in the scale
  have hmono : (∫ t in (0:ℝ)..X, Real.exp ((Real.log (q:ℝ) * (1 - β₁)) * t) * max (X - t) 0)
      ≤ (∫ t in (0:ℝ)..X, Real.exp ((13/10) * t) * max (X - t) 0) := by
    have h1 : Real.log (q:ℝ) * (1 - β₁) ≤ 13/10 := by
      have hlt : (1 - β₁) * Real.log (q:ℝ) < 1294/1000 := by rw [← hlamEq]; exact hcon
      linarith
    have h2 : ∀ t ∈ Set.Icc (0:ℝ) X, Real.exp ((Real.log (q:ℝ) * (1 - β₁)) * t) ≤ Real.exp ((13/10) * t) := by
      intro t ht
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right h1 ht.1
    have hint1 : IntervalIntegrable
        (fun t : ℝ => Real.exp ((Real.log (q:ℝ) * (1 - β₁)) * t) * max (X - t) 0)
        MeasureTheory.volume 0 X :=
      (by fun_prop : Continuous fun t : ℝ => Real.exp ((Real.log (q:ℝ) * (1 - β₁)) * t) * max (X - t) 0).intervalIntegrable _ _
    have hint2 : IntervalIntegrable
        (fun t : ℝ => Real.exp ((13/10) * t) * max (X - t) 0)
        MeasureTheory.volume 0 X :=
      (by fun_prop : Continuous fun t : ℝ => Real.exp ((13/10) * t) * max (X - t) 0).intervalIntegrable _ _
    exact intervalIntegral.integral_mono_on hXpos.le hint1 hint2
      (fun t ht => mul_le_mul_of_nonneg_right (h2 t ht) (le_max_right _ _))
  have hR' : 0 ≤ 2 * (∫ t in (0:ℝ)..X, Real.exp ((13/10) * t) * max (X - t) 0)
      - 4 * (∫ t in (0:ℝ)..X, max (X - t) 0)
      + max (X - 0) 0 * (2 * (1/6 + 1/1000000) + 3 * (1/1000)) := by
    linarith only [hR, hmono]
  have harith : 2 * ((Real.exp 1 - 2) * 100/169) - 4 * (X^2/2)
      + max (X - 0) 0 * (2 * (1/6 + 1/1000000) + 3 * (1/1000)) < 0 := by
    rw [hX13]
    have hexp : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hval : max ((10:ℝ)/13 - 0) 0 = 10/13 := by norm_num
    rw [hval]
    nlinarith [hexp]
  linarith only [hR', hF0val, hFlamval, harith]

end Work.ZeroFreeTables
