import Mathlib
import Submission.Work.LinnikAreas2.thetaF_defs

noncomputable section
open Set

namespace Work.LinnikAreas2

/-! ## 0. Small exponential helpers -/

theorem thetaF_exp_lt_one {t : ℝ} (ht : t < 0) : Real.exp t < 1 := by
  calc Real.exp t < Real.exp 0 := Real.exp_lt_exp.mpr ht
    _ = 1 := Real.exp_zero

theorem thetaF_one_lt_exp {t : ℝ} (ht : 0 < t) : (1 : ℝ) < Real.exp t := by
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp t := Real.exp_lt_exp.mpr ht

theorem thetaF_one_div_lt {A B : ℝ} (hB : 0 < B) (hBA : B < A) : 1 / A < 1 / B :=
  (one_div_lt_one_div (lt_trans hB hBA) hB).mpr hBA

/-! ## 1. `β t = t/(e^t − 1)` is antitone on `(0,∞)` -/

theorem thetaF_beta_denom_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have h := thetaF_one_lt_exp ht
  linarith

theorem thetaF_beta_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt beta ((Real.exp t * (1 - t) - 1) / (Real.exp t - 1) ^ 2) t := by
  have hne : Real.exp t - 1 ≠ 0 := ne_of_gt (thetaF_beta_denom_pos ht)
  have h1 : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun y : ℝ => Real.exp y - 1) (Real.exp t) t := by
    have h := (Real.hasDerivAt_exp t).sub (hasDerivAt_const t (1 : ℝ))
    rw [sub_zero] at h
    exact h
  have h := h1.div h2 hne
  have hval : (1 * (Real.exp t - 1) - t * Real.exp t) / (Real.exp t - 1) ^ 2
      = (Real.exp t * (1 - t) - 1) / (Real.exp t - 1) ^ 2 := by ring
  rw [hval] at h
  rw [show beta = (fun y : ℝ => y / (Real.exp y - 1)) from rfl]
  exact h

theorem thetaF_beta_antitone : AntitoneOn beta (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn beta (Set.Ioi (0 : ℝ)) := by
    apply ContinuousOn.div
    · exact continuousOn_id
    · fun_prop
    · intro x hx; exact ne_of_gt (thetaF_beta_denom_pos hx)
  refine antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ)) hcont ?_ ?_
  · intro x hx
    rw [isOpen_Ioi.interior_eq] at hx
    exact ((thetaF_beta_hasDerivAt x hx).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [isOpen_Ioi.interior_eq] at hx
    rw [(thetaF_beta_hasDerivAt x hx).deriv]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    have hmul : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h1 : Real.exp x * (1 - x) ≤ 1 := by
      calc Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
            mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg x) (Real.exp_pos x).le
        _ = 1 := hmul
    linarith

theorem thetaF_beta_ge_exp_neg (t : ℝ) (ht : 0 < t) : Real.exp (-t) ≤ beta t := by
  rw [beta, le_div_iff₀ (thetaF_beta_denom_pos ht)]
  have hmul : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [mul_sub, hmul, mul_one]
  linarith [Real.one_sub_le_exp_neg t]

theorem thetaF_beta_le_one (t : ℝ) (ht : 0 < t) : beta t ≤ 1 := by
  rw [beta, div_le_one (thetaF_beta_denom_pos ht)]
  linarith [Real.add_one_le_exp t]

/-! ## 2. `Φ` is strictly antitone, positive near `0`, negative at `+∞` -/

theorem thetaF_Phi_strictAntiOn (σ A B : ℝ) (hB : 0 < B) (hBA : B < A) :
    StrictAntiOn (Phi σ A B) (Set.Ioi (0 : ℝ)) := by
  have hA : 0 < A := lt_trans hB hBA
  have hc : 0 < 1 / B - 1 / A := by
    have := thetaF_one_div_lt hB hBA; linarith
  intro x hx y hy hxy
  have hb : beta ((1 / B - 1 / A) * y) ≤ beta ((1 / B - 1 / A) * x) :=
    thetaF_beta_antitone (mul_pos hc hx) (mul_pos hc hy) (mul_lt_mul_of_pos_left hxy hc).le
  have hx' : Phi σ A B x = (σ - 1) - x / A + beta ((1 / B - 1 / A) * x) := by
    simp only [Phi, beta]
  have hy' : Phi σ A B y = (σ - 1) - y / A + beta ((1 / B - 1 / A) * y) := by
    simp only [Phi, beta]
  rw [hx', hy']
  have h2 : (σ - 1) - y / A < (σ - 1) - x / A := by
    have : x / A < y / A := div_lt_div_of_pos_right hxy hA
    linarith
  linarith [hb, h2]

theorem thetaF_Phi_pos_of_lt (σ A B : ℝ) (hσ : 0 < σ) (hB : 0 < B) (hBA : B < A) {x : ℝ}
    (hx : 0 < x) (hxB : x / B < σ) : 0 < Phi σ A B x := by
  have hA : 0 < A := lt_trans hB hBA
  have hc : 0 < 1 / B - 1 / A := by
    have := thetaF_one_div_lt hB hBA; linarith
  have hcx : 0 < (1 / B - 1 / A) * x := mul_pos hc hx
  have h1 : Real.exp (-((1 / B - 1 / A) * x)) ≤ beta ((1 / B - 1 / A) * x) :=
    thetaF_beta_ge_exp_neg _ hcx
  have h2 : 1 - (1 / B - 1 / A) * x ≤ Real.exp (-((1 / B - 1 / A) * x)) :=
    Real.one_sub_le_exp_neg _
  have hx' : Phi σ A B x = (σ - 1) - x / A + beta ((1 / B - 1 / A) * x) := by
    simp only [Phi, beta]
  have hkey : (σ - 1) - x / A + (1 - (1 / B - 1 / A) * x) ≤ Phi σ A B x := by
    rw [hx']; linarith
  have hval : (σ - 1) - x / A + (1 - (1 / B - 1 / A) * x) = σ - x / B := by
    field_simp <;> ring
  rw [hval] at hkey
  linarith

theorem thetaF_Phi_neg_of_gt (σ A B : ℝ) (hB : 0 < B) (hBA : B < A) {x : ℝ}
    (hx : 0 < x) (hxA : σ < x / A) : Phi σ A B x < 0 := by
  have hA : 0 < A := lt_trans hB hBA
  have hc : 0 < 1 / B - 1 / A := by
    have := thetaF_one_div_lt hB hBA; linarith
  have hcx : 0 < (1 / B - 1 / A) * x := mul_pos hc hx
  have h1 : beta ((1 / B - 1 / A) * x) ≤ 1 := thetaF_beta_le_one _ hcx
  have hx' : Phi σ A B x = (σ - 1) - x / A + beta ((1 / B - 1 / A) * x) := by
    simp only [Phi, beta]
  rw [hx']
  have hval : (σ - 1) - x / A + 1 = σ - x / A := by ring
  linarith

theorem thetaF_Phi_exists_zero (σ A B : ℝ) (hσ : 0 < σ) (hB : 0 < B) (hBA : B < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧
      (∀ x : ℝ, 0 < x → x < x₀ → 0 < Phi σ A B x) ∧
      (∀ x : ℝ, x₀ < x → Phi σ A B x < 0) := by
  have hA : 0 < A := lt_trans hB hBA
  have hanti := thetaF_Phi_strictAntiOn σ A B hB hBA
  have hxlpos : 0 < σ * B / 2 := by positivity
  have hxl : (σ * B / 2) / B < σ := by
    rw [div_lt_iff₀ hB]; nlinarith [hσ, hB]
  have hxhpos : 0 < σ * A + 1 := by positivity
  have hxh : σ < (σ * A + 1) / A := by
    rw [lt_div_iff₀ hA]; linarith
  have hPxl : 0 < Phi σ A B (σ * B / 2) := thetaF_Phi_pos_of_lt σ A B hσ hB hBA hxlpos hxl
  have hPxh : Phi σ A B (σ * A + 1) < 0 := thetaF_Phi_neg_of_gt σ A B hB hBA hxhpos hxh
  have hle : σ * B / 2 ≤ σ * A + 1 := by nlinarith [hA, hσ, hBA, hB]
  have hcont : ContinuousOn (Phi σ A B) (Set.Icc (σ * B / 2) (σ * A + 1)) := by
    have hc : 0 < 1 / B - 1 / A := by have := thetaF_one_div_lt hB hBA; linarith
    have hden : ∀ x ∈ Set.Icc (σ * B / 2) (σ * A + 1),
        Real.exp ((1 / B - 1 / A) * x) - 1 ≠ 0 := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hxlpos hx.1
      exact ne_of_gt (thetaF_beta_denom_pos (mul_pos hc hx0))
    have hnum : ContinuousOn (fun x : ℝ => (1 / B - 1 / A) * x)
        (Set.Icc (σ * B / 2) (σ * A + 1)) := by fun_prop
    have hdenc : ContinuousOn (fun x : ℝ => Real.exp ((1 / B - 1 / A) * x) - 1)
        (Set.Icc (σ * B / 2) (σ * A + 1)) := by fun_prop
    have hfrac : ContinuousOn
        (fun x : ℝ => (1 / B - 1 / A) * x / (Real.exp ((1 / B - 1 / A) * x) - 1))
        (Set.Icc (σ * B / 2) (σ * A + 1)) := hnum.div hdenc hden
    have hlin : ContinuousOn (fun x : ℝ => (σ - 1) - x / A)
        (Set.Icc (σ * B / 2) (σ * A + 1)) := by fun_prop
    change ContinuousOn
      (fun x : ℝ => (σ - 1) - x / A + (1 / B - 1 / A) * x / (Real.exp ((1 / B - 1 / A) * x) - 1))
      (Set.Icc (σ * B / 2) (σ * A + 1))
    exact hlin.add hfrac
  have hmem : (0 : ℝ) ∈ Set.Icc (Phi σ A B (σ * A + 1)) (Phi σ A B (σ * B / 2)) :=
    ⟨le_of_lt hPxh, le_of_lt hPxl⟩
  obtain ⟨x₀, hx₀mem, hx₀eq⟩ := (intermediate_value_Icc' hle hcont) hmem
  have hx₀pos : 0 < x₀ := lt_of_lt_of_le hxlpos hx₀mem.1
  refine ⟨x₀, hx₀pos, ?_, ?_⟩
  · intro x hx hxx₀
    have h := hanti hx hx₀pos hxx₀
    rw [hx₀eq] at h
    exact h
  · intro x hxx₀
    have hx0I : x₀ ∈ Set.Ioi (0 : ℝ) := hx₀pos
    have hxI : x ∈ Set.Ioi (0 : ℝ) := lt_trans hx₀pos hxx₀
    have h := hanti hx0I hxI hxx₀
    rw [hx₀eq] at h
    exact h

/-! ## 3. Derivative of `Lfun` and the identity `exp ∘ Lfun = gfun` -/

theorem thetaF_hasDerivAt_Lfun (σ A B : ℝ) (hB : 0 < B) (hBA : B < A) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (Lfun σ A B) (Phi σ A B x / x) x := by
  have hA : 0 < A := lt_trans hB hBA
  have hc : 0 < 1 / B - 1 / A := by have := thetaF_one_div_lt hB hBA; linarith
  have hcx : 0 < (1 / B - 1 / A) * x := mul_pos hc hx
  have hxne : x ≠ 0 := ne_of_gt hx
  have h1 : HasDerivAt (fun y : ℝ => (σ - 1) * Real.log y) ((σ - 1) * x⁻¹) x :=
    (Real.hasDerivAt_log hxne).const_mul (σ - 1)
  have h2 : HasDerivAt (fun y : ℝ => y / A) (1 / A) x := by
    simpa only [id_eq] using (hasDerivAt_id x).div_const A
  have h12 : HasDerivAt (fun y : ℝ => (σ - 1) * Real.log y - y / A)
      ((σ - 1) * x⁻¹ - 1 / A) x := h1.sub h2
  have hexp1 : HasDerivAt (fun y : ℝ => Real.exp (-((1 / B - 1 / A) * y)))
      (Real.exp (-((1 / B - 1 / A) * x)) * (-(1 / B - 1 / A))) x := by
    have hlin : HasDerivAt (fun y : ℝ => -((1 / B - 1 / A) * y)) (-(1 / B - 1 / A)) x := by
      have h := (hasDerivAt_id x).const_mul (-(1 / B - 1 / A) : ℝ)
      simpa only [id_eq, mul_one, neg_mul] using h
    exact hlin.exp
  have hg : HasDerivAt (fun y : ℝ => 1 - Real.exp (-((1 / B - 1 / A) * y)))
      (0 - Real.exp (-((1 / B - 1 / A) * x)) * (-(1 / B - 1 / A))) x :=
    (hasDerivAt_const x (1 : ℝ)).sub hexp1
  have hgne : (1 - Real.exp (-((1 / B - 1 / A) * x))) ≠ 0 := by
    have hlt : Real.exp (-((1 / B - 1 / A) * x)) < 1 :=
      thetaF_exp_lt_one (by linarith)
    linarith
  have h3 : HasDerivAt (fun y : ℝ => Real.log (1 - Real.exp (-((1 / B - 1 / A) * y))))
      ((0 - Real.exp (-((1 / B - 1 / A) * x)) * (-(1 / B - 1 / A))) /
        (1 - Real.exp (-((1 / B - 1 / A) * x)))) x := hg.log hgne
  have h123 : HasDerivAt
      (fun y : ℝ => (σ - 1) * Real.log y - y / A + Real.log (1 - Real.exp (-((1 / B - 1 / A) * y))))
      ((σ - 1) * x⁻¹ - 1 / A +
        (0 - Real.exp (-((1 / B - 1 / A) * x)) * (-(1 / B - 1 / A))) /
          (1 - Real.exp (-((1 / B - 1 / A) * x)))) x := h12.add h3
  have hfun : (fun y : ℝ =>
      (σ - 1) * Real.log y - y / A + Real.log (1 - Real.exp (-((1 / B - 1 / A) * y))))
      = Lfun σ A B := rfl
  rw [hfun] at h123
  have hval : (σ - 1) * x⁻¹ - 1 / A +
        (0 - Real.exp (-((1 / B - 1 / A) * x)) * (-(1 / B - 1 / A))) /
          (1 - Real.exp (-((1 / B - 1 / A) * x)))
      = Phi σ A B x / x := by
    have hEgt : (1 : ℝ) < Real.exp ((1 / B - 1 / A) * x) := thetaF_one_lt_exp hcx
    have hE1 : Real.exp ((1 / B - 1 / A) * x) - 1 ≠ 0 := by linarith
    have hfrac : Real.exp (-((1 / B - 1 / A) * x)) * (1 / B - 1 / A) /
          (1 - Real.exp (-((1 / B - 1 / A) * x)))
        = (1 / B - 1 / A) / (Real.exp ((1 / B - 1 / A) * x) - 1) := by
      rw [Real.exp_neg]
      field_simp <;> ring
    have hphidiv : Phi σ A B x / x
        = (σ - 1) * x⁻¹ - 1 / A + (1 / B - 1 / A) / (Real.exp ((1 / B - 1 / A) * x) - 1) := by
      simp only [Phi]
      field_simp <;> ring
    rw [hphidiv]
    have : (0 - Real.exp (-((1 / B - 1 / A) * x)) * (-(1 / B - 1 / A))) /
          (1 - Real.exp (-((1 / B - 1 / A) * x)))
        = Real.exp (-((1 / B - 1 / A) * x)) * (1 / B - 1 / A) /
            (1 - Real.exp (-((1 / B - 1 / A) * x))) := by ring
    rw [this, hfrac]
  rw [hval] at h123
  exact h123

theorem thetaF_exp_Lfun_eq_gfun (σ A B : ℝ) (hB : 0 < B) (hBA : B < A) (x : ℝ) (hx : 0 < x) :
    Real.exp (Lfun σ A B x) = gfun σ A B x := by
  have hA : 0 < A := lt_trans hB hBA
  have hc : 0 < 1 / B - 1 / A := by have := thetaF_one_div_lt hB hBA; linarith
  have hcx : 0 < (1 / B - 1 / A) * x := mul_pos hc hx
  have hargpos : 0 < 1 - Real.exp (-((1 / B - 1 / A) * x)) := by
    have hlt : Real.exp (-((1 / B - 1 / A) * x)) < 1 := thetaF_exp_lt_one (by linarith)
    linarith
  have hexp1 : Real.exp ((σ - 1) * Real.log x) = x ^ (σ - 1) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  have hexp2 : Real.exp (Real.log (1 - Real.exp (-((1 / B - 1 / A) * x))))
      = 1 - Real.exp (-((1 / B - 1 / A) * x)) := Real.exp_log hargpos
  have hkey : Real.exp (-(x / A)) * (1 - Real.exp (-((1 / B - 1 / A) * x)))
      = Real.exp (-(x / A)) - Real.exp (-(x / B)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  have hL : Lfun σ A B x
      = (σ - 1) * Real.log x + (-(x / A)) + Real.log (1 - Real.exp (-((1 / B - 1 / A) * x))) := by
    rw [Lfun]; ring
  rw [hL, Real.exp_add, Real.exp_add]
  rw [hexp1, hexp2]
  rw [mul_assoc, hkey]
  rfl

/-! ## 4. The main monotonicity theorem -/

theorem thetaF_monotone_seq {σ A B : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hB : 0 < B) (hBA : B < A) :
    ∃ K : ℕ,
      (∀ n : ℕ, n < K →
        (n:ℝ)^(σ-1) * (Real.exp (-((n:ℝ)/A)) - Real.exp (-((n:ℝ)/B)))
          ≤ ((n+1 : ℕ):ℝ)^(σ-1) * (Real.exp (-(((n+1 : ℕ):ℝ)/A)) - Real.exp (-(((n+1 : ℕ):ℝ)/B))))
      ∧ (∀ n : ℕ, K ≤ n →
        (((n+1 : ℕ):ℝ)^(σ-1) * (Real.exp (-(((n+1 : ℕ):ℝ)/A)) - Real.exp (-(((n+1 : ℕ):ℝ)/B)))
          ≤ (n:ℝ)^(σ-1) * (Real.exp (-((n:ℝ)/A)) - Real.exp (-((n:ℝ)/B))))) := by
  have hA : 0 < A := lt_trans hB hBA
  obtain ⟨x₀, hx₀pos, hx₀pos', hx₀neg'⟩ := thetaF_Phi_exists_zero σ A B hσ hB hBA
  have hLcont : ContinuousOn (Lfun σ A B) (Set.Ioi (0 : ℝ)) :=
    fun x hx => (thetaF_hasDerivAt_Lfun σ A B hB hBA x hx).continuousAt.continuousWithinAt
  have hFcont : ContinuousOn (fun x : ℝ => Real.exp (Lfun σ A B x)) (Set.Ioi (0 : ℝ)) :=
    Real.continuous_exp.comp_continuousOn hLcont
  have hFmono : StrictMonoOn (fun x : ℝ => Real.exp (Lfun σ A B x)) (Set.Ioc 0 x₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc (0 : ℝ) x₀)
    · exact hFcont.mono (fun x hx => hx.1)
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(thetaF_hasDerivAt_Lfun σ A B hB hBA x hx.1).exp.deriv]
      exact mul_pos (Real.exp_pos _) (div_pos (hx₀pos' x hx.1 hx.2) hx.1)
  have hFanti : StrictAntiOn (fun x : ℝ => Real.exp (Lfun σ A B x)) (Set.Ici x₀) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici x₀)
    · exact hFcont.mono (fun x hx => lt_of_lt_of_le hx₀pos hx)
    · intro x hx
      rw [interior_Ici] at hx
      have hxpos : 0 < x := lt_trans hx₀pos hx
      rw [(thetaF_hasDerivAt_Lfun σ A B hB hBA x hxpos).exp.deriv]
      exact mul_neg_of_pos_of_neg (Real.exp_pos _)
        (div_neg_of_neg_of_pos (hx₀neg' x hx) hxpos)
  have haux : ∀ x : ℝ, 0 < x → gfun σ A B x = Real.exp (Lfun σ A B x) :=
    fun x hx => (thetaF_exp_Lfun_eq_gfun σ A B hB hBA x hx).symm
  have hgmono : StrictMonoOn (gfun σ A B) (Set.Ioc 0 x₀) := fun a ha b hb hab => by
    rw [haux a ha.1, haux b hb.1]
    exact hFmono ha hb hab
  have hganti : StrictAntiOn (gfun σ A B) (Set.Ici x₀) := fun a ha b hb hab => by
    rw [haux b (lt_of_lt_of_le hx₀pos hb), haux a (lt_of_lt_of_le hx₀pos ha)]
    exact hFanti ha hb hab
  let a : ℕ → ℝ := fun n => gfun σ A B (n : ℝ)
  have ha0 : a 0 = 0 := by simp [a, gfun]
  have ha1pos : 0 < a 1 := by
    have hAB : 1 / A < 1 / B := thetaF_one_div_lt hB hBA
    have hexp : Real.exp (-(1 / B)) < Real.exp (-(1 / A)) := Real.exp_lt_exp.mpr (by linarith)
    simp only [a, gfun, Nat.cast_one, Real.one_rpow, one_mul]
    linarith
  let N₀ : ℕ := Nat.floor x₀
  have hN₀le : (N₀ : ℝ) ≤ x₀ := Nat.floor_le hx₀pos.le
  have hx₀N₀ : x₀ < (N₀ : ℝ) + 1 := Nat.lt_floor_add_one x₀
  have step_up : ∀ n : ℕ, n < N₀ → a n ≤ a (n + 1) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [ha0]
      exact le_of_lt ha1pos
    · have hna : (n : ℝ) ∈ Set.Ioc (0 : ℝ) x₀ := by
        refine ⟨by exact_mod_cast hnpos, ?_⟩
        have h1 : n ≤ N₀ := le_of_lt hn
        exact le_trans (by exact_mod_cast h1) hN₀le
      have hnb : ((n + 1 : ℕ) : ℝ) ∈ Set.Ioc (0 : ℝ) x₀ := by
        refine ⟨by positivity, ?_⟩
        exact le_trans (by exact_mod_cast hn) hN₀le
      have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      have := hgmono hna hnb hlt
      simpa only [a] using this.le
  have step_down : ∀ n : ℕ, N₀ + 1 ≤ n → a (n + 1) ≤ a n := by
    intro n hn
    have hna : (n : ℝ) ∈ Set.Ici x₀ := by
      have h1 : (N₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      exact le_of_lt (lt_of_lt_of_le hx₀N₀ h1)
    have hnb : ((n + 1 : ℕ) : ℝ) ∈ Set.Ici x₀ := by
      have h1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact le_trans hna h1
    have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := hganti hna hnb hlt
    simpa only [a] using this.le
  by_cases hcase : a N₀ ≤ a (N₀ + 1)
  · refine ⟨N₀ + 1, ?_, ?_⟩
    · intro n hn
      have hnle : n ≤ N₀ := by omega
      rcases lt_or_eq_of_le hnle with hlt | heq
      · exact step_up n hlt
      · rw [heq]; exact hcase
    · intro n hn
      exact step_down n hn
  · have hcase' : a (N₀ + 1) < a N₀ := lt_of_not_ge hcase
    refine ⟨N₀, ?_, ?_⟩
    · intro n hn
      exact step_up n hn
    · intro n hn
      rcases lt_or_eq_of_le hn with hlt | heq
      · exact step_down n (by omega)
      · rw [← heq]; exact le_of_lt hcase'

end Work.LinnikAreas2
