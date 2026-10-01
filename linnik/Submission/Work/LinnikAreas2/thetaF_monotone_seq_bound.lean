import Mathlib
import Submission.Work.LinnikAreas2.thetaF_monotone_seq

noncomputable section
open Set

namespace Work.LinnikAreas2

/-!
# Bounding the peak of `x ↦ x^(σ-1)·(e^{-x/A} − e^{-x/B})`

`Work.LinnikAreas2.thetaF_monotone_seq` proves the unimodality of the sequence
`aₙ = n^(σ-1)·(e^{-n/A} − e^{-n/B})` by building the threshold `K = ⌊x₀⌋` or `⌊x₀⌋ + 1` out of a
zero `x₀` of the auxiliary function `Φ` (see `thetaF_defs`), but it gives no control on `x₀`, hence
none on `K`.

`Φ` is strictly antitone on `(0,∞)`, so its zero `x₀` is unique.  At
`x* = log(A/B)/(1/B − 1/A)` one computes exactly `Φ x* = σ − 1 ≤ 0`, so `x₀ ≤ x*`.  And
`x* = log(A/B)/(1/B − 1/A) ≤ B·(1 + log(A/B))`, because `log(A/B) ≤ A/B − 1`.

Consequently `K ≤ ⌊x₀⌋ + 1 ≤ x₀ + 1 ≤ B·(1 + log(A/B)) + 1 ≤ 2·B·(1 + log(A/B)) + 2`.
-/

/-- At `x* = log(A/B)/(1/B − 1/A)` the function `Φ` equals `σ − 1`. -/
theorem thetaF_Phi_at_xstar (σ A B : ℝ) (hB : 0 < B) (hBA : B < A) :
    Phi σ A B (Real.log (A / B) / (1 / B - 1 / A)) = σ - 1 := by
  have hA : 0 < A := lt_trans hB hBA
  have hc : 0 < 1 / B - 1 / A := by have := thetaF_one_div_lt hB hBA; linarith
  have hcne : (1 / B - 1 / A) ≠ 0 := ne_of_gt hc
  have hcx : (1 / B - 1 / A) * (Real.log (A / B) / (1 / B - 1 / A)) = Real.log (A / B) := by
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ (Real.log (A / B)) hcne
  have hcA : (1 / B - 1 / A) * A = A / B - 1 := by
    rw [sub_mul, one_div_mul_cancel (ne_of_gt hA), one_div_mul_eq_div]
  have hxA : (Real.log (A / B) / (1 / B - 1 / A)) / A = Real.log (A / B) / (A / B - 1) := by
    rw [div_div, hcA]
  have hfrac : (1 / B - 1 / A) * (Real.log (A / B) / (1 / B - 1 / A)) /
      (Real.exp ((1 / B - 1 / A) * (Real.log (A / B) / (1 / B - 1 / A))) - 1)
      = Real.log (A / B) / (A / B - 1) := by
    rw [hcx, Real.exp_log (div_pos hA hB)]
  simp only [Phi]
  rw [hxA, hfrac]
  ring

/-- `log(A/B)/(1/B − 1/A) ≤ B·(1 + log(A/B))`. -/
theorem thetaF_xstar_le (A B : ℝ) (hB : 0 < B) (hBA : B < A) :
    Real.log (A / B) / (1 / B - 1 / A) ≤ B * (1 + Real.log (A / B)) := by
  have hA : 0 < A := lt_trans hB hBA
  have hc : 0 < 1 / B - 1 / A := by have := thetaF_one_div_lt hB hBA; linarith
  have hlog : Real.log (A / B) ≤ A / B - 1 := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have h1 : (1 + Real.log (A / B)) * B ≤ A := by
    have h2 : 1 + Real.log (A / B) ≤ A / B := by linarith
    calc (1 + Real.log (A / B)) * B ≤ (A / B) * B := mul_le_mul_of_nonneg_right h2 hB.le
      _ = A := div_mul_cancel₀ A (ne_of_gt hB)
  have hkey : B * (1 + Real.log (A / B)) * (1 / B - 1 / A)
      = (1 + Real.log (A / B)) * (A - B) / A := by
    field_simp
  rw [div_le_iff₀ hc, hkey, le_div_iff₀ hA]
  nlinarith [h1]

/-- There is a zero `x₀` of `Φ` with the sign properties of `thetaF_Phi_exists_zero`, and
additionally `x₀ ≤ 2·B·(1 + log(A/B))`. -/
theorem thetaF_Phi_exists_zero_bounded (σ A B : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hB : 0 < B) (hBA : B < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 2 * B * (1 + Real.log (A / B)) ∧
      (∀ x : ℝ, 0 < x → x < x₀ → 0 < Phi σ A B x) ∧
      (∀ x : ℝ, x₀ < x → Phi σ A B x < 0) := by
  have hA : 0 < A := lt_trans hB hBA
  obtain ⟨x₀, hx₀pos, hpos, hneg⟩ := thetaF_Phi_exists_zero σ A B hσ hB hBA
  have hw : 0 < Real.log (A / B) := Real.log_pos ((one_lt_div hB).mpr hBA)
  have hc : 0 < 1 / B - 1 / A := by have := thetaF_one_div_lt hB hBA; linarith
  have hxstarpos : 0 < Real.log (A / B) / (1 / B - 1 / A) := div_pos hw hc
  have hxstarle := thetaF_xstar_le A B hB hBA
  have hval : Phi σ A B (Real.log (A / B) / (1 / B - 1 / A)) = σ - 1 :=
    thetaF_Phi_at_xstar σ A B hB hBA
  -- `Φ x* = σ - 1 ≤ 0`, while `Φ > 0` strictly below `x₀`: hence `x*` is not below `x₀`.
  have hle : x₀ ≤ Real.log (A / B) / (1 / B - 1 / A) := by
    by_contra h
    simp only [not_le] at h
    have hp := hpos _ hxstarpos h
    linarith
  refine ⟨x₀, hx₀pos, ?_, hpos, hneg⟩
  calc x₀ ≤ Real.log (A / B) / (1 / B - 1 / A) := hle
    _ ≤ B * (1 + Real.log (A / B)) := hxstarle
    _ ≤ 2 * B * (1 + Real.log (A / B)) := by
        have h2 : 0 ≤ B * (1 + Real.log (A / B)) := le_of_lt (mul_pos hB (by linarith))
        linarith

theorem thetaF_monotone_seq_bound {σ A B : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hB : 0 < B)
    (hBA : B < A) :
    ∃ K : ℕ, ((K:ℝ) ≤ 2 * B * (1 + Real.log (A / B)) + 2)
      ∧ (∀ n : ℕ, n < K →
        (n:ℝ)^(σ-1) * (Real.exp (-((n:ℝ)/A)) - Real.exp (-((n:ℝ)/B)))
          ≤ ((n+1 : ℕ):ℝ)^(σ-1) * (Real.exp (-(((n+1 : ℕ):ℝ)/A)) - Real.exp (-(((n+1 : ℕ):ℝ)/B))))
      ∧ (∀ n : ℕ, K ≤ n →
        (((n+1 : ℕ):ℝ)^(σ-1) * (Real.exp (-(((n+1 : ℕ):ℝ)/A)) - Real.exp (-(((n+1 : ℕ):ℝ)/B)))
          ≤ (n:ℝ)^(σ-1) * (Real.exp (-((n:ℝ)/A)) - Real.exp (-((n:ℝ)/B))))) := by
  have hA : 0 < A := lt_trans hB hBA
  obtain ⟨x₀, hx₀pos, hx₀bnd, hx₀pos', hx₀neg'⟩ :=
    thetaF_Phi_exists_zero_bounded σ A B hσ hσ1 hB hBA
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
  · refine ⟨N₀ + 1, ?_, ?_, ?_⟩
    · have hcast : ((N₀ + 1 : ℕ) : ℝ) = (N₀ : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [hN₀le, hx₀bnd]
    · intro n hn
      have hnle : n ≤ N₀ := by omega
      rcases lt_or_eq_of_le hnle with hlt | heq
      · exact step_up n hlt
      · rw [heq]; exact hcase
    · intro n hn
      exact step_down n hn
  · have hcase' : a (N₀ + 1) < a N₀ := lt_of_not_ge hcase
    refine ⟨N₀, ?_, ?_, ?_⟩
    · linarith [hN₀le, hx₀bnd]
    · intro n hn
      exact step_up n hn
    · intro n hn
      rcases lt_or_eq_of_le hn with hlt | heq
      · exact step_down n (by omega)
      · rw [← heq]; exact le_of_lt hcase'

end Work.LinnikAreas2
