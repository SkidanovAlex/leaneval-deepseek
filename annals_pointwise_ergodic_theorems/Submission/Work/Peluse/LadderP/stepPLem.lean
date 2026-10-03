import Mathlib
import Submission.Work.Peluse.LadderP.stepPBridge
import Submission.Work.Peluse.LadderP.stepShift3Bound

/-!
# The one-step lemma of the power-loss ladder: the pointwise Lemma 5.1 input

The instantiation of `lemma51P (2^j)` at `B₀ := j+1` on the peeled difference `Gof …` of the ladder
step, i.e. the pointwise input of the mass step: at a datum whose box average is at least `γ` and
whose exceptional set is at most `ε M₁`, the level-`s'` uniformity-norm power of the peeled
difference at the long window `c[D]` is at least `(C₅₁ γ^{e₅₁})^{2^{s'}}`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

theorem lemma51Step (j n M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    {η γ ε : ℝ} {s' e₅₁ : ℕ} {C₅₁ : ℝ}
    (hC₅₁ : 0 < C₅₁) (hC₅₁' : C₅₁ ≤ 1) (hs' : 1 ≤ s') (he₅₁ : 1 ≤ e₅₁)
    (h51 : ∀ (c' : ℤ) (M₁' M₂ N' D' : ℕ) (b : Fin (2^j) → ℤ) (γ' η' ε' : ℝ) (g : ℤ → ℂ),
      0 < c' → 2 ≤ M₂ → M₂ ≤ M₁' → 1 ≤ N' → ((M₁' : ℝ) * (M₂ : ℝ) ≤ (N' : ℝ) / (c' : ℝ)) → 1 ≤ D' →
      (∀ i : Fin (2^j), |b i| ≤ ((j+1 : ℕ) : ℤ) * (M₁' : ℤ)) →
      SupportIn g N' → (∀ x : ℤ, ‖g x‖ ≤ 1) →
      0 < γ' → γ' ≤ 1 → 0 < η' → η' ≤ C₅₁ * γ' ^ e₅₁ → 0 ≤ ε' → ε' ≤ C₅₁ * γ' ^ e₅₁ →
      (D' : ℝ) ≤ C₅₁ * (γ' * η') ^ e₅₁ * ((M₁' : ℝ) * (M₂ : ℝ)) →
      ((M₁' : ℝ) * (M₂ : ℝ)) ^ e₅₁ ≤ C₅₁ * (γ' * η' * (D' : ℝ)) ^ e₅₁ * (M₂ : ℝ) →
      (((Finset.Icc 1 M₁').filter (fun a : ℕ =>
          ¬ ((∀ i k : Fin (2^j), i ≠ k →
                ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b k) : ℕ) : ℝ) ≤ 1 / η')
              ∧ ∀ i : Fin (2^j), η' * (M₁' : ℝ) ≤ ((|((a : ℤ) + b i)| : ℤ) : ℝ)))).card : ℝ)
        ≤ ε' * (M₁' : ℝ) →
      γ' ≤ LadderQ.boxAvgA (2^j) c' M₁' M₂ b N' g →
      C₅₁ * γ' ^ e₅₁ ≤ uNorm s' (arithIcc c' D') (symIcc N') g)
    (hc : 0 < c) (hL2 : 2 ≤ L) (hLM : L ≤ M₁) (hN : 1 ≤ N)
    (hML : (M₁ : ℝ) * (L : ℝ) ≤ (N : ℝ) / (c : ℝ)) (hD1 : 1 ≤ D)
    (hfin : FinSuppZ f) (hbd : ∀ z : ℤ, ‖f z‖ ≤ 1) (hsup : SupportIn f N)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη0 : 0 < η) (hηle : η ≤ C₅₁ * γ ^ e₅₁)
    (hε0 : 0 ≤ ε) (hεle : ε ≤ C₅₁ * γ ^ e₅₁)
    (hDsmall : (D : ℝ) ≤ C₅₁ * (γ * η) ^ e₅₁ * ((M₁ : ℝ) * (L : ℝ)))
    (hnondeg : ((M₁ : ℝ) * (L : ℝ)) ^ e₅₁ ≤ C₅₁ * (γ * η * (D : ℝ)) ^ e₅₁ * (L : ℝ))
    (hs : Fin M₁) :
    ∀ (h₁ : Fin j → Fin M₁) (h₁' : Fin j → Fin M₁) (h'_s : Fin M₁)
      (km : KmT j n M₁ c L D h₁ h₁'),
      γ ≤ LadderQ.boxAvgA (2^j) c M₁ L
            (stepShift3E (enumAll j) h₁ h₁' h'_s) N (Gof j n M₁ c L D h₁ h₁' km f) →
      ¬ (ε * (M₁ : ℝ)
          < ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ)) →
      (C₅₁ * γ ^ e₅₁) ^ (2^s')
        ≤ Gpow j n s' M₁ c L D N h₁ h₁' km f := by
  intro h₁ h₁' h'_s km hbox hbad
  set g : ℤ → ℂ := Gof j n M₁ c L D h₁ h₁' km f with hg
  -- the peeled difference is `1`-bounded and has small support
  have hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1 := by
    intro x
    rw [hg]
    simp only [Gof]
    exact Ulower.norm_iterDelta_le_one n _
      (Ulower.iterDelta (2^j - 1) _ f)
      (Ulower.norm_iterDelta_le_one (2^j - 1) _ f hbd) x
  obtain ⟨p, hp⟩ : SuppSmall N g := by
    rw [hg]
    simp only [Gof]
    exact SuppSmall.iterDelta n _
      (SuppSmall.iterDelta (2^j - 1) _ (SuppSmall.of_supportIn hsup))
  have hgf : FinSuppZ g := SuppSmall.finSuppZ ⟨p, hp⟩
  -- the box-average hypothesis transports to the translate
  have hbox' : γ ≤ LadderQ.boxAvgA (2^j) c M₁ L
      (stepShift3E (enumAll j) h₁ h₁' h'_s) N (shift p g) := by
    rw [boxAvgA_shift (2^j) c M₁ L N _ g p hgf]
    exact hbox
  -- the exceptional set of the ladder step is the one of the Lemma 5.1 input
  have hset : stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)
      = (Finset.Icc 1 M₁).filter (fun a : ℕ =>
          ¬ ((∀ i k : Fin (2^j), i ≠ k →
                ((Int.gcd ((a : ℤ) + stepShift3E (enumAll j) h₁ h₁' h'_s i)
                  ((a : ℤ) + stepShift3E (enumAll j) h₁ h₁' h'_s k) : ℕ) : ℝ) ≤ 1 / η)
              ∧ ∀ i : Fin (2^j), η * (M₁ : ℝ)
                  ≤ ((|((a : ℤ) + stepShift3E (enumAll j) h₁ h₁' h'_s i)| : ℤ) : ℝ))) := by
    simp only [stepBad, stepShiftE_snoc]
  have hbad' : (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
      ¬ ((∀ i k : Fin (2^j), i ≠ k →
            ((Int.gcd ((a : ℤ) + stepShift3E (enumAll j) h₁ h₁' h'_s i)
              ((a : ℤ) + stepShift3E (enumAll j) h₁ h₁' h'_s k) : ℕ) : ℝ) ≤ 1 / η)
          ∧ ∀ i : Fin (2^j), η * (M₁ : ℝ)
              ≤ ((|((a : ℤ) + stepShift3E (enumAll j) h₁ h₁' h'_s i)| : ℤ) : ℝ)))).card : ℝ)
      ≤ ε * (M₁ : ℝ) := by
    have hthis := not_lt.mp hbad
    rwa [hset] at hthis
  -- apply the Lemma 5.1 input
  have hmain := h51 c M₁ L N D (stepShift3E (enumAll j) h₁ h₁' h'_s) γ η ε (shift p g)
    hc hL2 hLM hN hML hD1
    (fun i => by simpa only [stepShift3E] using stepShift3Bound j M₁ hM₁ h₁ h₁' h'_s (enumAll j i))
    hp (fun x => hg1 (x + p)) hγ0 hγ1 hη0 hηle hε0 hεle hDsmall hnondeg hbad' hbox'
  -- the norm is translation invariant
  rw [uNorm_shift s' (arithIcc c D) (symIcc N) g p hgf] at hmain
  -- raise to the `2^{s'}`-th power
  have hpow : (C₅₁ * γ ^ e₅₁) ^ (2^s') ≤ uNormPow s' (arithIcc c D) (symIcc N) g := by
    have h0 : (0 : ℝ) ≤ C₅₁ * γ ^ e₅₁ := le_of_lt (mul_pos hC₅₁ (pow_pos hγ0 _))
    have h1 : (0 : ℝ) ≤ uNormPow s' (arithIcc c D) (symIcc N) g := boxNormPow_nonneg'
    have h := pow_le_pow_left₀ h0 (by simpa only [uNorm] using hmain) (2^s')
    have hkn : (1 / (2:ℝ)^s') * ((2^s' : ℕ) : ℝ) = 1 := by
      rw [one_div, Nat.cast_pow]
      simp only [Nat.cast_ofNat]
      exact inv_mul_cancel₀ (by positivity)
    have hrewrite : ((uNormPow s' (arithIcc c D) (symIcc N) g) ^ (1 / (2:ℝ)^s')) ^ (2^s')
        = uNormPow s' (arithIcc c D) (symIcc N) g := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h1, hkn, Real.rpow_one]
    exact le_trans h (le_of_eq hrewrite)
  -- conclude
  have hEq : uNormPow s' (arithIcc c D) (symIcc N) g = Gpow j n s' M₁ c L D N h₁ h₁' km f := by
    simp only [Gpow, uNormPow, longBlk, hg]
    rfl
  exact le_trans hpow (le_of_eq hEq)

end

end Work.Peluse.LadderP
