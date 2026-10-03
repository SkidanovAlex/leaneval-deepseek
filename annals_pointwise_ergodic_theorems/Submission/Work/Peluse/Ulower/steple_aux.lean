import Mathlib
import Submission.Work.Peluse.Ulower.Defs
import Submission.Work.Peluse.Ulower.rankInduction
import Submission.Work.Peluse.Ulower.dSup_div_add_one_le

/-!
# Bookkeeping for the `StepLe` wiring

The single step of Peluse's Lemma 3.9 (`Work.Peluse.Ulower.StepLe`) is stated with a *free* support
box radius `B` (only `dSup P Ns N + 2 (t-2) D ≤ B` is assumed), and the constants of the step must
be uniform in the data.  The two lemmas here are what makes that uniformity work:

* `theta_mul_card_le`: the hypothesis `θ ≤ boxNormPow t (const [1,D]) (symIcc B) F` and the
  trivial bound `boxNormPow t (const [1,D]) (symIcc (dSup …)) F ≤ 1` force
  `θ · |symIcc B| ≤ |symIcc (dSup …)|`, i.e. `θ ≲ Ns / B`.  Hence a factor `(D/B)` produced
  anywhere in the chain is bounded below by a *positive power of* `θ · D/Ns`, which is exactly
  what the target's final comparison can absorb.
* `div_ge_of_mul_le`: the elementary consequence of that bound used in the arithmetic.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The box-norm power at the *small* support box is at most `1`, and the comparison of the two
boxes gives `θ · |symIcc B| ≤ |symIcc L₀|`. -/
lemma theta_mul_card_le {t : ℕ} {Q : Fin t → Finset ℤ} {B L₀ : ℕ} {F : ℤ → ℂ} {θ : ℝ}
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : ∀ x : ℤ, x ∉ symIcc L₀ → F x = 0)
    (hθ : θ ≤ boxNormPow t Q (symIcc B) F) :
    θ * (((symIcc B).card : ℕ) : ℝ) ≤ (((symIcc L₀).card : ℕ) : ℝ) := by
  have hS' : (symIcc L₀).Nonempty := ⟨0, by simp [symIcc]⟩
  have hmul := boxNormPow_eq_mul_card t Q (symIcc B) (symIcc L₀) F hS'
  have h1 : boxNormPow t Q (symIcc L₀) F ≤ 1 :=
    Work.Peluse.BoxNorm.boxNormPow_le_one hF1 (fun x hx => hFs x hx)
  have hcardL : (0 : ℝ) < (((symIcc L₀).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
  have hcardB : (0 : ℝ) < (((symIcc B).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
  have h2 : θ ≤ (((symIcc L₀).card : ℕ) : ℝ) / (((symIcc B).card : ℕ) : ℝ) := by
    rw [hmul] at hθ
    have h3 : (((symIcc L₀).card : ℕ) : ℝ) / (((symIcc B).card : ℕ) : ℝ) *
        boxNormPow t Q (symIcc L₀) F
        ≤ (((symIcc L₀).card : ℕ) : ℝ) / (((symIcc B).card : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  rwa [le_div_iff₀ hcardB] at h2

/-- If `θ · (2B) ≤ C_P · Ns` then `2·θ·D/(C_P·Ns) ≤ D/B`. -/
lemma div_ge_of_mul_le {θ D B Ns C_P : ℝ} (hθ0 : 0 < θ) (hD0 : 0 ≤ D) (hB0 : 0 < B)
    (hNs0 : 0 < Ns) (hCP0 : 0 < C_P) (h : θ * (2 * B) ≤ C_P * Ns) :
    2 * θ * D / (C_P * Ns) ≤ D / B := by
  have h1 : 2 * θ ≤ C_P * Ns / B := by
    rw [le_div_iff₀ hB0]
    linarith
  have h2 : 2 * θ * D ≤ (C_P * Ns / B) * D := mul_le_mul_of_nonneg_right h1 hD0
  have h3 : (C_P * Ns / B) * D = (C_P * Ns) * (D / B) := by
    field_simp
  rw [h3] at h2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < C_P * Ns)]
  linarith

end

end Work.Peluse.Ulower
