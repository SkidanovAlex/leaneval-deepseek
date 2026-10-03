/-
# Fourier coefficients of the mixed partial derivatives of a periodic symbol

This is the second half of the elementary dictionary between a `1`-periodic symbol
`σ : ℝ → ℝ → ℂ` and its Fourier coefficients on the unit square,
`coeff2 σ p₁ p₂ = ∫₀¹ ∫₀¹ σ(x,y) e(-p₁x - p₂y) dx dy`
(see `Submission.Work.KMTPlan.A6.SymToolbox`): differentiating in the two variables
multiplies the coefficient by the corresponding characters' frequencies,

  `coeff2 (∂₁^{j₁} ∂₂^{j₂} σ) p₁ p₂ = (2πi p₁)^{j₁} (2πi p₂)^{j₂} coeff2 σ p₁ p₂`

(`dp j₁ j₂ σ = ∂₁^{j₁} ∂₂^{j₂} σ` in the `iteratedDeriv`-of-slices sense of `SymToolbox`).

The proof is integration by parts in each variable against the character, exactly as in the
one-variable case `Work.KMTPlan.A6.SymToolbox_coeff1_iteratedDeriv`:

* the derivative in the *inner* variable `y` of the iterated integral can be handled pointwise in
  the outer variable, so it needs no joint regularity (`cdp_coeff2_dp2`);
* the derivative in the *outer* variable `x` requires first swapping the order of integration
  (`Work.KMTPlan.A6.SymToolbox_coeff2_swap`, Fubini for continuous functions on the unit square);
  the integrability hypotheses needed there come from the joint continuity of the iterated
  derivatives, which is `Work.KMTPlan.A6.SymToolbox_dp1_one_contDiff` iterated
  (`cdp_contDiff_dp1_iter`).

The two steps produce the factors for `p₂` and `p₁` respectively and are assembled in
`SymToolbox_coeff2_dp`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox_coeff1_iteratedDeriv
import Submission.Work.KMTPlan.A6.SymToolbox_coeff2_swap
import Submission.Work.KMTPlan.A6.SymToolbox_dp1_one_contDiff
import Submission.Work.KMTPlan.A6.SymToolbox_dp2_one_contDiff

open MeasureTheory intervalIntegral
open scoped BigOperators ENNReal

namespace Work.KMTPlan.A6

noncomputable section

/-! ## The character -/

lemma cdp_eeC_add (a b : ℝ) : eeC (a + b) = eeC a * eeC b := by
  rw [eeC, eeC, eeC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cdp_continuous_eeC : Continuous eeC := by
  unfold eeC
  fun_prop

/-! ## Fibres of a jointly smooth function of two variables -/

lemma cdp_fiber₂ (Φ : ℝ → ℝ → ℂ) (n : ℕ)
    (hsm : ContDiff ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ∀ x : ℝ, ContDiff ℝ (n : WithTop ℕ∞) (fun y => Φ x y) := by
  intro x
  have hγ : ContDiff ℝ (n : WithTop ℕ∞) (fun t : ℝ => (x, t)) := by fun_prop
  simpa [Function.comp_def] using hsm.comp hγ

lemma cdp_fiber₁ (Φ : ℝ → ℝ → ℂ) (n : ℕ)
    (hsm : ContDiff ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ∀ y : ℝ, ContDiff ℝ (n : WithTop ℕ∞) (fun x => Φ x y) := by
  intro y
  have hγ : ContDiff ℝ (n : WithTop ℕ∞) (fun t : ℝ => (t, y)) := by fun_prop
  simpa [Function.comp_def] using hsm.comp hγ

/-! ## Joint regularity of the iterated partial derivatives

`dp1 k Φ` is the `k`-th derivative in the first variable of the slices of `Φ`; if the uncurried
`Φ` is jointly `C^{m+k}`, then `dp1 k Φ` is jointly `C^m` (and similarly for `dp2`).  This is
obtained by iterating the single-step statements `SymToolbox_dp1_one_contDiff` /
`SymToolbox_dp2_one_contDiff`. -/

lemma cdp_dp2_one_dp2 (Φ : ℝ → ℝ → ℂ) (k : ℕ) (x y : ℝ) :
    dp2 1 (dp2 k Φ) x y = dp2 (k + 1) Φ x y := by
  simp only [dp2, iteratedDeriv_succ, iteratedDeriv_zero]

lemma cdp_dp1_one_dp1 (Φ : ℝ → ℝ → ℂ) (k : ℕ) (x y : ℝ) :
    dp1 1 (dp1 k Φ) x y = dp1 (k + 1) Φ x y := by
  simp only [dp1, iteratedDeriv_succ, iteratedDeriv_zero]

/-- The single-step regularity statement, with the index written as a single natural number cast
(so that the arithmetic in the induction below is arithmetic in `ℕ`). -/
lemma cdp_dp2_step (Φ : ℝ → ℝ → ℂ) (m : ℕ)
    (hsm : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => dp2 1 Φ p.1 p.2) :=
  SymToolbox_dp2_one_contDiff Φ m (by
    simpa only [Nat.cast_add, Nat.cast_one] using hsm)

/-- The single-step regularity statement for the first variable. -/
lemma cdp_dp1_step (Φ : ℝ → ℝ → ℂ) (m : ℕ)
    (hsm : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => dp1 1 Φ p.1 p.2) :=
  SymToolbox_dp1_one_contDiff Φ m (by
    simpa only [Nat.cast_add, Nat.cast_one] using hsm)

lemma cdp_contDiff_dp2_iter (Φ : ℝ → ℝ → ℂ) (m k : ℕ)
    (hsm : ContDiff ℝ (((m + k : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => dp2 k Φ p.1 p.2) := by
  induction k generalizing m with
  | zero => simpa only [dp2, iteratedDeriv_zero, Nat.add_zero] using hsm
  | succ k ih =>
      have h1 : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => dp2 k Φ p.1 p.2) :=
        ih (m + 1) (by
          have h : (m + 1) + k = m + (k + 1) := by omega
          rw [h]; exact hsm)
      have h2 : ContDiff ℝ (m : WithTop ℕ∞)
          (fun p : ℝ × ℝ => dp2 1 (dp2 k Φ) p.1 p.2) :=
        cdp_dp2_step (dp2 k Φ) m h1
      have hfun : (fun p : ℝ × ℝ => dp2 1 (dp2 k Φ) p.1 p.2)
          = (fun p : ℝ × ℝ => dp2 (k + 1) Φ p.1 p.2) :=
        funext fun p => cdp_dp2_one_dp2 Φ k p.1 p.2
      rw [hfun] at h2
      exact h2

lemma cdp_contDiff_dp1_iter (Φ : ℝ → ℝ → ℂ) (m k : ℕ)
    (hsm : ContDiff ℝ (((m + k : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => dp1 k Φ p.1 p.2) := by
  induction k generalizing m with
  | zero => simpa only [dp1, iteratedDeriv_zero, Nat.add_zero] using hsm
  | succ k ih =>
      have h1 : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => dp1 k Φ p.1 p.2) :=
        ih (m + 1) (by
          have h : (m + 1) + k = m + (k + 1) := by omega
          rw [h]; exact hsm)
      have h2 : ContDiff ℝ (m : WithTop ℕ∞)
          (fun p : ℝ × ℝ => dp1 1 (dp1 k Φ) p.1 p.2) :=
        cdp_dp1_step (dp1 k Φ) m h1
      have hfun : (fun p : ℝ × ℝ => dp1 1 (dp1 k Φ) p.1 p.2)
          = (fun p : ℝ × ℝ => dp1 (k + 1) Φ p.1 p.2) :=
        funext fun p => cdp_dp1_one_dp1 Φ k p.1 p.2
      rw [hfun] at h2
      exact h2

/-! ## The second-variable step -/

/-- Differentiating in the *second* variable of the iterated integral multiplies the two-dimensional
Fourier coefficient by `(2πi p₂)^m`.  Only fibrewise regularity in the second variable is needed:
the integration by parts happens inside the inner integral. -/
lemma cdp_coeff2_dp2 (σ : ℝ → ℝ → ℂ) (m : ℕ) (p₁ p₂ : ℤ)
    (hper2 : ∀ x y, σ x (y + 1) = σ x y)
    (hsm : ∀ x : ℝ, ContDiff ℝ (m : WithTop ℕ∞) (fun y => σ x y)) :
    coeff2 (dp2 m σ) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ m * coeff2 σ p₁ p₂ := by
  have hinner : ∀ x : ℝ,
      (∫ y in (0 : ℝ)..1, dp2 m σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ m *
          (∫ y in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) := by
    intro x
    have h1 := SymToolbox_coeff1_iteratedDeriv (fun y => σ x y) m p₂ (hper2 x) (hsm x)
    have h2 : (∫ y in (0 : ℝ)..1, dp2 m σ x y * eeC (-(p₂ : ℝ) * y))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ m *
          (∫ y in (0 : ℝ)..1, σ x y * eeC (-(p₂ : ℝ) * y)) := by
      simpa only [coeff1, dp2] using h1
    calc (∫ y in (0 : ℝ)..1, dp2 m σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
        = (∫ y in (0 : ℝ)..1, dp2 m σ x y * eeC (-(p₂ : ℝ) * y)) * eeC (-(p₁ : ℝ) * x) := by
          rw [← intervalIntegral.integral_mul_const]
          apply intervalIntegral.integral_congr
          intro y _
          dsimp only
          rw [show -(p₁ : ℝ) * x - (p₂ : ℝ) * y
                = (-(p₂ : ℝ) * y) + (-(p₁ : ℝ) * x) by ring, cdp_eeC_add]
          ring
      _ = ((2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ m *
            (∫ y in (0 : ℝ)..1, σ x y * eeC (-(p₂ : ℝ) * y))) * eeC (-(p₁ : ℝ) * x) := by
          rw [h2]
      _ = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ m *
            ((∫ y in (0 : ℝ)..1, σ x y * eeC (-(p₂ : ℝ) * y)) * eeC (-(p₁ : ℝ) * x)) := by
          ring
      _ = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ m *
            (∫ y in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) := by
          congr 1
          rw [← intervalIntegral.integral_mul_const]
          apply intervalIntegral.integral_congr
          intro y _
          dsimp only
          rw [show -(p₁ : ℝ) * x - (p₂ : ℝ) * y
                = (-(p₂ : ℝ) * y) + (-(p₁ : ℝ) * x) by ring, cdp_eeC_add]
          ring
  simp only [coeff2]
  rw [intervalIntegral.integral_congr (fun x _ => hinner x)]
  rw [intervalIntegral.integral_const_mul]

/-! ## The first-variable step, in the swapped order of integration -/

/-- Differentiating in the *first* variable, for the doubly iterated integral taken in the order
`∫_y ∫_x` (so that the `x`-integration is the inner one and the integration by parts is pointwise
in `y`).  Again only fibrewise regularity is needed. -/
lemma cdp_coeff2S_dp1 (σ : ℝ → ℝ → ℂ) (m : ℕ) (p₁ p₂ : ℤ)
    (hper1 : ∀ x y, σ (x + 1) y = σ x y)
    (hfib : ∀ y : ℝ, ContDiff ℝ (m : WithTop ℕ∞) (fun x => σ x y)) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
        dp1 m σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ m *
        (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) := by
  have hinner : ∀ y : ℝ,
      (∫ x in (0 : ℝ)..1, dp1 m σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ m *
          (∫ x in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) := by
    intro y
    have h1 := SymToolbox_coeff1_iteratedDeriv (fun x => σ x y) m p₁
      (fun x => hper1 x y) (hfib y)
    have h2 : (∫ x in (0 : ℝ)..1, dp1 m σ x y * eeC (-(p₁ : ℝ) * x))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ m *
          (∫ x in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x)) := by
      simpa only [coeff1, dp1] using h1
    calc (∫ x in (0 : ℝ)..1, dp1 m σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
        = (∫ x in (0 : ℝ)..1, dp1 m σ x y * eeC (-(p₁ : ℝ) * x)) * eeC (-(p₂ : ℝ) * y) := by
          rw [← intervalIntegral.integral_mul_const]
          apply intervalIntegral.integral_congr
          intro x _
          dsimp only
          rw [show -(p₁ : ℝ) * x - (p₂ : ℝ) * y
                = (-(p₁ : ℝ) * x) + (-(p₂ : ℝ) * y) by ring, cdp_eeC_add]
          ring
      _ = ((2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ m *
            (∫ x in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x))) * eeC (-(p₂ : ℝ) * y) := by
          rw [h2]
      _ = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ m *
            ((∫ x in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x)) * eeC (-(p₂ : ℝ) * y)) := by
          ring
      _ = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ m *
            (∫ x in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) := by
          congr 1
          rw [← intervalIntegral.integral_mul_const]
          apply intervalIntegral.integral_congr
          intro x _
          dsimp only
          rw [show -(p₁ : ℝ) * x - (p₂ : ℝ) * y
                = (-(p₁ : ℝ) * x) + (-(p₂ : ℝ) * y) by ring, cdp_eeC_add]
          ring
  rw [intervalIntegral.integral_congr (fun y _ => hinner y)]
  rw [intervalIntegral.integral_const_mul]

/-! ## The first-variable step -/

/-- Differentiating in the first variable: Fubini (`SymToolbox_coeff2_swap`) to put the
`x`-integration inside, the pointwise fibre computation above, and Fubini back.  Joint smoothness
of `dp1 m σ` (from `cdp_contDiff_dp1_iter`) supplies the integrability needed for Fubini. -/
lemma cdp_coeff2_dp1 (σ : ℝ → ℝ → ℂ) (m : ℕ) (p₁ p₂ : ℤ)
    (hper1 : ∀ x y, σ (x + 1) y = σ x y)
    (hsm : ContDiff ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => σ p.1 p.2)) :
    coeff2 (dp1 m σ) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ m * coeff2 σ p₁ p₂ := by
  have hfib : ∀ y : ℝ, ContDiff ℝ (m : WithTop ℕ∞) (fun x => σ x y) := cdp_fiber₁ σ m hsm
  have hcontσ : Continuous (fun p : ℝ × ℝ => σ p.1 p.2) := hsm.continuous
  have hcontD : Continuous (fun p : ℝ × ℝ => dp1 m σ p.1 p.2) :=
    (cdp_contDiff_dp1_iter σ 0 m (by simpa only [Nat.zero_add] using hsm)).continuous
  rw [SymToolbox_coeff2_swap (dp1 m σ) p₁ p₂ hcontD]
  rw [cdp_coeff2S_dp1 σ m p₁ p₂ hper1 hfib]
  rw [SymToolbox_coeff2_swap σ p₁ p₂ hcontσ]

/-! ## The target -/

theorem SymToolbox_coeff2_dp (σ : ℝ → ℝ → ℂ) (j₁ j₂ : ℕ)
    (hper1 : ∀ x y, σ (x + 1) y = σ x y) (hper2 : ∀ x y, σ x (y + 1) = σ x y)
    (hsm : ContDiff ℝ (j₁ + j₂) (fun p : ℝ × ℝ => σ p.1 p.2)) (p₁ p₂ : ℤ) :
    Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ j₁
        * (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j₂
        * Work.KMTPlan.A6.coeff2 σ p₁ p₂ := by
  -- put the joint smoothness hypothesis in the canonical shape indexed by a single natural
  have hsm' : ContDiff ℝ (((j₁ + j₂ : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => σ p.1 p.2) := by
    rw [Nat.cast_add]; exact hsm
  -- joint regularity of the second-variable derivative
  have hJ : ContDiff ℝ (j₁ : WithTop ℕ∞) (fun p : ℝ × ℝ => dp2 j₂ σ p.1 p.2) :=
    cdp_contDiff_dp2_iter σ j₁ j₂ hsm'
  -- periodicity in the first variable of the second-variable derivative
  have hper1τ : ∀ x y, dp2 j₂ σ (x + 1) y = dp2 j₂ σ x y := by
    intro x y
    simp only [dp2]
    rw [show (fun t => σ (x + 1) t) = (fun t => σ x t) from funext fun t => hper1 x t]
  have hF := cdp_coeff2_dp1 (dp2 j₂ σ) j₁ p₁ p₂ hper1τ hJ
  -- fibrewise regularity in the second variable
  have hfibAll : ∀ x : ℝ, ContDiff ℝ (((j₁ + j₂ : ℕ)) : WithTop ℕ∞) (fun y => σ x y) :=
    cdp_fiber₂ σ (j₁ + j₂) hsm'
  have hfib : ∀ x : ℝ, ContDiff ℝ (j₂ : WithTop ℕ∞) (fun y => σ x y) :=
    fun x => (hfibAll x).of_le (by rw [Nat.cast_add]; exact le_add_self)
  have hE := cdp_coeff2_dp2 σ j₂ p₁ p₂ hper2 hfib
  have hmain : coeff2 (dp1 j₁ (dp2 j₂ σ)) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ j₁
        * (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j₂
        * coeff2 σ p₁ p₂ := by
    rw [hF, hE]
    ring
  simpa only [dp] using hmain

end

end Work.KMTPlan.A6
