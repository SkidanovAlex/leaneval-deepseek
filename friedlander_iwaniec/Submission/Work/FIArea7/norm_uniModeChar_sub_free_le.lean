/-
# `Submission.Work.FIArea7.norm_uniModeChar_sub_free_le`

The per-`(b,e,k)` estimate underlying the coprimality-guard removal: the guarded mode
`uniModeChar` and its unguarded version `uniModeCharFree` differ exactly on the *non-coprime*
pairs of the box, and on such a pair the summand is bounded by `‖β z₁‖‖β z₂‖` whenever the
`unitInd` factors are non-zero (which forces `(N z_i, 4be) = 1`) and the `ω`-detection does not
vanish (which forces `4be ∣ |Δ(z₁,z₂)|`).  Hence the difference is bounded by the weighted
non-coprime pair mass `uniMode_pairInner`.
-/
import Mathlib
import Submission.Work.FIArea7.UniPairMassDefs

set_option linter.style.haveILetI false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary bounds -/

/-- `unitInd Q z` is `0` or `1`, hence has norm `≤ 1`. -/
lemma norm_unitInd_le_one (Q : ℕ) (z : GaussianInt) : ‖unitInd Q z‖ ≤ 1 := by
  unfold unitInd
  split <;> simp

/-- `unitInd Q z` vanishes unless `(N z, Q) = 1`. -/
lemma unitInd_eq_zero_of_not_coprime {Q : ℕ} {z : GaussianInt}
    (h : ¬ Nat.Coprime (Work.FIPlan.gnorm z) Q) : unitInd Q z = 0 := by
  unfold unitInd
  rw [if_neg h]

/-- `‖omegaDetect Q e z₁ z₂‖ ≤ 1` whenever `(N z_i, Q) = 1` (the `Q = 0` case is trivial because
`omegaDetect 0 e z₁ z₂ = 0` by definition). -/
lemma omegaDetect_norm_le_one_of_coprime (Q e : ℕ) (z1 z2 : GaussianInt)
    (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) Q) (h2 : Nat.Coprime (Work.FIPlan.gnorm z2) Q) :
    ‖omegaDetect Q e z1 z2‖ ≤ 1 := by
  by_cases hQ : Q = 0
  · subst hQ
    simp [omegaDetect]
  · haveI : NeZero Q := ⟨hQ⟩
    exact norm_omegaDetect_le_one Q e z1 z2 h1 h2

/-- **`‖uniCoeff ε β k z‖ ≤ ‖β z‖`** from the box hypothesis on the support of `β` and the
reflection-sign hypothesis `‖ε z‖ = 1` on the polar box. -/
lemma norm_uniCoeff_le_of_box (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (k : ℤ) (ε : GaussianInt → ℤ)
    (hβbox : ∀ z : GaussianInt, β z ≠ 0 → Work.FITop3.InPolarBox Pa φ z)
    (hεn : ∀ z : GaussianInt, Work.FITop3.InPolarBox Pa φ z → ‖((ε z : ℤ) : ℂ)‖ = 1)
    (z : GaussianInt) : ‖uniCoeff ε β k z‖ ≤ ‖β z‖ := by
  by_cases hz : β z = 0
  · have h0 : uniCoeff ε β k z = 0 := by simp [uniCoeff, betaPrime, hz]
    rw [h0, hz]
  · have hbox := hβbox z hz
    have hgn : Work.FIPlan.gnorm z ≠ 0 := by
      intro h0
      have h := hbox.2.1
      rw [h0] at h
      simp at h
      linarith [Pa.hN1]
    rw [uniCoeff, norm_mul, norm_mul, hεn z hbox, norm_uniPow z hgn k, one_mul, mul_one]
    exact norm_betaPrime_le β z

/-- **Pointwise bound for the guard-removal difference.**  The difference of the guarded and the
unguarded summand is `-(unitInd · unitInd · (c z₁ · conj (c z₂)) · omegaDetect)` off the coprime
pairs and `0` on them; it is bounded by `‖β z₁‖‖β z₂‖` precisely on the non-coprime pairs whose
norms are `4be`-units and on which `4be ∣ |Δ|`. -/
lemma norm_modeTerm_le (Pa : Work.FITop.Params) (φ : ℝ) (b e : ℕ)
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ)
    (hβbox : ∀ z : GaussianInt, β z ≠ 0 → Work.FITop3.InPolarBox Pa φ z)
    (hεn : ∀ z : GaussianInt, Work.FITop3.InPolarBox Pa φ z → ‖((ε z : ℤ) : ℂ)‖ = 1)
    (z1 z2 : GaussianInt) :
    ‖(if Work.FIPlan.GaussCoprime z1 z2 then (0:ℂ)
        else -(unitInd (4*b*e) z1 * unitInd (4*b*e) z2
              * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
              * omegaDetect (4*b*e) e z1 z2))‖
      ≤ (if ¬ Work.FIPlan.GaussCoprime z1 z2
            ∧ Nat.Coprime (Work.FIPlan.gnorm z1) (4*b*e)
            ∧ Nat.Coprime (Work.FIPlan.gnorm z2) (4*b*e)
            ∧ 4*b*e ∣ Work.FIPlan.absDelta z1 z2
          then ‖β z1‖ * ‖β z2‖ else 0) := by
  by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hcop]
    simp only [norm_zero]
    positivity
  · rw [if_neg hcop]
    by_cases h1 : Nat.Coprime (Work.FIPlan.gnorm z1) (4*b*e)
    · by_cases h2 : Nat.Coprime (Work.FIPlan.gnorm z2) (4*b*e)
      · by_cases hd : 4*b*e ∣ Work.FIPlan.absDelta z1 z2
        · rw [if_pos ⟨hcop, h1, h2, hd⟩]
          rw [norm_neg]
          simp only [norm_mul, norm_star]
          have hA := norm_unitInd_le_one (4*b*e) z1
          have hB := norm_unitInd_le_one (4*b*e) z2
          have hC1 := norm_uniCoeff_le_of_box Pa φ β k ε hβbox hεn z1
          have hC2 := norm_uniCoeff_le_of_box Pa φ β k ε hβbox hεn z2
          have hD := omegaDetect_norm_le_one_of_coprime (4*b*e) e z1 z2 h1 h2
          calc ‖unitInd (4*b*e) z1‖ * ‖unitInd (4*b*e) z2‖
                  * (‖uniCoeff ε β k z1‖ * ‖uniCoeff ε β k z2‖)
                  * ‖omegaDetect (4*b*e) e z1 z2‖
              ≤ 1 * 1 * (‖β z1‖ * ‖β z2‖) * 1 := by gcongr
              _ = ‖β z1‖ * ‖β z2‖ := by ring
        · rw [if_neg (fun h => hd h.2.2.2)]
          rw [omegaDetect_eq_zero_of_not_dvd b e z1 z2 hd]; simp
      · rw [if_neg (fun h => h2 h.2.2.1)]
        rw [unitInd_eq_zero_of_not_coprime h2]; simp
    · rw [if_neg (fun h => h1 h.2.1)]
      rw [unitInd_eq_zero_of_not_coprime h1]; simp

/-! ## The guard-removal bound -/

theorem norm_uniModeChar_sub_free_le (Pa : Work.FITop.Params) (φ : ℝ) (b e : ℕ)
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ)
    (hβbox : ∀ z : GaussianInt, β z ≠ 0 → Work.FITop3.InPolarBox Pa φ z)
    (hεn : ∀ z : GaussianInt, Work.FITop3.InPolarBox Pa φ z → ‖((ε z : ℤ) : ℂ)‖ = 1) :
    ‖Work.FIArea7.uniModeChar Pa b e β k ε - Work.FIArea7.uniModeCharFree Pa b e β k ε‖
      ≤ Work.FIArea7.uniMode_pairInner Pa b e β := by
  -- The difference of the two double sums is the sum of the pointwise differences; on the coprime
  -- pairs the two summands coincide, so only the non-coprime pairs survive.
  have key : uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε
      = ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (if Work.FIPlan.GaussCoprime z1 z2 then (0:ℂ)
              else -(unitInd (4*b*e) z1 * unitInd (4*b*e) z2
                    * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
                    * omegaDetect (4*b*e) e z1 z2)) := by
    rw [uniModeChar, uniModeCharFree, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z1 _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z2 _
    by_cases h : Work.FIPlan.GaussCoprime z1 z2 <;> simp [h]
  rw [key]
  calc ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (if Work.FIPlan.GaussCoprime z1 z2 then (0:ℂ)
              else -(unitInd (4*b*e) z1 * unitInd (4*b*e) z2
                    * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
                    * omegaDetect (4*b*e) e z1 z2))‖
      ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ‖∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (if Work.FIPlan.GaussCoprime z1 z2 then (0:ℂ)
              else -(unitInd (4*b*e) z1 * unitInd (4*b*e) z2
                    * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
                    * omegaDetect (4*b*e) e z1 z2))‖ := norm_sum_le _ _
    _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ‖(if Work.FIPlan.GaussCoprime z1 z2 then (0:ℂ)
              else -(unitInd (4*b*e) z1 * unitInd (4*b*e) z2
                    * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
                    * omegaDetect (4*b*e) e z1 z2))‖ := by
        apply Finset.sum_le_sum; intro z1 _
        exact norm_sum_le _ _
    _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (if ¬ Work.FIPlan.GaussCoprime z1 z2
              ∧ Nat.Coprime (Work.FIPlan.gnorm z1) (4*b*e)
              ∧ Nat.Coprime (Work.FIPlan.gnorm z2) (4*b*e)
              ∧ 4*b*e ∣ Work.FIPlan.absDelta z1 z2
             then ‖β z1‖ * ‖β z2‖ else 0) := by
        apply Finset.sum_le_sum; intro z1 _
        apply Finset.sum_le_sum; intro z2 _
        exact norm_modeTerm_le Pa φ b e β k ε hβbox hεn z1 z2
    _ = uniMode_pairInner Pa b e β := rfl

end

end Work.FIArea7
