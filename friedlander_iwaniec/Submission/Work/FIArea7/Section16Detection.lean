/-
# The rational-class detection of `z₁ ≡ ω z₂ (mod Q)` (§16/(17.9))

The `ω`-sum of (17.9)/(16.13) — summed over the *rational* classes `ω (mod Q)` with the weight
`(ω|e)` — is a sum over the Gaussian unit group `G = (ℤ[i]/Q)^*` restricted to its rational
subgroup.  This file proves that it is *literally* the group-theoretic detection sum

  `∑_{p ∈ G} ratWeight Q e p · [gaussUnitOf Q z₁ = p · gaussUnitOf Q z₂]`

for `z₁, z₂` invertible modulo `Q`: both sides collapse to the value of `ratWeight` at the unique
class `p₀ = π(z₁)π(z₂)⁻¹`, and `p₀` is rational exactly when the congruence `z₁ ≡ ω z₂ (mod Q)`
has a solution `ω`.

This is the input `char_expansion_pair` (i.e. *FI* (16.11)) consumes: it turns the congruence
detection into a sum over the finite abelian group `G`, whose characters are then summed by
orthogonality.
-/
import Mathlib
import Submission.Work.FIArea7.GaussUnitClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The inverse of the class of `z` in `G`, in coordinates (`(r,−s)/(r²+s²)`). -/
def gaussUnitInvCoord (Q : ℕ) (z : GaussianInt) : ZMod Q × ZMod Q :=
  (z.re * (gaussNorm (gaussCoord Q z))⁻¹, -(z.im * (gaussNorm (gaussCoord Q z))⁻¹))

/-- `gaussUnitInvCoord` really is the inverse of the class of `z`: the Gaussian product is `(1,0)`. -/
lemma gaussMul_gaussUnitInvCoord (Q : ℕ) (z : GaussianInt)
    (h : IsUnit (gaussNorm (gaussCoord Q z))) :
    gaussMul (gaussCoord Q z) (gaussUnitInvCoord Q z) = (1, 0) :=
  gaussMul_inv_cancel (gaussCoord Q z) h

/-- The coordinates of the inverse in the group `G`. -/
lemma gaussUnitOf_inv_val (Q : ℕ) (z : GaussianInt) (h : Nat.Coprime (Work.FIPlan.gnorm z) Q) :
    ((gaussUnitOf Q z h)⁻¹).1 = gaussUnitInvCoord Q z := rfl

/-- **The detection equivalence.**  For `z₂` invertible mod `Q` and any `ω : ZMod Q`, the scalar
congruence `ω z₂ ≡ z₁ (mod Q)` is equivalent to the statement that `(ω, 0)` *is* the class
`π(z₁)π(z₂)⁻¹` — i.e. that the quotient class is rational. -/
theorem gaussMul_rat_eq_iff (Q : ℕ) (z1 z2 : GaussianInt)
    (h2 : IsUnit (gaussNorm (gaussCoord Q z2))) (ω : ZMod Q) :
    gaussMul (ω, 0) (gaussCoord Q z2) = gaussCoord Q z1
      ↔ (ω, (0 : ZMod Q)) = gaussMul (gaussCoord Q z1) (gaussUnitInvCoord Q z2) := by
  have hinv := gaussMul_gaussUnitInvCoord Q z2 h2
  constructor
  · intro h
    have h' := congrArg (fun p => gaussMul p (gaussUnitInvCoord Q z2)) h
    rw [gaussMul_assoc, hinv, gaussMul_one] at h'
    exact h'
  · intro h
    have h' := congrArg (fun p => gaussMul p (gaussCoord Q z2)) h
    have h2' : gaussMul (gaussUnitInvCoord Q z2) (gaussCoord Q z2) = (1, 0) := by
      rw [gaussMul_comm]; exact hinv
    rw [gaussMul_assoc, h2', gaussMul_one] at h'
    exact h'

/-- **The `ω`-sum of (17.9) as a sum over the Gaussian unit group.**  For `z₁, z₂` invertible
modulo `Q`, the sum over the rational classes `ω (mod Q)` with the weight `(ω|e)` equals the sum
over `G = (ℤ[i]/Q)^*` of `ratWeight Q e` restricted to the unique class `π(z₁)π(z₂)⁻¹`. -/
theorem sum_omegaDetect_eq_ratWeight (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt)
    (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) Q) (h2 : Nat.Coprime (Work.FIPlan.gnorm z2) Q) :
    (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0))
      = ∑ p : {p : ZMod Q × ZMod Q // IsUnit (gaussNorm p)},
          (if gaussUnitOf Q z1 h1 = p * gaussUnitOf Q z2 h2 then ratWeight Q e p else 0) := by
  set p0 : {p : ZMod Q × ZMod Q // IsUnit (gaussNorm p)} :=
    gaussUnitOf Q z1 h1 * (gaussUnitOf Q z2 h2)⁻¹ with hp0
  have hunit : IsUnit (gaussNorm (gaussCoord Q z2)) :=
    (isUnit_gaussNorm_gaussCoord_iff Q z2).mpr h2
  -- ## the right-hand side collapses to `ratWeight p0`
  have hR : (∑ p : {p : ZMod Q × ZMod Q // IsUnit (gaussNorm p)},
        (if gaussUnitOf Q z1 h1 = p * gaussUnitOf Q z2 h2 then ratWeight Q e p else 0))
      = ratWeight Q e p0 := by
    have hiff : ∀ p, (gaussUnitOf Q z1 h1 = p * gaussUnitOf Q z2 h2) ↔ p = p0 := by
      intro p
      constructor
      · intro h
        have h' := congrArg (fun x => x * (gaussUnitOf Q z2 h2)⁻¹) h
        rw [mul_assoc, mul_inv_cancel, mul_one] at h'
        rw [← h', ← hp0]
      · intro h
        rw [h, hp0, mul_assoc, inv_mul_cancel, mul_one]
    have : ∀ p, (if gaussUnitOf Q z1 h1 = p * gaussUnitOf Q z2 h2 then ratWeight Q e p else 0)
        = (if p = p0 then ratWeight Q e p else 0) := by
      intro p
      by_cases h : p = p0
      · rw [if_pos ((hiff p).mpr h), if_pos h]
      · rw [if_neg (fun hc => h ((hiff p).mp hc)), if_neg h]
    rw [Finset.sum_congr rfl (fun p _ => this p), Finset.sum_ite_eq']
    simp
  -- ## the left-hand side collapses to `ratWeight p0` as well
  have hp0val : p0.1 = gaussMul (gaussCoord Q z1) (gaussUnitInvCoord Q z2) := by
    rw [hp0]
    show gaussMul (gaussCoord Q z1) ((gaussUnitOf Q z2 h2)⁻¹).1 = _
    rw [gaussUnitOf_inv_val]
  have hcollapse : ∀ ω : ZMod Q,
      (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)
      = (if (ω, (0 : ZMod Q)) = p0.1 then (jacobiSym (ω.val : ℤ) e : ℂ) else 0) := by
    intro ω
    have hgm : gaussMul (ω, 0) (gaussCoord Q z2)
        = ((ω * (z2.re : ZMod Q)), (ω * (z2.im : ZMod Q))) := by
      simp only [gaussMul, gaussCoord]
      ext <;> ring
    have hiff1 : (((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q)))
        ↔ gaussMul (ω, 0) (gaussCoord Q z2) = gaussCoord Q z1 := by
      rw [hgm]
      constructor
      · intro h; exact Prod.ext h.1.symm h.2.symm
      · intro h; exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
    have hiff : (((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q)))
        ↔ (ω, (0 : ZMod Q)) = p0.1 := by
      rw [hiff1, gaussMul_rat_eq_iff Q z1 z2 hunit ω, hp0val]
    by_cases h : (ω, (0 : ZMod Q)) = p0.1
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
  have hL : (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0))
      = ratWeight Q e p0 := by
    rw [Finset.sum_congr rfl (fun ω _ => hcollapse ω)]
    by_cases hr : p0.1.2 = 0
    · have hstep : ∀ ω : ZMod Q,
          (if (ω, (0 : ZMod Q)) = p0.1 then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)
          = (if ω = p0.1.1 then (jacobiSym (ω.val : ℤ) e : ℂ) else 0) := by
        intro ω
        have hiff1 : ((ω, (0 : ZMod Q)) = p0.1) ↔ ω = p0.1.1 := by
          constructor
          · intro h; exact congrArg Prod.fst h
          · intro h; exact Prod.ext h hr.symm
        by_cases h : ω = p0.1.1
        · rw [if_pos (hiff1.mpr h), if_pos h]
        · rw [if_neg (fun hc => h (hiff1.mp hc)), if_neg h]
      rw [Finset.sum_congr rfl (fun ω _ => hstep ω), Finset.sum_ite_eq', ratWeight, if_pos hr]
      simp
    · have hzero : ∀ ω : ZMod Q, ¬ ((ω, (0 : ZMod Q)) = p0.1) := by
        intro ω h
        exact hr (by rw [← h])
      rw [Finset.sum_eq_zero (fun ω _ => if_neg (hzero ω)), ratWeight, if_neg hr]
  rw [hL, hR]

end

end Work.FIArea7
