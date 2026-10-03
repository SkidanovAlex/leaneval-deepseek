import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea7.ratioSym_eq_jacobiSym_omega
import Submission.Work.FIArea7.existsUnique_omega_of_dvd_delta
import Submission.Work.FIArea7.dvd_delta_iff_exists_omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Two elementary unfoldings of `omegaDetect`

`Work.FIArea7.omegaDetect Q e z₁ z₂` is, by definition, the sum over the rational classes
`ω (mod Q)` of the weight `(ω|e)` on the (at most one) class with `z₁ ≡ ω z₂ (mod Q)`.  These two
lemmas merely restate that definition; they are stated here (rather than imported from
`Work.FIArea7.WBOmega6`) so that this module stays light. -/

/-- `omegaDetect` at a nonzero modulus is the sum over the classes `ω (mod Q)` of the weight
`(ω|e)`, restricted to the congruence `z₁ ≡ ω z₂ (mod Q)`. -/
private lemma omegaDetect_unfold (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt) :
    Work.FIArea7.omegaDetect Q e z1 z2
      = ∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0) := by
  rw [Work.FIArea7.omegaDetect, dif_neg (NeZero.ne Q)]

/-- When the congruence `z₁ ≡ ω z₂ (mod Q)` has the unique solution `ω₀`, the detection sum
`omegaDetect` collapses to the single weight `(ω₀|e)`. -/
private lemma omegaDetect_eq_of_unique (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt) {ω₀ : ZMod Q}
    (huniq : ∀ ω : ZMod Q, (((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
        ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))) ↔ ω = ω₀) :
    Work.FIArea7.omegaDetect Q e z1 z2 = (jacobiSym (ω₀.val : ℤ) e : ℂ) := by
  rw [omegaDetect_unfold Q e z1 z2]
  have hstep : ∀ ω : ZMod Q,
      (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)
      = (if ω = ω₀ then (jacobiSym (ω.val : ℤ) e : ℂ) else 0) := by
    intro ω
    by_cases h : ω = ω₀
    · rw [if_pos ((huniq ω).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((huniq ω).mp hc)), if_neg h]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω), Finset.sum_ite_eq']
  simp

/-- *FI* (16.3)/(16.4): for a pair of Gaussian integers both coprime to `4d`, the `ω`-detection sum over the rational classes `ω (mod 4d)` of the weight `(ω|d)` is `[4d ∣ |Δ(z₁,z₂)|]·(z₂/z₁|d)`. -/
theorem omegaDet_eq_ratioSym (d : ℕ) (hd : 1 ≤ d) (z1 z2 : GaussianInt)
    (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) (4 * d))
    (h2 : Nat.Coprime (Work.FIPlan.gnorm z2) (4 * d)) :
    Work.FIArea6.omegaDet d z1 z2
      = (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
          (Work.FITop4.ratioSym z1 z2 d : ℂ) else 0) := by
  have hQ0 : 0 < 4 * d := by omega
  have hQ : 4 * d ≠ 0 := by omega
  haveI : NeZero (4 * d) := ⟨hQ⟩
  haveI : NeZero d := ⟨by omega⟩
  -- `4d ∣ |Δ|` is the same as `(4d : ℤ) ∣ Δ`
  have hdvd_iff : 4 * d ∣ Work.FIPlan.absDelta z1 z2
      ↔ (4 * d : ℤ) ∣ Work.FIPlan.Delta z1 z2 := by
    simpa [Work.FIPlan.absDelta, show ((4 * d : ℤ)).natAbs = 4 * d by omega]
      using Int.natAbs_dvd_natAbs (a := (4 * d : ℤ)) (b := Work.FIPlan.Delta z1 z2)
  -- the congruence has a solution iff `4d ∣ Δ`
  have hcong : (4 * d : ℤ) ∣ Work.FIPlan.Delta z1 z2
      ↔ ∃ ω : ZMod (4 * d), (z1.re : ZMod (4 * d)) = ω * (z2.re : ZMod (4 * d))
        ∧ (z1.im : ZMod (4 * d)) = ω * (z2.im : ZMod (4 * d)) :=
    Work.FIArea7.dvd_delta_iff_exists_omega hQ0 z1 z2 h2
  rw [Work.FIArea6.omegaDet]
  by_cases hD : 4 * d ∣ Work.FIPlan.absDelta z1 z2
  · -- divisibility holds: the class is unique and the sum collapses to `(ω₀|d)`
    rw [if_pos hD]
    obtain ⟨ω₀, hω₀, huniq⟩ :=
      Work.FIArea7.existsUnique_omega_of_dvd_delta hQ0 z1 z2 h2 (hdvd_iff.mp hD)
    have huniq' : ∀ ω : ZMod (4 * d),
        (((z1.re : ZMod (4 * d)) = ω * (z2.re : ZMod (4 * d))) ∧
         ((z1.im : ZMod (4 * d)) = ω * (z2.im : ZMod (4 * d)))) ↔ ω = ω₀ :=
      fun ω => ⟨huniq ω, fun h => by rw [h]; exact hω₀⟩
    rw [omegaDetect_eq_of_unique (4 * d) d z1 z2 huniq']
    -- `ω₀` is a unit: `|z₁|² ≡ ω₀²|z₂|² (mod 4d)` with both norms invertible
    have hN1 : (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod (4 * d))
        = (z1.re : ZMod (4 * d)) ^ 2 + (z1.im : ZMod (4 * d)) ^ 2 := by
      rw [← Int.cast_natCast, Work.FIArea7.norm_eq]
      push_cast
      ring
    have hN2 : (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod (4 * d))
        = (z2.re : ZMod (4 * d)) ^ 2 + (z2.im : ZMod (4 * d)) ^ 2 := by
      rw [← Int.cast_natCast, Work.FIArea7.norm_eq]
      push_cast
      ring
    have hU1 : IsUnit (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod (4 * d)) :=
      (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z1) (4 * d)).mpr h1
    have hsq : ω₀ ^ 2 * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod (4 * d))
        = (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod (4 * d)) := by
      rw [hN1, hN2, hω₀.1, hω₀.2]
      ring
    have hu2 : IsUnit (ω₀ ^ 2) :=
      isUnit_of_mul_isUnit_left (by rw [hsq]; exact hU1)
    have hunit : IsUnit ω₀ := (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hu2
    have hrw : Work.FITop4.ratioSym z1 z2 d = jacobiSym (ω₀.val : ℤ) d :=
      Work.FIArea7.ratioSym_eq_jacobiSym_omega (q := 4 * d) (e := d)
        ⟨4, by ring⟩ hunit huniq' h2
    rw [hrw]
  · -- no class satisfies the congruence, so every summand vanishes
    rw [if_neg hD]
    rw [omegaDetect_unfold (4 * d) d z1 z2]
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    intro hc
    exact hD (hdvd_iff.mpr (hcong.mpr ⟨ω, hc⟩))

end

end Work.FIArea6
