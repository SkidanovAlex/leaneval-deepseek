import Mathlib
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.Cnt_eq_Nsol

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `∑_{i<N} ψ i = ∑_{x : ZMod N} ψ x.val`: the representatives `x.val ∈ [0,N)` enumerate `range N`,
so a `Finset.range` sum over `ℕ` is a sum over the residues `ZMod N` read through `.val`. -/
lemma sum_range_eq_sum_univ_val (N : ℕ) [NeZero N] (ψ : ℕ → ℂ) :
    (∑ i ∈ Finset.range N, ψ i) = ∑ x : ZMod N, ψ x.val := by
  symm
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.mpr x.val_lt
  · intro x _ y _ hxy; exact ZMod.val_injective N hxy
  · intro i hi
    exact ⟨(i : ZMod N), Finset.mem_univ _,
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hi)⟩
  · intro x _; rfl

/-- `Work.FIArea2.two_iff_one` with the residue `a` taken to be an integer (rather than a natural):
the two congruences (6.5) and the single congruence (8.2)/(8.8) have the same solutions in
`(ZMod |Δ|)²`.  The proof is that of `two_iff_one`, the only change being that `a` is an `ℤ`
from the start. -/
lemma two_iff_one_zint {z1 z2 : GaussianInt} {a : ℤ}
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)])
    (p : ZMod (Work.FIPlan.absDelta z1 z2) × ZMod (Work.FIPlan.absDelta z1 z2)) :
    ((z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 ∧
      (z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) ↔
    (a : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2 = p.2 ^ 2 := by
  have hu : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) ^ 2 + (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) ^ 2 := by
    rw [show (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))
        = ((Work.FIPlan.gnorm z1 : ℤ) : ZMod (Work.FIPlan.absDelta z1 z2))
        from (Int.cast_natCast _).symm]
    rw [gnorm_cast_sq z1]
    push_cast
    ring
  have hR : ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) + (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := congrArg (fun t : ℤ => (t : ZMod (Work.FIPlan.absDelta z1 z2)))
      (star_mul_re z1 z2)
    push_cast at h
    exact h
  have hDz : ((star z1 * z2).im : ZMod (Work.FIPlan.absDelta z1 z2)) = 0 :=
    star_mul_im_zmod_eq_zero hD
  have hid1 : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.re : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := congrArg (fun t : ℤ => (t : ZMod (Work.FIPlan.absDelta z1 z2)))
      (gnorm_mul_re z1 z2)
    push_cast at h
    rw [hDz, zero_mul, sub_zero] at h
    exact h
  have hid2 : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.im : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := congrArg (fun t : ℤ => (t : ZMod (Work.FIPlan.absDelta z1 z2)))
      (gnorm_mul_im z1 z2)
    push_cast at h
    rw [hDz, zero_mul, add_zero] at h
    exact h
  have huu : IsUnit ((Work.FIPlan.gnorm z1 : ℕ) : ZMod (Work.FIPlan.absDelta z1 z2)) :=
    (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2)).mpr hni
  have haZ : (a : ZMod (Work.FIPlan.absDelta z1 z2)) * (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))
      = ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := (ZMod.intCast_eq_intCast_iff ((a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ))
        ((star z1 * z2).re) (Work.FIPlan.absDelta z1 z2)).mpr ha
    push_cast at h
    exact h
  constructor
  · rintro ⟨h1, h2⟩
    have hRc : ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 := by
      rw [hR, hu]
      linear_combination (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * h1 + (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * h2
    have h0 : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((a : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2 - p.2 ^ 2) = 0 := by
      have hua : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (a : ZMod (Work.FIPlan.absDelta z1 z2)) = ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
        rw [mul_comm, haZ]
      rw [mul_sub, ← mul_assoc, hua, hRc, sub_self]
    have := (IsUnit.mul_right_eq_zero huu).mp h0
    rwa [sub_eq_zero] at this
  · intro h1
    have hRc : ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 := by
      calc ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
          = ((a : ZMod (Work.FIPlan.absDelta z1 z2)) * (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by rw [haZ]
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((a : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2) := by ring
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 := by rw [h1]
    refine ⟨?_, ?_⟩
    · apply IsUnit.mul_left_cancel huu
      calc (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2)
          = ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.re : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by ring
        _ = ((z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by rw [hid1]
        _ = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * (((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2) := by ring
        _ = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by rw [hRc]
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by ring
    · apply IsUnit.mul_left_cancel huu
      calc (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2)
          = ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.im : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by ring
        _ = ((z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by rw [hid2]
        _ = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * (((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2) := by ring
        _ = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by rw [hRc]
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by ring

/-- **The reduction (6.10) → (8.2)/(6.6).**  Let `a` be a residue of `z₂/z₁` modulo `|Δ|`, i.e.
`a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)` with `|z₁|² = gnorm z₁`, and assume `(|z₁|²,|Δ|) = 1` (automatic for
coprime primitive pairs, `Work.FIArea2.coprime_gnorm_absDelta`).  Then the two congruences
(6.4)/(6.5) of the definition of `Gsum` collapse to the single congruence `aγ₁² ≡ γ₂² (mod |Δ|)` of
(8.2)/(8.8) — `Work.FIArea2.Cnt_eq_Nsol` proves exactly this for the corresponding *counts* — and
therefore `G(h₁,h₂) = |Δ|⁻¹ · T(|Δ|, a, h₁, h₂)`.

Route: rewrite the two `Finset.range` sums of `Gsum` as sums over `ZMod |Δ|` (the bijection
`x ↦ x.val`), convert the two `%`-conditions into `ZMod` equations with `emod_zero_iff_zmod` and
then into the single equation with `two_iff_one` (both in
`Submission/Work/FIArea2/Cnt_eq_Nsol.lean`, which takes exactly the hypotheses `absDelta ≠ 0`,
`Nat.Coprime (gnorm z₁) (absDelta)` and `ha`), and identify `↑((|Δ|:ℝ)⁻¹)` with the complex
inverse of `↑(|Δ|:ℝ)` inside `Gsum`. -/
theorem Gsum_eq_Tsum (z1 z2 : GaussianInt)
    [NeZero (Work.FIPlan.absDelta z1 z2)] (a : ℤ)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)])
    (h1 h2 : ℤ) :
    Gsum z1 z2 h1 h2
      = (((Work.FIPlan.absDelta z1 z2 : ℝ))⁻¹ : ℂ)
          * Tsum (Work.FIPlan.absDelta z1 z2) a h1 h2 := by
  have hD : Work.FIPlan.absDelta z1 z2 ≠ 0 := NeZero.ne _
  -- the two systems of congruences have the same solutions, so the summands agree pointwise
  have hpoint : ∀ x y : ZMod (Work.FIPlan.absDelta z1 z2),
      (if (x.val ^ 2 * z2.re - y.val ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
           (x.val ^ 2 * z2.im - y.val ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
        then Complex.exp (2 * Real.pi * Complex.I
          * (((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
        else 0)
      = (if y ^ 2 = (a : ZMod (Work.FIPlan.absDelta z1 z2)) * x ^ 2
        then E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
        else 0) := by
    intro x y
    have hc : ((x.val ^ 2 * z2.re - y.val ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
               (x.val ^ 2 * z2.im - y.val ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0)
              ↔ (y ^ 2 = (a : ZMod (Work.FIPlan.absDelta z1 z2)) * x ^ 2) := by
      have e1 : (x.val ^ 2 * z2.re - y.val ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ↔
          (z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) * x ^ 2
            = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * y ^ 2 := by
        rw [emod_zero_iff_zmod (Work.FIPlan.absDelta z1 z2) x.val y.val z1.re z2.re]
        simp only [ZMod.natCast_zmod_val]
      have e2 : (x.val ^ 2 * z2.im - y.val ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ↔
          (z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) * x ^ 2
            = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * y ^ 2 := by
        rw [emod_zero_iff_zmod (Work.FIPlan.absDelta z1 z2) x.val y.val z1.im z2.im]
        simp only [ZMod.natCast_zmod_val]
      have e3 := two_iff_one_zint (z1 := z1) (z2 := z2) (a := a) hD hni ha (x, y)
      rw [e1, e2, e3]
      exact eq_comm
    by_cases h : ((x.val ^ 2 * z2.re - y.val ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
                  (x.val ^ 2 * z2.im - y.val ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0)
    · have h' : y ^ 2 = (a : ZMod (Work.FIPlan.absDelta z1 z2)) * x ^ 2 := hc.mp h
      rw [if_pos h, if_pos h']
      unfold E
      congr 1
      rw [mul_div_assoc, ← Complex.ofReal_div]
    · have h' : ¬ (y ^ 2 = (a : ZMod (Work.FIPlan.absDelta z1 z2)) * x ^ 2) :=
        fun hh => h (hc.mpr hh)
      rw [if_neg h, if_neg h']
  unfold Gsum Tsum
  congr 1
  · exact Complex.ofReal_inv _
  · have hS : (∑ γ1 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
                 ∑ γ2 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
                   (if (γ1 ^ 2 * z2.re - γ2 ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
                       (γ1 ^ 2 * z2.im - γ2 ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
                     then Complex.exp (2 * Real.pi * Complex.I
                       * (((γ1 : ℤ) * h1 + (γ2 : ℤ) * h2 : ℤ) : ℝ)
                           / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
                     else 0))
        = ∑ x : ZMod (Work.FIPlan.absDelta z1 z2), ∑ y : ZMod (Work.FIPlan.absDelta z1 z2),
                   (if (x.val ^ 2 * z2.re - y.val ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
                       (x.val ^ 2 * z2.im - y.val ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
                     then Complex.exp (2 * Real.pi * Complex.I
                       * (((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
                           / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
                     else 0) := by
      simp only [sum_range_eq_sum_univ_val]
    have hT : (∑ x : ZMod (Work.FIPlan.absDelta z1 z2), ∑ y : ZMod (Work.FIPlan.absDelta z1 z2),
                   (if y ^ 2 = (a : ZMod (Work.FIPlan.absDelta z1 z2)) * x ^ 2
                     then E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
                           / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
                     else 0))
        = ∑ x : ZMod (Work.FIPlan.absDelta z1 z2), ∑ y : ZMod (Work.FIPlan.absDelta z1 z2),
                   (if (x.val ^ 2 * z2.re - y.val ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
                       (x.val ^ 2 * z2.im - y.val ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
                     then Complex.exp (2 * Real.pi * Complex.I
                       * (((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ)
                           / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
                     else 0) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      exact (hpoint x y).symm
    exact hS.trans hT.symm

end

end Work.FIArea2
