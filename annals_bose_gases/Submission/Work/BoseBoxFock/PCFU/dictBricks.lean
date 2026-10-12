import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.Pieces.lowMult_eq_kernel_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.dictBricks` — the first position-space bricks of the cubic dictionary

The cubic dictionary (`PotCubicFreeU`) compares

* the **mode side** `ℓ⁻³Σ_{s,k}f_L(s)Ŵ₁(k)⟨Θ,(A_{s,k}+A†_{s,k})Θ⟩`, whose channel evaluations are
  PROVED (`PCFU/MiddleU_eq_four`, `PCFU/MiddleV_eq_four`, the frames `Ksfr_eq`/`Kfr_eq`/
  `KfrU_periodisation`), and
* the **position word** `q3lowWord fc κ ℓ w₁ Φ = 2Σ_{i≠j}∫_{abox}Q_{L,j}(Q_jP_iΦ)·(Q_jQ_iΦ)·w₁`,

by rewriting the word's `Q_L` (the low-momentum multiplier) and its projectors into position-space
kernels.  This module provides the two bricks that both routes need and that are *not* already on
disk:

* **`lowKer` + `lowMult_eq_lowKer`/`lowSlot_eq_lowKer`** — the position kernel
  `Κ(z) = (2π)^{-3}∫_p f(‖p‖/κ)cos⟪p,z⟫` of `lowMult` (the existing
  `Work.BoseFixB3.CS.Pieces.lowMult_eq_kernel_integral` writes it with a *complex* phase kernel
  `e^{i⟪p,x⟫}e^{-i⟪p,z⟫}`; the dictionary needs the real form `Κ(x-z)`);
* **`perm_update_swap`** — the *ket-slot swap*: on a bosonic state,
  `Θ(x[i↦y][j↦u]) = Θ(x[i↦u][j↦y])`, which is what aligns the mode side's frame
  `Ksfr(x_j−y)` (coupling the bra point `x_j` with the slot-`i` replacement `y`) with the word's
  `Κ(x_j − z)` (coupling the bra point `x_j` with the slot-`j` replacement `z`).

Both are `sorry`-free.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The position-space kernel of the low-momentum multiplier** `f(‖p‖/κ)`:
`Κ(z) = (2π)^{-3}∫_p f(‖p‖/κ)·cos⟪p,z⟫`.  This is the kernel of
`Work.BoseBoxFix.lowMult fc κ ℓ` (see `lowMult_eq_lowKer`), i.e. of FS's `f_L(√−Δ)` on the
zero-extension of the box. -/
noncomputable def lowKer (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (z : E3) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)

lemma lowKer_apply (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (z : E3) :
    lowKer fc κ z = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z) :=
  rfl

/-- `Κ` is even. -/
lemma lowKer_neg (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (z : E3) :
    lowKer fc κ (-z) = lowKer fc κ z := by
  simp only [lowKer]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [inner_neg_right, Real.cos_neg]

/-- **Elementary real-part identity**: `Re(e^{ia}·r·e^{-ib}) = r·cos(a−b)` for real `a,b,r`. -/
private lemma exp_re_mul (a b r : ℝ) :
    (Complex.exp (Complex.I * (a : ℂ)) * ((r : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (b : ℂ)))).re = r * Real.cos (a - b) := by
  have h1 : (Complex.I * (a : ℂ)).re = 0 := by simp
  have h2 : (Complex.I * (a : ℂ)).im = a := by simp
  have h3 : (-(Complex.I * (b : ℂ))).re = 0 := by simp
  have h4 : (-(Complex.I * (b : ℂ))).im = -b := by simp
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, h1, h2, h3, h4,
    Complex.ofReal_re, Complex.ofReal_im, Real.exp_zero, zero_mul, one_mul, mul_zero, mul_one,
    sub_zero, zero_sub, Real.cos_neg, Real.sin_neg, Real.cos_sub]
  ring

/-- **`lowMult` in position-kernel form**: the low-momentum multiplier of a box-restricted function
is the convolution with `Κ`, restricted to the box. -/
theorem lowMult_eq_lowKer {fc : Work.BoseBoxFix.LowCut} {κ ℓ C : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {ψ : E3 → ℝ} (hψm : MeasureTheory.AEStronglyMeasurable ψ MeasureTheory.volume)
    (hψb : ∀ z ∈ acube ℓ, |ψ z| ≤ C) (hC : 0 ≤ C) (x : E3) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ x
      = ∫ z : E3, lowKer fc κ (x - z) * (acube ℓ).indicator ψ z := by
  rw [Work.BoseFixB3.CS.Pieces.lowMult_eq_kernel_integral hκ hℓ hψm hψb hC x]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hpt : ∀ p : E3, (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re
      = fc.f (‖p‖ / κ) * Real.cos (inner ℝ p (x - z)) := by
    intro p
    rw [exp_re_mul (inner ℝ p x) (inner ℝ p z) (fc.f (‖p‖ / κ))]
    rw [inner_sub_right]
  have hfun : (fun p : E3 => (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re)
      = fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p (x - z)) :=
    funext fun p => hpt p
  simp only [hfun, lowKer]
  ring

/-- **`lowSlot` in position-kernel form**: the slot-`j` lift of `lowMult` is the convolution with
`Κ` in the `j`-th slot, restricted to the box. -/
theorem lowSlot_eq_lowKer {fc : Work.BoseBoxFix.LowCut} {κ ℓ C : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} {Ψ : X n → ℝ} (j : Fin n) (x : X n)
    (hΨm : MeasureTheory.AEStronglyMeasurable (fun z : E3 => Ψ (Function.update x j z))
      MeasureTheory.volume)
    (hΨb : ∀ z ∈ acube ℓ, |Ψ (Function.update x j z)| ≤ C) (hC : 0 ≤ C) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x
      = ∫ z : E3, lowKer fc κ (x j - z)
          * (acube ℓ).indicator (fun z : E3 => Ψ (Function.update x j z)) z :=
  lowMult_eq_lowKer hκ hℓ hΨm hΨb hC (x j)

/-- **The ket-slot swap.**  On a bosonic (permutation-invariant) state, replacing the two slots
`i ≠ j` by `(y,u)` gives the same value as replacing them by `(u,y)`:
`Θ(x[i↦y][j↦u]) = Θ(x[i↦u][j↦y])`.

This is the identity that lets the mode side's frame coupling `Ksfr(x_j − y)` (bra point `x_j`
against the slot-`i` replacement) be exchanged for the word's `Κ(x_j − z)` (bra point `x_j`
against the slot-`j` replacement). -/
theorem perm_update_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : X n → ℝ}
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (x : X n) (y u : E3) :
    Θ (Function.update (Function.update x i y) j u)
      = Θ (Function.update (Function.update x i u) j y) := by
  have hperm : Submission.BoseGases.actPerm n (Equiv.swap i j)
      (Function.update (Function.update x i u) j y)
      = Function.update (Function.update x i y) j u := by
    funext m
    simp only [Submission.BoseGases.actPerm, Function.update_apply]
    by_cases hmi : m = i
    · subst hmi
      simp [Equiv.swap_apply_left, hij]
    · by_cases hmj : m = j
      · subst hmj
        simp [Equiv.swap_apply_right, hij]
      · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]
        simp [hmi, hmj]
  rw [← hperm]
  exact hΘ (Equiv.swap i j) (Function.update (Function.update x i u) j y)

/-! ## API probes (cheap: batched into this build) -/

#check @MeasureTheory.integral_integral_swap
#check @Submission.BoseGases.acube_volume
#check @Submission.BoseGases.acube_measurable
#check @Submission.BoseGases.pairSet
#check @Submission.BoseGases.wLoc
#check @Work.BoseKinLoc.fibre
#check @Submission.BoseGases.abox
#check @Work.BoseBoxFix.LowCut.anti
#check @Work.BoseBoxFix.LowCut.zero
#check @Work.BoseBoxFix.LowCut.one
#check @Work.BoseBoxFix.q3lowWord

end Work.BoseBoxFock.PCFU
