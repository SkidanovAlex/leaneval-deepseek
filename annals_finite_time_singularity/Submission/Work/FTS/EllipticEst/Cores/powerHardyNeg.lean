import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.EllipticEst.Core.hardyBoundaryPower

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Hardy inequality `∫ x^{a-2} v² ≤ (4/(1-a)²) ∫ x^a (v')²` on `[lo,hi]`

For `0 < a < 1`, `0 < lo < hi < π/2` and `v` of class `C¹` on `(0, π/2)` with `v lo = 0`:

  `∫_{lo}^{hi} x^{a-2} v(x)² dx ≤ (4/(1-a)²) ∫_{lo}^{hi} x^a v'(x)² dx`.

This is the sharp weighted (power) Hardy inequality, with the anchor at the *left* endpoint `lo`
and with the exponent `a - 2` on the mass term ranging in `(-2,-1)` (equivalently the exponent `a`
on the derivative term ranges in `(0,1)`), so that `Work.Elliptic.power_hardy` and
`Work.FTS.EllipticEst.TT.powerHardy_at` do not apply directly: both require the derivative
exponent `-η` to be `≤ 0`, i.e. `η ≥ 0`.  The purpose of this file is the complementary range.

The proof is the standard completion of squares, exactly as in `powerHardy_at` (whose proof uses
`0 ≤ η < 1` only through `-1 < η`):

* `0 ≤ t^{-η} (g'(t) - (1+η)/2 · g(t)/t)²` rewrites as
  `(1+η)²/4 · g(t)² t^{-(2+η)} ≤ g'(t)² t^{-η} - ((1+η)/2) · Φ'(t)` with
  `Φ(t) = g(t)² t^{-(1+η)}`;
* integrating over `[ε,A]` and applying the fundamental theorem of calculus, the left boundary
  term `-((1+η)/2)Φ(ε)` vanishes because `g ε = 0`, while the right one `-((1+η)/2)Φ(A) ≤ 0`
  has the favourable sign (this is where `η > -1` is used), giving
  `(1+η)²/4 ∫ g² t^{-(2+η)} ≤ ∫ g'² t^{-η}`.

The tool lemma `powerHardy_at_gen` is stated for a general exponent `η > -1` (and is proved with
`derivWithin` on the closed interval so that every integrand is continuous there); the target
`powerHardyNeg` is its instance `η = -a` on `[lo,hi]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The sharp power-weighted Hardy inequality on `[ε,A]`, anchored at `ε`, for every exponent
`η > -1`.**

For `0 < ε < A`, `-1 < η` and `g` of class `C¹` on `[ε,A]` with `g ε = 0`,

  `∫_ε^A g(t)² t^{-(2+η)} dt ≤ 4/(1+η)² ∫_ε^A g'(t)² t^{-η} dt`.

(The sibling `Work.FTS.EllipticEst.TT.powerHardy_at` is the case `0 ≤ η < 1`; the proof only
needs `-1 < η`, which is the range needed for `powerHardyNeg` below.) -/
theorem powerHardy_at_gen {ε A η : ℝ} (hε : 0 < ε) (hεA : ε < A) (hη : -1 < η)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g (Set.Icc ε A)) (h0 : g ε = 0) :
    (∫ t in ε..A, g t ^ 2 * t ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * ∫ t in ε..A, (deriv g t) ^ 2 * t ^ (-η) := by
  have hεle : ε ≤ A := le_of_lt hεA
  set d : ℝ → ℝ := derivWithin g (Set.Icc ε A) with hddef
  have hdu : UniqueDiffOn ℝ (Set.Icc ε A) := uniqueDiffOn_Icc hεA
  have hdc : ContinuousOn d (Set.Icc ε A) :=
    hg.continuousOn_derivWithin hdu le_rfl
  have hgc : ContinuousOn g (Set.Icc ε A) := hg.continuousOn
  -- `d` agrees with the two-sided derivative on the interior
  have hdeq : ∀ t ∈ Set.Ioo ε A, d t = deriv g t := by
    intro t ht
    exact derivWithin_of_mem_nhds (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)
  -- the auxiliary function `Ψ` and its derivative `φ` (written with `d`)
  set Ψ : ℝ → ℝ := fun t => g t ^ 2 * t ^ (-(1 + η)) with hΨdef
  set φ : ℝ → ℝ := fun t =>
    2 * (g t * d t * t ^ (-(1 + η))) - (1 + η) * (g t ^ 2 * t ^ (-(2 + η))) with hφdef
  have hrpow1 : ContinuousOn (fun t : ℝ => t ^ (-(1 + η))) (Set.Icc ε A) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1)))
  have hrpow2 : ContinuousOn (fun t : ℝ => t ^ (-(2 + η))) (Set.Icc ε A) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1)))
  have hΨc : ContinuousOn Ψ (Set.Icc ε A) := by
    simp only [hΨdef]; exact (hgc.pow 2).mul hrpow1
  have hφc : ContinuousOn φ (Set.Icc ε A) := by
    simp only [hφdef]
    exact (((hgc.mul hdc).mul hrpow1).const_mul 2).sub
      ((hgc.pow 2 |>.mul hrpow2).const_mul (1 + η))
  have hIφ : IntervalIntegrable φ volume ε A := hφc.intervalIntegrable_of_Icc hεle
  -- the derivative identity on the interior
  have hderiv : ∀ x ∈ Set.Ioo ε A, HasDerivAt Ψ (φ x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hε hx.1)
    have hmem : Set.Icc ε A ∈ 𝓝 x :=
      mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
    have hdx : deriv g x = d x := (hdeq x hx).symm
    have hd : HasDerivAt g (d x) x := by
      have h1 : HasDerivAt g (deriv g x) x :=
        (hg.differentiableOn_one.differentiableAt hmem).hasDerivAt
      rwa [← hdx]
    have h1 : HasDerivAt (fun s : ℝ => g s ^ 2) (2 * g x ^ 1 * d x) x := hd.pow 2
    have h2 : HasDerivAt (fun s : ℝ => s ^ (-(1 + η))) (-(1 + η) * x ^ (-(1 + η) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0)
    have h3 := h1.mul h2
    rw [show -(1 + η) - 1 = -(2 + η) by ring] at h3
    simp only [hΨdef, hφdef]
    refine h3.congr_deriv ?_
    ring
  -- the fundamental theorem of calculus
  have hFTC : (∫ t in ε..A, φ t) = Ψ A - Ψ ε :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεle hΨc hderiv hIφ
  have hΨε : Ψ ε = 0 := by
    simp only [hΨdef, h0]; ring
  -- the pointwise completion of squares
  have hpt : ∀ t ∈ Set.Ioo ε A,
      (1 + η) ^ 2 / 4 * (g t ^ 2 * t ^ (-(2 + η)))
        ≤ (d t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hε ht.1
    simp only [hφdef]
    have hid1 : t ^ 2 * t ^ (-(2 + η)) = t ^ (-η) := by
      rw [← Real.rpow_two t, ← Real.rpow_add ht0]; congr 1; ring
    have hid2 : t * t ^ (-(1 + η)) = t ^ (-η) := by
      have h := Real.rpow_add ht0 (1 : ℝ) (-(1 + η))
      rw [show (1 : ℝ) + (-(1 + η)) = -η by ring] at h
      rw [Real.rpow_one] at h
      exact h.symm
    have h2 : (g t / t) ^ 2 * t ^ 2 = g t ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 ht0.ne')]
    have hx1 : g t ^ 2 * t ^ (-(2 + η)) = (g t / t) ^ 2 * t ^ (-η) := by
      calc g t ^ 2 * t ^ (-(2 + η)) = ((g t / t) ^ 2 * t ^ 2) * t ^ (-(2 + η)) := by rw [h2]
        _ = (g t / t) ^ 2 * (t ^ 2 * t ^ (-(2 + η))) := by ring
        _ = (g t / t) ^ 2 * t ^ (-η) := by rw [hid1]
    have hx2 : g t * d t * t ^ (-(1 + η)) = (g t / t) * d t * t ^ (-η) := by
      have h3 : (g t / t) * t = g t := div_mul_cancel₀ (g t) ht0.ne'
      calc g t * d t * t ^ (-(1 + η))
          = ((g t / t) * t) * d t * t ^ (-(1 + η)) := by rw [h3]
        _ = (g t / t) * d t * (t * t ^ (-(1 + η))) := by ring
        _ = (g t / t) * d t * t ^ (-η) := by rw [hid2]
    rw [hx1, hx2]
    nlinarith [mul_nonneg (Real.rpow_nonneg ht0.le (-η))
      (sq_nonneg (d t - (1 + η) / 2 * (g t / t)))]
  -- integrability of the two integrands of the pointwise bound
  have hint1 : IntervalIntegrable (fun t : ℝ => g t ^ 2 * t ^ (-(2 + η))) volume ε A :=
    ((hgc.pow 2).mul hrpow2).intervalIntegrable_of_Icc hεle
  have hint3 : IntervalIntegrable (fun t : ℝ => d t ^ 2 * t ^ (-η)) volume ε A := by
    have hc : ContinuousOn (fun t : ℝ => d t ^ 2 * t ^ (-η)) (Set.Icc ε A) :=
      (hdc.pow 2).mul (continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1))))
    exact hc.intervalIntegrable_of_Icc hεle
  have hmono : ∫ t in ε..A, (1 + η) ^ 2 / 4 * (g t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in ε..A, ((d t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hεle
      (hint1.const_mul _) (hint3.add (hIφ.const_mul _)) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_add hint3 (hIφ.const_mul _),
    intervalIntegral.integral_const_mul] at hmono
  rw [hFTC, hΨε, sub_zero] at hmono
  have hle : (-(1 + η) / 2) * Ψ A ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans hε.le hεle) _))
  have hkey : (1 + η) ^ 2 / 4 * (∫ t in ε..A, g t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in ε..A, (d t) ^ 2 * t ^ (-η) := by
    linarith [hmono, hle]
  -- replace `d` by `deriv g` on the interior
  have hdint : (∫ t in ε..A, (d t) ^ 2 * t ^ (-η))
      = ∫ t in ε..A, (deriv g t) ^ 2 * t ^ (-η) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton A)
    intro x hx
    simp only [Set.mem_setOf_eq, not_imp] at hx
    obtain ⟨hxmem, hxne⟩ := hx
    by_contra hxA
    simp only [Set.mem_singleton_iff] at hxA
    rw [Set.uIoc_of_le hεle] at hxmem
    have hxlt : x < A := lt_of_le_of_ne hxmem.2 hxA
    exact hxne (by rw [hdeq x ⟨hxmem.1, hxlt⟩])
  rw [hdint] at hkey
  have hsq : (0 : ℝ) < (1 + η) ^ 2 := pow_pos (by linarith) 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
  nlinarith [hkey, hsq]

/-- **Weighted Hardy inequality on `[lo,hi]` with the anchor at `lo`.**

For `0 < a < 1`, `0 < lo < hi < π/2` and `v` of class `C¹` on `(0, π/2)` with `v lo = 0`,

  `∫_{lo}^{hi} x^{a-2} v(x)² dx ≤ (4/(1-a)²) ∫_{lo}^{hi} x^a v'(x)² dx`. -/
lemma powerHardyNeg {a lo hi : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hlo : 0 < lo)
    (hlohi : lo < hi) (hhi : hi < Real.pi / 2) {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 1 v (Set.Ioo 0 (Real.pi / 2))) (hvlo : v lo = 0) :
    (∫ x in lo..hi, x ^ (a - 2) * v x ^ 2)
      ≤ (4 / (1 - a) ^ 2) * (∫ x in lo..hi, x ^ a * (deriv v x) ^ 2) := by
  have hsub : Set.Icc lo hi ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hlo hx.1, lt_of_le_of_lt hx.2 hhi⟩
  have hg : ContDiffOn ℝ 1 v (Set.Icc lo hi) := hv.mono hsub
  have hη : (-1 : ℝ) < -a := by linarith
  have h := powerHardy_at_gen (ε := lo) (A := hi) (η := -a) hlo hlohi hη hg hvlo
  rw [show -(2 + -a) = a - 2 by ring, show -(-a) = a by ring,
    show 1 + -a = 1 - a by ring] at h
  calc (∫ x in lo..hi, x ^ (a - 2) * v x ^ 2)
      = ∫ x in lo..hi, v x ^ 2 * x ^ (a - 2) := by
        refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    _ ≤ (4 / (1 - a) ^ 2) * (∫ x in lo..hi, (deriv v x) ^ 2 * x ^ a) := h
    _ = (4 / (1 - a) ^ 2) * (∫ x in lo..hi, x ^ a * (deriv v x) ^ 2) := by
        congr 1
        refine intervalIntegral.integral_congr (fun x _ => ?_); ring

end Work.FTS.EllipticEst.Cores
