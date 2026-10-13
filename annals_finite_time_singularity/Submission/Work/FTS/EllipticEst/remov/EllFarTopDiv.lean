import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarReflect
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_vBound
import Submission.Work.FTS.EllipticEst.remov.hardyDiv_fin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top-order reflected divided-derivative slot (independent proof)

`∫_0^{π/8} ((U/x)^{(k+1)})² sin(2x)^{2k-γ} ≤ C·FarR k γ u g`, `U = shiftU u` — the `i = k+1`
slot of `TopCoreB/far_vBound.lean` (whose `i ≤ k` case is
`TopCoreB.integrableOn_sinWeight_xDivX` / `TopCoreB.xTerm_le`).

Route: with the Leibniz identity `x·(U/x)^{(k+1)} = U^{(k+1)} - (k+1)(U/x)^{(k)}`, the factor
`sin(2x)²/x² ≤ 4` on `(0, π/8]` gives the pointwise bound

`((U/x)^{(k+1)})² sin(2x)^e ≤ 8 ((U^{(k+1)})² + (k+1)² ((U/x)^{(k)})²) sin(2x)^{e-2}`,

and both terms on the right are controlled by `FarR`: the first is the `j = k+1` slot of `FarR`
itself, the second by the weighted Hardy division `TopCoreB.hardyDiv_int_r` at
`(j, γ') = (k, γ+2)`, whose output `∫ x^{e-2} (U^{(k+1)})²` is again the `j = k+1` slot (after
`x ≤ sin 2x`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.EllFarTopDiv

open Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `sin (2x) ^ e = sin (2x) ^ (e - 2) · sin (2x)²`. -/
private lemma rpow_sin_two_split {x e : ℝ} (hs : 0 < Real.sin (2 * x)) :
    (Real.sin (2 * x)) ^ e = (Real.sin (2 * x)) ^ (e - 2) * (Real.sin (2 * x)) ^ 2 := by
  have h2 : (Real.sin (2 * x)) ^ (2 : ℝ) = (Real.sin (2 * x)) ^ 2 := by
    rw [Real.rpow_two, pow_two]
  have h1 : (Real.sin (2 * x)) ^ e = (Real.sin (2 * x)) ^ ((e - 2) + 2) := by
    congr 1
    ring
  rw [h1, Real.rpow_add hs, h2]

/-- `(A/x)² sin(2x)^e ≤ 4 A² sin(2x)^{e-2}` on `(0, π/8]`. -/
private lemma div_sq_rpow_le {A x e : ℝ} (hx : 0 < x) (hs : 0 < Real.sin (2 * x))
    (hle : Real.sin (2 * x) ≤ 2 * x) :
    (A / x) ^ 2 * (Real.sin (2 * x)) ^ e
      ≤ 4 * A ^ 2 * (Real.sin (2 * x)) ^ (e - 2) := by
  rw [rpow_sin_two_split hs]
  have hsnn : 0 ≤ (Real.sin (2 * x)) ^ (e - 2) := Real.rpow_nonneg hs.le _
  have hxne : x ≠ 0 := ne_of_gt hx
  have habs : |(A / x) * Real.sin (2 * x)| ≤ |(A / x) * (2 * x)| := by
    rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos (by positivity : 0 < 2 * x)]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  have h3 : ((A / x) * Real.sin (2 * x)) ^ 2 ≤ ((A / x) * (2 * x)) ^ 2 :=
    (sq_le_sq).mpr habs
  have h4 : ((A / x) * (2 * x)) ^ 2 = (2 * A) ^ 2 := by
    field_simp
  have h5 : (A / x) ^ 2 * (Real.sin (2 * x)) ^ 2 = ((A / x) * Real.sin (2 * x)) ^ 2 := by
    ring
  have key : (A / x) ^ 2 * (Real.sin (2 * x)) ^ 2 ≤ (2 * A) ^ 2 :=
    h5.le.trans (h3.trans h4.le)
  calc (A / x) ^ 2 * ((Real.sin (2 * x)) ^ (e - 2) * (Real.sin (2 * x)) ^ 2)
      = ((A / x) ^ 2 * (Real.sin (2 * x)) ^ 2) * (Real.sin (2 * x)) ^ (e - 2) := by ring
    _ ≤ (2 * A) ^ 2 * (Real.sin (2 * x)) ^ (e - 2) :=
        mul_le_mul_of_nonneg_right key hsnn
    _ = 4 * A ^ 2 * (Real.sin (2 * x)) ^ (e - 2) := by ring

/-- `sin (2x) ≤ 2x` for `x ≥ 0`. -/
private lemma sin_two_le_two_mul {x : ℝ} (hx : 0 ≤ x) : Real.sin (2 * x) ≤ 2 * x :=
  Real.sin_le (x := 2 * x) (by linarith)

/-- `2^{E-2} ≤ 4^k` when `E - 2 ≤ 2k`. -/
private lemma two_rpow_sub_le (k : ℕ) {E : ℝ} (hE : E - 2 ≤ 2 * (k : ℝ)) :
    Real.rpow (2 : ℝ) (E - 2) ≤ (4 : ℝ) ^ k := by
  have h1 : Real.rpow (2 : ℝ) (E - 2) ≤ Real.rpow (2 : ℝ) (2 * (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
  have h2 : Real.rpow (2 : ℝ) (2 * (k : ℝ)) = (4 : ℝ) ^ k := by
    rw [Real.rpow_eq_pow]
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_natCast]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  calc Real.rpow (2 : ℝ) (E - 2) ≤ Real.rpow (2 : ℝ) (2 * (k : ℝ)) := h1
    _ = (4 : ℝ) ^ k := h2

/-- The Leibniz identity `x·(U/x)^{(n+1)} = U^{(n+1)} - (n+1)(U/x)^{(n)}`. -/
private theorem x_mul_iteratedDeriv_div (n : ℕ) {a b : ℝ} {U : ℝ → ℝ}
    (hU : ContDiffOn ℝ (n + 1) U (Set.Ioo a b)) (ha : 0 ≤ a) :
    ∀ x ∈ Set.Ioo a b,
      x * iteratedDeriv (n + 1) (fun y : ℝ => U y / y) x
        = iteratedDeriv (n + 1) U x - (n + 1) * iteratedDeriv n (fun y : ℝ => U y / y) x := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hx.1)
  have hUat : ContDiffAt ℝ (n + 1) U x := hU.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hgn : ContDiffAt ℝ (n + 1) (fun y : ℝ => U y / y) x := hUat.div contDiffAt_id hx0
  have hev : U =ᶠ[𝓝 x] fun y : ℝ => y * (U y / y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have hy0 : y ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hy.1)
    field_simp
  have hmul := iteratedDeriv_mul (n := n + 1) (x := x)
    (f := fun y : ℝ => y) (g := fun y : ℝ => U y / y) contDiffAt_id hgn
  have hid1 : iteratedDeriv 1 (fun y : ℝ => y) x = 1 := by
    have hfun : (fun y : ℝ => y) = id := rfl
    rw [hfun, iteratedDeriv_id]
    rw [if_neg (by norm_num : ¬ ((1 : ℕ) = 0)), if_pos rfl]
  have hid0 : iteratedDeriv 0 (fun y : ℝ => y) x = x := by
    rw [iteratedDeriv_zero]
  have hsplit : (∑ i ∈ Finset.range (n + 2),
        ((n + 1).choose i : ℝ) * iteratedDeriv i (fun y : ℝ => y) x
          * iteratedDeriv (n + 1 - i) (fun y : ℝ => U y / y) x)
      = x * iteratedDeriv (n + 1) (fun y : ℝ => U y / y) x
        + ((n + 1 : ℕ) : ℝ) * iteratedDeriv n (fun y : ℝ => U y / y) x := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    have htail : (∑ k ∈ Finset.range n,
        ((n + 1).choose (k + 1 + 1) : ℝ) * iteratedDeriv (k + 1 + 1) (fun y : ℝ => y) x
          * iteratedDeriv (n + 1 - (k + 1 + 1)) (fun y : ℝ => U y / y) x) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have h0 : iteratedDeriv (k + 1 + 1) (fun y : ℝ => y) x = 0 := by
        have hfun : (fun y : ℝ => y) = id := rfl
        rw [hfun, iteratedDeriv_id,
          if_neg (by omega : ¬ (k + 1 + 1 = 0)), if_neg (by omega : ¬ (k + 1 + 1 = 1))]
      rw [h0, mul_zero, zero_mul]
    rw [htail]
    rw [Nat.zero_add]
    simp only [hid1, hid0, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one,
      Nat.cast_add, one_mul, mul_one, Nat.add_sub_cancel, Nat.sub_zero]
    ring
  have hU_eq : iteratedDeriv (n + 1) U x
      = ∑ i ∈ Finset.range (n + 2),
          ((n + 1).choose i : ℝ) * iteratedDeriv i (fun y : ℝ => y) x
            * iteratedDeriv (n + 1 - i) (fun y : ℝ => U y / y) x :=
    (Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hev).trans hmul
  rw [hU_eq, hsplit]
  push_cast
  ring

/-- **The `i = k+1` reflected divided-derivative slot.** -/
theorem sinWeight_xDivX_top_le' (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd) ∧
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C * TopCoreB.FarR k γ u g := by
  refine ⟨8 * (1 + (((k : ℝ) + 1) ^ 2 * (2 * (4 : ℝ) ^ k))) + 1, by positivity, ?_⟩
  intro γ u g h
  set E : ℝ := 2 * (k : ℝ) - γ with hEdef
  set WK : ℝ → ℝ := fun x => iteratedDeriv k (fun y : ℝ => TopCoreB.shiftU u y / y) x with hWKdef
  set WL : ℝ → ℝ := fun x => iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x
    with hWLdef
  set UU : ℝ → ℝ := fun x => iteratedDeriv (k + 1) (TopCoreB.shiftU u) x with hUUdef
  have hE2 : E - 2 = 2 * ((k + 1 : ℕ) : ℝ) - 4 - γ := by rw [hEdef]; push_cast; ring
  have hE2nn : 0 ≤ E - 2 := by
    rw [hE2]
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [h.hγ2]
  -- a.e. only the interior matters
  have haeIoo : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)),
      x ∈ Set.Ioo 0 TopCoreB.xEnd := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) TopCoreB.xEnd)),
        x ∈ Set.Ioo 0 TopCoreB.xEnd := ae_restrict_mem measurableSet_Ioo
    rwa [Measure.restrict_congr_set
      (Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := TopCoreB.xEnd))] at h1
  -- the Leibniz identity
  have hUU_C : ContDiffOn ℝ (k + 1) (TopCoreB.shiftU u) (Set.Ioo 0 TopCoreB.xEnd) :=
    TopCoreB.contDiffOn_shiftU (n := k + 1)
      (h.huC.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2)))
  have hid : ∀ x ∈ Set.Ioo (0:ℝ) TopCoreB.xEnd,
      x * WL x = UU x - ((k : ℝ) + 1) * WK x := by
    intro x hx
    have hmain := x_mul_iteratedDeriv_div k (U := TopCoreB.shiftU u) hUU_C le_rfl x hx
    simpa only [hWLdef, hUUdef, hWKdef, Nat.cast_add, Nat.cast_one] using hmain
  -- the pointwise bound
  have hP : ∀ x ∈ Set.Ioo (0:ℝ) TopCoreB.xEnd,
      (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E
        ≤ 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hsin : 0 < Real.sin (2 * x) := TopCoreB.sin_two_pos_Ioc ⟨hx.1, le_of_lt hx.2⟩
    have hle : Real.sin (2 * x) ≤ 2 * x := sin_two_le_two_mul hx0.le
    have hWL : WL x = (UU x - ((k : ℝ) + 1) * WK x) / x := by
      have h := hid x hx
      rw [eq_div_iff (ne_of_gt hx0), mul_comm]
      exact h
    rw [hWL]
    have hstep := div_sq_rpow_le (A := UU x - ((k : ℝ) + 1) * WK x) (x := x) (e := E)
      hx0 hsin hle
    have hsq : (UU x - ((k : ℝ) + 1) * WK x) ^ 2
        ≤ 2 * ((UU x) ^ 2 + (((k : ℝ) + 1) * WK x) ^ 2) := by
      nlinarith [sq_nonneg (UU x + ((k : ℝ) + 1) * WK x),
        sq_nonneg (UU x - ((k : ℝ) + 1) * WK x)]
    have hrnn : 0 ≤ Real.rpow (Real.sin (2 * x)) (E - 2) := Real.rpow_nonneg hsin.le _
    calc ((UU x - ((k : ℝ) + 1) * WK x) / x) ^ 2 * Real.rpow (Real.sin (2 * x)) E
        ≤ 4 * (UU x - ((k : ℝ) + 1) * WK x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (E - 2) := hstep
      _ ≤ 4 * (2 * ((UU x) ^ 2 + (((k : ℝ) + 1) * WK x) ^ 2))
            * Real.rpow (Real.sin (2 * x)) (E - 2) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hrnn
      _ = 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) := by
          ring
  -- integrability of the pieces
  have hAint' : MeasureTheory.IntegrableOn
      (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftU u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ))
      (Set.Ioc 0 TopCoreB.xEnd) :=
    TopCoreB.integrableOn_shift_slot_Ioc (k + 1) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ) u
      (h.hH3 (k + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  have hAint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      (Set.Ioc 0 TopCoreB.xEnd) := by
    rw [hE2, hUUdef]
    exact hAint'
  have hassUU : AEStronglyMeasurable
      (fun x : ℝ => Real.rpow x (E - 2) * (UU x) ^ 2)
      (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) := by
    refine TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn ?_
    have hc : ContinuousOn (UU) (Set.Ioo 0 TopCoreB.xEnd) := by
      rw [hUUdef]
      exact TopCoreB.continuousOn_shiftU_iteratedDeriv h (j := k + 1) (by omega)
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hc.pow 2)
  have hGUint : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.rpow x (E - 2) * (UU x) ^ 2) (Set.Ioc 0 TopCoreB.xEnd) := by
    refine Integrable.mono' (f := fun x : ℝ => Real.rpow x (E - 2) * (UU x) ^ 2)
      (g := fun x : ℝ => (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)) hAint hassUU ?_
    filter_upwards [haeIoo] with x hx
    rw [Real.rpow_eq_pow]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg (UU x)))]
    have hxle : x ≤ Real.sin (2 * x) := TopCoreB.self_le_sin_two ⟨hx.1, le_of_lt hx.2⟩
    have h1 : x ^ (E - 2) ≤ (Real.sin (2 * x)) ^ (E - 2) :=
      Real.rpow_le_rpow hx.1.le hxle hE2nn
    calc x ^ (E - 2) * (UU x) ^ 2 = (UU x) ^ 2 * x ^ (E - 2) := by ring
      _ ≤ (UU x) ^ 2 * (Real.sin (2 * x)) ^ (E - 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg (UU x))
  have hE2' : E - 2 = 2 * (k : ℝ) - (γ + 2) := by rw [hEdef]; ring
  have hEk : E - 2 ≤ 2 * (k : ℝ) := by
    rw [hEdef]
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [h.hγ1]
  have hGKint : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.rpow x (E - 2) * (WK x) ^ 2) (Set.Ioc 0 TopCoreB.xEnd) := by
    obtain ⟨_Chd, _hChdpos, hdiv⟩ :=
      hardyDiv_fin k (γ + 2) (by linarith [h.hγ1]) TopCoreB.xEnd TopCoreB.xEnd_pos
    have hmain := (hdiv (TopCoreB.shiftU u) (TopCoreB.contDiffOn_shiftU_Ioc (N := k + 2) h.huC)
      (TopCoreB.tendsto_shiftU h.hucont h.hupi)
      (by simpa only [Real.rpow_eq_pow, hE2'] using hGUint)).1
    simpa only [Real.rpow_eq_pow, hE2', hWKdef] using hmain
  have hassWK : AEStronglyMeasurable
      (fun x : ℝ => (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) := by
    refine TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn ?_
    have hc : ContinuousOn (WK) (Set.Ioo 0 TopCoreB.xEnd) := by
      rw [hWKdef]
      exact TopCoreB.continuousOn_divXDeriv (N := k + 1) h.huC (by omega)
    exact (hc.pow 2).mul (TopCoreB.continuousOn_sin_rpow (p := E - 2))
  have hBint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      (Set.Ioc 0 TopCoreB.xEnd) := by
    refine TopCoreB.integrableOn_of_le_const_mul (C := Real.rpow (2 : ℝ) (E - 2))
      (Real.rpow_nonneg (by norm_num) _) hGKint hassWK ?_ ?_
    · intro x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc hx) _)
    · intro x hx
      have hx0 : 0 ≤ x := hx.1.le
      have hsin0 : 0 ≤ Real.sin (2 * x) := TopCoreB.sin_two_nonneg_Ioc hx
      have hle : Real.sin (2 * x) ≤ 2 * x := sin_two_le_two_mul hx0
      have h1 : Real.rpow (Real.sin (2 * x)) (E - 2) ≤ Real.rpow (2 * x) (E - 2) :=
        Real.rpow_le_rpow hsin0 hle hE2nn
      have h2 : Real.rpow (2 * x) (E - 2)
          = Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2) :=
        Real.mul_rpow (x := (2 : ℝ)) (y := x) (z := E - 2) (by norm_num) hx0
      rw [h2] at h1
      calc (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
          ≤ (WK x) ^ 2 * (Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg (WK x))
        _ = Real.rpow (2 : ℝ) (E - 2) * (Real.rpow x (E - 2) * (WK x) ^ 2) := by ring
  -- integral comparisons
  have hUb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)) ≤ TopCoreB.FarR k γ u g := by
    have h1 : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
        = ∫ θ in TopCoreB.farSet, (iteratedDeriv (k + 1) u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ) := by
      rw [hE2, hUUdef]
      rw [← intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le]
      rw [← TopCoreB.integral_farSet_slot_eq (k + 1) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ) u]
    rw [h1]
    exact TopCoreB.farSet_slot_le_FarR hk h (j := k + 1) (by omega) le_rfl
  have hGUb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, Real.rpow x (E - 2) * (UU x) ^ 2)
      ≤ ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2) := by
    refine integral_mono_of_nonneg ?_ hAint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg _)
    · filter_upwards [haeIoo] with x hx
      have hxle : x ≤ Real.sin (2 * x) := TopCoreB.self_le_sin_two ⟨hx.1, le_of_lt hx.2⟩
      have h1 : Real.rpow x (E - 2) ≤ Real.rpow (Real.sin (2 * x)) (E - 2) :=
        Real.rpow_le_rpow hx.1.le hxle hE2nn
      calc Real.rpow x (E - 2) * (UU x) ^ 2
          ≤ Real.rpow (Real.sin (2 * x)) (E - 2) * (UU x) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2) := by ring
  have hGKb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, Real.rpow x (E - 2) * (WK x) ^ 2)
      ≤ 2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, Real.rpow x (E - 2) * (UU x) ^ 2) := by
    have hmain := TopCoreB.hardyDiv_int_r (j := k) (by omega) (γ := γ + 2)
      (by linarith [h.hγ1]) (x₁ := TopCoreB.xEnd) TopCoreB.xEnd_pos
      (f := TopCoreB.shiftU u) (TopCoreB.contDiffOn_shiftU_Ioc (N := k + 2) h.huC)
      (TopCoreB.tendsto_shiftU h.hucont h.hupi)
      (by simpa only [Real.rpow_eq_pow, hE2'] using hGUint)
    have hconv : ∀ f : ℝ → ℝ, (∫ x in (0 : ℝ)..TopCoreB.xEnd, f x)
        = ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, f x := fun f =>
      intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le
    rw [hconv, hconv] at hmain
    simpa only [Real.rpow_eq_pow, hE2', hWKdef, hUUdef] using hmain
  have hBb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      ≤ (4 : ℝ) ^ k * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          Real.rpow x (E - 2) * (WK x) ^ 2) := by
    have hmaj : Integrable
        (fun x : ℝ => (4 : ℝ) ^ k * (Real.rpow x (E - 2) * (WK x) ^ 2))
        (volume.restrict (Set.Ioc (0 : ℝ) TopCoreB.xEnd)) := hGKint.const_mul _
    refine (integral_mono_of_nonneg ?_ hmaj ?_).trans (le_of_eq ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc hx) _)
    · filter_upwards [haeIoo] with x hx
      have hx0 : 0 < x := hx.1
      have hsin : 0 < Real.sin (2 * x) := TopCoreB.sin_two_pos_Ioc ⟨hx.1, le_of_lt hx.2⟩
      have hle : Real.sin (2 * x) ≤ 2 * x := sin_two_le_two_mul hx0.le
      have h1 : Real.rpow (Real.sin (2 * x)) (E - 2) ≤ Real.rpow (2 * x) (E - 2) :=
        Real.rpow_le_rpow hsin.le hle hE2nn
      have h2 : Real.rpow (2 * x) (E - 2)
          = Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2) :=
        Real.mul_rpow (x := (2 : ℝ)) (y := x) (z := E - 2) (by norm_num) hx0.le
      have h3 : Real.rpow (2 : ℝ) (E - 2) ≤ (4 : ℝ) ^ k := two_rpow_sub_le k hEk
      rw [h2] at h1
      have h6 : Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2)
          ≤ (4 : ℝ) ^ k * Real.rpow x (E - 2) :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hx0.le _)
      calc (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
          ≤ (WK x) ^ 2 * (Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg (WK x))
        _ ≤ (WK x) ^ 2 * ((4 : ℝ) ^ k * Real.rpow x (E - 2)) :=
            mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
        _ = (4 : ℝ) ^ k * (Real.rpow x (E - 2) * (WK x) ^ 2) := by ring
    · exact integral_const_mul _ _
  -- the main integral bound
  have hassL : AEStronglyMeasurable
      (fun x : ℝ => (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) := by
    refine TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn ?_
    have hc : ContinuousOn (WL) (Set.Ioo 0 TopCoreB.xEnd) := by
      rw [hWLdef]
      exact TopCoreB.continuousOn_divXDeriv (N := k + 1) h.huC (by omega)
    exact (hc.pow 2).mul (TopCoreB.continuousOn_sin_rpow (p := E))
  have hLHSint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      (Set.Ioc 0 TopCoreB.xEnd) := by
    have hmaj : Integrable
        (fun x : ℝ => 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))))
        (volume.restrict (Set.Ioc (0 : ℝ) TopCoreB.xEnd)) :=
      ((hAint.add (hBint.const_mul _)).const_mul 8)
    refine hmaj.mono' hassL ?_
    filter_upwards [haeIoo] with x hx
    rw [Real.rpow_eq_pow]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg (WL x))
      (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _))]
    exact hP x hx
  have hPint : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      ≤ 8 * ((∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
            (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
          + ((k : ℝ) + 1) ^ 2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) := by
    have hmaj : Integrable
        (fun x : ℝ => 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))))
        (volume.restrict (Set.Ioc (0 : ℝ) TopCoreB.xEnd)) :=
      ((hAint.add (hBint.const_mul _)).const_mul 8)
    refine (integral_mono_of_nonneg ?_ hmaj ?_).trans (le_of_eq ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc hx) _)
    · filter_upwards [haeIoo] with x hx
      exact hP x hx
    · rw [integral_const_mul, integral_add hAint (hBint.const_mul _), integral_const_mul]
  -- conclusion
  have hFarRnn : 0 ≤ TopCoreB.FarR k γ u g := TopCoreB.FarR_nonneg hk h
  have h4k : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  have hbound : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      ≤ (8 * (1 + (((k : ℝ) + 1) ^ 2 * (2 * (4 : ℝ) ^ k))) + 1)
        * TopCoreB.FarR k γ u g := by
    have hBK : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
        ≤ (2 * (4 : ℝ) ^ k) * TopCoreB.FarR k γ u g := by
      calc (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
            (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
          ≤ (4 : ℝ) ^ k * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              Real.rpow x (E - 2) * (WK x) ^ 2) := hBb
        _ ≤ (4 : ℝ) ^ k * (2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              Real.rpow x (E - 2) * (UU x) ^ 2)) :=
            mul_le_mul_of_nonneg_left hGKb h4k.le
        _ ≤ (4 : ℝ) ^ k * (2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGUb (by norm_num)) h4k.le
        _ ≤ (4 : ℝ) ^ k * (2 * TopCoreB.FarR k γ u g) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUb (by norm_num)) h4k.le
        _ = (2 * (4 : ℝ) ^ k) * TopCoreB.FarR k γ u g := by ring
    have hstep : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
        ≤ 8 * (TopCoreB.FarR k γ u g
            + ((k : ℝ) + 1) ^ 2 * ((2 * (4 : ℝ) ^ k) * TopCoreB.FarR k γ u g)) := by
      refine hPint.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact add_le_add hUb (mul_le_mul_of_nonneg_left hBK (sq_nonneg ((k : ℝ) + 1)))
    refine hstep.trans ?_
    nlinarith [hFarRnn, h4k, sq_nonneg ((k : ℝ) + 1)]
  refine ⟨?_, ?_⟩
  · simpa only [hWLdef, hEdef] using hLHSint
  · rw [intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le]
    simpa only [hWLdef, hEdef] using hbound

end Work.FTS.EllipticEst.remov.EllFarTopDiv

