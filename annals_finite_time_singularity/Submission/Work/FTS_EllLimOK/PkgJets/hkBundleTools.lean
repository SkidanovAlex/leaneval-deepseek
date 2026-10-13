import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.EllipticEst.Honest.HonCosSliceIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Generic `ℋ⁰`-tools: the level-`0` integrand, domination, and slot extraction

The `ℋ⁰`-integrand of `Work.Spaces` collapses to the single square of the weighted function;
this module collects the elementary tools used to *produce* `ℋ⁰`-memberships:

* `hkIntegrand_zero_eq`, `hkIntegrand_zero_of_sin_eq_zero`: the collapse and its vanishing on
  the two angular endpoints;
* `wdivsin_nonneg`, `rpow_eta_le_rpow_gam`, `Wt_nonneg`, `wdivsin_le_Wt`: the comparison of the
  level-`0` weight with the `γ`-weight of the mixed slots (`η ≤ γ`);
* `hkMem_zero_of_majorant` and the domination corollaries `hkMem_zero_of_abs_le{,_two,_three}`:
  `ℋ⁰`-membership from a pointwise domination of the weighted function, with the domination
  required only for `z > 0` (at `z = 0` the integrand vanishes identically);
* `hkMem_zero_of_mem_DzIter`, `hkMem_zero_of_mem_mixed`: the level-`0` honesty of a single
  weighted slot `D_z^iF` resp. `D_z^jD_θ^iF` of an `ℋ^k`-function;
* `smoothOpen_div_cos`: `SmoothOpen`-closure under division by `cos θ`;
* `integrableOn_sq_Lop_iter`: the `θ`-square of an iterate of `Lop = sin(2·)∂_θ` applied to a
  function `C^∞` on an open neighbourhood of `Iθ` is integrable there (via
  `contDiffOn_infty_iff_deriv_of_isOpen`, i.e. `deriv` preserves the honest `C^∞` order on open
  sets — *not* the analytic order `⊤`).
-/

/-! ## §1  Elementary facts about the level-`0` integrand and its weight -/

/-- At level `0` the `ℋ^k`-integrand collapses to the single square of the weighted function. -/
theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The level-`0` integrand vanishes wherever `sin 2θ` does (the weight carries a factor
`sin(2θ)^{-η/2}` and `0^{-η/2} = 0`). -/
theorem hkIntegrand_zero_of_sin_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [hkIntegrand_zero_eq, h, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero, mul_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- A point of `Iθ` where `sin 2θ ≠ 0` is interior. -/
theorem mem_Ioo_of_mem_Iθ_of_sin_ne {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : Real.sin (2 * θ) ≠ 0) : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  refine ⟨lt_of_le_of_ne hθ.1 (Ne.symm ?_), lt_of_le_of_ne hθ.2 ?_⟩
  · intro h0; exact h (by rw [h0]; norm_num)
  · intro h2; exact h (by rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])

/-- `0 ≤ sin 2θ ≤ 1` on `Iθ`. -/
theorem sin_two_mem_Icc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ∈ Set.Icc 0 1 :=
  ⟨Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩,
    Real.sin_le_one _⟩

/-- The level-`0` weight is nonnegative on `Iθ`. -/
theorem wdivsin_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  rw [Work.Spaces.w]
  refine div_nonneg (by positivity) (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ?_) _)
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin(2θ)^{-η/2} ≤ sin(2θ)^{-γ/2}` on `Iθ` (since `γ ≥ η` and `sin 2θ ≤ 1`). -/
theorem rpow_eta_le_rpow_gam {α : ℝ} (_hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
  rcases eq_or_lt_of_le (sin_two_mem_Icc hθ).1 with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta / 2) ≠ 0),
      Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith)]
  · refine Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) ?_
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- The product weight `W = w · w_θ` is nonnegative on `Iθ`. -/
theorem Wt_nonneg {α : ℝ} (_hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Wt α z θ := by
  rw [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (sin_two_mem_Icc hθ).1 _)

/-- The level-`0` weight is dominated by the `γ`-weight of the mixed slots. -/
theorem wdivsin_le_Wt {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ Work.Spaces.Wt α z θ := by
  rcases eq_or_lt_of_le (sin_two_mem_Icc hθ).1 with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0), div_zero,
      Work.Spaces.Wt, Work.Spaces.wTheta, ← h0,
      Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith)]
    norm_num
  · have hle := rpow_eta_le_rpow_gam hα hθ
    have hrw : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
      rw [Real.rpow_neg hpos.le, div_eq_mul_inv]
    rw [hrw, Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_le_mul_of_nonneg_left hle (by rw [Work.Spaces.w]; positivity)

/-! ## §2  `ℋ⁰`-membership by domination -/

/-- `ℋ⁰`-membership from a pointwise majorant of the level-`0` integrand.  The domination is
only required for `z > 0`: at `z = 0` the integrand vanishes identically. -/
theorem hkMem_zero_of_majorant {α : ℝ} {f M : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hM0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ M 0 θ)
    (hle : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ ≤ M z θ) :
    Work.Spaces.HkMem α 0 f := by
  refine Work.FTS.LocData.HkMem_of_majorant α 0 (hf.continuousOn_HkIntegrand α 0)
    hMslice hMz ?_
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · rw [← h0,
      show Work.Spaces.HkIntegrand α 0 f 0 θ = 0 from Work.FTS.LocData.HkIntegrand_zero_fst α 0 f θ]
    exact hM0 θ hθ
  · exact hle z hpos θ hθ

/-- `ℋ⁰`-membership from a pointwise domination `|f| ≤ |g|` (with `g ∈ ℋ⁰`). -/
theorem hkMem_zero_of_abs_le {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 0 g)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f z θ| ≤ |g z θ|) :
    Work.Spaces.HkMem α 0 f := by
  refine hkMem_zero_of_majorant hf (M := Work.Spaces.HkIntegrand α 0 g)
    (fun z hz => hm.1 z hz) hm.2 (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g 0 θ) ?_
  intro z hz θ hθ
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [hkIntegrand_zero_of_sin_eq_zero α f hsin]
    exact Work.Spaces.HkIntegrand_nonneg α 0 g z θ
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := mem_Ioo_of_mem_Iθ_of_sin_ne hθ hsin
    have hr0 : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
      wdivsin_nonneg hθ
    have h1 : |f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ |g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr0]
      exact mul_le_mul_of_nonneg_right (h z hz θ hθ') hr0
    rw [hkIntegrand_zero_eq α f, hkIntegrand_zero_eq α g]
    calc (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = |f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| ^ 2 := by
          rw [sq_abs]
      _ ≤ |g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [sq_abs]

/-- `ℋ⁰`-membership from a domination by a sum of two `ℋ⁰`-functions. -/
theorem hkMem_zero_of_abs_le_two {α : ℝ} {f g₁ g₂ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (h₁ : Work.Spaces.HkMem α 0 g₁)
    (h₂ : Work.Spaces.HkMem α 0 g₂)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |f z θ| ≤ |g₁ z θ| + |g₂ z θ|) :
    Work.Spaces.HkMem α 0 f := by
  classical
  refine hkMem_zero_of_majorant hf
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 g₁ z θ
      + 2 * Work.Spaces.HkIntegrand α 0 g₂ z θ) ?_ ?_ ?_ ?_
  · intro z hz
    exact ((h₁.1 z hz).const_mul 2).add ((h₂.1 z hz).const_mul 2)
  · have htarget : IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 g₁ z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g₂ z θ))
        Work.Spaces.Iz :=
      (h₁.2.const_mul 2).add (h₂.2.const_mul 2)
    refine Integrable.congr htarget ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [MeasureTheory.integral_add (f := fun θ => 2 * Work.Spaces.HkIntegrand α 0 g₁ z θ)
        (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 g₂ z θ)
        ((h₁.1 z hz).const_mul 2) ((h₂.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro θ hθ
    have a := Work.Spaces.HkIntegrand_nonneg α 0 g₁ 0 θ
    have b := Work.Spaces.HkIntegrand_nonneg α 0 g₂ 0 θ
    linarith
  · intro z hz θ hθ
    by_cases hsin : Real.sin (2 * θ) = 0
    · rw [hkIntegrand_zero_of_sin_eq_zero α f hsin]
      have a := Work.Spaces.HkIntegrand_nonneg α 0 g₁ z θ
      have b := Work.Spaces.HkIntegrand_nonneg α 0 g₂ z θ
      linarith
    · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := mem_Ioo_of_mem_Iθ_of_sin_ne hθ hsin
      have hr0 : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        wdivsin_nonneg hθ
      set A : ℝ := f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hA
      set B : ℝ := g₁ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hB
      set C : ℝ := g₂ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hC
      have h1 : |A| ≤ |B| + |C| := by
        rw [hA, hB, hC, abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0]
        calc |f z θ| * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            ≤ (|g₁ z θ| + |g₂ z θ|)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
              mul_le_mul_of_nonneg_right (h z hz θ hθ') hr0
          _ = |g₁ z θ| * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
              + |g₂ z θ| * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
              ring
      have h2 : (|B| + |C|) ^ 2 ≤ 2 * B ^ 2 + 2 * C ^ 2 := by
        have hh := add_sq_le (a := |B|) (b := |C|)
        rw [sq_abs B, sq_abs C] at hh
        linarith [hh]
      rw [hkIntegrand_zero_eq α f, hkIntegrand_zero_eq α g₁, hkIntegrand_zero_eq α g₂,
        ← hA, ← hB, ← hC]
      calc A ^ 2 = |A| ^ 2 := by rw [sq_abs]
        _ ≤ (|B| + |C|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ ≤ 2 * B ^ 2 + 2 * C ^ 2 := h2

/-- `ℋ⁰`-membership from a domination by a sum of three `ℋ⁰`-functions. -/
theorem hkMem_zero_of_abs_le_three {α : ℝ} {f g₁ g₂ g₃ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (h₁ : Work.Spaces.HkMem α 0 g₁)
    (h₂ : Work.Spaces.HkMem α 0 g₂) (h₃ : Work.Spaces.HkMem α 0 g₃)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |f z θ| ≤ |g₁ z θ| + |g₂ z θ| + |g₃ z θ|) :
    Work.Spaces.HkMem α 0 f := by
  classical
  refine hkMem_zero_of_majorant hf
    (M := fun z θ => 4 * Work.Spaces.HkIntegrand α 0 g₁ z θ
      + 4 * Work.Spaces.HkIntegrand α 0 g₂ z θ
      + 4 * Work.Spaces.HkIntegrand α 0 g₃ z θ) ?_ ?_ ?_ ?_
  · intro z hz
    exact (((h₁.1 z hz).const_mul 4).add ((h₂.1 z hz).const_mul 4)).add
      ((h₃.1 z hz).const_mul 4)
  · have htarget : IntegrableOn (fun z => 4 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 g₁ z θ)
        + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g₂ z θ)
        + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g₃ z θ))
        Work.Spaces.Iz :=
      (((h₁.2.const_mul 4).add (h₂.2.const_mul 4)).add (h₃.2.const_mul 4))
    refine Integrable.congr htarget ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    have hc : (∫ θ in Work.Spaces.Iθ, 4 * Work.Spaces.HkIntegrand α 0 g₁ z θ
          + 4 * Work.Spaces.HkIntegrand α 0 g₂ z θ + 4 * Work.Spaces.HkIntegrand α 0 g₃ z θ)
        = (4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g₁ z θ)
          + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g₂ z θ))
          + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g₃ z θ) := by
      have h₁i := (h₁.1 z hz).const_mul 4
      have h₂i := (h₂.1 z hz).const_mul 4
      have h₃i := (h₃.1 z hz).const_mul 4
      rw [MeasureTheory.integral_add (f := fun θ => 4 * Work.Spaces.HkIntegrand α 0 g₁ z θ
            + 4 * Work.Spaces.HkIntegrand α 0 g₂ z θ)
          (g := fun θ => 4 * Work.Spaces.HkIntegrand α 0 g₃ z θ)
          (h₁i.add h₂i) h₃i,
        MeasureTheory.integral_add (f := fun θ => 4 * Work.Spaces.HkIntegrand α 0 g₁ z θ)
          (g := fun θ => 4 * Work.Spaces.HkIntegrand α 0 g₂ z θ) h₁i h₂i,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    exact hc.symm
  · intro θ hθ
    have a := Work.Spaces.HkIntegrand_nonneg α 0 g₁ 0 θ
    have b := Work.Spaces.HkIntegrand_nonneg α 0 g₂ 0 θ
    have c := Work.Spaces.HkIntegrand_nonneg α 0 g₃ 0 θ
    linarith
  · intro z hz θ hθ
    by_cases hsin : Real.sin (2 * θ) = 0
    · rw [hkIntegrand_zero_of_sin_eq_zero α f hsin]
      have a := Work.Spaces.HkIntegrand_nonneg α 0 g₁ z θ
      have b := Work.Spaces.HkIntegrand_nonneg α 0 g₂ z θ
      have c := Work.Spaces.HkIntegrand_nonneg α 0 g₃ z θ
      linarith
    · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := mem_Ioo_of_mem_Iθ_of_sin_ne hθ hsin
      have hr0 : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        wdivsin_nonneg hθ
      set A : ℝ := f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hA
      set B : ℝ := g₁ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hB
      set C : ℝ := g₂ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hC
      set D : ℝ := g₃ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hD
      have h1 : |A| ≤ |B| + |C| + |D| := by
        rw [hA, hB, hC, hD, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0]
        calc |f z θ| * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            ≤ (|g₁ z θ| + |g₂ z θ| + |g₃ z θ|)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
              mul_le_mul_of_nonneg_right (h z hz θ hθ') hr0
          _ = |g₁ z θ| * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
              + |g₂ z θ| * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
              + |g₃ z θ| * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
              ring
      have h2 : (|B| + |C| + |D|) ^ 2 ≤ 4 * B ^ 2 + 4 * C ^ 2 + 4 * D ^ 2 := by
        have hh1 : (|B| + |C|) ^ 2 ≤ 2 * (B ^ 2 + C ^ 2) := by
          have h := add_sq_le (a := |B|) (b := |C|)
          rw [sq_abs B, sq_abs C] at h
          linarith [h]
        calc (|B| + |C| + |D|) ^ 2 ≤ 2 * ((|B| + |C|) ^ 2 + |D| ^ 2) :=
              add_sq_le (a := |B| + |C|) (b := |D|)
          _ ≤ 2 * (2 * (B ^ 2 + C ^ 2) + D ^ 2) := by
              rw [sq_abs D]; linarith [hh1]
          _ ≤ 4 * B ^ 2 + 4 * C ^ 2 + 4 * D ^ 2 := by nlinarith [sq_nonneg D]
      rw [hkIntegrand_zero_eq α f, hkIntegrand_zero_eq α g₁, hkIntegrand_zero_eq α g₂,
        hkIntegrand_zero_eq α g₃, ← hA, ← hB, ← hC, ← hD]
      calc A ^ 2 = |A| ^ 2 := by rw [sq_abs]
        _ ≤ (|B| + |C| + |D|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ ≤ 4 * B ^ 2 + 4 * C ^ 2 + 4 * D ^ 2 := h2

/-- A level-`0` `D_z`-slot extracted from `ℋ^k`-membership. -/
theorem hkMem_zero_of_mem_DzIter {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hm : Work.Spaces.HkMem α k F)
    {i : ℕ} (hi : i ≤ k) : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i F) := by
  refine hkMem_zero_of_majorant (hF.DzIter i) (M := Work.Spaces.HkIntegrand α k F)
    (fun z hz => hm.1 z hz) hm.2 (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k F 0 θ) ?_
  intro z hz θ hθ
  rw [hkIntegrand_zero_eq]
  simp only [Work.Spaces.HkIntegrand]
  refine le_trans (Finset.single_le_sum
    (f := fun i' => (Work.Spaces.DzIter i' F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun i' _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) ?_
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> positivity)

/-- A level-`0` mixed slot extracted from `ℋ^k`-membership (with the `η ≤ γ` comparison). -/
theorem hkMem_zero_of_mem_mixed {α : ℝ} (hα : 0 < α) {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hm : Work.Spaces.HkMem α k F)
    {j i : ℕ} (hi : 1 ≤ i) (hji : i + j ≤ k) :
    Work.Spaces.HkMem α 0 (Work.Spaces.mixed j i F) := by
  refine hkMem_zero_of_majorant (hF.mixed j i) (M := Work.Spaces.HkIntegrand α k F)
    (fun z hz => hm.1 z hz) hm.2 (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k F 0 θ) ?_
  intro z hz θ hθ
  rw [hkIntegrand_zero_eq]
  simp only [Work.Spaces.HkIntegrand]
  have houter : (∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + b ≤ k
          then (Work.Spaces.mixed b i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ a ∧ a + b ≤ k
            then (Work.Spaces.mixed b a F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
    Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun a => ∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ a ∧ a + b ≤ k
          then (Work.Spaces.mixed b a F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      (fun a _ => Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)
      (a := i) (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
  have hinner : (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + b ≤ k
            then (Work.Spaces.mixed b i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    have h := Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun b => if 1 ≤ i ∧ i + b ≤ k
        then (Work.Spaces.mixed b i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      (fun b _ => by split_ifs <;> positivity)
      (a := j) (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
    rwa [if_pos ⟨hi, hji⟩] at h
  have hr0 : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    wdivsin_nonneg hθ
  have hsq : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    have hle := wdivsin_le_Wt (z := z) hα hθ
    exact pow_le_pow_left₀ hr0 hle 2
  have hmain : (Work.Spaces.mixed j i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    calc (Work.Spaces.mixed j i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.mixed j i F z θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
      _ ≤ (Work.Spaces.mixed j i F z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  exact le_trans (le_trans hmain (le_trans hinner houter))
    (le_add_of_nonneg_left (Finset.sum_nonneg fun a _ => sq_nonneg _))

/-! ## §3  `SmoothOpen`-closure under division by `cos θ` -/

theorem smoothOpen_div_cos {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ / Real.cos θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  have hnum : ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hF.forall n
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
    fun_prop
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := fun p hp =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos],
      by linarith [hp.2.2, Real.pi_pos]⟩)
  exact ContDiffOn.div hnum hden hne

/-! ## §4  Integrability of the `θ`-square of an iterated `Lop` -/

/-- The `θ`-square of `Lop^[n] B` is integrable on `Iθ` when `B` is `C^∞` (honest order) on an
open neighbourhood of `Iθ`.  This is what makes the `z = 0` slice of `D_θ^iΨ` integrable, via
`DthIter i Ψ 0 = Lop^[i] (θ ↦ Ψ 0 θ)` and the smoothness of the `θ`-slice of `E g` at `z = 0`. -/
theorem integrableOn_sq_Lop_iter {B : ℝ → ℝ} {n : ℕ}
    (hB : ContDiffOn ℝ Work.Stability.smoothOrder B (Set.Ioo (-1) (Real.pi / 2 + 1))) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Lop^[n] B θ) ^ 2) Work.Spaces.Iθ := by
  have hU : IsOpen (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := isOpen_Ioo
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hC : ∀ j : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder (Work.Spaces.Lop^[j] B)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    intro j
    induction j with
    | zero => simpa using hB
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        have hd : ContDiffOn ℝ Work.Stability.smoothOrder (deriv (Work.Spaces.Lop^[j] B))
            (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
          ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp ih).2
        have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
            (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by fun_prop
        exact hsin.mul hd
  exact ((hC n).continuousOn.mono hsub).pow 2 |>.integrableOn_compact isCompact_Icc

/-- `θ ↦ (B θ / cos θ)²` is integrable on `Iθ` when `B` is `C^∞` (honest order) on an open
neighbourhood of `[0, π/2]` and vanishes at `π/2`.  (The analytic-order version is
`PkgJets.integrableOn_sq_div_cos_slice_zero`; `SmoothStrip`-data only give the honest `C^∞`
order, so this is the version used for the `z = 0` slice of `Ψ`.) -/
theorem integrableOn_sq_div_cos_of_smoothOrder {B : ℝ → ℝ}
    (hB : ContDiffOn ℝ Work.Stability.smoothOrder B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hB0 : B (Real.pi / 2) = 0) :
    MeasureTheory.IntegrableOn (fun θ => (B θ / Real.cos θ) ^ 2) Work.Spaces.Iθ := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hcont : ContinuousOn B (Set.Icc (0 : ℝ) (Real.pi / 2)) := hB.continuousOn.mono hsub
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt B (deriv B θ) θ := by
    intro θ hθ
    have hs : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) := hsub ⟨hθ.1.le, hθ.2.le⟩
    exact ((hB.contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hn : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have hcontderiv : ContinuousOn (deriv B) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    (hB.continuousOn_deriv_of_isOpen isOpen_Ioo hn).mono hsub
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontderiv
  have hMb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv B θ| ≤ M := by
    intro θ hθ
    have h := hM θ ⟨hθ.1.le, hθ.2.le⟩
    rwa [Real.norm_eq_abs] at h
  have hOpen := Work.FTS.EllipticEst.Honest.HonCosSliceIntegrable (u := B) hcont hB0 hderiv hMb
  change Integrable (fun θ => (B θ / Real.cos θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    ← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  exact hOpen

end Work.FTS_EllLimOK.PkgJets
