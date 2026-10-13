import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le
import Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs
import Submission.Work.FTS.EllipticEst.Honest.I4AMGM
import Submission.Work.FTS.EllipticEst.Honest.I4CrossTermBound
import Submission.Work.FTS.EllipticEst.Honest.I4CSBound
import Submission.Work.FTS.EllipticEst.Honest.I4CosSqIntegralLe
import Submission.Work.FTS.EllipticEst.Honest.I4GHasDerivAt
import Submission.Work.FTS.EllipticEst.Honest.I4IntervalIdentity
import Submission.Work.FTS.EllipticEst.Honest.IntervalIntegralTendstoSetIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The single-slice `I₄` upper bound** (the analytic heart of `I4UpperHonest`).

`Φ` is the angular slice of a stream function, `σ = sin(2θ)^{-η}`, `η = 99/100`, `ψ = Φ/cos θ`.
Given the two `HkMem`-type integrability hypotheses, the *pointwise algebra* `hAlg` (four calculus
identities: `∂_θ(tan θ·Φ) = cos θ·ψ + sin θ·ψ'`; `Φ'' = cos θ·ψ'' − 2 sin θ·ψ' − cos θ·ψ`;
`P' = cos θ·(Φ''+Φ)` with `P = cos²θ·ψ'`; and
`(½·sin θ/cos³θ·σ·P²)' = (sin θ/cos³θ)σPP' + ½Σσ(ψ')²` with `Σ = (1−η)cos²θ + (3+η)sin²θ`),
and the *boundary vanishing* `hBound`: `(sin θ/cos³θ)·σ·P² → 0` as `θ → π/2⁻`, the slice estimate

`∫_θ ∂_θ(tan θ·Φ)·Φ''·σ ≤ 50∫_θ ψ²σ + √(∫_θψ²σ)·√(∫_θ(Φ'')²σ)`

holds (`50 = ½/(1−η)`).  Proof route: on `(δ,θ₁) ⊂ (0,π/2)` the two identities give
`∫_δ^{θ₁} u b σ = ∫_δ^{θ₁} cψbσ + ½[(sσ/c³)P²]_δ^{θ₁} − ½∫_δ^{θ₁}Σσψ'² − ∫_δ^{θ₁}sσψ'Φ`;
the AM–GM inequality `|sσψ'Φ| ≤ ½Σσψ'² + ½(s²σΦ²/Σ)` cancels the negative term;
`s²σΦ²/Σ ≤ σψ²/(1−η)`; drop `−½(sσ/c³)P²(δ) ≤ 0` and let `δ → 0` (ℒ¹ convergence of interval
integrals), then `θ₁ → π/2` using `hBound`; finally Cauchy–Schwarz in `θ`
(`Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le` with `F = cos θ·ψ`, `G = Φ''`,
`κ = σ`) turns `∫_θ cψ·Φ''·σ` into `√(∫_θψ²σ)·√(∫_θ(Φ'')²σ)`.  The case where the left-hand
side is not integrable is trivial (the set integral is the junk value `0`, and the right-hand
side is `≥ 0`). -/
theorem I4SliceBound (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)))
    (hAlg : (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => Real.tan θ' * Φ θ') θ
          = Real.cos θ * (Φ θ / Real.cos θ)
            + Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ)
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (deriv Φ) θ
          = Real.cos θ * deriv (deriv (fun θ' => Φ θ' / Real.cos θ')) θ
            - 2 * Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ
            - Real.cos θ * (Φ θ / Real.cos θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
          = Real.cos θ * (deriv (deriv Φ) θ + Φ θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (1/2) * (Real.sin θ' / (Real.cos θ')^3)
            * (Real.sin (2*θ'))^(-(99/100:ℝ))
            * ((Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ')^2) θ
          = (Real.sin θ / (Real.cos θ)^3) * (Real.sin (2*θ))^(-(99/100:ℝ))
              * ((Real.cos θ)^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ)
              * deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
            + (1/2) * ((1 - 99/100) * (Real.cos θ)^2 + (3 + 99/100) * (Real.sin θ)^2)
              * (Real.sin (2*θ))^(-(99/100:ℝ))
              * (deriv (fun θ' => Φ θ' / Real.cos θ') θ)^2))
    (hBound : Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3
        * ((Real.cos θ) ^ 2 * deriv (fun θ' => Φ θ' / Real.cos θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∫ θ in Set.Icc 0 (Real.pi / 2),
        deriv (fun θ' => Real.tan θ' * Φ θ') θ * deriv (deriv Φ) θ
          * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
      ≤ 50 * (∫ θ in Set.Icc 0 (Real.pi / 2),
            (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        + Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
            (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
          * Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
            (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
  -- normalise the hypotheses and the goal to the `I4*` vocabulary
  have hA' : MeasureTheory.IntegrableOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ := hA
  have hB' : MeasureTheory.IntegrableOn (fun θ => I4b Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ := hB
  have hBound' : Filter.Tendsto (I4H Φ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := hBound
  change (∫ θ in Work.Spaces.Iθ, I4u Φ θ * I4b Φ θ * I4sig θ)
      ≤ 50 * (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, I4b Φ θ ^ 2 * I4sig θ)
  -- the three integrals of the statement and the Cauchy–Schwarz bound
  set X : ℝ := ∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ with hX
  set Y : ℝ := ∫ θ in Work.Spaces.Iθ, I4b Φ θ ^ 2 * I4sig θ with hY
  set Z : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ with hZ
  set Bc : ℝ := Real.sqrt Z * Real.sqrt Y with hBc
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (I4sig_nonneg hθ))
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (I4sig_nonneg hθ))
  have hZX : Z ≤ X := by
    have h := I4CosSqIntegralLe Φ hA'
    rwa [← hZ, ← hX] at h
  have hBcle : Bc ≤ Real.sqrt X * Real.sqrt Y := by
    rw [hBc]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hZX) (Real.sqrt_nonneg Y)
  by_cases hint : MeasureTheory.IntegrableOn (fun θ => I4u Φ θ * I4b Φ θ * I4sig θ)
      Work.Spaces.Iθ
  · -- ## main case: truncate at `δ > 0` and `θ₁ < π/2`, then pass to the limits
    have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ q Ψv : ℝ,
        |Real.sin θ * I4sig θ * q * Ψv|
          ≤ (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
            + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2 :=
      fun θ hθ q Ψv => I4AMGM θ hθ q Ψv
    have hGder : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ := I4GHasDerivAt Φ hsm
    -- the truncated inequality
    have htrunc : ∀ δ θ₁ : ℝ, 0 < δ → δ ≤ θ₁ → θ₁ < Real.pi / 2 →
        (∫ θ in δ..θ₁, I4u Φ θ * I4b Φ θ * I4sig θ) ≤ Bc + I4G Φ θ₁ + 50 * X := by
      intro δ θ₁ hδ hδθ hθ₁
      have hid := I4IntervalIdentity Φ hsm hAlg hGder hδ hδθ hθ₁
      have hcross := I4CrossTermBound Φ hsm hA' hpt hδ hδθ hθ₁
      have hcs := I4CSBound Φ hA' hB' hδ hδθ hθ₁
      have hGδ : 0 ≤ I4G Φ δ := I4G_nonneg Φ ⟨hδ, lt_of_le_of_lt hδθ hθ₁⟩
      have hcs' : (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ) ≤ Bc := by
        rw [hBc, hZ, hY]
        exact hcs
      have hcross' : -(∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
          ≤ (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
            + 50 * X := by
        have h := hcross
        rw [hX]
        have hab : -(∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
            ≤ |∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ| := by
          have h2 := neg_abs_le (∫ θ in δ..θ₁,
            Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
          linarith
        linarith [hab, h]
      linarith [hid, hcs', hcross', hGδ]
    -- the limits
    have hGlim : Filter.Tendsto (I4G Φ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h1 := hBound'.const_mul (1 / 2 : ℝ)
      have h2 : (fun θ => (1 / 2 : ℝ) * I4H Φ θ) = fun θ => I4G Φ θ := by
        funext θ
        rw [I4H_eq_two_mul_I4G]
        ring
      rw [h2] at h1
      simpa using h1
    have hlimg : Filter.Tendsto
        (fun p : ℝ × ℝ => ∫ x in p.1..p.2, I4u Φ x * I4b Φ x * I4sig x)
        ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
        (nhds (∫ x in Set.Icc 0 (Real.pi / 2), I4u Φ x * I4b Φ x * I4sig x)) := by
      rw [Filter.prod_eq_inf]
      exact IntervalIntegralTendstoSetIntegral
        (g := fun x => I4u Φ x * I4b Φ x * I4sig x) hint
    have hRHS : Filter.Tendsto (fun p : ℝ × ℝ => Bc + I4G Φ p.2 + 50 * X)
        ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
        (nhds (Bc + 0 + 50 * X)) := by
      have h1 : Filter.Tendsto (fun p : ℝ × ℝ => I4G Φ p.2)
          ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
          (nhds 0) := hGlim.comp tendsto_snd
      exact (h1.const_add Bc).add_const (50 * X)
    have hev : ∀ᶠ p : ℝ × ℝ in
        ((nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))),
        (∫ x in p.1..p.2, I4u Φ x * I4b Φ x * I4sig x) ≤ Bc + I4G Φ p.2 + 50 * X := by
      rw [eventually_prod_iff]
      refine ⟨fun x => 0 < x ∧ x < 1, ?_, fun y => 1 < y ∧ y < Real.pi / 2, ?_, ?_⟩
      · refine Filter.Eventually.and ?_ ?_
        · exact self_mem_nhdsWithin
        · have h : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
            isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; norm_num)
          exact nhdsWithin_le_nhds h
      · refine Filter.Eventually.and ?_ ?_
        · have h : Set.Ioi (1 : ℝ) ∈ nhds (Real.pi / 2) :=
            isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith [Real.pi_gt_three])
          exact nhdsWithin_le_nhds h
        · exact self_mem_nhdsWithin
      · intro δ hδ θ₁ hθ₁
        exact htrunc δ θ₁ hδ.1 (by linarith [hδ.2, hθ₁.1]) hθ₁.2
    have hmain' : (∫ x in Set.Icc 0 (Real.pi / 2), I4u Φ x * I4b Φ x * I4sig x)
        ≤ Bc + 0 + 50 * X :=
      le_of_tendsto_of_tendsto hlimg hRHS hev
    have hmain : (∫ x in Work.Spaces.Iθ, I4u Φ x * I4b Φ x * I4sig x) ≤ Bc + 0 + 50 * X :=
      hmain'
    calc (∫ x in Work.Spaces.Iθ, I4u Φ x * I4b Φ x * I4sig x)
        ≤ Bc + 0 + 50 * X := hmain
      _ = Bc + 50 * X := by ring
      _ ≤ Real.sqrt X * Real.sqrt Y + 50 * X := by linarith [hBcle]
      _ = 50 * X + Real.sqrt X * Real.sqrt Y := by ring
  · -- ## junk case: the left-hand integral is `0`
    rw [MeasureTheory.integral_undef hint]
    have h1 : 0 ≤ 50 * X := mul_nonneg (by norm_num) hXnn
    have h2 : 0 ≤ Real.sqrt X * Real.sqrt Y :=
      mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Y)
    linarith



end Work.FTS.EllipticEst.Honest
