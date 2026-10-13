/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `(v')²σ` bound on a `θ`-slice

With `v = u / cos θ` and `σ = sin(2θ)^{2-γ}`, `1 ≤ γ ≤ 3/2`, this module proves

`∫_{Iθ} (v')² σ ≤ C (∫_{Iθ} g² σ + ∫_{Iθ} (u'')² sEta + ∫_{Iθ} (u')² + ∫_{Iθ} u²)`

for `u` of class `C³` on `(0, π/2)` solving `Lzero1 u = g`, `g` the right hand side of the
angular elliptic equation, and `sEta = sin(2θ)^{-η}` the `i = 0` angular weight
(`Work.FTS.EllipticEst.Lzero1`, `Work.FTS.EllipticEst.sEta`, `Work.Spaces.Iθ`).

The proof has two ingredients.

* The two explicit identities (on the open interval `(0, π/2)`, where `cos θ ≠ 0`)

  `v' = (u' + u tan θ)/cos θ`   and   `sin θ · v' = u'' + 5u + g`,

  the second being the exact form of `Lzero1 u = g` rewritten in terms of `v`.

* The `π/4`-split of the interval.  On `(0, π/4)` the first identity bounds `v'` by the
  bounded coefficients `1/cos θ ≤ √2`, `tan θ ≤ 1` and kills `σ ≤ 1`; on `(π/4, π/2)` the
  second identity together with `sin²θ ≥ 1/2` bounds `(v')²σ` by
  `6 (g²σ + 25 u² + (u'')² sEta)`.

Both bounds are pointwise, the quantifier over all of `Iθ = [0, π/2]` being obtained by
almost-everywhere domination (the two endpoints are null sets), and then the four resulting
elementary integrals are combined with `MeasureTheory.integral_mono_ae`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.memLp_Lzero_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ### The two first-order identities for `v = u / cos θ` -/

/-- On the open interval, `v = u / cos θ` has the derivative `(u' + u tan θ)/cos θ`. -/
private lemma Y2_psi_deriv (u : ℝ → ℝ) (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ + u θ * Real.tan θ) / Real.cos θ := by
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩)
  have hu_at : ContDiffAt ℝ 1 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hd1 : HasDerivAt u (deriv u θ) θ :=
    (hu_at.differentiableAt (by norm_num)).hasDerivAt
  have hd2 : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hd := hd1.div hd2 hcos
  have hd' : deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ * Real.cos θ - u θ * (-Real.sin θ)) / Real.cos θ ^ 2 := hd.deriv
  rw [hd', Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- The exact form of the equation `Lzero1 u = g` in terms of `v = u / cos θ`:
`sin θ · v' = u'' + 5u + g` on the open interval. -/
private lemma Y2_psi_ident (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ * deriv (fun t => u t / Real.cos t) θ = deriv (deriv u) θ + 5 * u θ + g θ := by
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩)
  have hu_at : ContDiffAt ℝ 3 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hd1 : HasDerivAt u (deriv u θ) θ :=
    (((hu_at.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).differentiableAt
      (by norm_num))).hasDerivAt
  have htan : deriv (fun t => Real.tan t * u t) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ :=
    ((Real.hasDerivAt_tan hcos).mul hd1).deriv
  have hL : -(deriv (fun t => deriv u t) θ) + deriv (fun t => Real.tan t * u t) θ
      - 6 * u θ = g θ := by
    have h := hode θ hθ
    simpa [Work.FTS.EllipticEst.Lzero1] using h
  have hpsi := Y2_psi_deriv u (hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) hθ
  rw [hpsi, ← hL, htan, Real.tan_eq_sin_div_cos]
  field_simp
  ring_nf
  rw [Real.sin_sq]
  ring

/-! ### The two halves of the pointwise bound -/

/-- On `(0, π/4]` the coefficients of `v' = (u' + u tan θ)/cos θ` are bounded by `√2` and by
`1`, and `σ = sin(2θ)^{2-γ} ≤ 1`; hence `(v')²σ ≤ 4 (u'² + u²)`. -/
private lemma Y2_left_bound (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioc 0 (Real.pi / 4),
      (deriv (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := by
  intro θ hθ
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2]⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1], hθ'.2⟩
  have hψ : deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ + u θ * Real.tan θ) / Real.cos θ :=
    Y2_psi_deriv u (hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) hθ'
  -- the weight is at most `1`
  have hsin2 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hσ1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsin2 (Real.sin_le_one _) (by linarith)
  -- `tan θ ≤ 1`
  have htan0 : 0 ≤ Real.tan θ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ.1.le (by linarith [hθ.2])
  have htan1 : Real.tan θ ≤ 1 := by
    rcases lt_or_eq_of_le hθ.2 with hlt | heq
    · have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hθ.1.le (by linarith) hlt
      rw [Real.tan_pi_div_four] at h
      exact le_of_lt h
    · rw [heq, Real.tan_pi_div_four]
  have htan2 : Real.tan θ ^ 2 ≤ 1 := by nlinarith
  -- `1/cos² θ ≤ 2`
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    have hc : Real.cos θ ^ 2 = 1 / 2 + Real.cos (2 * θ) / 2 := Real.cos_sq θ
    have hc2 : 0 ≤ Real.cos (2 * θ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    linarith
  -- numerator estimate
  have hnum : (deriv u θ + u θ * Real.tan θ) ^ 2
      ≤ 2 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := by
    nlinarith [sq_nonneg (deriv u θ - u θ * Real.tan θ), sq_nonneg (u θ), htan2]
  -- putting the pieces together
  have hkey : (deriv (fun t => u t / Real.cos t) θ) ^ 2
      ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := by
    rw [hψ, div_pow, div_le_iff₀ (pow_pos hcos 2)]
    have hA : (deriv u θ + u θ * Real.tan θ) ^ 2
        ≤ 2 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := hnum
    have hB : 2 * ((deriv u θ) ^ 2 + (u θ) ^ 2)
        ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) * Real.cos θ ^ 2 := by
      nlinarith [sq_nonneg (deriv u θ), sq_nonneg (u θ), hcos2]
    linarith
  calc (deriv (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hσ1 (sq_nonneg _)
    _ = (deriv (fun t => u t / Real.cos t) θ) ^ 2 := mul_one _
    _ ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := hkey

/-- On `(π/4, π/2)` the exact identity `sin θ v' = u'' + 5u + g` together with `sin²θ ≥ 1/2`,
`σ ≤ 1` and `σ ≤ sEta` gives `(v')²σ ≤ 6 (g²σ + 25u² + (u'')²sEta)`. -/
private lemma Y2_right_bound (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 6 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) + 25 * (u θ) ^ 2
            + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  intro θ hθ
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1], hθ.2⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ'.1, by linarith [hθ'.2]⟩
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hident := Y2_psi_ident u g hu hode hθ'
  have hψ : deriv (fun t => u t / Real.cos t) θ
      = (deriv (deriv u) θ + 5 * u θ + g θ) / Real.sin θ := by
    rw [eq_div_iff hsin.ne']
    rw [mul_comm]
    exact hident
  -- `sin² θ ≥ 1/2`
  have hsin2half : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by
    have hc : Real.cos θ ^ 2 = 1 / 2 + Real.cos (2 * θ) / 2 := Real.cos_sq θ
    have hc2 : Real.cos (2 * θ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.1]) (by linarith [hθ.2])
    have hs := Real.sin_sq θ
    linarith
  -- the Cauchy–Schwarz step
  have hnum : (deriv (deriv u) θ + 5 * u θ + g θ) ^ 2
      ≤ 3 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2) := by
    nlinarith [sq_nonneg (deriv (deriv u) θ - 5 * u θ),
      sq_nonneg (5 * u θ - g θ), sq_nonneg (deriv (deriv u) θ - g θ)]
  have hkey : (deriv (fun t => u t / Real.cos t) θ) ^ 2
      ≤ 6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2) := by
    rw [hψ, div_pow, div_le_iff₀ (pow_pos hsin 2)]
    have hA : 0 ≤ (deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2 := by positivity
    nlinarith [hnum, hsin2half, hA]
  -- the weight comparisons
  have hσ1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsin2.le (Real.sin_le_one _) (by linarith)
  have hσsEta : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ Work.FTS.EllipticEst.sEta θ := by
    have heta : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_le_rpow_of_exponent_ge hsin2 (Real.sin_le_one _) (by linarith)
  have hσ0 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin2.le _
  have hsEta0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_nonneg hsin2.le _
  -- assembling
  have step1 : (deriv (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2))
        * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    mul_le_mul_of_nonneg_right hkey hσ0
  have step2 : (6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2))
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 6 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 25 * (u θ) ^ 2
          + (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
    have h1 : (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      mul_le_mul_of_nonneg_left hσsEta (sq_nonneg _)
    have h2 : 25 * (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 25 * (u θ) ^ 2 := by
      have h := mul_le_of_le_one_right (a := 25 * (u θ) ^ 2) (b := Real.rpow (Real.sin (2 * θ)) (2 - γ))
        (by positivity) hσ1
      simpa using h
    nlinarith [h1, h2]
  calc (deriv (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2))
        * Real.rpow (Real.sin (2 * θ)) (2 - γ) := step1
    _ ≤ 6 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 25 * (u θ) ^ 2
          + (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := step2
    _ = 6 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) + 25 * (u θ) ^ 2
          + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

/-! ### The requested bound -/

/-- **The `(v')²σ`-bound.**  For `v = u/cos θ` and `σ = sin(2θ)^{2-γ}`, `1 ≤ γ ≤ 3/2`:
`∫ (v')²σ ≤ C (∫ g²σ + ∫ (u'')²sEta + ∫ (u')² + ∫ u²)`.

Proof route.  From `Lzero1 u = g`, expanded in terms of `v = u/cos θ`,
`-cos θ v'' + 3 sin θ v' - 4 cos θ v = g`, and `u'' = cos θ v'' - 2 sin θ v' - cos θ v`,
one gets the *exact* identity `sin θ · v' = u'' + 5u + g`, hence `∫(v')²σ = ∫(u''+5u+g)²σ/sin²θ`.
Split at `π/4`:
* on `(π/4, π/2)`, `sin²θ ≥ 1/2`, so the integral is `≤ 2∫(u''+5u+g)²σ ≤ 6(∫g²σ + ∫(u'')²σ + 25∫u²σ)`,
  and `σ ≤ sEta`, `σ ≤ 1`.
* on `(0, π/4)`, `sin²θ ≥ cθ²` cancels the vanishing of `σ`, and `v' = (u' + u tan θ)/cos θ`
  with bounded coefficients there, so the integral is `≤ C(∫(u')² + ∫u²)`.
-/
theorem slice_Y2_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  refine ⟨160, by norm_num, ?_⟩
  intro u g hu hcont hu0 hupi hode hgI hu2I hu1I hu0I
  set F : ℝ → ℝ := fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ) with hF
  -- ### the pointwise bound on the open interval
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      F θ ≤ 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
    intro θ hθ
    have hsin2 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hσ0 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin2 _
    have hη0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta]
      exact Real.rpow_nonneg
        (le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)) _
    have hA : 0 ≤ (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) hσ0
    have hB : 0 ≤ (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      mul_nonneg (sq_nonneg _) hη0
    have hC : 0 ≤ (deriv u θ) ^ 2 := sq_nonneg _
    have hD : 0 ≤ (u θ) ^ 2 := sq_nonneg _
    simp only [hF]
    by_cases hle : θ ≤ Real.pi / 4
    · have h1 := Y2_left_bound γ hγ1 hγ2 u hu θ ⟨hθ.1, hle⟩
      have h2 : 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2)
          ≤ 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
              + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
        nlinarith [hA, hB, hC, hD]
      linarith [h1, h2]
    · have hlt : Real.pi / 4 < θ := lt_of_not_ge hle
      have h1 := Y2_right_bound γ hγ1 hγ2 u g hu hode θ ⟨hlt, hθ.2⟩
      have h2 : 6 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) + 25 * (u θ) ^ 2
              + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
              + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
        nlinarith [hA, hB, hC, hD]
      linarith [h1, h2]
  -- ### almost-everywhere statement and measurability
  have hle_ae : F ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (deriv u θ) ^ 2 + (u θ) ^ 2)) :=
    Work.FTS.EllipticEst.ae_restrict_Iθ_of_Ioo_memLp hpt
  have hF_aesm : MeasureTheory.AEStronglyMeasurable F
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hF]
    have h1 : MeasureTheory.AEStronglyMeasurable (deriv (fun t => u t / Real.cos t))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aestronglyMeasurable_deriv _ _
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    exact h1.pow 2 |>.mul h2
  have hF_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] F := by
    have aux : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
        (0 : ℝ) ≤ F θ := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      simp only [hF]
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
          by linarith [hθ.2]⟩) _)
    exact aux
  -- ### integrability of the dominating function and of `F`
  have hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := hgI
  have hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := hu2I
  have hC : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2) Work.Spaces.Iθ := hu1I
  have hD : MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ) ^ 2) Work.Spaces.Iθ := hu0I
  have hAB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hA.add hB
  have hABC : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2)
      Work.Spaces.Iθ := hAB.add hC
  have hABCD : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
        + (u θ) ^ 2) Work.Spaces.Iθ := hABC.add hD
  have hJ_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
        + (u θ) ^ 2)) Work.Spaces.Iθ := hABCD.const_mul 160
  have hF_int : MeasureTheory.IntegrableOn F Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono_nonneg hJ_int hF_aesm hF_nonneg hle_ae
  -- ### the value of the dominating integral
  have hJ_eval : (∫ θ in Work.Spaces.Iθ, 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
        + (u θ) ^ 2))
      = 160 * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
    simp only [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hA hB,
      MeasureTheory.integral_add hAB hC, MeasureTheory.integral_add hABC hD]
  refine ⟨hF_int, ?_⟩
  calc ∫ θ in Work.Spaces.Iθ, F θ
      ≤ ∫ θ in Work.Spaces.Iθ, 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
          + (u θ) ^ 2) := MeasureTheory.integral_mono_ae hF_int hJ_int hle_ae
    _ = 160 * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := hJ_eval

end Work.FTS.EllipticEst.remov
