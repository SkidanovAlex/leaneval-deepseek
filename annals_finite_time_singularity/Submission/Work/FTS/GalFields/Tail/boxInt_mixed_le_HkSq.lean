/-
# `Tail/boxInt_mixed_le_HkSq` — the box integral of a mixed derivative is controlled by `HkSq`

The Galerkin "tail route" (`Tail/NOTES_tail_route.md`) evaluates the profile of a Galerkin
combination on a *box* `[a,b] × [δ, π/2 - δ]` strictly inside the open quadrant.  The estimates
there need the elementary localisation fact proved in this file: a single mixed derivative
`D_z^j D_θ^i f` (`j + i ≤ 4`) of a function that is `C^∞` on the open quadrant and of class
`ℋ⁴` in the weighted sense of the paper satisfies

`∫_{[a,b] × [δ, π/2-δ]} (D_z^j D_θ^i f)² ≤ C · HkSq α 4 f`.

The point is that on a compact box *away from the boundary* of the quadrant the weights
`w(z) = (1+z)²/z²` and `sin(2θ)^{-γ/2}` are bounded below by a positive constant, so the plain
`L²`-norm of the derivative is dominated by the weighted one — and the weighted one is a single
summand of `HkIntegrand α 4 f`, the integrand of `HkSq α 4 f`
(`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).

The only slightly non-elementary step is the exchange of the two integrations on the box
(`MeasureTheory.setIntegral_prod`), which applies because the integrand is continuous on the
compact box (`ContinuousOn.integrableOn_compact`); no measurability input beyond this is needed.
The two extensions of the domain of integration are then performed in the iterated form, where
the hypotheses of `Work.Spaces.HkMem` supply the integrability at once.

Explicit constant: `C = b⁴ + 1` (the constant is irrelevant downstream; the statement only asks
for existence).  Note that in the degenerate case `b < a` the box is empty and the constant `1`
would do; `b⁴ + 1` covers both cases uniformly.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

set_option autoImplicit false

/-! ## The pointwise lower bounds for the weights on a box -/

/-- The radial weight beats `1/b²` on `(0,b]`: `1/b² ≤ w(z) = (1+z)²/z²` for `0 < z ≤ b`.
Indeed `1/z² ≥ 1/b²` and `(1+z)² ≥ 1`. -/
private theorem one_div_sq_le_w {z b : ℝ} (hz : 0 < z) (hzb : z ≤ b) :
    1 / b ^ 2 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hzb2 : z ^ 2 ≤ b ^ 2 := by nlinarith
  have h1 : 1 / b ^ 2 ≤ 1 / z ^ 2 := one_div_le_one_div_of_le hz2 hzb2
  have h2 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  calc 1 / b ^ 2 ≤ 1 / z ^ 2 := h1
    _ = 1 * (1 / z ^ 2) := by ring
    _ ≤ (1 + z) ^ 2 * (1 / z ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = Work.Spaces.w z := by rw [Work.Spaces.w]; field_simp

/-- `sin(2θ) > 0` on the angular box `[δ, π/2 - δ]` (the left endpoint forcing `θ ∈ (0,π/2)`). -/
private theorem sin_two_pos_box {δ θ : ℝ} (hδ : 0 < δ)
    (hθ : θ ∈ Set.Icc δ (Real.pi / 2 - δ)) : 0 < Real.sin (2 * θ) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- For a negative exponent `-c`, `c ≥ 0`, and a base `sin(2θ) ∈ (0,1]`, the power is at
least `1`. -/
private theorem one_le_sin_rpow_neg {θ c : ℝ} (hpos : 0 < Real.sin (2 * θ)) (hc : 0 ≤ c) :
    1 ≤ Real.sin (2 * θ) ^ (-c) := by
  have h := Real.rpow_le_rpow_of_nonpos hpos (Real.sin_le_one (2 * θ)) (by linarith : -c ≤ 0)
  rwa [Real.one_rpow] at h

/-- The `ℋ⁰`-weight `w(z)/sin(2θ)^{η/2}` is bounded below by `1/b²` on the box. -/
private theorem one_div_sq_le_wdivsin {b z θ : ℝ} (hz : 0 < z) (hzb : z ≤ b)
    (hsin : 0 < Real.sin (2 * θ)) :
    1 / b ^ 2 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
  have hw := one_div_sq_le_w hz hzb
  have hs : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) :=
    one_le_sin_rpow_neg hsin (by norm_num [Work.Spaces.eta])
  have h3 : (0 : ℝ) ≤ Work.Spaces.w z := le_trans (by positivity) hw
  have h4 : 1 / b ^ 2 ≤ Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) := by
    simpa using mul_le_mul hw hs (by norm_num : (0:ℝ) ≤ 1) h3
  have hgoal : Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hsin)]
  rw [hgoal]
  exact h4

/-- The mixed weight `W = w(z)·sin(2θ)^{-γ/2}` is bounded below by `1/b²` on the box. -/
private theorem one_div_sq_le_Wt {α b z θ : ℝ} (hα : 0 < α) (hz : 0 < z) (hzb : z ≤ b)
    (hsin : 0 < Real.sin (2 * θ)) :
    1 / b ^ 2 ≤ Work.Spaces.Wt α z θ := by
  have hw := one_div_sq_le_w hz hzb
  have hgam : (0 : ℝ) ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith
  have hs : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)) :=
    one_le_sin_rpow_neg hsin hgam
  have h3 : (0 : ℝ) ≤ Work.Spaces.w z := le_trans (by positivity) hw
  have h4 : 1 / b ^ 2 ≤ Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)) := by
    simpa using mul_le_mul hw hs (by norm_num : (0:ℝ) ≤ 1) h3
  simpa only [Work.Spaces.Wt, Work.Spaces.wTheta] using h4

/-! ## The algebraic consequence: a square dominated by its weighted version -/

/-- If `Σ ≥ 1/b²` (`b > 0`) then `1 ≤ b⁴ Σ²`. -/
private theorem one_le_const_mul_sq {S b : ℝ} (hb : 0 < b) (hS : 1 / b ^ 2 ≤ S) :
    1 ≤ b ^ 4 * S ^ 2 := by
  have h1 : (1 / b ^ 2) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by positivity) hS 2
  have h2 : (1 : ℝ) = b ^ 4 * (1 / b ^ 2) ^ 2 := by field_simp
  calc (1 : ℝ) = b ^ 4 * (1 / b ^ 2) ^ 2 := h2
    _ ≤ b ^ 4 * S ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `D² ≤ b⁴ (D Σ)²` as soon as `1 ≤ b⁴ Σ²`. -/
private theorem sq_le_const_mul_sq {D S b : ℝ} (h : 1 ≤ b ^ 4 * S ^ 2) :
    D ^ 2 ≤ b ^ 4 * (D * S) ^ 2 := by
  calc D ^ 2 = D ^ 2 * 1 := by ring
    _ ≤ D ^ 2 * (b ^ 4 * S ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg D)
    _ = b ^ 4 * (D * S) ^ 2 := by ring

/-! ## The pointwise bound on the box -/

/-- **The pointwise bound.**  On the box `[a,b] × [δ, π/2-δ]` (`0 < a`, `0 < δ < π/2 - δ`) every
mixed derivative `D_z^j D_θ^i f` of order `j + i ≤ 4` satisfies
`(D_z^j D_θ^i f)² ≤ (b⁴+1) · HkIntegrand α 4 f`.

The two cases are `i = 0`, where the relevant weighted slot is `D_z^j f · w/sin(2θ)^{η/2}`
(`Work.Spaces.sq_le_HkIntegrand_z`), and `i ≥ 1`, where it is `D_z^jD_θ^if · W`
(`Work.Spaces.sq_le_HkIntegrand_mixed`); in both cases the weight is `≥ 1/b²` on the box, so the
unweighted square is at most `b⁴` times the weighted one. -/
private theorem mixed_sq_le_HkIntegrand_box {α : ℝ} (hα : 0 < α) {a b δ : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) {f : ℝ → ℝ → ℝ} {j i : ℕ} (hji : j + i ≤ 4)
    {z θ : ℝ} (hz : z ∈ Set.Icc a b) (hθ : θ ∈ Set.Icc δ (Real.pi / 2 - δ)) :
    (Work.Spaces.mixed j i f z θ) ^ 2 ≤ (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
  have hb : 0 < b := lt_of_lt_of_le hz0 hz.2
  have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_box hδ hθ
  have hji' : i + j ≤ 4 := by omega
  have hstep : ∀ {D S : ℝ}, 1 / b ^ 2 ≤ S → D ^ 2 ≤ (b ^ 4 + 1) * (D * S) ^ 2 := by
    intro D S hS
    have h1 := sq_le_const_mul_sq (D := D) (S := S) (one_le_const_mul_sq hb hS)
    calc D ^ 2 ≤ b ^ 4 * (D * S) ^ 2 := h1
      _ ≤ (b ^ 4 + 1) * (D * S) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have hS : 1 / b ^ 2 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      one_div_sq_le_wdivsin hz0 hz.2 hsin
    have hkey := hstep (D := Work.Spaces.DzIter j f z θ)
      (S := Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) hS
    calc (Work.Spaces.mixed j 0 f z θ) ^ 2 = (Work.Spaces.DzIter j f z θ) ^ 2 := rfl
      _ ≤ (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ :=
          le_trans hkey (mul_le_mul_of_nonneg_left
            (Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ j (by omega)) (by positivity))
  · have hS : 1 / b ^ 2 ≤ Work.Spaces.Wt α z θ := one_div_sq_le_Wt hα hz0 hz.2 hsin
    have hkey := hstep (D := Work.Spaces.mixed j i f z θ) (S := Work.Spaces.Wt α z θ) hS
    exact le_trans hkey (mul_le_mul_of_nonneg_left
      (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hji') (by positivity))

/-! ## The box integral -/

theorem boxInt_mixed_le_HkSq {α : ℝ} (hα : 0 < α) (a b δ : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hδ2 : δ < Real.pi / 2 - δ) (j i : ℕ) (hji : j + i ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 4 f →
      (∫ p in Set.Icc a b ×ˢ Set.Icc δ (Real.pi / 2 - δ),
          (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
        ≤ C * Work.Spaces.HkSq α 4 f := by
  refine ⟨b ^ 4 + 1, by positivity, ?_⟩
  intro f hF hmem
  -- the box is contained in the closed quadrant, and in the open quadrant
  have hsZsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_of_lt (lt_of_lt_of_le ha hz.1)
  have hsΘsub : Set.Icc δ (Real.pi / 2 - δ) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_trans (le_of_lt hδ) hθ.1, by linarith [hθ.2]⟩
  have hpt : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc δ (Real.pi / 2 - δ),
      (Work.Spaces.mixed j i f z θ) ^ 2 ≤ (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z hz θ hθ => mixed_sq_le_HkIntegrand_box hα ha hδ hji hz hθ
  have hboxsub : Set.Icc a b ×ˢ Set.Icc δ (Real.pi / 2 - δ) ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨lt_of_lt_of_le ha hz.1, lt_of_lt_of_le hδ hθ.1,
      lt_of_le_of_lt hθ.2 (by linarith [hδ])⟩
  -- continuity of the integrand on the compact box, hence integrability
  have hcontG : ContinuousOn
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.mixed j i f z θ) ^ 2))
      (Set.Icc a b ×ˢ Set.Icc δ (Real.pi / 2 - δ)) :=
    (((hF.mixed j i).forall 0).continuousOn.mono hboxsub).pow 2
  have hIntG : IntegrableOn
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.mixed j i f z θ) ^ 2))
      (Set.Icc a b ×ˢ Set.Icc δ (Real.pi / 2 - δ)) volume :=
    hcontG.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- Fubini on the box
  have hFub := MeasureTheory.setIntegral_prod (μ := (volume : MeasureTheory.Measure ℝ))
      (ν := (volume : MeasureTheory.Measure ℝ))
      (f := Function.uncurry (fun z θ : ℝ => (Work.Spaces.mixed j i f z θ) ^ 2))
      (s := Set.Icc a b) (t := Set.Icc δ (Real.pi / 2 - δ)) hIntG
  -- the pointwise bound, integrated in `θ` and then in `z`
  have hstep1 : (∫ z in Set.Icc a b,
        ∫ θ in Set.Icc δ (Real.pi / 2 - δ), (Work.Spaces.mixed j i f z θ) ^ 2)
      ≤ ∫ z in Set.Icc a b,
          (∫ θ in Work.Spaces.Iθ, (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ) := by
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) ?_ ?_
    · exact integral_nonneg fun θ => sq_nonneg _
    · refine MeasureTheory.IntegrableOn.congr_fun
        (f := fun z => (b ^ 4 + 1) * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 f z θ) ?_ (fun z hz => ?_) measurableSet_Icc
      · exact MeasureTheory.IntegrableOn.mono_set
          (hmem.2.const_mul (b ^ 4 + 1)) hsZsub
      · exact (MeasureTheory.integral_const_mul (b ^ 4 + 1)
          (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)).symm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
      have hzI : z ∈ Work.Spaces.Iz := hsZsub hz
      have h1 : (∫ θ in Set.Icc δ (Real.pi / 2 - δ), (Work.Spaces.mixed j i f z θ) ^ 2)
          ≤ ∫ θ in Set.Icc δ (Real.pi / 2 - δ),
              (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ :=
        MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
          (MeasureTheory.IntegrableOn.mono_set
            ((hmem.1 z hzI).const_mul (b ^ 4 + 1)) hsΘsub)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => hpt z hz θ hθ))
      have h2 : (∫ θ in Set.Icc δ (Real.pi / 2 - δ),
            (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ)
          = (b ^ 4 + 1) * ∫ θ in Set.Icc δ (Real.pi / 2 - δ),
              Work.Spaces.HkIntegrand α 4 f z θ :=
        MeasureTheory.integral_const_mul _ _
      have h3 : (∫ θ in Set.Icc δ (Real.pi / 2 - δ), Work.Spaces.HkIntegrand α 4 f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
        MeasureTheory.setIntegral_mono_set (hmem.1 z hzI)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
          (Eventually.of_forall fun θ hθ => hsΘsub hθ)
      have h4 : (b ^ 4 + 1) * (∫ θ in Set.Icc δ (Real.pi / 2 - δ),
            Work.Spaces.HkIntegrand α 4 f z θ)
          ≤ (b ^ 4 + 1) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : (b ^ 4 + 1) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          = ∫ θ in Work.Spaces.Iθ, (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ :=
        (MeasureTheory.integral_const_mul _ _).symm
      linarith
  have hstep2 : (∫ z in Set.Icc a b,
        (∫ θ in Work.Spaces.Iθ, (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ))
      = (b ^ 4 + 1) * ∫ z in Set.Icc a b,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := by
    have h1 : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ)
        = fun z : ℝ => (b ^ 4 + 1) * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 f z θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
    rw [h1, MeasureTheory.integral_const_mul]
  -- enlarge the angular interval and then the radial domain
  have hstep3 : (∫ z in Set.Icc a b,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ))
      ≤ ∫ z in Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
    MeasureTheory.setIntegral_mono_set hmem.2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
      (Eventually.of_forall fun z hz => hsZsub hz)
  have hfinal : (∫ z in Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ))
      = Work.Spaces.HkSq α 4 f := rfl
  calc (∫ p in Set.Icc a b ×ˢ Set.Icc δ (Real.pi / 2 - δ),
          (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc δ (Real.pi / 2 - δ),
          (Work.Spaces.mixed j i f z θ) ^ 2 := hFub
    _ ≤ ∫ z in Set.Icc a b,
          (∫ θ in Work.Spaces.Iθ, (b ^ 4 + 1) * Work.Spaces.HkIntegrand α 4 f z θ) := hstep1
    _ = (b ^ 4 + 1) * ∫ z in Set.Icc a b,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := hstep2
    _ ≤ (b ^ 4 + 1) * ∫ z in Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = (b ^ 4 + 1) * Work.Spaces.HkSq α 4 f := by rw [hfinal]

end Work.FTS.GalFields.Tail
