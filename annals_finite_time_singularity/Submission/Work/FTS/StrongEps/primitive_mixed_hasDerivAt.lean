/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/primitive_mixed_hasDerivAt.lean`

The `s`-integral of a family of profiles `s ↦ W s`, all `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`, is differentiable in the spatial variables, with the derivative given by
the integral of the (next) mixed slot:

  `∂_z ∫_a^b D_z^j D_θ^i (W s) z θ ds = (∫_a^b D_z^{j+1}D_θ^i (W s) z θ ds) / z`,
  `∂_θ ∫_a^b D_z^j D_θ^i (W s) z θ ds = (∫_a^b D_z^{j}D_θ^{i+1}(W s) z θ ds) / sin(2θ)`.

The proof is the one-step parametric differentiation
(`hasDerivAt_intervalIntegral_of_deriv_le`, the `IntervalIntegral` form of Mathlib's
dominated-convergence differentiation lemma) applied to `G t x = D_z^jD_θ^i (W t) x θ` with

* `G' t x = D_z^{j+1}D_θ^i (W t) x θ / x`, using `∂_z D_z^jD_θ^i = D_z^{j+1}D_θ^i / z`
  (`Work.FTS.StrongEps.LocUnif.pz_mixed_div`), resp.
* `G' t y = D_z^{j}D_θ^{i+1} (W t) z y / sin 2y`, using
  `∂_θ D_z^jD_θ^i = D_z^{j}D_θ^{i+1} / sin 2θ` (`Work.FTS.StrongEps.LocUnif.pth_mixed_div`),

the domination constant coming from the hypothesis `hbdd` (a uniform bound on *all* the mixed
slots on any compact subset of `Q0`), after dividing by `z > 0` resp. `sin(2θ) > 0`.

Everything here is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- A function which is a.e. strongly measurable and bounded on `uIoc a b` is interval
integrable there. -/
theorem primitive_mixed_intervalIntegrable_of_bound {f : ℝ → ℝ} {a b C : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.uIoc a b)))
    (hbd : ∀ t ∈ Set.uIoc a b, |f t| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ hmeas C ?_
  · show volume (Set.Ioc (min a b) (max a b)) < ⊤
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Real.norm_eq_abs]
    exact hbd t ht

/-- `uIoc a b` is contained in `Icc 0 T` when `a, b ∈ Icc 0 T`. -/
theorem uIoc_subset_Icc_of_mem {a b T : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) T)
    (hb : b ∈ Set.Icc (0 : ℝ) T) : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
  intro t ht
  rw [Set.mem_uIoc] at ht
  rcases ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
  · exact ⟨le_trans ha.1 ht1.le, le_trans ht2 hb.2⟩
  · exact ⟨le_trans hb.1 ht1.le, le_trans ht2 ha.2⟩

/-! ## The two one-step differentiations -/

/-- **Differentiation of the `s`-integral in the radial variable.**  Under the hypotheses of the
statement (with `B` the uniform bound of all the mixed slots on the box
`Icc (z/2) (2z) ×ˢ Icc θ θ`), the map `z' ↦ ∫_a^b D_z^jD_θ^i(W s) z' θ ds` is differentiable at
`z` with derivative `(∫_a^b D_z^{j+1}D_θ^i(W s) z θ ds)/z`. -/
theorem hasDerivAt_integral_mixed_z {W : ℝ → ℝ → ℝ → ℝ} {T a b z θ B : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (W s))
    (hmeas : ∀ (k l : ℕ) (x y : ℝ), (x, y) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (W s) x y)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hB : 0 ≤ B)
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), ∀ q : ℝ × ℝ,
      q ∈ Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc θ θ →
        |Work.Spaces.mixed k l (W s) q.1 q.2| ≤ B)
    (hz0 : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (j i : ℕ) :
    HasDerivAt (fun z' => ∫ s in a..b, Work.Spaces.mixed j i (W s) z' θ)
      ((∫ s in a..b, Work.Spaces.mixed (j + 1) i (W s) z θ) / z) z := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := uIoc_subset_Icc_of_mem ha hb
  have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ.1, hθ.2⟩
  have hboxQ : Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc θ θ ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith [hx.1, hz0], by linarith [hy.1, hθ.1], by linarith [hy.2, hθ.2]⟩
  have hzK : (z, θ) ∈ Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc θ θ :=
    ⟨⟨by linarith [hz0], by linarith [hz0]⟩, ⟨le_rfl, le_rfl⟩⟩
  refine (hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b) (x₀ := z)
    (x₁ := z / 2) (x₂ := 2 * z)
    (G := fun t x => Work.Spaces.mixed j i (W t) x θ)
    (G' := fun t x => Work.Spaces.mixed (j + 1) i (W t) x θ / x)
    (bound := fun _ => B / (z / 2)) (by linarith) (by linarith) ?_ ?_ ?_ ?_ ?_ ?_).congr_deriv ?_
  · -- measurability of `G · x`
    intro x hx
    rw [Set.mem_Ioo] at hx
    have hxQ : (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, ⟨le_rfl, le_rfl⟩⟩
    exact (hmeas j i x θ hxQ).mono_measure (Measure.restrict_mono hsub le_rfl)
  · -- integrability of `G · z`
    refine primitive_mixed_intervalIntegrable_of_bound (C := B)
      ((hmeas j i z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)) ?_
    intro t ht
    exact hbdd t (hsub ht) j i (z, θ) hzK
  · -- measurability of `G' · z`
    have h1 := (hmeas (j + 1) i z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [div_eq_mul_inv] using h1.mul_const z⁻¹
  · -- the domination bound
    intro t ht x hx
    rw [Set.mem_Ioo] at hx
    have hxpos : 0 < x := by linarith
    have hxz : z / 2 ≤ x := le_of_lt hx.1
    have hb := hbdd t (hsub ht) (j + 1) i (x, θ)
      ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, ⟨le_rfl, le_rfl⟩⟩
    rw [abs_div, abs_of_pos hxpos]
    calc |Work.Spaces.mixed (j + 1) i (W t) x θ| / x
        ≤ B / x := div_le_div_of_nonneg_right hb (le_of_lt hxpos)
      _ ≤ B / (z / 2) := div_le_div_of_nonneg_left hB (by linarith [hz0]) hxz
  · exact intervalIntegrable_const
  · -- the pointwise derivative
    intro t ht x hx
    rw [Set.mem_Ioo] at hx
    have hxpos : 0 < x := by linarith
    have hxQ : (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, ⟨le_rfl, le_rfl⟩⟩
    exact (Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice
        ((hsm t (hsub ht)).mixed j i) hθ hxpos).congr_deriv
      (Work.FTS.StrongEps.LocUnif.pz_mixed_div j i (hsm t (hsub ht)) x θ hxQ)
  · -- convert the integral of the derivative
    rw [intervalIntegral.integral_div]

/-- **Differentiation of the `s`-integral in the angular variable.**  Under the hypotheses of the
statement (with `B` the uniform bound of all the mixed slots on the box
`Icc (z/2) (2z) ×ˢ Icc (θ/2) ((θ+π/2)/2)`), the map
`θ' ↦ ∫_a^b D_z^jD_θ^i(W s) z θ' ds` is differentiable at `θ` with derivative
`(∫_a^b D_z^{j}D_θ^{i+1}(W s) z θ ds)/sin(2θ)`. -/
theorem hasDerivAt_integral_mixed_th {W : ℝ → ℝ → ℝ → ℝ} {T a b z θ B : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (W s))
    (hmeas : ∀ (k l : ℕ) (x y : ℝ), (x, y) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (W s) x y)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hB : 0 ≤ B)
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), ∀ q : ℝ × ℝ,
      q ∈ Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2) →
        |Work.Spaces.mixed k l (W s) q.1 q.2| ≤ B)
    (hz0 : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (j i : ℕ) :
    HasDerivAt (fun θ' => ∫ s in a..b, Work.Spaces.mixed j i (W s) z θ')
      ((∫ s in a..b, Work.Spaces.mixed j (i + 1) (W s) z θ) / Real.sin (2 * θ)) θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := uIoc_subset_Icc_of_mem ha hb
  have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ.1, hθ.2⟩
  have hboxQ : Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)
      ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith [hx.1, hz0], by linarith [hy.1, hθ.1], by linarith [hy.2, hθ.2]⟩
  have hzK : z ∈ Set.Icc (z / 2) (2 * z) := ⟨by linarith [hz0], by linarith [hz0]⟩
  have hθK : θ ∈ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  obtain ⟨smin, hsmin_pos, hsmin_le⟩ :=
    exists_pos_min_sin_two (θlo := θ / 2) (θhi := (θ + Real.pi / 2) / 2)
      (by linarith [hθ.1]) (by linarith [hθ.2])
  -- the two points of the inner `θ`-interval carry all the box data
  have hmem : ∀ y ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
      (z, y) ∈ Work.FTS.EllipticEst.Q0 ∧
        (z, y) ∈ Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2) ∧
        0 < Real.sin (2 * y) := by
    intro y hy
    rw [Set.mem_Ioo] at hy
    have hyI : y ∈ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2) := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hyK : (z, y) ∈ Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2) :=
      ⟨hzK, hyI⟩
    exact ⟨hboxQ hyK, hyK, lt_of_lt_of_le hsmin_pos (hsmin_le y hyI)⟩
  refine (hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b) (x₀ := θ)
    (x₁ := θ / 2) (x₂ := (θ + Real.pi / 2) / 2)
    (G := fun t y => Work.Spaces.mixed j i (W t) z y)
    (G' := fun t y => Work.Spaces.mixed j (i + 1) (W t) z y / Real.sin (2 * y))
    (bound := fun _ => B / smin) (by linarith [hθ.1]) (by linarith [hθ.2])
      ?_ ?_ ?_ ?_ ?_ ?_).congr_deriv ?_
  · intro y hy
    rw [Set.mem_Ioo] at hy
    have hyI : y ∈ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2) := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hyQ : (z, y) ∈ Work.FTS.EllipticEst.Q0 := hboxQ ⟨hzK, hyI⟩
    exact (hmeas j i z y hyQ).mono_measure (Measure.restrict_mono hsub le_rfl)
  · refine primitive_mixed_intervalIntegrable_of_bound (C := B)
      ((hmeas j i z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)) ?_
    intro t ht
    exact hbdd t (hsub ht) j i (z, θ) ⟨hzK, hθK⟩
  · have h1 := (hmeas j (i + 1) z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa only [div_eq_mul_inv] using h1.mul_const (Real.sin (2 * θ))⁻¹
  · intro t ht y hy
    obtain ⟨-, hyK, hsin⟩ := hmem y hy
    have hb := hbdd t (hsub ht) j (i + 1) (z, y) hyK
    rw [abs_div, abs_of_pos hsin]
    calc |Work.Spaces.mixed j (i + 1) (W t) z y| / Real.sin (2 * y)
        ≤ B / Real.sin (2 * y) := div_le_div_of_nonneg_right hb (le_of_lt hsin)
      _ ≤ B / smin := div_le_div_of_nonneg_left hB hsmin_pos (hsmin_le y hyK.2)
  · exact intervalIntegrable_const
  · intro t ht y hy
    obtain ⟨hyQ, _, _⟩ := hmem y hy
    rw [Set.mem_Ioo] at hy
    exact (Work.FTS.StrongEps.SmoothOpen.hasDerivAt_slice_th
        ((hsm t (hsub ht)).mixed j i) hz0
        ⟨by linarith [hy.1, hθ.1], by linarith [hy.2, hθ.2]⟩).congr_deriv
      (Work.FTS.StrongEps.LocUnif.pth_mixed_div j i (hsm t (hsub ht)) z y hyQ)
  · rw [intervalIntegral.integral_div]

/-! ## The statement -/

theorem primitive_mixed_hasDerivAt {W : ℝ → ℝ → ℝ → ℝ} {T a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (W s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (W s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), ∀ q : ℝ × ℝ, q ∈ K →
        |Work.Spaces.mixed k l (W s) q.1 q.2| ≤ B)
    (j i : ℕ) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' => ∫ s in a..b, Work.Spaces.mixed j i (W s) z' θ)
        ((∫ s in a..b, Work.Spaces.mixed (j + 1) i (W s) z θ) / z) z) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' => ∫ s in a..b, Work.Spaces.mixed j i (W s) z θ')
        ((∫ s in a..b, Work.Spaces.mixed j (i + 1) (W s) z θ) / Real.sin (2 * θ)) θ) := by
  constructor
  · intro z θ hzθ
    obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hK : IsCompact (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc θ θ) :=
      isCompact_Icc.prod isCompact_Icc
    have hKQ : Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc θ θ ⊆ Work.FTS.EllipticEst.Q0 := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨by linarith [hx.1, hz0], by linarith [hy.1, hθ0], by linarith [hy.2, hθ1]⟩
    obtain ⟨B, hB0, hB⟩ := hbdd _ hK hKQ
    exact hasDerivAt_integral_mixed_z ha hb hsm hmeas hB0 hB hz0 ⟨hθ0, hθ1⟩ j i
  · intro z θ hzθ
    obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hK : IsCompact (Set.Icc (z / 2) (2 * z) ×ˢ
        Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)) := isCompact_Icc.prod isCompact_Icc
    have hKQ : Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)
        ⊆ Work.FTS.EllipticEst.Q0 := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨by linarith [hx.1, hz0], by linarith [hy.1, hθ0], by linarith [hy.2, hθ1]⟩
    obtain ⟨B, hB0, hB⟩ := hbdd _ hK hKQ
    exact hasDerivAt_integral_mixed_th ha hb hsm hmeas hB0 hB hz0 ⟨hθ0, hθ1⟩ j i

end Work.FTS.StrongEps
