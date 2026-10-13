/-
# `Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_pihalf`

The doubly-mollified datum `zmoll G δ ε` vanishes on the angular boundary line `θ = π/2`
(one half of the `StripAdm` field of `Work.FTS.EllSol.EllPkgAux.mollAdm`).

The mathematical content is the *reflection symmetry* of the angular mollification: the
doubly-odd extension `Qext G w` of the slice `s ↦ G w s` is odd about `π/2`
(`K5c.Qext_pihalf_odd`), and the kernel `sKer ε` is even with support in `[-ε, ε]`; since
`ε ≤ 1/2 < π/2`, the reflection `u ↦ π/2 - u` of the convolution variable turns the whole
integrand `u ↦ sKer ε u · Qext G w (π/2 - u)` into its negative (a.e., the single point
`u = 0` being the only exception).  Hence the angular mollification at `θ = π/2` is zero,
and integrating the resulting identically-zero function in the logarithmic radial variable
gives the claim.  No hypothesis whatsoever on the datum `G` is needed.

The proof is carried out with the two Haar-measure substitution lemmas
`MeasureTheory.integral_sub_left_eq_self` and `MeasureTheory.integral_add_left_eq_self`
(no integrability of `G` is assumed anywhere: the argument only uses `∫ f = -∫ f`, and
`MeasureTheory.integral_neg` is unconditional).
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open MeasureTheory Set Filter

open Work.FTS.EllSol.PkgK5.K5c

/-- **The angular mollification vanishes at `θ = π/2`.**  For every datum `G`, every `w`, and
every scale `ε ∈ (0, 1/2]`, the angular mollification `thMoll G ε w` of the slice
`s ↦ G w s` (through the doubly-odd extension `Qext G w`) is `0` at `θ = π/2`.

Indeed `sKer ε` is even and supported in `[-ε, ε]`, and on `(-ε, ε) \ {0}` the oddness of
`Qext` about `π/2` gives `Qext G w (π/2 - u) = -Qext G w (π/2 + u)`, so the substitution
`u ↦ π/2 - u` (which preserves Lebesgue measure) exhibits the integral as the integral of
its own negative. -/
theorem thMoll_pihalf_eq_zero (G : ℝ → ℝ → ℝ) (ε w : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    thMoll G ε w (Real.pi / 2) = 0 := by
  change (∫ s : ℝ, sKer ε (Real.pi / 2 - s) * Qext G w s) = 0
  set f : ℝ → ℝ := fun s => sKer ε (Real.pi / 2 - s) * Qext G w s with hf
  -- The pointwise oddness of the shifted integrand away from `u = 0`.
  have key : ∀ u : ℝ, u ≠ 0 → f (Real.pi / 2 - u) = -f (Real.pi / 2 + u) := by
    intro u hu0
    have hFu : f (Real.pi / 2 - u) = sKer ε u * Qext G w (Real.pi / 2 - u) := by
      simp only [hf]
      rw [show Real.pi / 2 - (Real.pi / 2 - u) = u by ring]
    have hFv : f (Real.pi / 2 + u) = sKer ε u * Qext G w (Real.pi / 2 + u) := by
      simp only [hf]
      rw [show Real.pi / 2 - (Real.pi / 2 + u) = -u by ring, sKer_even]
    rw [hFu, hFv]
    by_cases hbig : ε ≤ |u|
    · -- outside the support of the kernel both sides vanish
      rw [sKer_eq_zero_of_le_abs hε hbig]
      ring
    · have hu_lt : |u| < ε := not_le.mp hbig
      have hpos : 0 < |u| := abs_pos.mpr hu0
      have hpi2 : |u| ≤ Real.pi / 2 := by
        have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      have hQ : Qext G w (Real.pi / 2 - |u|) = -Qext G w (Real.pi / 2 + |u|) :=
        Qext_pihalf_odd G w |u| hpos hpi2
      rcases lt_or_ge 0 u with hu | hu
      · -- `u > 0`: the identity is `Qext_pihalf_odd` at `s = u`
        rw [abs_of_pos hu] at hQ
        rw [hQ]
        ring
      · -- `u < 0`: the same identity at `s = -u`, using evenness of the kernel
        have huneg : u < 0 := lt_of_le_of_ne hu hu0
        have habs : |u| = -u := abs_of_neg huneg
        have hsu : sKer ε u = sKer ε |u| := by rw [habs, sKer_even]
        rw [hsu, show Real.pi / 2 - u = Real.pi / 2 + |u| by rw [habs]; ring,
          show Real.pi / 2 + u = Real.pi / 2 - |u| by rw [habs]; ring, hQ]
        ring
  -- The shifted integrands are a.e. negatives of each other.
  have hgh : (fun u : ℝ => f (Real.pi / 2 - u)) =ᵐ[volume]
      (fun u : ℝ => -f (Real.pi / 2 + u)) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    by_contra hne
    exact hu (key u hne)
  -- The reflection `s ↦ π/2 - s` and the translation `s ↦ π/2 + s` preserve Lebesgue measure.
  have A1 : (∫ s : ℝ, f s) = ∫ u : ℝ, f (Real.pi / 2 - u) :=
    (MeasureTheory.integral_sub_left_eq_self f volume (Real.pi / 2)).symm
  have A2 : (∫ s : ℝ, f s) = ∫ u : ℝ, f (Real.pi / 2 + u) :=
    (MeasureTheory.integral_add_left_eq_self f (Real.pi / 2)).symm
  have C : (∫ u : ℝ, f (Real.pi / 2 - u)) = -∫ u : ℝ, f (Real.pi / 2 + u) := by
    rw [MeasureTheory.integral_congr_ae hgh, MeasureTheory.integral_neg]
  linarith [A1, A2, C]

theorem zmoll_theta_pihalf (G : ℝ → ℝ → ℝ) (δ ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (z : ℝ) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z (Real.pi / 2) = 0 := by
  have hth : ∀ w : ℝ, Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w (Real.pi / 2) = 0 :=
    fun w => thMoll_pihalf_eq_zero G ε w hε hε2
  simp only [Work.FTS.EllSol.PkgK5.K5c.zmoll, hth, mul_zero]
  exact MeasureTheory.integral_zero ℝ ℝ

end Work.FTS.EllSol.EllPkgAux.MollSmooth
