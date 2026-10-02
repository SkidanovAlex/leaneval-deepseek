import Mathlib
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Set Filter Metric

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Work.GATE2.PL

noncomputable section

/-! ## The affine normalisation of a germ

If `F` is complex differentiable and we form the normalised germ
`u ↦ (F (z₀ + lam * u) - z₀) / lam`, the second and third derivatives at `0` are the
corresponding derivatives of `F` at `z₀`, weighted by `lam` and `lam ^ 2`.  Following the
normalisation used for parabolic germs, the first derivative is normalised to `1`, so the
second and third derivatives acquire one half-power of `lam` less than the naive chain rule
would give. -/
lemma iteratedDeriv_two_three_affine_normalised (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (z₀ lam : ℂ) :
    iteratedDeriv 2 (fun u => (F (z₀ + lam * u) - z₀) / lam) 0 = iteratedDeriv 2 F z₀ * lam ∧
      iteratedDeriv 3 (fun u => (F (z₀ + lam * u) - z₀) / lam) 0 =
        iteratedDeriv 3 F z₀ * lam ^ 2 := by
  have hdA : deriv (fun u : ℂ => z₀ + lam * u) 0 = lam := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_mul lam).const_add z₀).deriv
  have hA2 : iteratedDeriv 2 (fun u : ℂ => z₀ + lam * u) 0 = 0 := by
    rw [iteratedDeriv_const_add (f := fun u : ℂ => lam * u) (x := 0) (by norm_num) z₀,
      iteratedDeriv_const_mul (f := fun u : ℂ => u) (x := 0) lam (by fun_prop),
      iteratedDeriv_fun_id_zero]
    norm_num
  have hA3 : iteratedDeriv 3 (fun u : ℂ => z₀ + lam * u) 0 = 0 := by
    rw [iteratedDeriv_const_add (f := fun u : ℂ => lam * u) (x := 0) (by norm_num) z₀,
      iteratedDeriv_const_mul (f := fun u : ℂ => u) (x := 0) lam (by fun_prop),
      iteratedDeriv_fun_id_zero]
    norm_num
  have hH2 : ∀ x : ℂ,
      iteratedDeriv 2 (fun v : ℂ => (F v - z₀) / lam) x = lam⁻¹ * iteratedDeriv 2 F x := by
    intro x
    have he : (fun v : ℂ => (F v - z₀) / lam) = fun v => (-(lam⁻¹ * z₀)) + lam⁻¹ * F v := by
      funext v; rw [div_eq_inv_mul]; ring
    rw [he, iteratedDeriv_const_add (f := fun v : ℂ => lam⁻¹ * F v) (x := x) (by norm_num)
        (-(lam⁻¹ * z₀)),
      iteratedDeriv_const_mul (f := F) (x := x) lam⁻¹ ((hF.contDiff : ContDiff ℂ 2 F).contDiffAt)]
  have hH3 : ∀ x : ℂ,
      iteratedDeriv 3 (fun v : ℂ => (F v - z₀) / lam) x = lam⁻¹ * iteratedDeriv 3 F x := by
    intro x
    have he : (fun v : ℂ => (F v - z₀) / lam) = fun v => (-(lam⁻¹ * z₀)) + lam⁻¹ * F v := by
      funext v; rw [div_eq_inv_mul]; ring
    rw [he, iteratedDeriv_const_add (f := fun v : ℂ => lam⁻¹ * F v) (x := x) (by norm_num)
        (-(lam⁻¹ * z₀)),
      iteratedDeriv_const_mul (f := F) (x := x) lam⁻¹ ((hF.contDiff : ContDiff ℂ 3 F).contDiffAt)]
  have hcH2 : ContDiffAt ℂ 2 (fun v : ℂ => (F v - z₀) / lam)
      ((fun u : ℂ => z₀ + lam * u) 0) := by
    have h1 : ContDiffAt ℂ 2 (fun v : ℂ => F v - z₀) z₀ :=
      ((hF.contDiff : ContDiff ℂ 2 F).contDiffAt).sub contDiffAt_const
    simpa using h1.div_const lam
  have hcH3 : ContDiffAt ℂ 3 (fun v : ℂ => (F v - z₀) / lam)
      ((fun u : ℂ => z₀ + lam * u) 0) := by
    have h1 : ContDiffAt ℂ 3 (fun v : ℂ => F v - z₀) z₀ :=
      ((hF.contDiff : ContDiff ℂ 3 F).contDiffAt).sub contDiffAt_const
    simpa using h1.div_const lam
  have hcA2 : ContDiffAt ℂ 2 (fun u : ℂ => z₀ + lam * u) (0 : ℂ) := by fun_prop
  have hcA3 : ContDiffAt ℂ 3 (fun u : ℂ => z₀ + lam * u) (0 : ℂ) := by fun_prop
  constructor
  · have key2 : iteratedDeriv 2 (fun u : ℂ => (F (z₀ + lam * u) - z₀) / lam) 0 =
        iteratedDeriv 2 (fun v : ℂ => (F v - z₀) / lam) ((fun u : ℂ => z₀ + lam * u) 0) *
          deriv (fun u : ℂ => z₀ + lam * u) 0 ^ 2 +
        deriv (fun v : ℂ => (F v - z₀) / lam) ((fun u : ℂ => z₀ + lam * u) 0) *
          iteratedDeriv 2 (fun u : ℂ => z₀ + lam * u) 0 :=
      iteratedDeriv_comp_two (g := fun v : ℂ => (F v - z₀) / lam)
        (f := fun u : ℂ => z₀ + lam * u) (x := 0) hcH2 hcA2
    rw [key2]
    simp only [mul_zero, add_zero]
    rw [hH2, hdA, hA2, mul_zero, add_zero]
    by_cases h : lam = 0
    · subst h; ring
    · field_simp
  · have key3 : iteratedDeriv 3 (fun u : ℂ => (F (z₀ + lam * u) - z₀) / lam) 0 =
        iteratedDeriv 3 (fun v : ℂ => (F v - z₀) / lam) ((fun u : ℂ => z₀ + lam * u) 0) *
          deriv (fun u : ℂ => z₀ + lam * u) 0 ^ 3 +
        3 * iteratedDeriv 2 (fun v : ℂ => (F v - z₀) / lam) ((fun u : ℂ => z₀ + lam * u) 0) *
          iteratedDeriv 2 (fun u : ℂ => z₀ + lam * u) 0 * deriv (fun u : ℂ => z₀ + lam * u) 0 +
        deriv (fun v : ℂ => (F v - z₀) / lam) ((fun u : ℂ => z₀ + lam * u) 0) *
          iteratedDeriv 3 (fun u : ℂ => z₀ + lam * u) 0 :=
      iteratedDeriv_comp_three (g := fun v : ℂ => (F v - z₀) / lam)
        (f := fun u : ℂ => z₀ + lam * u) (x := 0) hcH3 hcA3
    rw [key3]
    simp only [mul_zero, add_zero]
    rw [hH3, hH2, hdA, hA2, hA3]
    simp only [mul_zero, zero_mul, add_zero]
    by_cases h : lam = 0
    · subst h; ring
    · field_simp

/-- The parameter `a` of a `ParabolicBounds` germ is the affine-normalisation
invariant `(2/3) F'''(z₀)/F''(z₀)²` of the map `F` it is a normalisation of.

The ingredients are already in the workspace: `Work.FatouCoord.Petal.parabolic_iteratedDeriv_two`
(`f''(0) = 2`) and `Work.FatouCoord.Petal.parabolic_iteratedDeriv_three` (`f'''(0) = 6a`) in
`Submission/Work/FatouCoord/Petal/reflected_inverse_germ.lean`, together with the identity
`iteratedDeriv k (fun u => (F (z₀ + lam * u) - z₀) / lam) 0 = iteratedDeriv k F z₀ * lam ^ (k-1)`
for `k = 2, 3` (Faà di Bruno for an affine substitution / repeated `deriv_comp`, valid also for
`lam = 0` since both sides vanish there). -/
theorem parabolicBounds_a_value {F f h : ℂ → ℂ} {z₀ a lam : ℂ} {r A A' : ℝ}
    (hF : Differentiable ℂ F) (h2 : iteratedDeriv 2 F z₀ ≠ 0)
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hfeq : ∀ u ∈ Metric.ball 0 r, f u = (F (z₀ + lam * u) - z₀) / lam) :
    a = (2 / 3 : ℂ) * iteratedDeriv 3 F z₀ / (iteratedDeriv 2 F z₀) ^ 2 := by
  have h2f : iteratedDeriv 2 f 0 = 2 := Work.FatouCoord.Petal.parabolic_iteratedDeriv_two hb
  have h3f : iteratedDeriv 3 f 0 = 6 * a := Work.FatouCoord.Petal.parabolic_iteratedDeriv_three hb
  have hfe : f =ᶠ[𝓝 (0 : ℂ)] fun u => (F (z₀ + lam * u) - z₀) / lam := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hb.hr] with u hu
    exact hfeq u hu
  obtain ⟨hA2, hA3⟩ := iteratedDeriv_two_three_affine_normalised F hF z₀ lam
  have e2 : iteratedDeriv 2 f 0 = iteratedDeriv 2 F z₀ * lam := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hfe]; exact hA2
  have e3 : iteratedDeriv 3 f 0 = iteratedDeriv 3 F z₀ * lam ^ 2 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 3 hfe]; exact hA3
  have h2e : iteratedDeriv 2 F z₀ * lam = 2 := by rw [← e2, h2f]
  have h3e : iteratedDeriv 3 F z₀ * lam ^ 2 = 6 * a := by rw [← e3, h3f]
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2e
    norm_num at h2e
  have hF2 : iteratedDeriv 2 F z₀ = 2 / lam := by
    rw [eq_div_iff hlam]; exact h2e
  have hF3 : iteratedDeriv 3 F z₀ = 6 * a / lam ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hlam)]; exact h3e
  rw [hF3, hF2]
  field_simp
  ring

end

end Work.GATE2.PL
