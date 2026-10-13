/-
# The weighted `L²` slot bound in `ℋ^k`, for arbitrary `k`

`SlotL2LeHkSq.integral_slot_sq_rpow_le_HkSq` proves, in `ℋ⁴`,

  `∫_μ w²·sin(2θ)^c · (D_z^j D_θ^i f)² ≤ HkSq α 4 f`  for `j + i ≤ 4`, `c ≥ -η`.

The present module is the same statement with `4` replaced by an arbitrary `k`; the two
pointwise slot bounds of `SlotWt/` (`dzSlot_weight_le_HkIntegrand4`,
`mixedSlot_weight_le_HkIntegrand4`) are generalized here to arbitrary `k`
(`dzSlot_weight_le_HkIntegrand_gen`, `mixedSlot_weight_le_HkIntegrand_gen`) and the assembly
is verbatim the one of the `ℋ⁴` proof.

Ingredients:

* `HkIntegrand_integrable_prod_fts` (`k` arbitrary) — product-integrability of the
  `ℋ^k`-integrand from `HkMem`;
* `ae_mem_openQuadrant_fts` — the product measure is carried by the open quadrant, where
  `0 < sin(2θ) ≤ 1`, so that the exponent `c ≥ -η ≥ -γ` can be split off as
  `sin(2θ)^c = sin(2θ)^{-η}·sin(2θ)^{c+η}` (resp. `sin(2θ)^{-γ}·sin(2θ)^{c+γ}`);
* the two extraction lemmas `Work.Spaces.sq_le_HkIntegrand_z` /
  `Work.Spaces.sq_le_HkIntegrand_mixed`, now with the matching `k`.

Every declaration below is complete (no placeholders).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipSlotIntegrable
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.SlotHkGen

set_option autoImplicit false

/-! ## A single pure `D_z`-slot of the strong weight, in `ℋ^k` -/

/-- For `c ≥ -η` and a slot `m ≤ k`, the weighted square
`w(z)²·sin(2θ)^c·(D_z^m g)²` is bounded pointwise by `HkIntegrand α k g` on the open strip
`θ ∈ (0,π/2)`.  This is `SlotWt.dzSlot_weight_le_HkIntegrand4` with `4` replaced by `k`. -/
theorem dzSlot_weight_le_HkIntegrand_gen {α c : ℝ} {g : ℝ → ℝ → ℝ} {k m : ℕ}
    (hc : -(Work.Spaces.eta) ≤ c) (hm : m ≤ k) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.DzIter m g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  -- `sin(2θ) ∈ (0,1]` on the open strip
  have hsin_pos : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    have hp := Real.pi_pos
    linarith [hθ.2]
  have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hcη : 0 ≤ c + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  -- the resulting power of `sin(2θ)` is at most `1`
  have hs_cη_le : (Real.sin (2 * θ)) ^ (c + Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hsin_pos.le hsin_le hcη
  -- the matching slot of the `H^k`-integrand
  have hterm := Work.Spaces.sq_le_HkIntegrand_z α k g z θ m hm
  -- split `sin(2θ)^c = sin(2θ)^{-η} · sin(2θ)^{c+η}`
  have h1 : (Real.sin (2 * θ)) ^ c
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.eta) := by
    rw [← Real.rpow_add hsin_pos]
    congr 1
    ring
  -- `(sin(2θ)^{η/2})² = sin(2θ)^{η}`
  have h3 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hsin_pos.le]
    congr 1
    ring
  -- expand the weighted `D_z`-slot
  have h2 : (Work.Spaces.DzIter m g z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter m g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_pow, h3, Real.rpow_neg hsin_pos.le]
    ring
  calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.DzIter m g z θ) ^ 2
      = (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.eta) := by
        rw [h1, h2]; ring
    _ ≤ (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs_cη_le
          (sq_nonneg (Work.Spaces.DzIter m g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))))
    _ = (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := mul_one _
    _ ≤ Work.Spaces.HkIntegrand α k g z θ := hterm

/-! ## A single mixed slot of the strong weight, in `ℋ^k` -/

/-- For `c ≥ -γ(α)` and a slot `(b,a)` with `a ≥ 1`, `a + b ≤ k`, the weighted square
`w(z)²·sin(2θ)^c·(D_z^b D_θ^a g)²` is bounded pointwise by `HkIntegrand α k g` on the open
strip `θ ∈ (0,π/2)`.  This is `SlotWt.mixedSlot_weight_le_HkIntegrand4` with `4` replaced
by `k`. -/
theorem mixedSlot_weight_le_HkIntegrand_gen {α c : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    {k a b : ℕ}
    (hc : -(Work.Spaces.gam α) ≤ c) (ha : 1 ≤ a) (hab : a + b ≤ k) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθ2 : θ < Real.pi / 2 := hθ.2
  -- `sin(2θ) ∈ (0,1]` on the open strip
  have hsin_pos : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    have hp := Real.pi_pos
    linarith
  have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : 0 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.gam_pos hα)
  have hcg : 0 ≤ c + Work.Spaces.gam α := by linarith
  -- the resulting power of `sin(2θ)` is at most `1`
  have hs_cg_le : (Real.sin (2 * θ)) ^ (c + Work.Spaces.gam α) ≤ 1 :=
    Real.rpow_le_one hsin_pos.le hsin_le hcg
  -- the matching slot of the `H^k`-integrand
  have hterm := Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ a b ha hab
  -- split `sin(2θ)^c = sin(2θ)^{-γ} · sin(2θ)^{c+γ}`
  have h1 : (Real.sin (2 * θ)) ^ c
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.gam α) := by
    rw [← Real.rpow_add hsin_pos]
    congr 1
    ring
  -- `(sin(2θ)^{-γ/2})² = sin(2θ)^{-γ}`
  have h3 : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hsin_pos.le]
    congr 1
    ring
  -- expand the weighted mixed slot
  have h2 : (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.mixed b a g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, h3]
    ring
  calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.mixed b a g z θ) ^ 2
      = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.gam α) := by
        rw [h1, h2]; ring
    _ ≤ (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs_cg_le
          (sq_nonneg (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ))
    _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := mul_one _
    _ ≤ Work.Spaces.HkIntegrand α k g z θ := hterm

/-! ## The target -/

theorem integral_slot_sq_rpow_le_HkSq_gen {α : ℝ} {g : ℝ → ℝ → ℝ} {c : ℝ} {k j i : ℕ}
    (hα : 0 < α) (hc : -(Work.Spaces.eta) ≤ c) (hji : j + i ≤ k)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    (∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ Work.Spaces.HkSq α k g := by
  have hHk : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.StrongEps.EpsE4Thr.HkIntegrand_integrable_prod_fts (k := k) hsm hmem
  -- the pointwise domination on the open quadrant
  have hdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ c)
        * (Work.Spaces.mixed j i g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g z θ := by
    intro z θ hz hθ hθ2
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      exact dzSlot_weight_le_HkIntegrand_gen (α := α) (c := c) (g := g) (k := k) (m := j)
        hc (by omega) ⟨hθ, hθ2⟩
    · have heta_gam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
        have h1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
        have h2 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
        linarith
      have hcg : -(Work.Spaces.gam α) ≤ c := by linarith
      exact mixedSlot_weight_le_HkIntegrand_gen (α := α) (c := c) (g := g) (k := k)
        (a := i) (b := j) hα hcg hi (by omega) ⟨hθ, hθ2⟩
  have hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g p.1 p.2 := by
    filter_upwards [Work.FTS.StrongEps.EpsE4Thr.ae_mem_openQuadrant_fts] with p hp
    exact hdom p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 ≤ (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2 := by
    filter_upwards [Work.FTS.StrongEps.EpsE4Thr.ae_mem_openQuadrant_fts] with p hp
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ c)) (sq_nonneg _)
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])).le
  have hle := MeasureTheory.integral_mono_of_nonneg hnn hHk hae
  have heq : (∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α k g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = Work.Spaces.HkSq α k g := by
    rw [Work.Spaces.HkSq]
    exact (MeasureTheory.integral_integral
      (f := fun z θ => Work.Spaces.HkIntegrand α k g z θ) hHk).symm
  calc (∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α k g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hle
    _ = Work.Spaces.HkSq α k g := heq

end Work.FTS.StrongEps.EpsE4Thr.SlotHkGen
