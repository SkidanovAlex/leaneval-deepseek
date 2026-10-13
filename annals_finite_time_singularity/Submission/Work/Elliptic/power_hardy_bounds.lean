import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Power-type Hardy bounds for a `C¹` function vanishing at `0`

If `f : ℝ → ℝ` is `C¹` on `[0,a]` (`0 < a`) and `f 0 = 0`, then there is a constant `C ≥ 0`
with `|f t| ≤ C t` and `|deriv f t| ≤ C` for all `t ∈ (0,a)`.

The argument is short and uses only the elementary mean value theorem on the convex set
`[0,a]`:

* `ContDiffOn.continuousOn_derivWithin` shows that `derivWithin f (Icc 0 a)` is continuous on
  the compact set `[0,a]`, hence bounded there by some `C₀` — this gives the bound on `deriv f`
  on the interior, because `derivWithin f (Icc 0 a) t = deriv f t` for `t` in the interior.
* `Convex.norm_image_sub_le_of_norm_derivWithin_le` (the convex mean value inequality) applied
  to `s = Icc 0 a` turns the bound on the within-derivative into `‖f t - f 0‖ ≤ C₀ * ‖t - 0‖`,
  i.e. `|f t| ≤ C₀ * t` on the interior.
-/

open scoped Topology

namespace Work.Elliptic

theorem power_hardy_bounds {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) (h0 : f 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ t ∈ Set.Ioo 0 a, |f t| ≤ C * t) ∧
      (∀ t ∈ Set.Ioo 0 a, |deriv f t| ≤ C) := by
  -- The within-derivative on `[0,a]` is continuous on the compact interval, hence bounded.
  have hs : UniqueDiffOn ℝ (Set.Icc 0 a) := uniqueDiffOn_Icc ha
  have hcont : ContinuousOn (derivWithin f (Set.Icc 0 a)) (Set.Icc 0 a) :=
    hf.continuousOn_derivWithin hs le_rfl
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₀ 0, le_max_right C₀ 0, ?_, ?_⟩
  · -- Bound on `f` itself, via the convex mean value inequality on `[0,a]`.
    intro t ht
    have hmem : t ∈ Set.Icc 0 a := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h0mem : (0 : ℝ) ∈ Set.Icc 0 a := ⟨le_refl 0, ha.le⟩
    have hd : DifferentiableOn ℝ f (Set.Icc 0 a) := hf.differentiableOn_one
    have hb : ∀ x ∈ Set.Icc 0 a, ‖derivWithin f (Set.Icc 0 a) x‖ ≤ max C₀ 0 :=
      fun x hx => (hC₀ x hx).trans (le_max_left _ _)
    have hmain := Convex.norm_image_sub_le_of_norm_derivWithin_le (f := f) (s := Set.Icc 0 a)
      (C := max C₀ 0) (x := 0) (y := t) hd hb (convex_Icc 0 a) h0mem hmem
    simpa only [h0, sub_zero, Real.norm_eq_abs, abs_of_pos ht.1] using hmain
  · -- Bound on `deriv f`: on the interior the within-derivative agrees with `deriv`.
    intro t ht
    have hmem : t ∈ Set.Icc 0 a := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hnhds : Set.Icc (0 : ℝ) a ∈ 𝓝 t :=
      Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
    have hdt : deriv f t = derivWithin f (Set.Icc 0 a) t :=
      (derivWithin_of_mem_nhds hnhds).symm
    rw [hdt]
    simpa only [Real.norm_eq_abs] using (hC₀ t hmem).trans (le_max_left _ _)

end Work.Elliptic
