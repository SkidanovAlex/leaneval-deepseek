import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

open Convexity

theorem denseSimplex3 (i : Fin 3) :
    Dense {w : Convexity.StdSimplex ℝ (Fin 3) | 0 < w.weights i} := by
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun x => ?_
  let A : Set ↑unitInterval := {t | 0 < (t : ℝ)}
  let g : ↑unitInterval → Convexity.StdSimplex ℝ (Fin 3) := fun t =>
    convexCombPair (R := ℝ) (unitInterval.symm t) t
      (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) x (Convexity.StdSimplex.single i)
  have hg : Continuous g :=
    Convexity.StdSimplex.continuous_convexCombPair x (Convexity.StdSimplex.single i)
  have hg0 : g 0 = x := by simp [g]
  have hstep : ∀ t : ↑unitInterval, 0 < (t : ℝ) →
      0 < (convexCombPair (R := ℝ) (unitInterval.symm t) t
        (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) x
        (Convexity.StdSimplex.single i)).weights i := by
    intro t ht
    rw [Convexity.StdSimplex.weights_convexCombPair]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Convexity.StdSimplex.weights_single, Finsupp.single_eq_same, mul_one]
    have hprod : 0 ≤ ↑(unitInterval.symm t) * x.weights i :=
      mul_nonneg (unitInterval.nonneg _) (x.weights_nonneg i)
    linarith
  have hA : g '' A ⊆ {w : Convexity.StdSimplex ℝ (Fin 3) | 0 < w.weights i} := by
    rintro _ ⟨t, ht, rfl⟩
    exact hstep t ht
  have h0A : (0 : ↑unitInterval) ∈ closure A := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hr0 : (0 : ℝ) < min (ε / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
    have hr1 : min (ε / 2) (1 / 2) ≤ 1 := (min_le_right _ _).trans (by norm_num)
    refine ⟨⟨min (ε / 2) (1 / 2), hr0.le, hr1⟩, hr0, ?_⟩
    rw [Subtype.dist_eq, Real.dist_eq]
    have h : (↑(0 : ↑unitInterval) : ℝ) = 0 := rfl
    rw [h, zero_sub, abs_neg, abs_of_pos hr0]
    calc min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  have hxA : x ∈ g '' closure A := ⟨0, h0A, hg0⟩
  exact closure_mono hA (image_closure_subset_closure_image hg hxA)

end Work.BridgeSquare
