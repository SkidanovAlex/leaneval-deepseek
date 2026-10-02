import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The box outside a disc is preconnected

The region

`{w : ℂ | |w.re - R| < a ∧ |w.im| < b ∧ R < ‖w‖}`

-- a horizontal strip `|w.re - R| < a`, `|w.im| < b` of width `2a` centred at the point `R`
of the real axis, from which the closed disc of radius `R` around the origin has been
removed -- is preconnected, whenever `0 < a`, `0 < b`, `0 < R` and `a < R`.

Because `a < R` the strip lies in the open right half plane `w.re > R - a > 0`, so that
`R < ‖w‖` is equivalent to `w.re > √(R² - w.im²)`, i.e. to

`max (R - a) (√(R² - w.im²)) < w.re < R + a`.

Hence the region is the union, over `y ∈ (-b, b)`, of the open horizontal segments

`{(x, y) | max (R - a) (√(R² - y²)) < x < R + a}`,

and each of these segments meets the vertical segment `{(R + a/2, t) | |t| < b}` (which lies
strictly to the right of the disc, and hence is contained in the region).  A union of
preconnected sets with a common point is preconnected, which gives the result.

* `reIm_box_inter_exterior` : the region is preconnected.
-/

namespace Work.Top

open Set

theorem reIm_box_inter_exterior {R a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) (haR : a < R) :
    IsPreconnected {w : ℂ | |w.re - R| < a ∧ |w.im| < b ∧ R < ‖w‖} := by
  -- `R < ‖w‖` as an inequality between squares
  have hnorm : ∀ w : ℂ, R < ‖w‖ ↔ R ^ 2 < w.re ^ 2 + w.im ^ 2 := by
    intro w
    have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← Real.sqrt_sq (norm_nonneg w), Real.lt_sqrt (le_of_lt hR), hsq]
  -- the lower boundary of the region as a function of the imaginary part
  set l : ℝ → ℝ := fun y => max (R - a) (Real.sqrt (R ^ 2 - y ^ 2)) with hl_def
  have hl_le_R : ∀ y, l y ≤ R := by
    intro y
    apply max_le
    · linarith
    · rcases lt_or_ge 0 (R ^ 2 - y ^ 2) with hc | hc
      · calc Real.sqrt (R ^ 2 - y ^ 2) ≤ Real.sqrt (R ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
          _ = R := Real.sqrt_sq (le_of_lt hR)
      · rw [Real.sqrt_eq_zero_of_nonpos hc]; linarith
  have hl_lt : ∀ y, l y < R + a := fun y => lt_of_le_of_lt (hl_le_R y) (by linarith)
  -- the region, described by its horizontal slices
  have hchar : ∀ w : ℂ, (|w.re - R| < a ∧ |w.im| < b ∧ R < ‖w‖) ↔
      (|w.im| < b ∧ l w.im < w.re ∧ w.re < R + a) := by
    intro w
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨h1l, h1r⟩ := abs_lt.mp h1
      have hwre : 0 < w.re := by linarith
      have hsq : R ^ 2 - w.im ^ 2 < w.re ^ 2 := by have := (hnorm w).mp h3; linarith
      refine ⟨h2, max_lt ?_ ?_, by linarith⟩
      · linarith
      · rcases lt_or_ge 0 (R ^ 2 - w.im ^ 2) with hc | hc
        · exact (Real.sqrt_lt (le_of_lt hc) (le_of_lt hwre)).mpr hsq
        · rw [Real.sqrt_eq_zero_of_nonpos hc]; exact hwre
    · rintro ⟨h2, hl, hu⟩
      have hRl : R - a < w.re := lt_of_le_of_lt (le_max_left _ _) hl
      have hwre : 0 < w.re := by linarith
      have hwre2 : 0 < w.re ^ 2 := by positivity
      have hsq : R ^ 2 - w.im ^ 2 < w.re ^ 2 := by
        rcases lt_or_ge 0 (R ^ 2 - w.im ^ 2) with hc | hc
        · exact (Real.sqrt_lt (le_of_lt hc) (le_of_lt hwre)).mp
            (lt_of_le_of_lt (le_max_right _ _) hl)
        · linarith
      refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, h2, (hnorm w).mpr (by linarith)⟩
  -- the two families of horizontal and vertical segments
  have hcont_g : ∀ y : ℝ, Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro y
    have heq : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [heq]; fun_prop
  have hcont_V : Continuous (fun t : ℝ => (⟨R + a / 2, t⟩ : ℂ)) := by
    have heq : (fun t : ℝ => (⟨R + a / 2, t⟩ : ℂ))
        = fun t : ℝ => ((R + a / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      funext t; apply Complex.ext <;> simp
    rw [heq]; fun_prop
  set H : ℝ → Set ℂ := fun y => (fun x : ℝ => (⟨x, y⟩ : ℂ)) '' Set.Ioo (l y) (R + a) with hH_def
  set V : Set ℂ := (fun t : ℝ => (⟨R + a / 2, t⟩ : ℂ)) '' Set.Ioo (-b) b with hV_def
  have hVpre : IsPreconnected V := isPreconnected_Ioo.image _ hcont_V.continuousOn
  have hHpre : ∀ y, IsPreconnected (H y) :=
    fun y => isPreconnected_Ioo.image _ (hcont_g y).continuousOn
  -- each horizontal slice together with the vertical segment is preconnected
  have hGpre : ∀ y : Set.Ioo (-b) b, IsPreconnected (H y.1 ∪ V) := by
    intro y
    refine IsPreconnected.union' (s := H y.1) (t := V)
      ⟨(⟨R + a / 2, y.1⟩ : ℂ), ?_, ?_⟩ (hHpre y.1) hVpre
    · exact ⟨R + a / 2, ⟨lt_of_le_of_lt (hl_le_R y.1) (by linarith), by linarith⟩, rfl⟩
    · exact ⟨y.1, y.2, rfl⟩
  -- they all contain the point `(R + a/2, 0)`
  have hne : (⋂ y : Set.Ioo (-b) b, (H y.1 ∪ V)).Nonempty := by
    refine ⟨(⟨R + a / 2, 0⟩ : ℂ), ?_⟩
    rw [Set.mem_iInter]
    intro y
    exact Or.inr ⟨0, ⟨by linarith, hb⟩, rfl⟩
  have hpre : IsPreconnected (⋃ y : Set.Ioo (-b) b, (H y.1 ∪ V)) :=
    isPreconnected_iUnion hne hGpre
  -- that union is exactly the region
  have hU : (⋃ y : Set.Ioo (-b) b, (H y.1 ∪ V))
      = {w : ℂ | |w.re - R| < a ∧ |w.im| < b ∧ R < ‖w‖} := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hyH | hyV⟩
      · obtain ⟨x, hx, hxw⟩ := hyH
        rw [← hxw]
        exact (hchar ⟨x, y.1⟩).mpr ⟨abs_lt.mpr y.2, hx.1, hx.2⟩
      · obtain ⟨t, ht, htw⟩ := hyV
        rw [← htw]
        exact (hchar ⟨R + a / 2, t⟩).mpr
          ⟨abs_lt.mpr ht, lt_of_le_of_lt (hl_le_R t) (by linarith), by linarith⟩
    · intro hw
      obtain ⟨him, hl, hu⟩ := (hchar w).mp hw
      refine ⟨⟨w.im, abs_lt.mp him⟩, Or.inl ?_⟩
      exact ⟨w.re, ⟨hl, hu⟩, by apply Complex.ext <;> rfl⟩
  exact hU ▸ hpre

end Work.Top
