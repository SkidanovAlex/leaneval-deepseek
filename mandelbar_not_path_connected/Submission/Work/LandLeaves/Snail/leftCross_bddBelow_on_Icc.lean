import Mathlib
import Submission.Work.LandLeaves.Snail.barrierDefs
import Submission.Work.LandLeaves.Snail.pathTail_isClosed
import Submission.Work.LandLeaves.Snail.leftCross_tendsto_atBot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `leftCross` is bounded below on a compact height band

`leftCross P t₀ h` is the (infimum of the) leftmost real part among points of the barrier
`pathTail P t₀ = P '' [t₀, ∞)` at height `h`.  This file shows that on any compact band
`h ∈ [a, b]` with `a ≥ (P t₀).im` it admits a uniform lower bound.

The mechanism: by `im_lower_bound_linear` the height along the tail grows at least linearly,
`(P u).im ≥ m + (u - t₀ - 1) * (c.im / 2)` for `u ≥ t₀`.  Hence every point of the barrier at a
height `h ≤ b` occurs at a time `u` inside the *fixed* compact interval
`[t₀, t₀ + 1 + (b - m) / (c.im / 2)]`, on which `(P u).re` is continuous and therefore bounded
below.  That uniform bound is the desired `M`.
-/

open Filter Set
open scoped Topology

namespace Work.LandLeaves.Snail

theorem leftCross_bddBelow_on_Icc {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀)
    {a b : ℝ} (hab : (P t₀).im ≤ a) :
    ∃ M : ℝ, ∀ h ∈ Set.Icc a b, M ≤ Work.LandLeaves.Snail.leftCross P t₀ h := by
  rcases lt_or_ge b a with hba | hab'
  · -- the height band is empty
    refine ⟨0, fun h hh => ?_⟩
    exact absurd hh.2 (not_le.mpr (lt_of_lt_of_le hba hh.1))
  · have hc2 : 0 < c.im / 2 := by linarith
    -- the linear lower bound on the height along the tail
    obtain ⟨m, hm1, hm2⟩ := im_lower_bound_linear (F := F) (P := P) (c := c) (T := T)
      (X₀ := X₀) (t₀ := t₀) hc_im hheight hPinv hPc htT hPt
    have hm_le : ∀ t : ℝ, t₀ ≤ t → m ≤ (P t).im := by
      intro t ht
      rcases lt_or_ge t (t₀ + 1) with hcase | hcase
      · exact hm1 t ⟨ht, le_of_lt hcase⟩
      · have hpos : 0 ≤ (t - t₀ - 1) * (c.im / 2) :=
          mul_nonneg (by linarith) (le_of_lt hc2)
        linarith [hm2 t ht]
    have hm_t0 : m ≤ (P t₀).im := hm_le t₀ le_rfl
    have hb : m ≤ b := le_trans (le_trans hm_t0 hab) hab'
    -- the fixed compact interval of times that can realise a height `≤ b`
    set U : ℝ := t₀ + 1 + (b - m) / (c.im / 2) with hU
    have hU_ge : t₀ ≤ U := by
      have : 0 ≤ (b - m) / (c.im / 2) := div_nonneg (by linarith) (le_of_lt hc2)
      rw [hU]; linarith
    have hcontR : ContinuousOn (fun u : ℝ => (P u).re) (Set.Icc t₀ U) := by
      have h1 : ContinuousOn P (Set.Icc t₀ U) :=
        hPc.mono (fun u hu => le_trans htT hu.1)
      simpa [Function.comp_def] using Complex.continuous_re.comp_continuousOn h1
    obtain ⟨x, _hxmem, hxmin⟩ :=
      (isCompact_Icc (a := t₀) (b := U)).exists_isMinOn
        ⟨t₀, le_rfl, hU_ge⟩ hcontR
    refine ⟨(P x).re, fun h hh => ?_⟩
    have hh_ge_t0 : (P t₀).im ≤ h := le_trans hab hh.1
    have hc2ne : (c.im / 2) ≠ 0 := ne_of_gt hc2
    -- a time at which the height exceeds `h`
    set U₀ : ℝ := t₀ + 1 + (h - m) / (c.im / 2) + 1 with hU₀
    have hU₀_ge : t₀ ≤ U₀ := by
      have : 0 ≤ (h - m) / (c.im / 2) := div_nonneg (by linarith) (le_of_lt hc2)
      rw [hU₀]; linarith
    have hu0gt : h < (P U₀).im := by
      have hlin := hm2 U₀ hU₀_ge
      have hslack : ((h - m) / (c.im / 2)) * (c.im / 2) = h - m :=
        div_mul_cancel₀ _ hc2ne
      have hdiff : U₀ - t₀ - 1 = (h - m) / (c.im / 2) + 1 := by rw [hU₀]; ring
      rw [hdiff, add_mul, one_mul, hslack] at hlin
      linarith
    -- the intermediate value theorem produces a barrier point at height `h`
    have hcontIm : ContinuousOn (fun u : ℝ => (P u).im) (Set.Icc t₀ U₀) := by
      have h1 : ContinuousOn P (Set.Icc t₀ U₀) :=
        hPc.mono (fun u hu => le_trans htT hu.1)
      simpa [Function.comp_def] using Complex.continuous_im.comp_continuousOn h1
    obtain ⟨u, hu_mem, hu_eq⟩ :=
      intermediate_value_Icc hU₀_ge hcontIm ⟨hh_ge_t0, le_of_lt hu0gt⟩
    -- every barrier point at height `h` occurs at a time `≤ U`
    have hbound : ∀ u' : ℝ, t₀ ≤ u' → (P u').im = h → (P x).re ≤ (P u').re := by
      intro u' hu' him'
      have hlin := hm2 u' hu'
      rw [him'] at hlin
      have h1 : (u' - t₀ - 1) * (c.im / 2) ≤ h - m := by linarith
      have h2 : u' - t₀ - 1 ≤ (h - m) / (c.im / 2) := (le_div_iff₀ hc2).mpr h1
      have h4 : (h - m) / (c.im / 2) ≤ (b - m) / (c.im / 2) :=
        div_le_div_of_nonneg_right (by linarith [hh.2]) (le_of_lt hc2)
      have huU : u' ≤ U := by rw [hU]; linarith
      exact hxmin ⟨hu', huU⟩
    -- the set of real parts at height `h` is nonempty and bounded below by `(P x).re`
    have hmem : (P u).re ∈ (fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h}) :=
      ⟨P u, ⟨⟨u, hu_mem.1, rfl⟩, hu_eq⟩, rfl⟩
    have hSne : ((fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h})).Nonempty :=
      ⟨_, hmem⟩
    have hkey : (P x).re ≤
        sInf ((fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h})) :=
      le_csInf hSne (fun y hy => by
        obtain ⟨W, hW, hWy⟩ := hy
        obtain ⟨hWtail, hWim⟩ := hW
        simp only [Set.mem_ofPred_eq] at hWim
        rw [pathTail] at hWtail
        obtain ⟨u', hu', hu'eq⟩ := hWtail
        subst hu'eq
        rw [← hWy]
        exact hbound u' hu' hWim)
    simpa only [leftCross] using hkey

end Work.LandLeaves.Snail
