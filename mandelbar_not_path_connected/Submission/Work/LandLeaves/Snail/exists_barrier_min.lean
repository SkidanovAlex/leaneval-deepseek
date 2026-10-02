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
# The leftmost point of the barrier at a prescribed height is attained

For the snail path `P` (a forward orbit of the germ `F`: `F (P t) = P (t + 1)`), the barrier
`pathTail P t₀ = P '' Ici t₀` is the image of the tail of the path.  `leftCross P t₀ h` is the
infimum of the real parts of the barrier points of height `h`.

Here we show that this infimum is attained, i.e. that there is a point of the barrier at height
`h` (with `h` at least the height of `P t₀`) whose real part is *minimal* among all barrier
points of that height.

The mechanism is the linear growth of the height along the tail
(`im_lower_bound_linear`): if `(P u).im = h` with `u ≥ t₀`, then
`(u - t₀ - 1) * (c.im / 2) ≤ h - m`, so the parameters of the barrier at height `h` lie in a
fixed compact interval `[t₀, B]`.  On that interval `u ↦ (P u).re` and `u ↦ (P u).im` are
continuous, whence the set of parameters at height `h` is compact and the image of its real
parts is a compact (nonempty) subset of `ℝ`, whose minimum is attained.
-/

open Filter Set
open scoped Topology

namespace Work.LandLeaves.Snail

theorem exists_barrier_min {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀)
    {h : ℝ} (hh : (P t₀).im ≤ h) :
    ∃ W ∈ Work.LandLeaves.Snail.pathTail P t₀, W.im = h ∧
      W.re = Work.LandLeaves.Snail.leftCross P t₀ h ∧
      ∀ W' ∈ Work.LandLeaves.Snail.pathTail P t₀, W'.im = h → W.re ≤ W'.re := by
  have hc2 : 0 < c.im / 2 := by linarith
  -- the linear lower bound for the height along the tail
  obtain ⟨m, hm1, hm2⟩ := im_lower_bound_linear (F := F) (P := P) (c := c)
    (T := T) (X₀ := X₀) (t₀ := t₀) hc_im hheight hPinv hPc htT hPt
  have hm_le_h : m ≤ h := le_trans (hm1 t₀ ⟨le_rfl, by linarith⟩) hh
  -- a parameter bound for the tail points of height `h`
  set B : ℝ := t₀ + 1 + (h - m) / (c.im / 2) with hB
  -- the set of parameters of the tail at height `h`
  set S : Set ℝ := {u : ℝ | t₀ ≤ u ∧ (P u).im = h} with hS
  have hSsub : S ⊆ Set.Icc t₀ B := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have hlin := hm2 u hu.1
    rw [hu.2] at hlin
    have h1 : (u - t₀ - 1) * (c.im / 2) ≤ h - m := by linarith
    have h2 : u - t₀ - 1 ≤ (h - m) / (c.im / 2) := (le_div_iff₀ hc2).mpr h1
    simp only [hB]
    linarith
  have hcontIcc : ContinuousOn (fun u : ℝ => (P u).im) (Set.Icc t₀ B) :=
    Complex.continuous_im.comp_continuousOn (hPc.mono (fun u hu => le_trans htT hu.1))
  -- `S` is nonempty: the height crosses the level `h`
  have hSne : S.Nonempty := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, h < m + ((N : ℝ) - 1) * (c.im / 2) := by
      obtain ⟨N, hN⟩ := exists_nat_gt ((h - m) / (c.im / 2) + 1)
      refine ⟨N, ?_⟩
      have h3 : (h - m) / (c.im / 2) < (N : ℝ) - 1 := by linarith
      have h4 := mul_lt_mul_of_pos_right h3 hc2
      rw [div_mul_cancel₀ _ (ne_of_gt hc2)] at h4
      linarith
    have hb : h < (P (t₀ + (N : ℝ))).im := by
      have hlin := hm2 (t₀ + (N : ℝ)) (by linarith)
      have hsimp : t₀ + (N : ℝ) - t₀ - 1 = (N : ℝ) - 1 := by ring
      rw [hsimp] at hlin
      linarith
    have hab : t₀ ≤ t₀ + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
    have hcont : ContinuousOn (fun u : ℝ => (P u).im) (Set.Icc t₀ (t₀ + (N : ℝ))) :=
      Complex.continuous_im.comp_continuousOn (hPc.mono (fun u hu => le_trans htT hu.1))
    have hmem : h ∈ Set.Icc ((fun u : ℝ => (P u).im) t₀)
        ((fun u : ℝ => (P u).im) (t₀ + (N : ℝ))) := ⟨hh, le_of_lt hb⟩
    obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc hab hcont hmem
    exact ⟨u, hu.1, hueq⟩
  -- `S` is closed
  have hSclosed : IsClosed S := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    have hxI : x ∈ Set.Icc t₀ B := (isClosed_Icc.closure_subset_iff.mpr hSsub) hx
    rw [mem_closure_iff_seq_limit] at hx
    obtain ⟨u, hu_mem, hu_tend⟩ := hx
    have h1 : Tendsto (fun u : ℝ => (P u).im) (𝓝[Set.Icc t₀ B] x) (𝓝 ((P x).im)) :=
      hcontIcc.continuousWithinAt hxI
    have h2 : Tendsto u atTop (𝓝[Set.Icc t₀ B] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu_tend, Eventually.of_forall fun n => hSsub (hu_mem n)⟩
    have h3 : Tendsto (fun n => (P (u n)).im) atTop (𝓝 ((P x).im)) := h1.comp h2
    have h4 : (fun n => (P (u n)).im) = fun _ => h := funext fun n => (hu_mem n).2
    rw [h4] at h3
    have h5 : h = (P x).im := tendsto_nhds_unique tendsto_const_nhds h3
    exact ⟨hxI.1, h5.symm⟩
  -- hence `S` is compact and the real parts of its image attain their minimum
  have hScomp : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed hSsub
  have hcontf : ContinuousOn (fun u : ℝ => (P u).re) (Set.Icc t₀ B) :=
    Complex.continuous_re.comp_continuousOn (hPc.mono (fun u hu => le_trans htT hu.1))
  have hcontfS : ContinuousOn (fun u : ℝ => (P u).re) S := hcontf.mono hSsub
  have hAcomp : IsCompact ((fun u : ℝ => (P u).re) '' S) := hScomp.image_of_continuousOn hcontfS
  have hAne : ((fun u : ℝ => (P u).re) '' S).Nonempty := hSne.image _
  obtain ⟨a, haA, hamin⟩ := hAcomp.exists_isMinOn hAne continuousOn_id
  have hmin : ∀ y ∈ (fun u : ℝ => (P u).re) '' S, a ≤ y := fun y hy => hamin hy
  have haeq : sInf ((fun u : ℝ => (P u).re) '' S) = a := IsLeast.csInf_eq ⟨haA, hmin⟩
  obtain ⟨u₀, hu₀S, hu₀eq⟩ := haA
  have hu₀eq' : (P u₀).re = a := hu₀eq
  -- the two descriptions of the set of real parts agree
  have hAeq : (fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h})
      = (fun u : ℝ => (P u).re) '' S := by
    ext y
    constructor
    · rintro ⟨W, ⟨hWt, hWim⟩, rfl⟩
      rw [pathTail] at hWt
      obtain ⟨u, hu, rfl⟩ := hWt
      exact ⟨u, ⟨hu, hWim⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hueq⟩, rfl⟩
      exact ⟨P u, ⟨⟨u, hu, rfl⟩, hueq⟩, rfl⟩
  refine ⟨P u₀, ⟨u₀, hu₀S.1, rfl⟩, hu₀S.2, ?_, ?_⟩
  · rw [leftCross, hAeq, hu₀eq', ← haeq]
  · intro W' hW' hW'im
    have hmem : W'.re ∈ (fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h}) :=
      ⟨W', ⟨hW', hW'im⟩, rfl⟩
    rw [hAeq] at hmem
    have := hmin W'.re hmem
    rw [hu₀eq']
    exact this

end Work.LandLeaves.Snail
