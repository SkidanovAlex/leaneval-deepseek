import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

/-!
# The closure of a ray piece in the dynamical plane

This module proves that the piece of the ray of angle `β` between the levels `0` and `R`
(`1 < R`) has closure `{y} ∪ R(β)`, where `y` is the landing point of the ray of angle `β`.

The ray piece is the image of the level interval `(1, R]` under the (continuous, on `(1,∞)`)
parametrization `t ↦ rayPt hN β t`; the only point of its closure which is not already on the
piece is the limit as `t ↘ 1`, which is `y` by the landing hypothesis.  Equivalently, the
piece together with its landing point is compact (it is the image of `[1,R]` under the map
which equals `rayPt hN β ·` above level `1` and takes the value `y` at level `1`).
-/

variable {c : ℂ} {φ : ℂ → ℂ}

/-- The piece of the ray of angle `β` between the levels `0` and `R` is the image of the
level interval `(1, R]`.  (The condition `0 ≤ potential` is automatic on a ray.) -/
theorem rayPiece_eq_image_of_lt (hN : Work.EL.DynB c φ) {β R : ℝ} (hR : 1 < R) :
    Work.EL.rayPiece hN β 0 R = (fun t : ℝ => Work.EL.rayPt hN β t) '' Set.Ioc 1 R := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzray, -, hzR⟩ := hz
    obtain ⟨hzK, t, ht, hΦ⟩ := hzray
    have hφz : φ z = Work.Top.NakaneData.rayPoint β t := by
      rw [Work.EL.dynPhi_of_notMem hzK] at hΦ
      exact hΦ
    have htpos : (0 : ℝ) < t := by linarith
    have hpot : Work.EL.pot hN z = Real.log t := by
      rw [Work.EL.pot_of_notMem hN hzK, Work.EL.dynPhi_of_notMem hzK, hφz,
        Work.Top.NakaneData.norm_rayPoint, abs_of_pos htpos]
    have htR : t ≤ R := by
      have h1 : Real.log t ≤ Real.log R := by rw [← hpot]; exact hzR
      exact (Real.log_le_log_iff htpos (by linarith)).mp h1
    refine ⟨t, ⟨ht, htR⟩, ?_⟩
    exact hN.injOn_Phi (hN.rayPt_notMem ht) hzK (by rw [hΦ, hN.Phi_rayPt ht])
  · rintro ⟨t, ⟨ht, htR⟩, rfl⟩
    refine ⟨Work.EL.rayPt_mem_paramRay hN ht, ?_, ?_⟩
    · show (0 : ℝ) ≤ Work.Top.potential (Work.EL.K c) (Work.EL.dynPhi c φ)
        (Work.EL.rayPt hN β t)
      rw [Work.Top.NakaneData.potential_rayPt hN ht]
      exact Real.log_nonneg (by linarith)
    · show Work.Top.potential (Work.EL.K c) (Work.EL.dynPhi c φ) (Work.EL.rayPt hN β t)
        ≤ Real.log R
      rw [Work.Top.NakaneData.potential_rayPt hN ht]
      exact Real.log_le_log (by linarith) htR

theorem closure_rayPiece {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {β R : ℝ} (hR : 1 < R) {y : ℂ}
    (h : Work.EL.LandsN hN β y) :
    closure (Work.EL.rayPiece hN β 0 R) = {y} ∪ Work.EL.rayPiece hN β 0 R := by
  let f : ℝ → ℂ := fun t => Work.EL.rayPt hN β t
  have hpiece : Work.EL.rayPiece hN β 0 R = f '' Set.Ioc (1 : ℝ) R := by
    simpa only [f] using rayPiece_eq_image_of_lt hN hR
  have hcont : ContinuousOn f (Set.Ioi 1) := Work.Top.continuousOn_rayPt hN β
  have hland : Tendsto f (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 y) := h
  -- the level interval `(1,R]` is a neighbourhood of `1` within `(1,∞)`, so the ray points
  -- at those levels converge to `y`
  have hIoc : Set.Ioc (1 : ℝ) R ∈ 𝓝[Set.Ioi (1 : ℝ)] 1 := by
    have h1 : Set.Ioo (1 : ℝ) R ∈ 𝓝[Set.Ioi (1 : ℝ)] 1 :=
      Filter.inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by linarith : (1 : ℝ) < R)))
    exact Filter.mem_of_superset h1 (fun t ht => ⟨ht.1, le_of_lt ht.2⟩)
  have hy : y ∈ closure (f '' Set.Ioc (1 : ℝ) R) :=
    mem_closure_of_tendsto hland
      ((show ∀ᶠ t in 𝓝[Set.Ioi (1 : ℝ)] 1, t ∈ Set.Ioc (1 : ℝ) R from hIoc).mono
        fun t ht => ⟨t, ht, rfl⟩)
  -- the piece together with `y` is the continuous image of the compact interval `[1,R]`
  have hgcont : ContinuousOn (fun t : ℝ => if t = 1 then y else f t) (Set.Icc (1 : ℝ) R) := by
    intro t ht
    obtain rfl | ht1 := eq_or_lt_of_le ht.1
    · have hsub : Set.Icc (1 : ℝ) R ⊆ ({1} ∪ Set.Ioi (1 : ℝ)) := by
        intro x hx
        obtain h | h := eq_or_lt_of_le hx.1
        · exact Or.inl h.symm
        · exact Or.inr h
      have hle := nhdsWithin_mono (1 : ℝ) hsub
      rw [nhdsWithin_union] at hle
      have ha : Tendsto (fun t : ℝ => if t = 1 then y else f t) (𝓝[{1}] (1 : ℝ)) (𝓝 y) := by
        rw [nhdsWithin_singleton]
        simpa using tendsto_pure_nhds (fun t : ℝ => if t = 1 then y else f t) (1 : ℝ)
      have hb : Tendsto (fun t : ℝ => if t = 1 then y else f t) (𝓝[Set.Ioi (1 : ℝ)] 1)
          (𝓝 y) := by
        refine hland.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [Set.mem_Ioi] at hs
        simp only [ite_eq_right (ne_of_gt hs)]
      have hsup := (Filter.Tendsto.sup ha hb).mono_left hle
      simpa [ContinuousWithinAt] using hsup
    · have hft : ContinuousAt f t := hcont.continuousAt (isOpen_Ioi.mem_nhds ht1)
      have hgt : ContinuousAt (fun t : ℝ => if t = 1 then y else f t) t := by
        refine hft.congr ?_
        filter_upwards [eventually_ne_nhds (a := t) (b := (1 : ℝ)) (ne_of_gt ht1)] with s hs
        simp only [ite_eq_right hs]
      exact hgt.continuousWithinAt
  have hgimg : (fun t : ℝ => if t = 1 then y else f t) '' Set.Icc (1 : ℝ) R
      = {y} ∪ f '' Set.Ioc (1 : ℝ) R := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases ht1 : t = 1
      · exact Or.inl (by simp [ht1])
      · exact Or.inr ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht1), ht.2⟩,
          by simp only [ite_eq_right ht1]⟩
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · exact ⟨1, ⟨le_refl 1, hR.le⟩, by simp⟩
      · exact ⟨t, ⟨ht.1.le, ht.2⟩, by simp only [ite_eq_right (ne_of_gt ht.1)]⟩
  have hclosed : IsClosed ({y} ∪ f '' Set.Ioc (1 : ℝ) R) := by
    rw [← hgimg]
    exact (isCompact_Icc.image_of_continuousOn hgcont).isClosed
  have hcl : closure (f '' Set.Ioc (1 : ℝ) R) = {y} ∪ f '' Set.Ioc (1 : ℝ) R := by
    refine Subset.antisymm (closure_minimal (fun z hz => Or.inr hz) hclosed) ?_
    rintro z (rfl | hz)
    · exact hy
    · exact subset_closure hz
  rw [hpiece, hcl]

end Work.ELTop
