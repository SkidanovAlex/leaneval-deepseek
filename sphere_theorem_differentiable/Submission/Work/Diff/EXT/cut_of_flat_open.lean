import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cutting a function that is flat to order `m` at the seam of a slab

Let `δ : ℝ × E → Z` be `C^m` on the half-open slab `W = (Ico 0 T) ×ˢ U` (with `U` open in `E`,
`T > 0`) and suppose that all its within-`W` iterated derivatives of order `≤ m` vanish at the
seam points `(0, y)`, `y ∈ U`.  Then the Heaviside cut
`p ↦ if 0 < p.1 then δ p else 0` is `C^m` on the two-sided set `(Ioo (-T) T) ×ˢ U`.

The hypothesis that `U` is *open* is essential: it makes the slab `W` uniquely differentiable at
the seam, so that Mathlib's (junk-valued) `iteratedFDerivWithin` at `(0,y)` is the honest
within-derivative and the statement is the usual flat-extension lemma.  (Without `IsOpen U` the
statement is false, see `Work.Diff.EXT.cut_of_flat`.)

The proof glues two one-sided Taylor series at the seam:

* the tree of within-derivatives of `δ` on the large slab `W` (Mathlib's
  `ContDiffOn.ftaylorSeriesWithin`) restricted to a small closed piece `sR = [0, T/2] × V` of the
  seam neighbourhood, and
* the zero series on the closed piece `sL = (-∞, 0] × V` (`V` a small closed ball around `y`),

where the agreement of the two series on `sL ∩ sR = {0} × V` is exactly the flatness hypothesis.
-/

open Set Filter
open scoped Topology ContDiff

namespace Work.Diff.EXT

/-- **Gluing two one-sided Taylor series across a closed interface.**  Let `w : E → F` and let
`sL, sR` be two *closed* subsets whose union is a neighbourhood of `x₀`, each carrying a Taylor
series for `w` up to order `n` (`HasFTaylorSeriesUpToOn n w pL sL`,
`HasFTaylorSeriesUpToOn n w pR sR`).  If the two series agree on the overlap `sL ∩ sR`, then `w`
is `C^n` at `x₀`.

This is `Work.Diff.EXT.contDiffAt_of_hasFTaylorSeries_glue` with the (unnecessary) completeness
assumption on the target space dropped. -/
private theorem glue_of_hasFTaylorSeriesUpToOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : E → F} {x₀ : E} {n : ℕ}
    {sL sR : Set E} {pL pR : E → FormalMultilinearSeries ℝ E F}
    (hL : HasFTaylorSeriesUpToOn (n : WithTop ℕ∞) w pL sL)
    (hR : HasFTaylorSeriesUpToOn (n : WithTop ℕ∞) w pR sR)
    (hcL : IsClosed sL) (hcR : IsClosed sR) (hu : sL ∪ sR ∈ nhds x₀)
    (hagree : ∀ z ∈ sL ∩ sR, pL z = pR z) :
    ContDiffAt ℝ (n : WithTop ℕ∞) w x₀ := by
  classical
  -- The glued series: `pL` where available, `pR` otherwise.
  let p : E → FormalMultilinearSeries ℝ E F := fun z => if z ∈ sL then pL z else pR z
  have hpL : ∀ z ∈ sL, p z = pL z := by
    intro z hz; show (if z ∈ sL then pL z else pR z) = pL z; exact ite_eq_left hz
  have hpR : ∀ z ∈ sR, p z = pR z := by
    intro z hz
    by_cases hzL : z ∈ sL
    · rw [hpL z hzL, hagree z ⟨hzL, hz⟩]
    · show (if z ∈ sL then pL z else pR z) = pR z; exact ite_eq_right hzL
  -- One-sided derivative statements for the glued series.
  have keyL : ∀ m : ℕ, m < (n : WithTop ℕ∞) → ∀ x ∈ sL,
      HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sL x := by
    intro m hm x hxL
    have heq : Set.EqOn (fun y => p y m) (fun y => pL y m) sL :=
      fun y hy => by simp only [hpL y hy]
    simpa [hpL x hxL] using (hL.fderivWithin m hm x hxL).congr' heq hxL
  have keyR : ∀ m : ℕ, m < (n : WithTop ℕ∞) → ∀ x ∈ sR,
      HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sR x := by
    intro m hm x hxR
    have heq : Set.EqOn (fun y => p y m) (fun y => pR y m) sR :=
      fun y hy => by simp only [hpR y hy]
    simpa [hpR x hxR] using (hR.fderivWithin m hm x hxR).congr' heq hxR
  -- The glued series is a Taylor series on the union.
  have hglue : HasFTaylorSeriesUpToOn (n : WithTop ℕ∞) w p (sL ∪ sR) :=
    { zero_eq := by
        intro x hx
        rcases hx with hxL | hxR
        · rw [hpL x hxL]; exact hL.zero_eq x hxL
        · rw [hpR x hxR]; exact hR.zero_eq x hxR
      fderivWithin := by
        intro m hm x hx
        have h1 : HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sL x := by
          by_cases hxL : x ∈ sL
          · exact keyL m hm x hxL
          · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hcL.closure_eq])
        have h2 : HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sR x := by
          by_cases hxR : x ∈ sR
          · exact keyR m hm x hxR
          · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hcR.closure_eq])
        exact h1.union h2
      cont := by
        intro m hm
        exact ContinuousOn.union_of_isClosed
          ((hL.cont m hm).congr fun y hy => by rw [hpL y hy])
          ((hR.cont m hm).congr fun y hy => by rw [hpR y hy]) hcL hcR }
  exact hglue.contDiffOn.contDiffAt hu

/-- A function on `ℝ × E` that vanishes identically on `s` has the zero formal series as Taylor
series up to any order `n` on `s`. -/
private theorem hasFTaylorSeriesUpToOn_zero_series
    {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (n : ℕ) {w : ℝ × E → Z} {s : Set (ℝ × E)} (hw : ∀ x ∈ s, w x = 0) :
    HasFTaylorSeriesUpToOn (n : WithTop ℕ∞) w
      (0 : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) Z) s := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hw x hx]
    simp
  · intro k hk x hx
    have hfun : (fun y : ℝ × E => (0 : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) Z) y k)
        = (fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) Z)) := by
      funext y; simp
    have hmap : ((0 : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) Z) x k.succ).curryLeft
        = (0 : (ℝ × E) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) Z) := by
      apply ContinuousLinearMap.ext
      intro v
      ext m
      simp
    rw [hfun, hmap]
    exact hasFDerivWithinAt_const _ x s
  · intro k hk
    simpa using (continuousOn_const (s := s)
      (c := (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) Z)))

theorem cut_of_flat_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U) (δ : ℝ × E → Z) (m : ℕ)
    (hδ : ContDiffOn ℝ m δ ((Set.Ico 0 T) ×ˢ U))
    (hflat : ∀ y ∈ U, ∀ j ≤ m,
      iteratedFDerivWithin ℝ j δ ((Set.Ico 0 T) ×ˢ U) (0, y) = 0) :
    ContDiffOn ℝ m (fun p : ℝ × E => if 0 < p.1 then δ p else 0)
      (Set.Ioo (-T) T ×ˢ U) := by
  -- The zero-th flatness condition says that `δ` vanishes on the seam `{0} × U`.
  have hδ0 : ∀ y ∈ U, δ (0, y) = 0 := by
    intro y hy
    have h0 := hflat y hy 0 (Nat.zero_le m)
    have h1 := iteratedFDerivWithin_zero_apply (𝕜 := ℝ) (f := δ)
      (s := (Set.Ico 0 T) ×ˢ U) (x := (0, y)) (fun i : Fin 0 => i.elim0)
    rw [h0] at h1
    simpa using h1.symm
  -- The cut agrees with `δ` on the slab `(Ico 0 T) ×ˢ U`.
  have hfeqW : ∀ p ∈ (Set.Ico 0 T) ×ˢ U,
      (fun p : ℝ × E => if 0 < p.1 then δ p else 0) p = δ p := by
    rintro p hp
    obtain ⟨hp1, hpT⟩ := hp.1
    rcases lt_or_eq_of_le hp1 with hlt | heq
    · show (if 0 < p.1 then δ p else 0) = δ p
      rw [ite_eq_left hlt]
    · have hpp : p = (0, p.2) := Prod.ext heq.symm rfl
      have hnp : ¬ (0 < p.1) := by rw [← heq]; exact lt_irrefl 0
      show (if 0 < p.1 then δ p else 0) = δ p
      rw [ite_eq_right hnp, hpp, hδ0 p.2 hp.2]
  have hcontW : ContDiffOn ℝ m (fun p : ℝ × E => if 0 < p.1 then δ p else 0)
      ((Set.Ico 0 T) ×ˢ U) := hδ.congr hfeqW
  -- Smoothness is local; at every point of the two-sided set.
  intro x hx
  rcases lt_trichotomy x.1 0 with hlt | heq | hgt
  · -- `x.1 < 0`: near `x` the cut is the zero function.
    have hnb : {p : ℝ × E | p.1 < 0} ∈ 𝓝 x :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
    have hev : (fun p : ℝ × E => if 0 < p.1 then δ p else 0) =ᶠ[𝓝 x]
        (fun _ => (0 : Z)) := by
      filter_upwards [hnb] with p hp
      exact ite_eq_right (not_lt.mpr (le_of_lt hp))
    exact ((contDiffAt_const (c := (0 : Z))).congr_of_eventuallyEq hev).contDiffWithinAt
  · -- `x.1 = 0`: glue the two one-sided Taylor series at the seam.
    have hy : x.2 ∈ U := hx.2
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x.2 hy
    have hr2 : (0 : ℝ) < r / 2 := by linarith
    have hr2r : r / 2 < r := by linarith
    set V : Set E := Metric.closedBall x.2 (r / 2) with hVdef
    have hVU : V ⊆ U := by
      rw [hVdef]
      exact fun z hz => hrU (Metric.closedBall_subset_ball hr2r hz)
    set sL : Set (ℝ × E) := Set.Iic 0 ×ˢ V with hsLdef
    set sR : Set (ℝ × E) := Set.Icc 0 (T / 2) ×ˢ V with hsRdef
    have hT2 : (0 : ℝ) < T / 2 := by linarith
    have hsLclosed : IsClosed sL := isClosed_Iic.prod Metric.isClosed_closedBall
    have hsRclosed : IsClosed sR := isClosed_Icc.prod Metric.isClosed_closedBall
    -- the union of the two pieces is a neighbourhood of `(0, x.2)`
    have hunion : sL ∪ sR = Set.Iic (T / 2) ×ˢ V := by
      rw [hsLdef, hsRdef]
      ext p
      simp only [Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨le_trans h1 (le_of_lt hT2), h2⟩
        · exact ⟨h1.2, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases h0 : p.1 ≤ 0
        · exact Or.inl ⟨h0, h2⟩
        · exact Or.inr ⟨⟨by linarith, h1⟩, h2⟩
    have hnhds : sL ∪ sR ∈ 𝓝 (0, x.2) := by
      rw [hunion, hVdef]
      refine mem_of_superset
        ((isOpen_Iio.prod Metric.isOpen_ball).mem_nhds
          ⟨hT2, Metric.mem_ball_self hr2⟩) ?_
      rintro ⟨t, y⟩ ⟨ht, hy'⟩
      exact ⟨Set.mem_Iic.mpr (le_of_lt ht), Metric.ball_subset_closedBall hy'⟩
    -- the canonical Taylor series of `δ` on the slab
    have huniqW : UniqueDiffOn ℝ ((Set.Ico 0 T) ×ˢ U) :=
      (uniqueDiffOn_Ico 0 T).prod hU.uniqueDiffOn
    let pW : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) Z :=
      ftaylorSeriesWithin ℝ δ ((Set.Ico 0 T) ×ˢ U)
    have hW : HasFTaylorSeriesUpToOn (m : WithTop ℕ∞) δ pW ((Set.Ico 0 T) ×ˢ U) :=
      ContDiffOn.ftaylorSeriesWithin hδ huniqW
    have hsRsub : sR ⊆ (Set.Ico 0 T) ×ˢ U := by
      rw [hsRdef, hVdef]
      rintro ⟨t, y⟩ ⟨ht, hy'⟩
      exact ⟨⟨ht.1, by linarith [ht.2, hT]⟩,
        hrU (Metric.closedBall_subset_ball hr2r hy')⟩
    have hR0 : HasFTaylorSeriesUpToOn (m : WithTop ℕ∞) δ pW sR := hW.mono hsRsub
    -- truncate the series above order `m` so that it vanishes identically at the seam
    let pR : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) Z :=
      fun z k => if k ≤ m then pW z k else 0
    have hR1 : HasFTaylorSeriesUpToOn (m : WithTop ℕ∞) δ pR sR := by
      refine hR0.congr_series ?_
      intro k hk x hx
      have hk' : k ≤ m := by exact_mod_cast hk
      show pW x k = (if k ≤ m then pW x k else 0)
      rw [ite_eq_left hk']
    have hR : HasFTaylorSeriesUpToOn (m : WithTop ℕ∞)
        (fun p : ℝ × E => if 0 < p.1 then δ p else 0) pR sR :=
      hR1.congr (fun z hz => hfeqW z (hsRsub hz))
    have hwL : ∀ z ∈ sL, (fun p : ℝ × E => if 0 < p.1 then δ p else 0) z = 0 := by
      intro z hz
      rw [hsLdef] at hz
      obtain ⟨h1, h2⟩ := hz
      show (if 0 < z.1 then δ z else 0) = 0
      rw [ite_eq_right (not_lt.mpr (show z.1 ≤ 0 from h1))]
    have hL : HasFTaylorSeriesUpToOn (m : WithTop ℕ∞)
        (fun p : ℝ × E => if 0 < p.1 then δ p else 0)
        (0 : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) Z) sL :=
      hasFTaylorSeriesUpToOn_zero_series m hwL
    have hagree : ∀ z ∈ sL ∩ sR,
        (0 : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) Z) z = pR z := by
      intro z hz
      obtain ⟨hzL, hzR⟩ := hz
      rw [hsLdef] at hzL
      obtain ⟨hzL1, hzL2⟩ := hzL
      rw [hsRdef] at hzR
      obtain ⟨hzR1, hzR2⟩ := hzR
      have hz0 : z.1 = 0 := le_antisymm hzL1 hzR1.1
      have hzU : z.2 ∈ U := hVU hzR2
      funext k
      by_cases hk : k ≤ m
      · have hpz : pW z k = 0 := by
          change iteratedFDerivWithin ℝ k δ ((Set.Ico 0 T) ×ˢ U) z = 0
          rw [show z = (0, z.2) from Prod.ext hz0 rfl, hflat z.2 hzU k hk]
        rw [show pR z k = pW z k from ite_eq_left hk, hpz]
        simp
      · rw [show pR z k = 0 from ite_eq_right hk]
        simp
    have hgoal : ContDiffAt ℝ (m : WithTop ℕ∞)
        (fun p : ℝ × E => if 0 < p.1 then δ p else 0) x := by
      rw [show x = (0, x.2) from Prod.ext heq rfl]
      exact glue_of_hasFTaylorSeriesUpToOn hL hR hsLclosed hsRclosed hnhds hagree
    exact hgoal.contDiffWithinAt
  · -- `0 < x.1`: `x` lies in the interior of the slab.
    have hxW : (Set.Ico 0 T ×ˢ U) ∈ 𝓝 x :=
      mem_of_superset ((isOpen_Ioo.prod hU).mem_nhds ⟨⟨hgt, hx.1.2⟩, hx.2⟩)
        (fun q hq => ⟨⟨le_of_lt hq.1.1, hq.1.2⟩, hq.2⟩)
    exact (hcontW.contDiffAt hxW).contDiffWithinAt

end Work.Diff.EXT
