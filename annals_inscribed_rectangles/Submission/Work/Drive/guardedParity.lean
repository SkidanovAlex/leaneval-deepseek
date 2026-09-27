import Mathlib
import Submission.Work.Drive.germLevelBridge
import Submission.Work.Drive.hn2CountInterface
import Submission.Work.Drive.refTripleOneT

/-!
# The guarded (`‖·‖ < ε`) variants of the cross-level parity chain

*(H4 lane, node `Work.Drive.orderSplit_model`.  Written for the lead's message of 2026-09-27, item 4
tail: "`hparA`/`hparN` (`∀ s`, unguarded) may be false for large `s`; guard them with `‖s‖ < ε`" —
the same remark as `NOTES_LEAD_hdense.md` §4 step 5 on `sideGerm_eq_of_level_lt`.)*

The cross-level parity statements of the germ lane relate the parity of the perturbed count at two
truncation levels `c`, `c'` at a configuration good at **both**.  As written
(`Work.Drive.sideGerm_eq_of_level_lt` and `Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt` in
`germLevelBridge.lean`, `Work.Drive.sideGerm_add_neg_eq_one_of_counts_at_levels` in
`hn2CountInterface.lean`, `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine` in
`refTripleEndpoint.lean`, `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleOneT` in
`refTripleOneT.lean`) their cross-level hypothesis

> `hpar : ∀ t, GoodAt Ξ Q c w t → GoodAt Ξ Q c' w t → Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c' w t)`

is **unguarded**, i.e. it is asked at *every* good configuration, including ones far from the origin,
where the honest input (`Work.Drive.odd_coreSideCount_eq_of_levelBand`) is only available on a
*neighbourhood* of `0`.  Every *proof* in the chain uses `hpar` only at a point `t₀` for which the ball
membership `‖t₀‖ < ε` is already in hand (`hJ.exists` supplies `hlt₀`).  This module therefore records
the guarded variants — same statements, same proofs, with `‖t‖ < ε →` inserted into `hpar`, `hparA` and
`hparN` — so that the design can use the box-restricted hypothesis it can actually produce.

The four declarations are the exact guarded counterparts, in the same order of the chain:

* `Work.Drive.sideGerm_eq_of_level_lt_guarded`;
* `Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt_guarded`;
* `Work.Drive.sideGerm_add_neg_eq_one_of_counts_at_levels_guarded`;
* `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine_guarded`;
* `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleOneT_guarded`.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.unusedVariables false

/-! ## 1. The germ value is level independent, with the guard -/

/-- **`Work.Drive.sideGerm_eq_of_level_lt` with the cross-level hypothesis guarded by `‖t‖ < ε`.**
The proof is the same dense-bridge argument; the only change is that `hpar` is applied at the point
`t₀` of `hJ` (whose ball membership is available). -/
theorem sideGerm_eq_of_level_lt_guarded {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (w : UnitAddCircle) {ε : ℝ} (hε : 0 < ε)
    (hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    (hU : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    (hE' : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c' w t)
    (hU' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c' w t → GoodAt Ξ Q c' w t' →
        Odd (CntAt Ξ Q c' w t) = Odd (CntAt Ξ Q c' w t'))
    (hpar : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
      GoodAt Ξ Q c w t → GoodAt Ξ Q c' w t →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c' w t)) :
    sideGerm Ξ Q c w = sideGerm Ξ Q c' w := by
  -- the joint density of good configurations at the two levels
  have hJ : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      ‖t‖ < ε ∧ GoodAt Ξ Q c w t ∧ GoodAt Ξ Q c' w t := by
    refine ((sideGerm_good_exists_two_levels Ξ Q c c' hΞ hQ hc hc' w).and_eventually
      (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin m)) hε)).mono ?_
    rintro t ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by simpa [Metric.mem_ball, dist_zero_right] using h3, h1, h2⟩
  have hiff := sideGerm_eq_one_iff_frequently_good_odd Ξ Q c w hE ⟨ε, hε, hU⟩
  have hiff' := sideGerm_eq_one_iff_frequently_good_odd Ξ Q c' w hE' ⟨ε, hε, hU'⟩
  have hkey : (∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Odd (CntAt Ξ Q c w t)) ↔
      (∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c' w t ∧ Odd (CntAt Ξ Q c' w t)) := by
    constructor
    · intro hf
      obtain ⟨t₀, hlt₀, hg₀, hg₀'⟩ := hJ.exists
      obtain ⟨t₁, ht₁⟩ :=
        (hf.and_eventually
          (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
            EuclideanSpace ℝ (Fin m)) hε)).exists
      obtain ⟨⟨hg₁, ho₁⟩, hmem₁⟩ := ht₁
      have hlt₁ : ‖t₁‖ < ε := by
        simpa [Metric.mem_ball, dist_zero_right] using hmem₁
      have ho₀ : Odd (CntAt Ξ Q c w t₀) := by
        rw [hU t₀ t₁ hlt₀ hlt₁ hg₀ hg₁]
        exact ho₁
      have ho₀' : Odd (CntAt Ξ Q c' w t₀) := by
        rw [← hpar t₀ hlt₀ hg₀ hg₀']
        exact ho₀
      refine hJ.mono fun t ht => ⟨ht.2.2, ?_⟩
      rw [hU' t t₀ ht.1 hlt₀ ht.2.2 hg₀']
      exact ho₀'
    · intro hf
      obtain ⟨t₀, hlt₀, hg₀, hg₀'⟩ := hJ.exists
      obtain ⟨t₁, ht₁⟩ :=
        (hf.and_eventually
          (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
            EuclideanSpace ℝ (Fin m)) hε)).exists
      obtain ⟨⟨hg₁, ho₁⟩, hmem₁⟩ := ht₁
      have hlt₁ : ‖t₁‖ < ε := by
        simpa [Metric.mem_ball, dist_zero_right] using hmem₁
      have ho₀ : Odd (CntAt Ξ Q c' w t₀) := by
        rw [hU' t₀ t₁ hlt₀ hlt₁ hg₀' hg₁]
        exact ho₁
      have ho₀'' : Odd (CntAt Ξ Q c w t₀) := by
        rw [hpar t₀ hlt₀ hg₀ hg₀']
        exact ho₀
      refine hJ.mono fun t ht => ⟨ht.2.1, ?_⟩
      rw [hU t t₀ ht.1 hlt₀ ht.2.1 hg₀]
      exact ho₀''
  have h1 : sideGerm Ξ Q c w = 1 ↔ sideGerm Ξ Q c' w = 1 :=
    hiff.trans (hkey.trans hiff'.symm)
  by_cases h : sideGerm Ξ Q c w = 1
  · have h' : sideGerm Ξ Q c' w = 1 := h1.mp h
    rw [h, h']
  · have h' : sideGerm Ξ Q c' w ≠ 1 := fun hh => h (h1.mpr hh)
    rw [zmod2_eq_zero_of_ne_one h, zmod2_eq_zero_of_ne_one h']

/-- **`Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt` with the guard**: at a good configuration inside
the ball, the count at the truncation level `c'` is the germ value at the design's level `c`. -/
theorem CntAt_cast_eq_sideGerm_of_level_lt_guarded {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    {c c' : ℝ} (w : UnitAddCircle) {ε : ℝ} (hε : 0 < ε) (hc : 0 < c) (hc' : 0 < c')
    (hU : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    (hU' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c' w t → GoodAt Ξ Q c' w t' →
        Odd (CntAt Ξ Q c' w t) = Odd (CntAt Ξ Q c' w t'))
    (hpar : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
      GoodAt Ξ Q c w t → GoodAt Ξ Q c' w t →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c' w t))
    {t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ < ε) (hg : GoodAt Ξ Q c' w t) :
    ((CntAt Ξ Q c' w t : ℕ) : ZMod 2) = sideGerm Ξ Q c w := by
  have hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t := sideGerm_good_exists Ξ Q c hΞ hQ hc w
  have hE' : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c' w t := sideGerm_good_exists Ξ Q c' hΞ hQ hc' w
  rw [CntAt_cast_eq_sideGerm Ξ Q c' hE' hε hU' ht hg,
    ← sideGerm_eq_of_level_lt_guarded Ξ Q hΞ hQ hc hc' w hε hE hU hE' hU' hpar]

/-! ## 2. The two-term identity with the guards -/

/-- **`Work.Drive.sideGerm_add_neg_eq_one_of_counts_at_levels` with `hparA`/`hparN` guarded.** -/
theorem sideGerm_add_neg_eq_one_of_counts_at_levels_guarded {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (c c₀ c₁ : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (a : UnitAddCircle) {ε : ℝ} (hε : 0 < ε)
    (hUa : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c a t → GoodAt Ξ Q c a t' →
        Odd (CntAt Ξ Q c a t) = Odd (CntAt Ξ Q c a t'))
    (hUa' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c₀ a t → GoodAt Ξ Q c₀ a t' →
        Odd (CntAt Ξ Q c₀ a t) = Odd (CntAt Ξ Q c₀ a t'))
    (hparA : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
      GoodAt Ξ Q c a t → GoodAt Ξ Q c₀ a t → Odd (CntAt Ξ Q c a t) = Odd (CntAt Ξ Q c₀ a t))
    (hUn : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c (-a) t → GoodAt Ξ Q c (-a) t' →
        Odd (CntAt Ξ Q c (-a) t) = Odd (CntAt Ξ Q c (-a) t'))
    (hUn' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c₁ (-a) t → GoodAt Ξ Q c₁ (-a) t' →
        Odd (CntAt Ξ Q c₁ (-a) t) = Odd (CntAt Ξ Q c₁ (-a) t'))
    (hparN : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
      GoodAt Ξ Q c (-a) t → GoodAt Ξ Q c₁ (-a) t →
        Odd (CntAt Ξ Q c (-a) t) = Odd (CntAt Ξ Q c₁ (-a) t))
    {t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ < ε) (ht' : ‖t'‖ < ε) (hg : GoodAt Ξ Q c₀ a t) (hg' : GoodAt Ξ Q c₁ (-a) t')
    (hkey : ((CntAt Ξ Q c₀ a t : ℕ) : ZMod 2) + ((CntAt Ξ Q c₁ (-a) t' : ℕ) : ZMod 2) = 1) :
    sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1 := by
  rw [← CntAt_cast_eq_sideGerm_of_level_lt_guarded Ξ Q hΞ hQ (c := c) (c' := c₀) a hε hc hc₀
      hUa hUa' hparA ht hg,
    ← CntAt_cast_eq_sideGerm_of_level_lt_guarded Ξ Q hΞ hQ (c := c) (c' := c₁) (-a) hε hc hc₁
      hUn hUn' hparN ht' hg']
  exact hkey

/-! ## 3. The reference-triple engine and endpoint, guarded -/

/-- **`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine` with `hparA`/`hparN` guarded.** -/
theorem sideGerm_add_neg_eq_one_of_refTripleEngine_guarded
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (hΞ : ChartPert Q 4 Ξ) (hQ : IsSmoothChart Q) (c : ℝ) (hc : 0 < c)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (a : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin 12)) (cblk : Fin 3 → ℝ) (g : Fin 3 → Fin 3 → ℕ)
    (hg01 : g 0 1 = CntAt Ξ Q (cblk 1) a (blk 0 t, blk 1 t))
    (hg10 : g 1 0 = CntAt Ξ Q (cblk 0) (-a) (blk 1 t, blk 0 t))
    (hcpos : ∀ k : Fin 3, 0 < cblk k)
    (hc1 : cblk 1 < cblk 0) (hc2 : cblk 2 < cblk 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < levelOf ((fun z => Ξ (blk k t) (P k z)) y))
    (hmeet : Meet3Hyp CappingSpace (sweepChartFam P Ξ cblk t))
    (hodd : Odd (classTripleSet (fun k => fun z => Ξ (blk k t) (P k z))).ncard)
    (hblock : ∀ k : Fin 3,
      Odd ((topBdryMeet CappingSpace (sweepChartFam P Ξ cblk t) k).ncard) ↔
        (Odd (g k (k + 1)) ∧ Odd (g k (k + 2))))
    (h20 : Even (g 2 0)) (h21 : Even (g 2 1)) (h02 : Odd (g 0 2)) (h12 : Odd (g 1 2))
    {ε : ℝ} (hε : 0 < ε)
    (hUa : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c a s → GoodAt Ξ Q c a s' →
        Odd (CntAt Ξ Q c a s) = Odd (CntAt Ξ Q c a s'))
    (hUa' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 1) a s → GoodAt Ξ Q (cblk 1) a s' →
        Odd (CntAt Ξ Q (cblk 1) a s) = Odd (CntAt Ξ Q (cblk 1) a s'))
    (hparA : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖s‖ < ε →
      GoodAt Ξ Q c a s → GoodAt Ξ Q (cblk 1) a s →
        Odd (CntAt Ξ Q c a s) = Odd (CntAt Ξ Q (cblk 1) a s))
    (hUn : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c (-a) s → GoodAt Ξ Q c (-a) s' →
        Odd (CntAt Ξ Q c (-a) s) = Odd (CntAt Ξ Q c (-a) s'))
    (hUn' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 0) (-a) s → GoodAt Ξ Q (cblk 0) (-a) s' →
        Odd (CntAt Ξ Q (cblk 0) (-a) s) = Odd (CntAt Ξ Q (cblk 0) (-a) s'))
    (hparN : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖s‖ < ε →
      GoodAt Ξ Q c (-a) s → GoodAt Ξ Q (cblk 0) (-a) s →
        Odd (CntAt Ξ Q c (-a) s) = Odd (CntAt Ξ Q (cblk 0) (-a) s))
    (ht : ‖(blk 0 t, blk 1 t)‖ < ε) (ht' : ‖(blk 1 t, blk 0 t)‖ < ε)
    (hgood01 : GoodAt Ξ Q (cblk 1) a (blk 0 t, blk 1 t))
    (hgood10 : GoodAt Ξ Q (cblk 0) (-a) (blk 1 t, blk 0 t)) :
    sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1 := by
  have htop := odd_sum_topBdryMeet_sweepChartFam P Ξ cblk t hcpos hc1 hc2 hlev hmeet hodd
  have hkey := cntAt_pair_eq_one_of_threeBlockT6 Ξ Q ![0, a, 0] (fun k => blk k t) cblk
    (fun k => (topBdryMeet CappingSpace (sweepChartFam P Ξ cblk t) k).ncard) g
    (by simpa using hg01) (by simpa using hg10) htop hblock h20 h21 h02 h12
  have hkey' : ((CntAt Ξ Q (cblk 1) a (blk 0 t, blk 1 t) : ℕ) : ZMod 2)
      + ((CntAt Ξ Q (cblk 0) (-a) (blk 1 t, blk 0 t) : ℕ) : ZMod 2) = 1 := by
    simpa using hkey
  exact sideGerm_add_neg_eq_one_of_counts_at_levels_guarded Ξ Q hΞ hQ c (cblk 1) (cblk 0)
    hc (hcpos 1) (hcpos 0) a hε hUa hUa' hparA hUn hUn' hparN
    ht ht' hgood01 hgood10 hkey'

/-- **`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleOneT` with `hparA`/`hparN` guarded**: the `hn2`
endpoint at one angle, from the reference-triple data at one small parameter. -/
theorem sideGerm_add_neg_eq_one_of_refTripleOneT_guarded
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    {Q : ℂ → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (hQ : IsChartData Q) (c : ℝ) (hc : 0 < c)
    (R : EuclideanSpace ℝ (Fin 2) → CappingSpace) (u v : UnitAddCircle) (cblk : Fin 3 → ℝ)
    (hcpos : ∀ k : Fin 3, 0 < cblk k) (hc1 : cblk 1 < cblk 0) (hc2 : cblk 2 < cblk 0)
    {ε : ℝ} (hε : 0 < ε)
    (hUa : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c (v - u) s → GoodAt Ξ Q c (v - u) s' →
        Odd (CntAt Ξ Q c (v - u) s) = Odd (CntAt Ξ Q c (v - u) s'))
    (hUa' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 1) (v - u) s → GoodAt Ξ Q (cblk 1) (v - u) s' →
        Odd (CntAt Ξ Q (cblk 1) (v - u) s) = Odd (CntAt Ξ Q (cblk 1) (v - u) s'))
    (hparA : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖s‖ < ε →
      GoodAt Ξ Q c (v - u) s → GoodAt Ξ Q (cblk 1) (v - u) s →
        Odd (CntAt Ξ Q c (v - u) s) = Odd (CntAt Ξ Q (cblk 1) (v - u) s))
    (hUn : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c (-(v - u)) s → GoodAt Ξ Q c (-(v - u)) s' →
        Odd (CntAt Ξ Q c (-(v - u)) s) = Odd (CntAt Ξ Q c (-(v - u)) s'))
    (hUn' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 0) (-(v - u)) s →
        GoodAt Ξ Q (cblk 0) (-(v - u)) s' →
        Odd (CntAt Ξ Q (cblk 0) (-(v - u)) s) = Odd (CntAt Ξ Q (cblk 0) (-(v - u)) s'))
    (hparN : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖s‖ < ε →
      GoodAt Ξ Q c (-(v - u)) s → GoodAt Ξ Q (cblk 0) (-(v - u)) s →
        Odd (CntAt Ξ Q c (-(v - u)) s) = Odd (CntAt Ξ Q (cblk 0) (-(v - u)) s))
    (hgen : ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ RefTripleAt (Ξ := Ξ) Q R u v cblk t) :
    sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1 := by
  classical
  obtain ⟨t, ht, hlev, hmeet, hodd, hgood01, hgood10, g, hg01, hg10, hblock, h20, h21, h02, h12⟩ := hgen
  have ht1 : ‖(blk 0 t, blk 1 t)‖ < ε := lt_of_le_of_lt (norm_pair_blk_le 0 1 t) ht
  have ht2 : ‖(blk 1 t, blk 0 t)‖ < ε := lt_of_le_of_lt (norm_pair_blk_le 1 0 t) ht
  have hgood10' : GoodAt Ξ Q (cblk 0) (-(v - u)) (blk 1 t, blk 0 t) := by
    rw [neg_sub]
    exact hgood10
  have hmain := sideGerm_add_neg_eq_one_of_refTripleEngine_guarded Ξ Q hΞ hQ.isSmoothChart c hc
    (refTriple Q R u v) (v - u) t cblk g hg01 (by rw [neg_sub]; exact hg10) hcpos hc1 hc2
    hlev hmeet hodd hblock h20 h21 h02 h12
    hε hUa hUa' hparA hUn hUn' hparN ht1 ht2 hgood01 hgood10'
  rwa [neg_sub] at hmain

end

end Work.Drive
