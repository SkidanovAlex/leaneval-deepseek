import Mathlib
import Submission.Work.Drive.Mono.exists_smallSlab_tiltData
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.junctionGoodAux
import Submission.Work.Drive.Mono.LevelFrontierGen
import Submission.Work.Drive.Mono.exists_levelFrontierGen
import Submission.Work.Drive.Mono.tiltData_small_of_dir_near_junction

/-!
# The tilt data of the deliverable at an arbitrarily thin slab

The deliverable `Work.Drive.Mono.TiltedTraceDataWExists` needs, at every crux configuration, tilt
data whose slab is **thin**: the fat slab of `Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized`
(with half-width `h = ε*R + R + |u| + 1`) *strictly contains* the box, so its removed chunk never
cuts the box and its trace data are provably false
(`Work.Drive.Mono.not_tiltedTraceDataW_of_slab_contains_box`); the data which witness the trace
data are those with `h` small compared with the extent of the box in the direction `v`
(`Work.Drive.Mono.exists_smallSlab_tiltData` produces the whole *genericity* at an arbitrarily small
half-width, together with the size condition and the cutting condition `h + |u| < boxWidth s σ v`).

What is missing is only the *bookkeeping* which turns that genericity datum into the full
`Work.Drive.Mono.TiltData` of the deliverable: the window conditions (the range of `ℓ` on the box is
contained in `(lam0, lam1)`, and `exc` too).  This module supplies it, so that the `TiltData`
conjunct of every residual of the deliverable can be discharged by the thin-slab producer — in
particular **for every cutting level `u` and every box level `s`**, with no almost-everywhere
hypothesis and no general-position hypothesis on the box level (the thin-slab producer of
`Mono/Band` needs neither).

Main declarations:

* `Work.Drive.Mono.exists_window_of_genericity` — the window bookkeeping at an abstract genericity
  datum (this is the window part of `Work.Drive.Final.tiltedGenericity_data_exists` and of
  `Work.Drive.Mono.DataExists_holds`, extracted);
* `Work.Drive.Mono.exists_tiltData_smallSlab` — **the thin-slab `TiltData` producer**: for every
  `η > 0` there are `v, h < η, R, ℓ, lam0, lam1, exc` with
  `TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧ h + |u| < boxWidth s σ v`;
* `Work.Drive.Mono.exists_tiltData_smallSlab_cuts` — the same with the two derived conjuncts
  `‖v‖ = 1`, `0 < h`, `SlabCutsBox` (the slab really cuts the box) and the radius bound
  `∀ y ∈ PBox, ‖y - c‖ ≤ 5/2 * s` exposed, in the shape in which the geometric inputs of clause 1
  consume them (`Work.Drive.Mono.levelSphereDecomposition_of_levelFrontierGen`).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- **The window bookkeeping of the tilt data.**  From the genericity `TiltedGenericity` at a fixed
half-width, the size condition and a radius bound on the *closed* box, there are window ends
`lam0 < lam1` such that the range of `ℓ` on the closed box and every element of `exc` lie in
`(lam0, lam1)`, i.e. the full `Work.Drive.Mono.TiltData`, together with the window bounds on the
closed box which `Work.Drive.Mono.exists_levelFrontierGen` consumes.  (The proof is the window part
of `Work.Drive.Final.tiltedGenericity_data_exists`.) -/
theorem exists_window_of_genericity {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    (hs : 0 < s)
    (hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc)
    (hv1 : ‖v‖ = 1) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0)
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h)
    (hRbox : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ R) :
    ∃ lam0 lam1 : ℝ,
      TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
        (∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) := by
  have hc : c ∈ closure (Submission.PBox s c σ) :=
    subset_closure (by
      rw [Submission.mem_PBox]
      intro i
      rw [sub_self, abs_zero]
      exact mul_pos (Submission.boxSide_pos i) hs)
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hRbox c hc)
  have hh : 0 < h := lt_of_le_of_lt (mul_nonneg (norm_nonneg _) hR0) hsize
  -- bounds on `ℓ` over the closed box and on the elements of `exc`
  set q : ℝ := |ℓ c| + ‖ℓ‖ * R + 1 with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith [abs_nonneg (ℓ c), norm_nonneg ℓ, hR0]
  have hℓy : ∀ y ∈ closure (Submission.PBox s c σ), |ℓ y| ≤ q - 1 := by
    intro y hy
    have h1 : ‖y - c‖ ≤ R := hRbox y hy
    have h2 : ℓ y - ℓ c = ℓ (y - c) := by rw [map_sub]
    have h3 : |ℓ (y - c)| ≤ ‖ℓ‖ * ‖y - c‖ := by
      have := ContinuousLinearMap.le_opNorm ℓ (y - c)
      rwa [Real.norm_eq_abs] at this
    have h4 : |ℓ y| ≤ |ℓ y - ℓ c| + |ℓ c| := by
      have h5 : ℓ y = (ℓ y - ℓ c) + ℓ c := by ring
      calc |ℓ y| = |(ℓ y - ℓ c) + ℓ c| := congrArg (fun t : ℝ => |t|) h5
        _ ≤ |ℓ y - ℓ c| + |ℓ c| := abs_add_le _ _
    rw [h2] at h4
    have h6 : ‖ℓ‖ * ‖y - c‖ ≤ ‖ℓ‖ * R := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have : |ℓ y| ≤ ‖ℓ‖ * R + |ℓ c| := by linarith
    rw [hq]; linarith
  set m : ℝ := 1 + ∑ t ∈ exc, |t| with hm
  have hm1 : 1 ≤ m := by
    rw [hm]; linarith [Finset.sum_nonneg (fun t (_ : t ∈ exc) => abs_nonneg t)]
  have hexc : ∀ t ∈ exc, |t| ≤ m - 1 := by
    intro t ht
    have h1 : |t| ≤ ∑ t' ∈ exc, |t'| :=
      Finset.single_le_sum (fun t' (_ : t' ∈ exc) => abs_nonneg t') ht
    rw [hm]; linarith
  have hwin : ∀ y ∈ closure (Submission.PBox s c σ),
      -(q + m) < ℓ y ∧ ℓ y < q + m := by
    intro y hy
    have h1 := hℓy y hy
    constructor
    · have h2 : -|ℓ y| ≤ ℓ y := neg_abs_le _
      have h3 : -(q - 1) ≤ -|ℓ y| := neg_le_neg h1
      linarith
    · have h2 : ℓ y ≤ |ℓ y| := le_abs_self _
      linarith
  refine ⟨-(q + m), q + m, ⟨hgen, hv1, hℓne, hℓv, hsize, hh, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, by linarith, fun t ht => ?_⟩, hwin⟩
  · exact le_trans (hRbox y (subset_closure hy)) le_rfl
  · exact (hwin y (subset_closure hy)).1
  · exact (hwin y (subset_closure hy)).2
  · have h1 := hexc t ht
    have h2 := neg_abs_le t
    have h3 := le_abs_self t
    constructor <;> linarith

/-- **`Work.Drive.Mono.LevelFrontierGen` is monotone in the exceptional set.** -/
theorem levelFrontierGen_mono_exc {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {exc B : Finset ℝ} {lam0 lam1 : ℝ}
    (hLF : LevelFrontierGen s c σ u v h ℓ exc lam0 lam1) :
    LevelFrontierGen s c σ u v h ℓ (exc ∪ B) lam0 lam1 := by
  intro lam hlam hne
  exact hLF lam hlam (fun hmem => hne (Finset.mem_union_left B hmem))

/-- **`Work.Drive.Final.TiltedGenericity` is monotone in the exceptional set** (all four clauses have
the form `∀ lam ∉ exc`). -/
theorem tiltedGenericity_monoExc {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc B : Finset ℝ}
    (hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc) :
    Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ (exc ∪ B) := by
  obtain ⟨h1, h2, h3, h4⟩ := hgen
  have hsub : (exc : Set ℝ) ⊆ ((exc ∪ B : Finset ℝ) : Set ℝ) := by
    intro x hx
    rw [Finset.mem_coe] at hx ⊢
    exact Finset.mem_union_left B hx
  refine ⟨fun lam hlam => h1 lam (fun hmem => hlam (hsub hmem)),
    fun lam hlam => h2 lam (fun hmem => hlam (hsub hmem)), ?_, h4⟩
  intro p hp1 hp2 hp3
  exact ⟨(h3 p hp1 hp2 hp3).1, Finset.mem_union_left B (h3 p hp1 hp2 hp3).2⟩

/-- **The thin-slab `TiltData` producer.**  At *every* cutting level `u` and every box level `s`
(of the crux's range) and for every prescribed `η > 0` there are tilt data of the deliverable with
half-width `h < η`, radius bound `R = 5/2 * s` (the radius of the ball containing the box,
`Submission.PBox_subset_ball`) and with the slab really cutting the box
(`h + |u| < boxWidth s σ v`).

Neither an almost-everywhere hypothesis on `u` nor a general-position hypothesis on the box level
`s` is needed: the producer `Work.Drive.Mono.exists_smallSlab_tiltData` of `Mono/Band` is
unconditional, and this lemma only adds the window bookkeeping
(`Work.Drive.Mono.exists_window_of_genericity`). -/
theorem exists_tiltData_smallSlab
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u r η : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) (hη : 0 < η) :
    ∃ (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
      TiltData ψ s c σ u v h (5 / 2 * s) ℓ exc lam0 lam1 ∧ h < η ∧
      h + |u| < Work.Drive.Mono.boxWidth s σ v := by
  have hs0 : 0 < s := lt_trans hr hrs
  obtain ⟨v, n, h, exc, hv1, hn1, hvn, _hh0, hhη, hsize5, hcut, hgen⟩ :=
    exists_smallSlab_tiltData ψ s c σ u r η hr hrs hs hu hη
  have hℓne : (innerSL ℝ) n ≠ 0 := by
    intro h0
    have h1 : inner ℝ n n = 0 := by
      rw [← innerSL_apply_apply (𝕜 := ℝ) n n, h0]
      rfl
    have h2 : ‖n‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq n]; exact h1
    have h3 : ‖n‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    rw [hn1] at h3
    exact one_ne_zero h3
  have hℓv : (innerSL ℝ) n v = 0 := by
    rw [innerSL_apply_apply, real_inner_comm]
    exact hvn
  have hRbox : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ 5 / 2 * s :=
    fun y hy => norm_sub_le_of_mem_closure_PBox (s := s) (c := c) (σ := σ) (le_of_lt hs0) hy
  obtain ⟨lam0, lam1, hT, _hwin⟩ :=
    exists_window_of_genericity hs0 hgen hv1 hℓne hℓv hsize5 hRbox
  exact ⟨v, h, (innerSL ℝ) n, lam0, lam1, exc, hT, hhη, hcut⟩

/-- **The thin-slab `TiltData` producer, with the derived geometric conjuncts exposed.**  This is
`Work.Drive.Mono.exists_tiltData_smallSlab` with, in addition, the unit norm of `v`, the positivity
of `h` and the derived `SlabCutsBox` (the slab really cuts the box across its width), in the shape in
which the geometric inputs of clause 1 consume them
(`Work.Drive.Mono.levelSphereDecomposition_of_levelFrontierGen` takes `TiltData` and `SlabCutsBox`). -/
theorem exists_tiltData_smallSlab_cuts
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u r η : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) (hη : 0 < η) :
    ∃ (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
      TiltData ψ s c σ u v h (5 / 2 * s) ℓ exc lam0 lam1 ∧ ‖v‖ = 1 ∧ 0 < h ∧ h < η ∧
      SlabCutsBox s c σ (inner ℝ v c + u) h v := by
  have hs0 : 0 < s := lt_trans hr hrs
  obtain ⟨v, h, ℓ, lam0, lam1, exc, hT, hhη, hcut⟩ :=
    exists_tiltData_smallSlab ψ s c σ u r η hr hrs hs hu hη
  exact ⟨v, h, ℓ, lam0, lam1, exc, hT, hT.2.1, hT.2.2.2.2.2.1, hhη,
    slabCutsBox_of_width hs0 hT.2.2.2.2.2.1 hcut⟩

/-- **The thin-slab `TiltData` producer, with the level-frontier genericity.**  This is
`Work.Drive.Mono.exists_tiltData_smallSlab_cuts` together with the *choice* of the exceptional set
which makes the level frontier of the sweep a finite disjoint union of embedded spheres
(`Work.Drive.Mono.LevelFrontierGen`, the geometric input of clause 1, whose offending levels are
finitely many — `Work.Drive.Mono.exists_levelFrontierGen`).

This discharges, at *every* cutting level and *every* box level, three of the conjuncts of the
residual `Work.Drive.Mono.TraceDataInputsF` — the tilt data, the slab-cutting condition and the
level-frontier genericity — with the *thin* slab which the trace data require. -/
theorem exists_tiltData_smallSlab_levelFrontier
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u r η : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) (hη : 0 < η) :
    ∃ (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
      TiltData ψ s c σ u v h (5 / 2 * s) ℓ exc lam0 lam1 ∧ ‖v‖ = 1 ∧ 0 < h ∧ h < η ∧
      SlabCutsBox s c σ (inner ℝ v c + u) h v ∧
      LevelFrontierGen s c σ u v h ℓ exc lam0 lam1 := by
  have hs0 : 0 < s := lt_trans hr hrs
  obtain ⟨v, n, h, exc, hv1, hn1, hvn, hh0, hhη, hsize5, hcut, hgen⟩ :=
    exists_smallSlab_tiltData ψ s c σ u r η hr hrs hs hu hη
  have hℓne : (innerSL ℝ) n ≠ 0 := by
    intro h0
    have h1 : inner ℝ n n = 0 := by
      rw [← innerSL_apply_apply (𝕜 := ℝ) n n, h0]
      rfl
    have h2 : ‖n‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq n]; exact h1
    have h3 : ‖n‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    rw [hn1] at h3
    exact one_ne_zero h3
  have hℓv : (innerSL ℝ) n v = 0 := by
    rw [innerSL_apply_apply, real_inner_comm]
    exact hvn
  have hRbox : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ 5 / 2 * s :=
    fun y hy => norm_sub_le_of_mem_closure_PBox (s := s) (c := c) (σ := σ) (le_of_lt hs0) hy
  obtain ⟨lam0, lam1, hT, hwin⟩ :=
    exists_window_of_genericity hs0 hgen hv1 hℓne hℓv hsize5 hRbox
  have hcut' : SlabCutsBox s c σ (inner ℝ v c + u) h v := slabCutsBox_of_width hs0 hh0 hcut
  obtain ⟨B, hBwin, hLF⟩ := exists_levelFrontierGen s c σ u v h ((innerSL ℝ) n) lam0 lam1
    hv1 hh0 hℓv hℓne hcut' hwin
  -- the enlarged exceptional set
  obtain ⟨hgen', hv1', hℓne', hℓv', hsize', hh', hbox', hlow', hhigh', hl', hexc'⟩ := hT
  have hLF' : LevelFrontierGen s c σ u v h ((innerSL ℝ) n) (exc ∪ B) lam0 lam1 := by
    simpa [Finset.union_comm] using levelFrontierGen_mono_exc (B := exc) hLF
  refine ⟨v, h, (innerSL ℝ) n, lam0, lam1, exc ∪ B, ?_, hv1', hh', hhη, hcut', hLF'⟩
  refine ⟨tiltedGenericity_monoExc hgen', hv1', hℓne', hℓv', hsize', hh', hbox', hlow', hhigh',
    hl', ?_⟩
  intro t ht
  rcases Finset.mem_union.mp ht with h | h
  · exact hexc' t h
  · exact hBwin t h

/-- **The thin-slab `TiltData` producer, with the face regularity and the level-frontier
genericity.**  This is `Work.Drive.Mono.exists_tiltData_smallSlab_levelFrontier` with one more
conjunct, `faceReg`: the level planes of the two slab faces are *transverse* to the surface on the
box (the slab-height is regular at every parameter of the fundamental domain whose image lies in the
closed box and at the slab level).

The direction is the one produced by `Work.Drive.Mono.exists_dirData_close` (orthonormal to the good
height direction `n`, within `1/8` of `shiftVσ σ 1`), and the face regularity comes from
`Work.Drive.Mono.tiltData_small_of_dir_near_junction`, whose two "face regularity" outputs are
exactly this condition on the fundamental domain; the reduction of an arbitrary lift to the
fundamental domain is `Work.Drive.Mono.Band.fundamentalDomain_reduction`. -/
theorem exists_tiltData_smallSlab_faceReg
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u r η : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) (hη : 0 < η) :
    ∃ (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
      TiltData ψ s c σ u v h (5 / 2 * s) ℓ exc lam0 lam1 ∧ ‖v‖ = 1 ∧ 0 < h ∧ h < η ∧
      SlabCutsBox s c σ (inner ℝ v c + u) h v ∧
      LevelFrontierGen s c σ u v h ℓ exc lam0 lam1 ∧
      (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
        |inner ℝ v z - (inner ℝ v c + u)| = h →
        ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
          fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) := by
  classical
  have hs0 : 0 < s := lt_trans hr hrs
  obtain ⟨v, n, hv1, hn1, hvn, hgood, hve, hvη⟩ :=
    exists_dirData_close ψ s σ η hs0 hη
  obtain ⟨h, nn, exc, hh0, hhη, hsize, hcut, _hclose, hnn1, hvnn, hgen, _hV, hfaceP, hfaceM⟩ :=
    tiltData_small_of_dir_near_junction ψ s c σ u r η 1 v n (∅ : Finset ℝ)
      hr hrs hu hη (by norm_num) hv1 hn1 hvn hgood hve hvη
  have hℓne : (innerSL ℝ) nn ≠ 0 := by
    intro h0
    have h1 : inner ℝ nn nn = 0 := by
      rw [← innerSL_apply_apply (𝕜 := ℝ) nn nn, h0]; rfl
    have h2 : ‖nn‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq nn]; exact h1
    have h3 : ‖nn‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    rw [hnn1] at h3
    exact one_ne_zero h3
  have hℓv : (innerSL ℝ) nn v = 0 := by
    rw [innerSL_apply_apply, real_inner_comm]; exact hvnn
  have hRbox : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ 5 / 2 * s :=
    fun y hy => norm_sub_le_of_mem_closure_PBox (s := s) (c := c) (σ := σ) (le_of_lt hs0) hy
  obtain ⟨lam0, lam1, hT, hwin⟩ :=
    exists_window_of_genericity hs0 hgen hv1 hℓne hℓv hsize hRbox
  have hcut' : SlabCutsBox s c σ (inner ℝ v c + u) h v := slabCutsBox_of_width hs0 hh0 hcut
  obtain ⟨B, hBwin, hLF⟩ := exists_levelFrontierGen s c σ u v h ((innerSL ℝ) nn) lam0 lam1
    hv1 hh0 hℓv hℓne hcut' hwin
  have hLF' : LevelFrontierGen s c σ u v h ((innerSL ℝ) nn) (exc ∪ B) lam0 lam1 := by
    simpa [Finset.union_comm] using levelFrontierGen_mono_exc (B := exc) hLF
  -- the face regularity, from the fundamental-domain outputs
  have hface : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
    intro z hzc hzbox hzface
    rw [Work.Drive.EpsSphere.torusOf, Work.Smooth.Morse.torus_carrier] at hzc
    obtain ⟨p, hp⟩ := hzc
    have hp' : Work.BoxShrink.Pinch.par ψ p = z := hp
    obtain ⟨p₀, hp₀Icc, hp₀par, _hp₀fd⟩ :=
      Work.Drive.Mono.Band.fundamentalDomain_reduction ψ p
    have hp₀box : Work.BoxShrink.Pinch.par ψ p₀ ∈ closure (Submission.PBox s c σ) := by
      rw [hp₀par, hp']
      exact subset_closure hzbox
    have hhpos : 0 < h := lt_of_le_of_lt (mul_nonneg (norm_nonneg _) (by positivity)) hsize
    have hval : Work.Drive.Mono.Band.heightV ψ v p₀ = inner ℝ v c + u + h ∨
        Work.Drive.Mono.Band.heightV ψ v p₀ = inner ℝ v c + u - h := by
      have hh2 : inner ℝ v (Work.BoxShrink.Pinch.par ψ p₀) = inner ℝ v z := by
        rw [hp₀par, hp']
      rw [Work.Drive.Mono.Band.heightV, hh2]
      rcases abs_eq hhpos.le |>.mp hzface with h' | h'
      · exact Or.inl (by linarith [h'])
      · exact Or.inr (by linarith [h'])
    refine ⟨p₀, hp₀par.trans hp', ?_⟩
    rcases hval with h' | h'
    · exact hfaceP p₀ ⟨hp₀Icc, hp₀box⟩ h'
    · exact hfaceM p₀ ⟨hp₀Icc, hp₀box⟩ h'
  -- assemble, with the enlarged exceptional set
  obtain ⟨hgen', hv1', hℓne', hℓv', hsize', hh', hbox', hlow', hhigh', hl', hexc'⟩ := hT
  refine ⟨v, h, (innerSL ℝ) nn, lam0, lam1, exc ∪ B, ?_, hv1', hh', hhη, hcut', hLF', hface⟩
  refine ⟨tiltedGenericity_monoExc hgen', hv1', hℓne', hℓv', hsize', hh', hbox', hlow', hhigh',
    hl', ?_⟩
  intro t ht
  rcases Finset.mem_union.mp ht with hmem | hmem
  · exact hexc' t hmem
  · exact hBwin t hmem

end

end Work.Drive.Mono
