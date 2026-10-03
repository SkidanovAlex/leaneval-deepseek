import Mathlib
import Submission.Work.Pert.pert2v2.DE_add_one
import Submission.Work.Pert.DE_down.DE_sub_nat
import Submission.Work.Pert.pert2v2.window_shift

/-!
# `Work.Pert.pert2v2.DRSub` — the low/band half of `DR_sub` for the two-piece return map

`PertData.DR_sub` for the two-piece `R` (`pert2v2.twoPieceR_exists`) needs

  `K ∪ {w | y₁ ≤ |w.im|} ⊆ DR = ⋃ n : ℤ, (· + n) '' (Ulow ∪ Uhigh)`.

This file supplies the **band half**: every point of the datum's horn domain `d.DE` in the band
`y₁ ≤ |Im w| < Hband` lies in the `ℤ`-saturation of the low chart, provided `Ulow` contains the
window points `{|Re| < R1} ∩ d.DE ∩ {y₁' < |Im| < Hband}` with `1/2 < R1` and `y₁' < y₁`.

Two ingredients (both proved elsewhere) are combined:

* `d.DE` is `T`-invariant — forward by `pert2v2.DE_add_one`, backward by `DE_down.DE_sub_nat` — so
  the `ℤ`-saturation is `T`-invariant and we may move the point left into the half line `Re < R1`
  (`mem_iUnion_intShift_add_nat_iff`) without changing saturation membership;
* `pert2v2.exists_shift_mem_window`: a window of half-width `R1 > 1/2` is met by the right half-line
  `{Re w + m : m ∈ ℕ}`, so a *nonnegative* shift lands inside, and real shifts preserve height.

The high half of `DR_sub` (`Hband ≤ |Im w|`, `|Re w| ≤ 1`) is the conclusion of
`Work.Pert.waist_cover_pinned_v2` (through `pert2v2.retDR_strip`), and the `K`-part is handled by
putting `K` itself into the low chart (`NOTES_pert2v2_session30.md` §6.4).
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- **The `ℤ`-saturation of a set is `T`-invariant.** -/
theorem mem_iUnion_intShift_add_one_iff (U : Set ℂ) (w : ℂ) :
    w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' U ↔
      w + 1 ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' U := by
  constructor
  · intro hw
    simp only [Set.mem_iUnion, Set.mem_image] at hw ⊢
    obtain ⟨n, u, hu, hnu⟩ := hw
    exact ⟨n + 1, u, hu, by
      push_cast
      rw [show u + ((n : ℂ) + 1) = (u + (n : ℂ)) + 1 from by ring, hnu]⟩
  · intro hw
    simp only [Set.mem_iUnion, Set.mem_image] at hw ⊢
    obtain ⟨n, u, hu, hnu⟩ := hw
    refine ⟨n - 1, u, hu, ?_⟩
    push_cast
    rw [show u + ((n : ℂ) - 1) = (u + (n : ℂ)) - 1 from by ring, hnu]
    ring

/-- Iterated form: membership in the `ℤ`-saturation is unchanged by a nonnegative integer shift. -/
theorem mem_iUnion_intShift_add_nat_iff (U : Set ℂ) (w : ℂ) (j : ℕ) :
    w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' U ↔
      w + (j : ℂ) ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' U := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hstep := mem_iUnion_intShift_add_one_iff U (w + (k : ℂ))
    have hcast : w + ((k + 1 : ℕ) : ℂ) = (w + (k : ℂ)) + 1 := by push_cast; ring
    rw [hcast, ← hstep]
    exact ih

/-- **The band half of `DR_sub` (closed height bounds).**  If `Ulow` contains the window points
`{|Re| < R1} ∩ d.DE ∩ {y₁' < |Im| ≤ Hband}` (`1/2 < R1`, `y₁' < y₁`), then every point of `d.DE`
with `y₁ ≤ |Im| ≤ Hband` lies in the `ℤ`-saturation of `Ulow`.

The height bounds are **closed** on purpose: this is what lets the low chart carry the level
`|Im| = Hband` that `glue_window_bool_wide`'s strict separation leaves to neither chart
(`NOTES_pert2v2_session30.md` §7.1).  The glue is then applied with threshold `Hband + 1`
(`Ulow ⊆ {|Im| < Hband + 1}` and `Uhigh ⊆ {Hband + 1 < |Im|}` hold whenever the charts are
`≤ Hband` and `> Hband`). -/
theorem band_subset_saturation {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {Ulow : Set ℂ} {R1 y₁ y₁' Hband : ℝ}
    (hR1 : 1 / 2 < R1) (hy' : y₁' < y₁)
    (hUlow : ∀ w : ℂ, |w.re| < R1 → w ∈ d.DE → y₁' < |w.im| → |w.im| ≤ Hband → w ∈ Ulow)
    {w : ℂ} (hw : w ∈ d.DE) (hlo : y₁ ≤ |w.im|) (hhi : |w.im| ≤ Hband) :
    w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' Ulow := by
  -- move `w` into the half line `Re < R1` by a nonnegative left shift
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (w - (j : ℂ)).re < R1 := by
    obtain ⟨j, hj⟩ := exists_nat_gt (w.re - R1)
    refine ⟨j, ?_⟩
    have : (w - (j : ℂ)).re = w.re - (j : ℝ) := by simp
    rw [this]; linarith
  have hwj : w - (j : ℂ) ∈ d.DE := Work.Pert.DE_down.DE_sub_nat d hd hw j
  have him : |(w - (j : ℂ)).im| ≤ Hband := by
    have : (w - (j : ℂ)).im = w.im := by simp
    rw [this]; exact hhi
  -- the saturation is invariant under `+ j`
  have hsat : w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' Ulow ↔
      (w - (j : ℂ)) ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' Ulow := by
    have h := mem_iUnion_intShift_add_nat_iff Ulow (w - (j : ℂ)) j
    rw [show (w - (j : ℂ)) + (j : ℂ) = w from by ring] at h
    exact h.symm
  rw [hsat]
  -- the window shift of `w - j`
  -- the window lemma is stated with a strict height bound; run it at `Hband + 1` and use that a
  -- real shift preserves the height, so the *closed* bound `Hband` is inherited from `w`
  obtain ⟨m, hmDE, hmre, _⟩ :=
    exists_shift_mem_window (DE := d.DE) (x₀ := 0) (R1 := R1) (Hband := Hband + 1)
      (fun u hu => DE_add_one d hd u hu) hR1 hwj (by linarith) (by simpa using hj)
  have hmim : |((w - (j : ℂ)) + (m : ℂ)).im| ≤ Hband := by
    have h1 : ((w - (j : ℂ)) + (m : ℂ)).im = w.im := by simp
    rw [h1]; exact hhi
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨-(m : ℤ), (w - (j : ℂ)) + (m : ℂ), ?_, ?_⟩
  · have hre : |((w - (j : ℂ)) + (m : ℂ)).re| < R1 := by simpa using hmre
    have hlt : y₁' < |((w - (j : ℂ)) + (m : ℂ)).im| := by
      have h1 : ((w - (j : ℂ)) + (m : ℂ)).im = w.im := by simp
      rw [h1]
      exact lt_of_lt_of_le hy' hlo
    exact hUlow _ hre hmDE hlt hmim
  · push_cast; ring

/-- **The band coverage with NO lower height bound** — the form the `K`-part of `DR_sub` needs.
With `Ulow` containing the whole window `{|Re| < R1} ∩ d.DE ∩ {|Im| < Hband}` (no `y₁`-type lower
bound, so that a caller's compact `K ⊆ d.DE` at *any* height is covered), every `d.DE`-point of
height `< Hband` is an integer translate of `Ulow`.  (This matters because `Ulow` is then bounded —
`|Re| < R1`, `|Im| < Hband` — hence can sit inside the crux's compact `Kb`,
`pert2v2.exists_Kb`, which is what makes the low piece's relation available on the chart.)

The proof is `exists_shift_mem_window` at `Hband`, with no height bookkeeping. -/
theorem band_subset_saturation_of_lt {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {Ulow : Set ℂ} {R1 Hband : ℝ}
    (hR1 : 1 / 2 < R1)
    (hUlow : ∀ w : ℂ, |w.re| < R1 → w ∈ d.DE → |w.im| < Hband → w ∈ Ulow)
    {w : ℂ} (hw : w ∈ d.DE) (hhi : |w.im| < Hband) :
    w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' Ulow := by
  -- move `w` into the half line `Re < R1`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (w - (j : ℂ)).re < R1 := by
    obtain ⟨j, hj⟩ := exists_nat_gt (w.re - R1)
    refine ⟨j, ?_⟩
    have : (w - (j : ℂ)).re = w.re - (j : ℝ) := by simp
    rw [this]; linarith
  have hwj : w - (j : ℂ) ∈ d.DE := Work.Pert.DE_down.DE_sub_nat d hd hw j
  have him : |(w - (j : ℂ)).im| < Hband := by
    have : (w - (j : ℂ)).im = w.im := by simp
    rw [this]; exact hhi
  have hsat : w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' Ulow ↔
      (w - (j : ℂ)) ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' Ulow := by
    have h := mem_iUnion_intShift_add_nat_iff Ulow (w - (j : ℂ)) j
    rw [show (w - (j : ℂ)) + (j : ℂ) = w from by ring] at h
    exact h.symm
  rw [hsat]
  obtain ⟨m, hmDE, hmre, hmim⟩ :=
    exists_shift_mem_window (DE := d.DE) (x₀ := 0) (R1 := R1) (Hband := Hband)
      (fun u hu => DE_add_one d hd u hu) hR1 hwj him (by simpa using hj)
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨-(m : ℤ), (w - (j : ℂ)) + (m : ℂ), ?_, ?_⟩
  · exact hUlow _ (by simpa using hmre) hmDE (by simpa using hmim)
  · push_cast; ring

/-- **The `K`-part of `DR_sub`**: a subset of the low chart lies in the saturation at level `0`. -/
theorem subset_saturation_of_subset {Ulow DR : Set ℂ} (hDR : DR = ⋃ n : ℤ,
      (fun u : ℂ => u + (n : ℂ)) '' Ulow) {K : Set ℂ} (hK : K ⊆ Ulow) : K ⊆ DR := by
  intro w hw
  rw [hDR]
  exact Set.mem_iUnion.mpr ⟨0, by
    simpa using Set.mem_image_of_mem (fun u : ℂ => u + ((0 : ℤ) : ℂ)) (hK hw)⟩

/-- **The high half of `DR_sub`**, from the window coverage of the waist image.  If the high chart is
`{|Re| < 1} ∩ {Hband ≤ |Im|} ∩ (Φ '' Q)` and above height `Hband` every point is an integer
translate of a point of `Φ '' Q` inside the window `|Re| < 1` (which is the conclusion of
`Work.Pert.waist_cover_pinned_v2`), then the whole high band lies in the `ℤ`-saturation of the high
chart.  The height bound is **closed** so that, together with the low chart's strict
`{|Im| < Hband}`, the two together tile the band with no hole (`NOTES_pert2v2_session30.md` §9).  (A real translate does not change the imaginary part, so the height clause is inherited.) -/
theorem high_subset_saturation {Φ : ℂ → ℂ} {Q Uhigh : Set ℂ} {Hband : ℝ}
    (hUhigh : Uhigh = {w : ℂ | |w.re| < 1 ∧ Hband ≤ |w.im| ∧ w ∈ Φ '' Q})
    (hcov : ∀ w : ℂ, Hband ≤ |w.im| →
      ∃ n : ℤ, |(w + (n : ℂ)).re| < 1 ∧ w + (n : ℂ) ∈ Φ '' Q)
    {w : ℂ} (him : Hband ≤ |w.im|) :
    w ∈ ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' Uhigh := by
  obtain ⟨n, hre, hmem⟩ := hcov w him
  have hu : w + (n : ℂ) ∈ Uhigh := by
    rw [hUhigh]
    exact ⟨hre, by simpa using him, hmem⟩
  refine Set.mem_iUnion.mpr ⟨-n, ?_⟩
  simp only [Set.mem_image]
  exact ⟨w + (n : ℂ), hu, by push_cast; ring⟩

end

end Work.Pert.pert2v2
