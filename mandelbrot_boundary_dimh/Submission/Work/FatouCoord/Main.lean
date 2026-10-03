/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Exist.fatouCoordW_differentiable
import Submission.Work.FatouCoord.Exist.fatouCoordW_abel
import Submission.Work.FatouCoord.Exist.fatouCoordW_injOn
import Submission.Work.FatouCoord.Exist.fatouCoordW_image_bdd
import Submission.Work.FatouCoord.Petal.petal_mapsTo_tendsto_of_le
import Submission.Work.FatouCoord.Unique.fatouCoordinate_unique

/-!
# The attracting Fatou coordinate of a parabolic germ: existence

This is the assembly of the Leau–Fatou existence theorem from the estimates in
`FatouCoord/Estimate/*` and `FatouCoord/Exist/*`.  For a germ
`f z = z + z ^ 2 * h z` (`h 0 = 1`) satisfying the quantitative hypotheses `ParabolicBounds`,
the function `fatouCoord f (1 - a) z = fatouCoordW f (1 - a) (-1/z)` is a Fatou coordinate on
the attracting petal `Petal r M`: `φ ∘ f = φ + 1`, `φ` holomorphic and injective on the petal,
with image containing, in every strip `|Im τ| ≤ B`, all points of sufficiently large real part.

Note on the image: the image of the petal under a Fatou coordinate is *not* a half plane (the
logarithmic correction tilts it), but it contains the tail of every horizontal strip; that is
what `exists_petal_fatouCoord` provides and what the Écalle cylinder statement uses.

Main exports:

* `exists_petal_fatouCoord` — existence of the petal and the coordinate;
* `petal_orbit_rel_iff` — the orbit relation on the petal is `φ z' - φ z ∈ ℤ`, i.e. the Écalle
  cylinder of the petal is `ℂ/ℤ`;
* `fatouCoordinate_difference_eq_const` — uniqueness up to additive constants.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {z z' w : ℂ} {M N B C : ℝ}

/-! ## Elementary chart bookkeeping -/

theorem chart_mem_of_mem_petal {M : ℝ} (hz : z ∈ Petal r M) : M < (chart z).re := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_Petal hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz.1
  exact ((chart_mem_Petal_iff hr hz0).mp hz).1

/-- The chart `w = -1/z` is holomorphic on a petal. -/
theorem differentiableOn_chart_petal : DifferentiableOn ℂ chart (Petal r M) := by
  have h : DifferentiableOn ℂ (fun z : ℂ => (-1 : ℂ) / z) (Petal r M) :=
    (differentiableOn_const (c := (-1 : ℂ))).div differentiableOn_id
      (fun z hz => ne_zero_of_mem_Petal hz)
  exact h

/-- In the chart, the dynamics is conjugated: `chart (f z) = wMap f (chart z)`. -/
theorem chart_comp (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) : chart (f z) = wMap f (chart z) := by
  rw [wMap, chart_chart hz]

/-! ## Existence of the attracting Fatou coordinate -/

/-- **Leau–Fatou, existence.**  For a germ `f z = z + z ^ 2 * h z` with `h 0 = 1` satisfying the
quantitative bounds `ParabolicBounds`, there is a level `M > 0` such that the petal
`Petal r M` is forward invariant with all orbits converging to `0`, and the explicitly
constructed function `fatouCoord f (1 - a)` is a Fatou coordinate on it, injective, whose image
contains the tail of every horizontal strip (`∀ B, ∃ C, ∀ τ, C < Re τ → |Im τ| ≤ B → ∃ z`). -/
theorem exists_petal_fatouCoord (hb : ParabolicBounds f h a r A A') :
    ∃ M : ℝ, 0 < M ∧ MapsTo f (Petal r M) (Petal r M) ∧
      (∀ z ∈ Petal r M, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0)) ∧
      IsFatouCoordinateOn f (fatouCoord f (1 - a)) (Petal r M) ∧
      Set.InjOn (fatouCoord f (1 - a)) (Petal r M) ∧
      (∀ B : ℝ, ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
        ∃ z ∈ Petal r M, fatouCoord f (1 - a) z = τ) := by
  obtain ⟨M₁, hM₁⟩ := Petal.petal_mapsTo_tendsto_of_le hb
  obtain ⟨N₃, hN₃, hr₃, hdiff⟩ := Exist.fatouCoordW_differentiable hb
  obtain ⟨N₄, hN₄, hr₄, habel⟩ := Exist.fatouCoordW_abel hb
  obtain ⟨N₅, hN₅, hr₅, hinj⟩ := Exist.fatouCoordW_injOn hb
  have hr : 0 < r := hb.hr
  -- the level is the maximum of all the thresholds, and at least 1
  let s : Finset ℝ := {M₁, 1, N₃, N₄, N₅, 1 / r}
  have hs : s.Nonempty := ⟨M₁, by simp [s]⟩
  set M : ℝ := s.max' hs with hMdef
  have hle : ∀ x ∈ s, x ≤ M := fun x hx => by rw [hMdef]; exact Finset.le_max' s x hx
  have hM₁' : M₁ ≤ M := hle M₁ (by simp [s])
  have h1M : (1 : ℝ) ≤ M := hle 1 (by simp [s])
  have hN₃' : N₃ ≤ M := hle N₃ (by simp [s])
  have hN₄' : N₄ ≤ M := hle N₄ (by simp [s])
  have hN₅' : N₅ ≤ M := hle N₅ (by simp [s])
  have h1r : 1 / r ≤ M := hle (1 / r) (by simp [s])
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one h1M
  have hpetal := hM₁ M hM₁'
  refine ⟨M, hMpos, hpetal.1, hpetal.2, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hmaps : MapsTo chart (Petal r M) {w : ℂ | N₃ < w.re} := fun z hz =>
        lt_of_le_of_lt hN₃' (chart_mem_of_mem_petal hz)
      exact hdiff.comp differentiableOn_chart_petal hmaps
    · intro z hz
      have hcw : N₄ < (chart z).re := lt_of_le_of_lt hN₄' (chart_mem_of_mem_petal hz)
      have h1 : chart (f z) = wMap f (chart z) := chart_comp f (ne_zero_of_mem_Petal hz)
      simp only [fatouCoord_eq]
      rw [h1, habel (chart z) hcw]
  · intro z hz z' hz' heq
    have hcz : N₅ < (chart z).re := lt_of_le_of_lt hN₅' (chart_mem_of_mem_petal hz)
    have hcz' : N₅ < (chart z').re := lt_of_le_of_lt hN₅' (chart_mem_of_mem_petal hz')
    have hch : chart z = chart z' := hinj hcz hcz' heq
    calc z = chart (chart z) := (chart_chart (ne_zero_of_mem_Petal hz)).symm
      _ = chart (chart z') := by rw [hch]
      _ = z' := chart_chart (ne_zero_of_mem_Petal hz')
  · intro B
    obtain ⟨C, hC⟩ := Exist.fatouCoordW_image_bdd hb M B
    refine ⟨C, ?_⟩
    intro τ hτ hτB
    obtain ⟨w, hw, hψ⟩ := hC τ hτ hτB
    have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hw
      simp at hw
      exact absurd hw (not_lt_of_ge hMpos.le)
    have hwr : 1 / r < ‖w‖ :=
      lt_of_lt_of_le (lt_of_le_of_lt h1r hw) (Complex.re_le_norm w)
    refine ⟨chart w, ?_, ?_⟩
    · have hcz : chart (chart w) = w := chart_chart hw0
      rw [chart_mem_Petal_iff hr (chart_ne_zero hw0), hcz]
      exact ⟨hw, hwr⟩
    · simp only [fatouCoord_eq, chart_chart hw0, hψ]

/-! ## Uniqueness up to additive constants -/

/-- **Uniqueness up to additive constants.**  Two Fatou coordinates on a petal on which the
orbits converge to `0` differ by a constant, as soon as their difference has a limit at `0`
along the petal.  (The limit hypothesis is exactly the normalization: two coordinates with the
same asymptotics at `0` do not differ at all, and the difference of two Fatou coordinates is
always `f`-invariant.) -/
theorem fatouCoordinate_difference_eq_const {f φ₁ φ₂ : ℂ → ℂ} {P : Set ℂ} {c : ℂ}
    (h₁ : IsFatouCoordinateOn f φ₁ P) (h₂ : IsFatouCoordinateOn f φ₂ P) (hP : MapsTo f P P)
    (hP0 : ∀ z ∈ P, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0))
    (hlim : Tendsto (fun z => φ₁ z - φ₂ z) (nhdsWithin 0 P) (nhds c)) :
    ∀ z ∈ P, φ₁ z - φ₂ z = c := by
  have h₁' : IsFatouCoordinateOn f (fun z => φ₁ z - c) P := h₁.sub_const c
  have hlim' : Tendsto (fun z => (fun z => φ₁ z - c) z - φ₂ z) (nhdsWithin 0 P) (nhds 0) := by
    have h := hlim.sub_const c
    have hfun : (fun z => (fun z => φ₁ z - c) z - φ₂ z) = fun z => φ₁ z - φ₂ z - c := by
      funext z; ring
    rw [hfun]
    simpa using h
  have huniq := Unique.fatouCoordinate_unique h₁' h₂ hP hP0 hlim'
  intro z hz
  have h := huniq z hz
  linear_combination h

/-! ## The Écalle cylinder: the orbit relation is `φ` modulo `ℤ` -/

/-- **The Écalle cylinder of a petal is `ℂ / ℤ`.**  For `z, z'` in the petal `Petal r M`,
`z` and `z'` are on the same `f`-orbit (some forward iterates agree) if and only if their
`φ`-coordinates differ by an integer.  In particular the quotient of the petal by the orbit
relation of `f` is identified with the quotient of the image of `φ` by the translation action
of `ℤ`, and the latter is the standard cylinder `ℂ/ℤ`: every `ℤ`-orbit meets the image of `φ`
(`exists_petal_fatouCoord`, applied to a point of bounded imaginary part of that orbit). -/
theorem petal_orbit_rel_iff (hb : ParabolicBounds f h a r A A') :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ Petal r M, ∀ z' ∈ Petal r M,
      (∃ m n : ℕ, f^[m] z = f^[n] z') ↔
        ∃ k : ℤ, fatouCoord f (1 - a) z' = fatouCoord f (1 - a) z + k := by
  obtain ⟨M, hM, hmap, hconv, hfatou, hinj, _⟩ := exists_petal_fatouCoord hb
  refine ⟨M, hM, ?_⟩
  intro z hz z' hz'
  constructor
  · rintro ⟨m, n, hmn⟩
    have hm : fatouCoord f (1 - a) (f^[m] z) = fatouCoord f (1 - a) z + m :=
      hfatou.iterate hmap hz m
    have hn : fatouCoord f (1 - a) (f^[n] z') = fatouCoord f (1 - a) z' + n :=
      hfatou.iterate hmap hz' n
    rw [hmn] at hm
    rw [hn] at hm
    exact ⟨(m : ℤ) - (n : ℤ), by push_cast; linear_combination hm⟩
  · rintro ⟨k, hk⟩
    obtain ⟨n, hkn | hkn⟩ := Int.eq_nat_or_neg k
    · subst hkn
      have hn : fatouCoord f (1 - a) (f^[n] z) = fatouCoord f (1 - a) z + n :=
        hfatou.iterate hmap hz n
      have hz'n : f^[n] z ∈ Petal r M := mapsTo_iterate_of_mapsTo hmap n hz
      have hk' : fatouCoord f (1 - a) z' = fatouCoord f (1 - a) (f^[n] z) := by
        simp only [Int.cast_natCast] at hk
        rw [hn]
        exact hk
      exact ⟨n, 0, by simpa using (hinj (by simpa using hz') hz'n hk').symm⟩
    · subst hkn
      have hn : fatouCoord f (1 - a) (f^[n] z') = fatouCoord f (1 - a) z' + n :=
        hfatou.iterate hmap hz' n
      have hzn : f^[n] z' ∈ Petal r M := mapsTo_iterate_of_mapsTo hmap n hz'
      have hk' : fatouCoord f (1 - a) (f^[n] z') = fatouCoord f (1 - a) z := by
        simp only [Int.cast_neg, Int.cast_natCast] at hk
        rw [hn, hk]
        ring
      exact ⟨0, n, by simpa using (hinj hzn (by simpa using hz) hk').symm⟩

end

end Work.FatouCoord
