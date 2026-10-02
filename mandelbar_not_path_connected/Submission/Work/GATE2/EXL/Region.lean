/-
# GATE2 / EXL — the exit loop from the properties of the leak rectangle

`Work.GATE2.ExitLoop` asks for a compactum `𝒦` off `K c₀` on which the `α`-deviation is small, a
loop-confinement `K₀ ⊆ {Re < −1}`, and for every `u` of the leak disc a loop `λ` from `u − 1` to
`u` inside `K₀` with the potential floor `(3/4)·G(Ψ(u−1))` and the offset-avoidance `(W)`.

The **linear loop** `λ t := u − 1 + t` makes all of this a statement about a single rectangle: the
loop of `u ∈ closedBall x₀ r₀` runs along the horizontal segment of height `Im u` from `Re u − 1`
to `Re u`, so the union of the loops is exactly

    Λ := {w | x₀ − r₀ − 1 ≤ Re w ≤ x₀ + r₀, |Im w| ≤ r₀} ,

the leak disc thickened by one unit to the left.  With `K₀ := Λ` and `𝒦 := fl.Ψ '' Λ`, the fields
of `ExitLoop` are precisely

* `Λ ⊆ {Re < −1}`  (so that UT's exit window applies),
* `fl.Ψ '' Λ` avoids `K c₀`  (so that the transit is off the filled Julia set),
* `|deviation (varphiCrit c₀) α₁ ·| < 1/16384` on `fl.Ψ '' Λ`  (the `α₁`-window),
* the potential floor `(3/4)·G(Ψ(u−1)) ≤ G(Ψ w)` for `u` in the disc and `w ∈ Λ`.

The offset-avoidance `(W)` is then *automatic*: `(v : ℂ) + (λ t − (u − 1)) = v + t`, and `v + t` is
real with `Re ≥ v > v − 1/2`, hence in `slitAt v`.

This module records that reduction, so that the geometric content of EXL is isolated in the four
properties of `Λ`; the construction of `Λ` from the `ρ`-max / Stolz-sector route of
`Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §4 is the lemma
`Work.GATE2.EXL.loopRegion_window`.
-/
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.EXL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The leak rectangle** `Λ = {x₀ − r₀ − 1 ≤ Re ≤ x₀ + r₀, |Im| ≤ r₀}`: the union of the linear
exit loops `λ t = u − 1 + t`, `u ∈ closedBall x₀ r₀`. -/
def loopRegion (x₀ r₀ : ℝ) : Set ℂ :=
  {w : ℂ | x₀ - r₀ - 1 ≤ w.re ∧ w.re ≤ x₀ + r₀ ∧ |w.im| ≤ r₀}

theorem mem_loopRegion {x₀ r₀ : ℝ} {w : ℂ} :
    w ∈ loopRegion x₀ r₀ ↔ x₀ - r₀ - 1 ≤ w.re ∧ w.re ≤ x₀ + r₀ ∧ |w.im| ≤ r₀ := Iff.rfl

theorem isCompact_loopRegion (x₀ r₀ : ℝ) : IsCompact (loopRegion x₀ r₀) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_closedBall ((x₀ : ℝ) : ℂ) (2 * r₀ + 1)) ?_ ?_
  · have h1 : IsClosed {w : ℂ | x₀ - r₀ - 1 ≤ w.re} :=
      isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {w : ℂ | w.re ≤ x₀ + r₀} :=
      isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {w : ℂ | |w.im| ≤ r₀} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have heq : loopRegion x₀ r₀
        = {w : ℂ | x₀ - r₀ - 1 ≤ w.re} ∩ {w : ℂ | w.re ≤ x₀ + r₀} ∩ {w : ℂ | |w.im| ≤ r₀} := by
      ext w
      simp only [mem_loopRegion, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
    rw [heq]
    exact (h1.inter h2).inter h3
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := mem_loopRegion.mp hw
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have hnorm : ‖w - ((x₀ : ℝ) : ℂ)‖ ≤ |(w - ((x₀ : ℝ) : ℂ)).re| + |(w - ((x₀ : ℝ) : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hnorm
    have h4 : |w.re - x₀| ≤ r₀ + 1 := by
      rw [abs_le]; constructor <;> linarith
    linarith [abs_le.mp h3]

theorem loopRegion_mem_of_disc {x₀ r₀ : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) r₀) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    u - 1 + (t : ℂ) ∈ loopRegion x₀ r₀ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hu
  have hre : |u.re - x₀| ≤ r₀ := by
    have h := Complex.abs_re_le_norm (u - ((x₀ : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    linarith
  have him : |u.im| ≤ r₀ := by
    have h := Complex.abs_im_le_norm (u - ((x₀ : ℝ) : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith
  obtain ⟨hr1, hr2⟩ := abs_le.mp hre
  refine mem_loopRegion.mpr ⟨?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [ht.1]
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [ht.2]
  · simpa using him

/-- **The offset-avoidance `(W)` is automatic for the linear loop.**  `λ t = u − 1 + t` gives
`(v : ℂ) + (λ t − (u − 1)) = v + t`, which is real with real part `≥ v > v − 1/2`. -/
theorem linearLoop_slitAt {v : ℝ} {u : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (v : ℂ) + (u - 1 + (t : ℂ) - (u - 1)) ∈ slitAt v := by
  have h1 : u - 1 + (t : ℂ) - (u - 1) = (t : ℂ) := by ring
  rw [h1, slitAt, Set.mem_ofPred_eq]
  intro h
  have him : ((v : ℂ) + (t : ℂ)).im = 0 := by simpa using h.1
  have hre : ((v : ℂ) + (t : ℂ)).re ≤ v - 1 / 2 := h.2
  simp at him hre
  linarith [ht.1]

/-- **EXL from the properties of the leak rectangle.**  If the leak rectangle `Λ` is confined to
`{Re < −1}`, its `Ψ`-image avoids `K c₀` and carries the `α₁`-deviation bound, and the potential
floor holds on it for every `u` of the disc, then `ExitLoop c₀ fl.Ψ x₀ r₀ v α₁` holds — with
`𝒦 := fl.Ψ '' Λ`, `K₀ := Λ` and the linear loops. -/
theorem exitLoop_of_region {c₀ : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (x₀ r₀ v : ℝ)
    (hre : ∀ w ∈ loopRegion x₀ r₀, w.re < -1)
    (hoffK : ∀ w ∈ loopRegion x₀ r₀, fl.Ψ w ∉ Work.EL.K c₀)
    (hwin : ∀ w ∈ loopRegion x₀ r₀,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha1 (fl.Ψ w)| < (1 / 16384 : ℝ))
    (hgreen : ∀ u ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) r₀, ∀ w ∈ loopRegion x₀ r₀,
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u - 1)) ≤ Work.Bottcher.green c₀ (fl.Ψ w)) :
    Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha1) := by
  refine ⟨{ 𝒦 := fl.Ψ '' (loopRegion x₀ r₀)
            isCompact := (isCompact_loopRegion x₀ r₀).image fl.Ψ_diff.continuous
            offK := ?_
            win := ?_
            discs := ?_
            K₀ := loopRegion x₀ r₀
            isCompact_K₀ := isCompact_loopRegion x₀ r₀
            K₀_re := hre
            K₀_sub := fun w hw => ⟨w, hw, rfl⟩
            loop := ?_ }⟩
  · rintro z ⟨w, hw, rfl⟩
    exact hoffK w hw
  · rintro z ⟨w, hw, rfl⟩
    exact hwin w hw
  · intro u hu
    refine ⟨⟨u - 1 + ((0:ℝ):ℂ), loopRegion_mem_of_disc hu ⟨le_refl 0, zero_le_one⟩, ?_⟩,
      ⟨u - 1 + ((1:ℝ):ℂ), loopRegion_mem_of_disc hu ⟨zero_le_one, le_refl 1⟩, ?_⟩⟩
    · show fl.Ψ (u - 1 + ((0:ℝ):ℂ)) = fl.Ψ (u - 1)
      rw [Complex.ofReal_zero, add_zero]
    · show fl.Ψ (u - 1 + ((1:ℝ):ℂ)) = fl.Ψ u
      rw [Complex.ofReal_one, sub_add_cancel]
  · intro u hu
    refine ⟨⟨fun t => u - 1 + ((t : ℝ) : ℂ), by fun_prop⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro t
      exact loopRegion_mem_of_disc hu t.2
    · intro t
      exact hgreen u hu _ (loopRegion_mem_of_disc hu t.2)
    · intro t
      exact linearLoop_slitAt t.2

/-- **EXL from the deep Stolz sector.**  If the leak rectangle lies in `{Re < −1}` *and* in the
Stolz sector `stolz fl R κ`, where the potential bound `κ·G` is below `1/16384`, and carries the
potential floor, then `ExitLoop c₀ fl.Ψ x₀ r₀ v α₁` holds.  This is the interface that the `ρ`-max
construction of `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §4 must feed: the near-maximal
choice of the leak centre puts the leak rectangle in the *deep* sector, and the design loop gives
the potential floor. -/
theorem exitLoop_of_stolz {c₀ : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (x₀ r₀ v R κ : ℝ)
    (hre : ∀ w ∈ loopRegion x₀ r₀, w.re < -1)
    (hstolz : ∀ w ∈ loopRegion x₀ r₀, w ∈ stolz fl R κ)
    (hdepth : ∀ w ∈ loopRegion x₀ r₀,
      κ * Work.Bottcher.green c₀ (fl.Ψ w) < (1 / 16384 : ℝ))
    (hgreen : ∀ u ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) r₀, ∀ w ∈ loopRegion x₀ r₀,
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u - 1)) ≤ Work.Bottcher.green c₀ (fl.Ψ w)) :
    Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha1) :=
  exitLoop_of_region fl x₀ r₀ v hre
    (fun w hw => stolz_offK (hstolz w hw))
    (fun w hw => lt_of_le_of_lt (mem_stolz.mp (hstolz w hw)).2.2 (hdepth w hw))
    hgreen

end Work.GATE2.EXL
