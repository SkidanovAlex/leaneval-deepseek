import Mathlib
import Submission.Work.Drive.Mono.OneEventNDDefs
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.no_eventOnFace_null

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped _root_.Topology

noncomputable section

/-!
# The bad set of the triple-point clause is null

`Work.Drive.Mono.Geom2Data`'s twentieth conjunct is

    ∀ p, Work.Drive.Final.IsTriplePoint ψ s c σ u v h p →
         fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0

i.e. no point of the parameter plane whose image has **two extremal box coordinates** and lies on the
slab face `|slabFn c u v ·| = h` (with the level functional `ℓ = innerSL (dirOf τ a₀ b₀)`) is a
critical point of the level functional on the surface.  This declaration is the nullity which lets
the producer avoid that configuration when it chooses `(h, τ)`: the set of pairs `(h, τ)` at which
such a point exists is null.

Note that the condition is stated on the **extended** box-edge locus — the two extremal coordinate
equations *without* `boxNorm c σ (par ψ p) = s`; that is exactly how `Work.Drive.Final.IsTriplePoint`
(`Submission/Work/Drive/Final/LTypes.lean`) is written, and it is also the form which is robust to the
proposed repair of that definition (adding `boxNorm = s` there only shrinks the bad set).

## Proof

The box-edge condition is *irrelevant* for the nullity: the argument bounds the larger set of pairs
`(h, τ)` for which *some* critical point of the level functional `F_τ = q ↦ ⟪dirOf τ a₀ b₀, par ψ q⟫`
has slab level `h`, and `dirOf τ a₀ b₀` is a `HeightGood` direction.

* The good parameters `G = {τ | HeightGood ψ (dirOf τ a₀ b₀)}` are **open**
  (`Work.Drive.Mono.Band.heightGood_open` composed with the continuity of `τ ↦ dirOf τ a₀ b₀`), hence
  covered by countably many intervals `[a,b]` with rational endpoints contained in `G`.
* For a compact interval `[a,b] ⊆ G` the image under `(τ,p) ↦ (|slabFn c u v (par ψ p)|, τ)` of the
  critical locus over `[a,b]` intersected with the fundamental square is compact, so measurable, and
  every one of its `τ`-sections is **finite**: for a good direction the critical points of the height
  inside the fundamental square are finite (`Work.Drive.Mono.Band.finite_critSet_isCompact`).
  Tonelli/Fubini (`Work.Drive.Mono.NoEventOnFace.slab_image_null`) gives that each such piece is null.
* Periodicity of `par ψ` (and hence of `slabFn c u v (par ψ ·)`) moves every critical point into the
  fundamental square without changing `τ`, its criticality or the slab level
  (`Work.Drive.EpsForm.exists_fundBox_of_crit`).

The three ingredients are exactly those of `Work.Drive.Mono.no_eventOnFace_null` (the same statement
with "lies in the open box and on a slab face" in place of "has two extremal box coordinates"); the
box condition is dropped here, which only makes the bad set larger.
-/

/-- **`Work.Drive.Mono.g3_tripleBad_null`.** -/
theorem g3_tripleBad_null (ψ : Submission.Diffeo) (s u : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) :
    MeasureTheory.volume {(h, τ) : ℝ × ℝ | ∃ p : ℝ × ℝ,
      (∃ i j : Fin 3, i ≠ j ∧
        |(Work.BoxShrink.Pinch.par ψ p) (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| = Submission.boxSide j * s) ∧
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h ∧
      Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) p = 0} = 0 := by
  classical
  -- The good parameters.
  set G : Set ℝ := {τ | Work.Drive.Mono.Band.HeightGood ψ
    (Work.Drive.Mono.Band.dirOf τ a₀ b₀)} with hGdef
  -- ## the good parameters form an open set
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    obtain ⟨ρ, hρ, hρgood⟩ := Work.Drive.Mono.Band.heightGood_open ψ hτ
    have hev : ∀ᶠ τ' in 𝓝 τ, ‖Work.Drive.Mono.Band.dirOf τ' a₀ b₀ -
        Work.Drive.Mono.Band.dirOf τ a₀ b₀‖ < ρ :=
      (NoEventOnFace.continuous_dirOf a₀ b₀ ha hb hab).continuousAt.eventually
        (Metric.ball_mem_nhds _ hρ)
    show {τ' : ℝ | Work.Drive.Mono.Band.HeightGood ψ
      (Work.Drive.Mono.Band.dirOf τ' a₀ b₀)} ∈ 𝓝 τ
    exact Filter.mem_of_superset hev (fun τ' hτ' => hρgood _ hτ')
  -- ## a good parameter lies in a closed interval with rational endpoints contained in `G`
  have hcoverG : ∀ τ ∈ G, ∃ a b : ℚ, (a : ℝ) < τ ∧ τ < (b : ℝ) ∧
      Set.Icc (a : ℝ) (b : ℝ) ⊆ G := by
    intro τ hτ
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.mp hGopen τ hτ
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show τ - ε < τ by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show τ < τ + ε by linarith)
    refine ⟨a, b, ha2, hb1, ?_⟩
    intro y hy
    apply hεG
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- ## the covering family of compact pieces
  set I : Set (ℚ × ℚ) := {q | Set.Icc (q.1 : ℝ) (q.2 : ℝ) ⊆ G} with hIdef
  -- ## the bad set is contained in the union of the pieces
  have hsub : {x : ℝ × ℝ | ∃ p : ℝ × ℝ,
      (∃ i j : Fin 3, i ≠ j ∧
        |(Work.BoxShrink.Pinch.par ψ p) (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| = Submission.boxSide j * s) ∧
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = x.1 ∧
      Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀) ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀))) p = 0} ⊆
      ⋃ q : {q : ℚ × ℚ // q ∈ I},
        NoEventOnFace.slab ψ v (inner ℝ v c + u) ''
          (NoEventOnFace.critSet ψ a₀ b₀ ∩
            (Set.Icc (q.1.1 : ℝ) (q.1.2 : ℝ) ×ˢ Work.Drive.EpsForm.fundBox)) := by
    rintro ⟨h, τ⟩ ⟨p, -, hpabs, hgood, hcrit⟩
    -- the criticality, phrased for the height in the direction `dirOf τ a₀ b₀`
    have hcrit' : fderiv ℝ (Work.Drive.EpsForm.heightOf ψ
        (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p = 0 := by
      have h := hcrit
      rw [Work.Drive.EpsForm.sweepHeight_innerSL] at h
      exact h
    -- move the critical point into the fundamental square
    obtain ⟨p', hp'box, hp'crit, -, -, hp'par⟩ :=
      Work.Drive.EpsForm.exists_fundBox_of_crit ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) hcrit'
    -- a good parameter lies in a rational interval contained in `G`
    obtain ⟨a, b, haτ, hτb, hIab⟩ := hcoverG τ hgood
    refine Set.mem_iUnion.mpr ⟨⟨(a, b), hIab⟩, (τ, p'),
      ⟨hp'crit, ⟨⟨haτ.le, hτb.le⟩, hp'box⟩⟩, ?_⟩
    -- the image under the slab map is the desired pair
    refine Prod.ext ?_ ?_
    · show |inner ℝ v (Work.BoxShrink.Pinch.par ψ p') - (inner ℝ v c + u)| = h
      rw [hp'par]
      rw [show |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)|
          = |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| from by
        rw [Work.Drive.Final.slabFn_apply]]
      simpa using hpabs
    · rfl
  -- ## conclusion
  refine measure_mono_null hsub ?_
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro q
  exact NoEventOnFace.slab_image_null ψ v a₀ b₀ (inner ℝ v c + u) ha hb hab
    (Set.Icc (q.1.1 : ℝ) (q.1.2 : ℝ)) isCompact_Icc (fun τ hτ => q.2 hτ)

end

end Work.Drive.Mono
