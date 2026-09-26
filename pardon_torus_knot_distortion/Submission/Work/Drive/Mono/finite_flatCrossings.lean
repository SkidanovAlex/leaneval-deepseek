import Mathlib
import Submission.Work.Drive.Mono.CutTransverse
import Submission.Work.Drive.Mono.intervalZeros.injOn_of_deriv_ne_zero

/-!
# The flat crossing set is finite

A knot meeting the cutting plane `{y (σ 2) = c (σ 2) + u}` inside the closed Pardon box at a
*cut-transverse* level (every meeting is in the *open* box and the `σ 2`-coordinate of the knot is
non-critical there, `Work.Drive.Mono.CutTransverse`) meets it in finitely many parameters of one
period.

The proof is the elementary one: the set `S` of such parameters is closed (it is the intersection of
the compact interval `[0, 2π]`, the preimage of the closed box under the continuous curve `K.curve`,
and the level set of the continuous `σ 2`-coordinate), hence compact; and every one of its points is
isolated, because `CutTransverse` makes the derivative of `g t = (K.curve t) (σ 2) - (c (σ 2) + u)`
nonzero there, the derivative is continuous (the knot is smooth), so `g` is strictly monotone — in
particular injective — in a neighbourhood of the point, and `g` vanishes at the point.  A compact
set whose points are all isolated is finite, by the finite-subcover extraction
`IsCompact.elim_nhds_subcover`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
/-- The knot meets the cutting level inside the closed box in finitely many parameters of one period, when the level is cut-transverse. -/
theorem finite_flatCrossings (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (s u : ℝ)
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u) :
    ({t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ K.curve t ∈ closure (Submission.PBox s c σ) ∧
      (K.curve t) (σ 2) = c (σ 2) + u}).Finite := by
  classical
  set g : ℝ → ℝ := fun t => (K.curve t) (σ 2) - (c (σ 2) + u) with hgdef
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧
      K.curve t ∈ closure (Submission.PBox s c σ) ∧ (K.curve t) (σ 2) = c (σ 2) + u} with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ t ∈ Set.Icc 0 (2 * Real.pi) ∧
      K.curve t ∈ closure (Submission.PBox s c σ) ∧ (K.curve t) (σ 2) = c (σ 2) + u := by
    intro t; simp only [hSdef, Set.mem_ofPred_eq]
  have hKc : Continuous K.curve := K.smooth.continuous
  have hcoord : Continuous (fun t : ℝ => (K.curve t) (σ 2)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp hKc
  have hgc : Continuous g := by rw [hgdef]; exact hcoord.sub continuous_const
  have hgd1 : ContDiff ℝ 1 g := by
    rw [hgdef]
    exact (((EuclideanSpace.proj (𝕜 := ℝ) (σ 2)).contDiff.comp K.smooth).of_le
      (by exact_mod_cast le_top)).sub contDiff_const
  have hgdcont : Continuous (deriv g) := hgd1.continuous_deriv_one
  have hderiv_eq : ∀ t : ℝ, deriv g t = deriv (fun r : ℝ => (K.curve r) (σ 2)) t := by
    intro t
    rw [hgdef]
    exact deriv_sub_const (c (σ 2) + u)
  -- Every point of `S` is isolated in `S`.
  have hloc : ∀ x ∈ S, ∃ U : Set ℝ, U ∈ nhds x ∧ S ∩ U ⊆ {x} := by
    intro x hx
    obtain ⟨_, hxbox, hxlev⟩ := (hSmem x).mp hx
    obtain ⟨_, hdx⟩ := hcut x hxbox hxlev
    have hdgx : deriv g x ≠ 0 := by rw [hderiv_eq x]; exact hdx
    have hopen : IsOpen {y : ℝ | deriv g y ≠ 0} :=
      isOpen_compl_singleton.preimage hgdcont
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hdgx)
    refine ⟨Set.Ioo (x - ε) (x + ε), isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩, ?_⟩
    rintro y ⟨hyS, hyU⟩
    have hgy : g y = 0 := by rw [hgdef]; linarith [((hSmem y).mp hyS).2.2]
    have hgx : g x = 0 := by rw [hgdef]; linarith [hxlev]
    have hsub : Set.Ioo (x - ε) (x + ε) ⊆ {y : ℝ | deriv g y ≠ 0} := by
      intro z hz
      exact hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact abs_sub_lt_iff.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩)
    have hInj : Set.InjOn g (Set.Ioo (x - ε) (x + ε)) :=
      intervalZeros.injOn_of_deriv_ne_zero (by linarith) (fun z hz => hsub hz)
    have hyx : y = x := hInj hyU ⟨by linarith, by linarith⟩ (by rw [hgy, hgx])
    simpa [hyx]
  -- `S` is closed and lies in the compact interval `[0, 2π]`.
  have hSsub : S ⊆ Set.Icc (0 : ℝ) (2 * Real.pi) := fun t ht => ((hSmem t).mp ht).1
  have hSclosed : IsClosed S := by
    rw [hSdef]
    have h1 : IsClosed (Set.Icc (0 : ℝ) (2 * Real.pi)) := isClosed_Icc
    have h2 : IsClosed (K.curve ⁻¹' closure (Submission.PBox s c σ)) :=
      isClosed_closure.preimage hKc
    have h3 : IsClosed ((fun t : ℝ => (K.curve t) (σ 2)) ⁻¹' ({c (σ 2) + u} : Set ℝ)) :=
      isClosed_singleton.preimage hcoord
    have heq : {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧
          K.curve t ∈ closure (Submission.PBox s c σ) ∧ (K.curve t) (σ 2) = c (σ 2) + u}
        = Set.Icc (0 : ℝ) (2 * Real.pi) ∩ (K.curve ⁻¹' closure (Submission.PBox s c σ)) ∩
          ((fun t : ℝ => (K.curve t) (σ 2)) ⁻¹' ({c (σ 2) + u} : Set ℝ)) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      tauto
    rw [heq]
    exact (h1.inter h2).inter h3
  have hScomp : IsCompact S := IsCompact.of_isClosed_subset isCompact_Icc hSclosed hSsub
  -- A compact set all of whose points are isolated is finite.
  obtain ⟨F, hFsub, hFcover⟩ := hScomp.elim_nhds_subcover
    (fun x => if hx : x ∈ S then Classical.choose (hloc x hx) else Set.univ)
    (fun x hx => by
      rw [dif_pos hx]
      exact (Classical.choose_spec (hloc x hx)).1)
  refine Set.Finite.subset (s := (↑F : Set ℝ)) (t := S) (Finset.finite_toSet F) ?_
  intro y hy
  obtain ⟨x, hxF, hyU⟩ := by simpa only [Set.mem_iUnion] using hFcover hy
  have hxS : x ∈ S := hFsub x hxF
  have hsub := (Classical.choose_spec (hloc x hxS)).2
  have hyU' : y ∈ Classical.choose (hloc x hxS) := by simpa only [dif_pos hxS] using hyU
  have hyx : y = x := Set.mem_singleton_iff.mp (hsub ⟨hy, hyU'⟩)
  rw [hyx]
  simpa using hxF

end Work.Drive.Mono
