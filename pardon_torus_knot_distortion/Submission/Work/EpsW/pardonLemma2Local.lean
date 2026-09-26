import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.not_exists_weakCompressingLoop_of_counts
import Submission.Work.CoreTopology.min_le_encard_inter_of_boundsDiskW
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.BoxShrink.Core.All
import Submission.Work.BoxShrink.crux
import Submission.Work.Smooth.Morse.Defs

/-!
# Pardon's Lemma 2 and the footprint count, locally

This module is a **verbatim local copy** of the five declarations of
`Submission/Work/Drive/EpsForm/countingHalfEps_holds.lean` that the arcs case of the ε-form consumes:

* `encard_range_inter_le_param` — the reduction of `range K.curve ∩ S` to a parameter set;
* `footprintCountBound` — the knot meets the footprint `sphereSet ∪ cutDisc` in fewer than `min p q`
  points (this is where the crux's two counts and `countConst = 150` are spent: `75 d + 2 · 37.5 d`);
* `sphereTrace_inessential_of_countsW` — Pardon's Lemma 2 at the box sphere;
* `trace_inessential_of_slicing_of_countsW` — Pardon's Lemma 2 at an arbitrary sliced sphere;
* `trace_inessential_of_slicing_of_subset_footprint` — the two together, at any sphere inside the
  footprint (the "cleanliness of a member" brick of the pinch).

**Why the copy.**  That module is mid-migration from `Work.Drive.CleansDiscsW` to the corrected
`Work.Drive.CleansDiscsWd` (`Submission/Work/Drive/InterfacesD.lean`): its own binders are still
`CleansDiscsW` while the lemmas it calls were already migrated, so it currently does not compile and
nothing importing it can be built.  The five declarations above are unaffected by that migration
(their proofs use only `CleansDiscsW`, which is still defined), so they are reproduced here
unchanged, with the same names, in namespace `Work.EpsW`, so that
`Submission/Work/EpsW/arcsCaseEps.lean` (and the target's dependency closure) can be built.

**To be removed** when the sibling migrates: delete this module and restore the import of
`Submission.Work.Drive.EpsForm.countingHalfEps_holds` (the names of the copies are chosen to match,
so the call sites in `arcsCaseEps.lean` are then ambiguous and must be re-qualified).

Nothing else of that module is copied: in particular the ε-forms, the sweep machinery and the
`SideSweepExists` consumer are not needed here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.EpsW

noncomputable section

/-- **The knot meets a set only through its parameters.**  For a set `S` of `ℝ³`, the intersections
of the knot curve with `S` are hit by parameters in the fundamental period `[0, 2π)`: this is the
reduction of the cardinality of `range K.curve ∩ S` to a cardinality of parameters, and it is the
step at which the two counts of the crux (which count *parameters*) are consumed. -/
theorem encard_range_inter_le_param (K : Knot) (S : Set R3) :
    Set.encard (Set.range K.curve ∩ S) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ S} := by
  refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le K.curve _)
  rintro y ⟨⟨t, rfl⟩, hyS⟩
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
  have hnle : (n : ℝ) ≤ t / (2 * Real.pi) := by rw [hn]; exact Int.floor_le _
  have hnlt : t / (2 * Real.pi) < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have hle : 0 ≤ t - (n : ℝ) * (2 * Real.pi) := by
    have := (le_div_iff₀ hpos).mp hnle
    linarith
  have hlt : t - (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    have := (div_lt_iff₀ hpos).mp hnlt
    linarith
  have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
  have hcurve : K.curve (t - (n : ℝ) * (2 * Real.pi)) = K.curve t :=
    hper.sub_int_mul_eq n
  exact ⟨t - (n : ℝ) * (2 * Real.pi), ⟨⟨hle, hlt⟩, by rw [hcurve]; exact hyS⟩, hcurve⟩

/-- **The knot meets the footprint of Pardon's double bubble in fewer than `min p q` points.**  If
the knot meets the boundary sphere `∂PBox s c σ` in at most `10 (1+ε)/ε · d` parameters and the flat
disc `cutDisc s c σ u` in at most `5 (1+ε)/ε · d` parameters, and `countConst · d < min p q`, then
the knot meets the footprint `sphereSet c σ s ∪ cutDisc s c σ u` in fewer than
`min p q = I(F, β)` points.  Since each of the two half-spheres of the double bubble is a subset of
the footprint, the same holds for each of them: this is exactly the hypothesis of Pardon's Lemma 2
at `S = H±` (`Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW`), the cleanliness of the
two spheres at which the pinch ends. -/
theorem footprintCountBound (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hcountS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hcountU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    Set.encard (Set.range K.curve ∩ (Work.BoxShrink.Core.sphereSet c σ s ∪
      Work.BoxShrink.Core.cutDisc s c σ u)) < (Nat.min p q : ℕ∞) := by
  have h75 : 10 * (1 + Submission.eps) / Submission.eps * d = 75 * d := by
    rw [Submission.eps]; ring
  have h37 : 5 * (1 + Submission.eps) / Submission.eps * d = 75 / 2 * d := by
    rw [Submission.eps]; ring
  have h112 : (75 : ℝ) * d + 75 / 2 * d = 112.5 * d := by ring
  -- the parameter set of the footprint is the union of the two counted parameter sets
  have hset : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ (Work.BoxShrink.Core.sphereSet c σ s ∪
        Work.BoxShrink.Core.cutDisc s c σ u)}
      = {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s}
        ∪ {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨ht, hy | hy⟩
      · exact Or.inl ⟨ht, Work.BoxShrink.Core.mem_sphereSet.mp hy⟩
      · exact Or.inr ⟨ht, (Work.BoxShrink.Core.mem_cutDisc.mp hy).1,
          (Work.BoxShrink.Core.mem_cutDisc.mp hy).2⟩
    · rintro (⟨ht, hy⟩ | ⟨ht, hb, hy⟩)
      · exact ⟨ht, Or.inl (Work.BoxShrink.Core.mem_sphereSet.mpr hy)⟩
      · exact ⟨ht, Or.inr (Work.BoxShrink.Core.mem_cutDisc.mpr ⟨hb, hy⟩)⟩
  have hA : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}) : ENNReal) ≤ ENNReal.ofReal (75 * d) := by
    simpa [h75] using hcountS
  have hB : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (75 / 2 * d) := by
    simpa [h37] using hcountU
  have hpar : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ (Work.BoxShrink.Core.sphereSet c σ s ∪
        Work.BoxShrink.Core.cutDisc s c σ u)}) : ENNReal) ≤ ENNReal.ofReal (112.5 * d) := by
    rw [hset]
    calc (↑(Set.encard ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}
            ∪ {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u})) : ENNReal)
        ≤ ↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}
            + Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) := by
          rw [ENat.toENNReal_le]
          exact Set.encard_union_le _ _
      _ = (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            + ↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) :=
          ENat.toENNReal_add _ _
      _ ≤ ENNReal.ofReal (75 * d) + ENNReal.ofReal (75 / 2 * d) := add_le_add hA hB
      _ = ENNReal.ofReal (112.5 * d) := by
          rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hd)
            (mul_nonneg (by norm_num) hd), h112]
  have hmin : (112.5 : ℝ) * d < (Nat.min p q : ℝ) := by
    have hle : (112.5 : ℝ) * d ≤ Submission.countConst * d := by
      rw [Submission.countConst]
      nlinarith [hd]
    linarith
  refine lt_of_le_of_lt (encard_range_inter_le_param K _) ?_
  exact Work.BoxShrink.Core.encard_lt_of_coe_le_ofReal (n := Nat.min p q)
    (ne_of_gt (lt_min hp hq)) hpar hmin

/-- **The trace `F ∩ ∂PBox s c σ` carries no essential loop**, from the crux's sphere count, the
general position of the box sphere and the *weak* cut-and-paste input.  This is
`Work.PinchCounted.sphereTrace_inessential_of_counts` with `Work.InnermostDisk.CleansDiscs` replaced
by `Work.Drive.CleansDiscsW` — the hypothesis carried by the ε-form. -/
theorem sphereTrace_inessential_of_countsW
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) := by
  intro hcon
  have hIn : Work.InnermostDisk.InnermostDiscInput (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hslice.some
  obtain ⟨D⟩ := hIn hcon
  exact Work.Drive.not_exists_weakCompressingLoop_of_counts p q hp hq hc ψ K hd himg hsmall
    c σ hcount ⟨D.α, D.simple, D.essential, hcl _ D, D.mem⟩

/-- **Pardon's Lemma 2 for an arbitrary slicing, weak-disc vocabulary.**  Let `S` be sliced by the
surface in general position (`Work.InnermostDisk.SphereSlicing`), suppose the weak cut-and-paste
`Work.Drive.CleansDiscsW` holds, and suppose `S` meets the knot `K` in fewer than `min p q` points.
Then no essential loop of the surface lies in `S`. -/
theorem trace_inessential_of_slicing_of_countsW
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {S : Set R3} (hslice : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ) S)
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcount : Set.encard (Set.range K.curve ∩ S) < (Nat.min p q : ℕ∞)) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop S := by
  intro hcon
  obtain ⟨D⟩ :=
    (Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hslice) hcon
  have hle := Work.Drive.min_le_encard_inter_of_boundsDiskW p q hp hq hc ψ K himg
    D.simple D.essential (hcl S D)
  have hmono : Set.encard (Set.range D.α.γ ∩ Set.range K.curve) ≤
      Set.encard (Set.range K.curve ∩ S) := by
    apply Set.encard_le_encard
    rintro x ⟨⟨t, rfl⟩, hxK⟩
    exact ⟨hxK, D.mem t⟩
  exact absurd (lt_of_le_of_lt (le_trans hle hmono) hcount) (lt_irrefl _)

/-- **The count and Pardon's Lemma 2 compose: any sliced sphere inside the footprint is clean.**
If `S` is a subset of the footprint `sphereSet c σ s ∪ cutDisc s c σ u`, sliced by the surface in
general position, then the crux's two counts (via `footprintCountBound`) show that `S` meets the knot
in fewer than `min p q` points, and Pardon's Lemma 2
(`Work.Drive.EpsForm.trace_inessential_of_slicing_of_countsW`) makes every closed curve of `F` in `S`
inessential.  Both half-spheres `H± = closedUpperCap ∪ closure (cutDisc)` are subsets of the
footprint, so this is the cleanliness of the two spheres at which Pardon's pinch ends, in the form its
consumers (`Work.Drive.PinchArc.halvesSpan_of_cleanHalfSpheres`) use. -/
theorem trace_inessential_of_slicing_of_subset_footprint
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    {S : Set R3}
    (hsub : S ⊆ Work.BoxShrink.Core.sphereSet c σ s ∪ Work.BoxShrink.Core.cutDisc s c σ u)
    (hslice : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ) S)
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcountS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hcountU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop S := by
  refine trace_inessential_of_slicing_of_countsW p q hp hq hc ψ K himg hslice hcl ?_
  refine lt_of_le_of_lt (Set.encard_le_encard ?_) (footprintCountBound p q hp hq K hd hsmall
    c σ u hcountS hcountU)
  rintro x ⟨hxK, hxS⟩
  exact ⟨hxK, hsub hxS⟩

end

end Work.EpsW
