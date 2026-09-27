import Mathlib
import Submission.Work.Sard.block_fderiv_prodMk

namespace Work.Sard

/-- **Slice lemma.**  Suppose the theorem "critical values have empty interior" is known for smooth maps
`C → W` (hypothesis `IH`).  Then for any smooth `g : G × C → W` and compact `L`, the set of critical
values of `z ↦ (z.1, g z)` on `L` has empty interior.

Proof sketch: write `Ψ := fun z : G × C => (z.1, g z)`.  By the workspace lemma
`Work.Sard.block_fderiv_prodMk` (file `Submission/Work/Sard/block_fderiv_prodMk.lean`, sorry-free;
`hg` provides the differentiability hypothesis), `z` is critical for `Ψ` iff `z.2` is critical for the
slice map `c ↦ g (z.1, c)`.  Hence
`Ψ '' (crit Ψ ∩ L) = ⋃ w, ({w} : Set G) ×ˢ S w` where
`S w := (fun c => g (w, c)) '' ({c : C | ¬ Surjective (fderiv ℝ (fun c => g (w,c)) c)} ∩ {c | (w,c) ∈ L})`
is the set of critical values of a smooth map `C → W` on the compact set `{c | (w,c) ∈ L}` (compact since
`L` is compact and `c ↦ (w,c)` is a closed embedding), so `interior (S w) = ∅` by `IH`.
Finish with the purely topological lemma (prove it inline; it is `interior_iUnion_slices_eq_empty` in
`Submission/Work/Drive/sard_weak_empty_interior.lean` but that file still contains `sorry`s, so do NOT
import it): if every slice `S w` has empty interior then `interior (⋃ w, {w} ×ˢ S w) = ∅` — indeed a
product neighbourhood `U ×ˢ V ⊆ ⋃ w, {w} ×ˢ S w` would force `V ⊆ S w` for every `w ∈ U`
(because `(w, y) ∈ {w} ×ˢ S w` for `w` the first coordinate), giving `S w` nonempty interior,
contradiction.

The argument is carried out below in the "pointwise" form of the box argument: if
`(x, y) ∈ interior (Ψ '' (crit Ψ ∩ L))`, then the set
`V := {b : W | (x, b) ∈ interior (Ψ '' (crit Ψ ∩ L))}` is an open neighbourhood of `y` contained in the
slice `S x`, whence `y ∈ interior (S x)`, contradicting `IH`.  The inclusion `V ⊆ S x` is where
`block_fderiv_prodMk` is used: a point of `Ψ '' (crit Ψ ∩ L)` with first coordinate `x` is the image of
some `z` with `z.1 = x` which is critical for `Ψ`, hence its second coordinate is critical for the slice
map `c ↦ g (x, c)`. -/
theorem slice_image_interior_eq_empty {G C W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {m' : ℕ}
    (hC : Module.finrank ℝ C = m' + 1) (hW : Module.finrank ℝ W = m')
    (IH : ∀ (g : C → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ L : Set C, IsCompact L →
      interior (g '' ({x : C | ¬ Function.Surjective (fderiv ℝ g x)} ∩ L)) = ∅)
    (g : G × C → W) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (L : Set (G × C))
    (hL : IsCompact L) :
    interior ((fun z : G × C => (z.1, g z)) ''
      ({z : G × C |
        ¬ Function.Surjective (fderiv ℝ (fun z : G × C => (z.1, g z)) z)} ∩ L)) = ∅ := by
  classical
  -- `ψ` is the map whose critical values we study.
  set F : G × C → G × W := fun z => (z.1, g z) with hF
  -- It suffices to show that the interior has no points.
  refine Set.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨⟨x, y⟩, hy⟩
  -- `g` is differentiable (at every point), so the block lemma applies.
  have hdiff : ∀ z : G × C, DifferentiableAt ℝ g z :=
    fun z => hg.contDiffAt.differentiableAt (by simp)
  -- Criticality of `F` at `z` is criticality of the slice map `c ↦ g (z.1, c)` at `z.2`.
  have hcrit : ∀ z : G × C, (¬ Function.Surjective (fderiv ℝ F z)) ↔
      (¬ Function.Surjective (fderiv ℝ (fun c : C => g (z.1, c)) z.2)) := by
    intro z
    have h := block_fderiv_prodMk g z (hdiff z)
    rw [hF]
    exact not_congr h
  -- The slice `S x` through the first coordinate `x` of the alleged interior point, on the compact
  -- set `{c | (x, c) ∈ L}`, has empty interior by the induction hypothesis.
  have hslice : interior ((fun c : C => g (x, c)) ''
      ({c : C | ¬ Function.Surjective (fderiv ℝ (fun c : C => g (x, c)) c)} ∩
        {c : C | (x, c) ∈ L})) = ∅ := by
    refine IH (fun c : C => g (x, c)) ?_ {c : C | (x, c) ∈ L} ?_
    · exact hg.comp (contDiff_const.prodMk contDiff_id)
    · -- `c ↦ (x, c)` is a closed embedding, so the slice of the compact set `L` is compact.
      have hce : Topology.IsClosedEmbedding (fun c : C => (x, c)) := by
        refine ⟨isEmbedding_prodMkRight x, ?_⟩
        have hrange : Set.range (fun c : C => (x, c)) =
            ({x} : Set G) ×ˢ (Set.univ : Set C) := by
          ext p
          constructor
          · rintro ⟨c, rfl⟩
            simp
          · intro hp
            simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hp
            exact ⟨p.2, by rw [← hp]⟩
        rw [hrange]
        exact isClosed_singleton.prod isClosed_univ
      exact hce.isCompact_preimage hL
  -- A point of `F '' (crit F ∩ L)` whose first coordinate is `x` lies in the slice `S x`.
  have hVsub : {b : W | (x, b) ∈
        interior (F '' ({z : G × C | ¬ Function.Surjective (fderiv ℝ F z)} ∩ L))}
      ⊆ (fun c : C => g (x, c)) ''
        ({c : C | ¬ Function.Surjective (fderiv ℝ (fun c : C => g (x, c)) c)} ∩
          {c : C | (x, c) ∈ L}) := by
    intro b hb
    have hb' : (x, b) ∈ F '' ({z : G × C | ¬ Function.Surjective (fderiv ℝ F z)} ∩ L) :=
      interior_subset hb
    obtain ⟨z, hz, hzF⟩ := hb'
    obtain ⟨hzcrit, hzL⟩ := hz
    have hz1 : z.1 = x := congrArg Prod.fst hzF
    have hz2 : g z = b := congrArg Prod.snd hzF
    have hzeq : (x, z.2) = z := by rw [← hz1]
    refine ⟨z.2, ⟨?_, ?_⟩, ?_⟩
    · -- `z.2` is critical for the slice map at `x`
      have h := (hcrit z).mp hzcrit
      rwa [hz1] at h
    · show (x, z.2) ∈ L
      simpa [hzeq] using hzL
    · show g (x, z.2) = b
      simpa [hzeq] using hz2
  -- The set `V` of second coordinates over `x` in the interior is open and contains `y`.
  have hyV : y ∈ {b : W | (x, b) ∈
      interior (F '' ({z : G × C | ¬ Function.Surjective (fderiv ℝ F z)} ∩ L))} := hy
  have hVopen : IsOpen {b : W | (x, b) ∈
      interior (F '' ({z : G × C | ¬ Function.Surjective (fderiv ℝ F z)} ∩ L))} :=
    isOpen_interior.preimage (continuous_const.prodMk continuous_id)
  have hyint : y ∈ interior ((fun c : C => g (x, c)) ''
      ({c : C | ¬ Function.Surjective (fderiv ℝ (fun c : C => g (x, c)) c)} ∩
        {c : C | (x, c) ∈ L})) :=
    interior_maximal hVsub hVopen hyV
  rw [hslice] at hyint
  simp at hyint

end Work.Sard
