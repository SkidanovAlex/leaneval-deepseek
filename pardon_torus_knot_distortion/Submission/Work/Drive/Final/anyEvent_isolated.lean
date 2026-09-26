import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.SweepGeom3

/-!
# The events of the tilted sweep are isolated

`Work.Drive.Final.anyEvent_isolated`: at every event `pp` of the tilted sweep there is a radius
`r₁ > 0` (in *space*, i.e. for the images `par ψ ·` of parameter points) such that every event whose
image is within `r₁` of the image of `pp` has the *same* image.

The statement says that the image `par ψ pp` of an event is isolated in the set

  `Z := {par ψ p | p is an event}`

of event images.  The proof has two halves.

**Finiteness of `Z`.**  Two ingredients of the datum `GoodDataPackage3` combine:

* *every event value lies in the exceptional set `exc`*: the three event types are covered by the
  three value clauses of the bundle —
  - `IsEvent` (a critical point of the sweep height in the box ∩ closed slab): clause (iii) of
    `TiltedGenericity` (part of `TiltData`, hence of the datum) puts the critical value in `exc`;
  - `IsFaceEvent` (a tangency of the level with a slab face): clause (ii) of `TiltedGenericity`
    says that at a level *outside* `exc` the sweep height is never parallel to the slab functional
    on the slab faces, so a face event with a value outside `exc` cannot exist: its value too lies
    in `exc`.  (The slab functional of the criterion is `q ↦ ⟪v, par ψ q⟫`, whose derivative is
    that of `slabFnPar ψ c u v`; the two differ by the constant `⟪v,c⟫ + u`.)
  - `IsCornerEvent` (a point of the surface on the box sphere ∩ a slab face): clause (d) of
    `JunctionGenC` (also part of the datum) puts the value of every such *point* in `exc`.
* *one event per level* (a clause of `GoodSweepData3`): two events of the same value have the same
  image.  Hence `ℓ` is injective on `Z` while `ℓ '' Z ⊆ exc` is finite, so `Z` is finite.

**Isolation.**  `Z` is finite and `par ψ pp ∈ Z`; the distance from `par ψ pp` to the finite set
`Z \ {par ψ pp}` attains a positive minimum `ρ`, and `r₁ := ρ / 2` works.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- The slab functional of the *criterion* `TiltedGenericity` (clause (ii)) is `q ↦ ⟪v, par ψ q⟫`;
its derivative is that of `slabFnPar ψ c u v` (the two differ by the constant `⟪v,c⟫ + u`). -/
theorem fderiv_slabFnPar_eq (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3) (p : ℝ × ℝ) :
    fderiv ℝ (slabFnPar ψ c u v) p =
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
  have h : slabFnPar ψ c u v =
      fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u) := rfl
  rw [h, fderiv_sub_const]

/-- **The value of every event lies in the exceptional set** `exc`. -/
theorem eventValue_mem_exc {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {p' : ℝ × ℝ} (hp' : IsAnyEvent ψ s c σ u v h ℓ p') :
    ℓ (Work.BoxShrink.Pinch.par ψ p') ∈ (exc : Set ℝ) := by
  have hgen : TiltedGenericity ψ s c σ u v h ℓ exc := hDP.1.tilt.1
  have hjg : Work.Drive.Mono.JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1 := hDP.1.junc
  rcases hp' with h1 | h2 | h3
  · -- an interior critical point: clause (iii) of `TiltedGenericity`
    exact (hgen.2.2.1 p' h1.1 h1.2.1 h1.2.2).2
  · -- a tangency on a slab face: clause (ii) of `TiltedGenericity`
    by_contra hne
    obtain ⟨t, ht⟩ := h2.2.2
    refine hgen.2.1 (ℓ (Work.BoxShrink.Pinch.par ψ p')) hne p' h2.1 h2.2.1 rfl t ?_
    rw [ht, fderiv_slabFnPar_eq]
  · -- a point on the box sphere ∩ a slab face: clause (d) of `JunctionGenC`
    exact hjg.2.2.2 (Work.BoxShrink.Pinch.par ψ p')
      (Work.BoxShrink.Pinch.par_mem_carrier ψ p') h3.2.1 h3.2.2

/-- **The set of event images is finite.** -/
theorem finite_eventImages {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    {z : R3 | ∃ p' : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p' ∧
      Work.BoxShrink.Pinch.par ψ p' = z}.Finite := by
  obtain ⟨-, -, -, -, -, -, -, -, hone, -⟩ := hDP.2.1
  set Z : Set R3 := {z : R3 | ∃ p' : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p' ∧
    Work.BoxShrink.Pinch.par ψ p' = z} with hZ
  refine Set.Finite.of_finite_image (f := fun z : R3 => ℓ z) ?_ ?_
  · -- the value map takes the event images into the finite set `exc`
    refine Set.Finite.subset (Finset.finite_toSet exc) ?_
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨p', hp', rfl⟩ := hz
    exact eventValue_mem_exc hDP hp'
  · -- two events of the same value have the same image
    rintro z₁ hz₁ z₂ hz₂ heq
    obtain ⟨p₁, hp₁, rfl⟩ := hz₁
    obtain ⟨p₂, hp₂, rfl⟩ := hz₂
    exact hone p₁ p₂ hp₁ hp₂ heq

theorem anyEvent_isolated {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pp : ℝ × ℝ} (hp : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
      ‖Work.BoxShrink.Pinch.par ψ p' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ r₁ →
      Work.BoxShrink.Pinch.par ψ p' = Work.BoxShrink.Pinch.par ψ pp := by
  have hZfin : {z : R3 | ∃ p' : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p' ∧
      Work.BoxShrink.Pinch.par ψ p' = z}.Finite := finite_eventImages hDP
  set Z : Set R3 := {z : R3 | ∃ p' : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p' ∧
    Work.BoxShrink.Pinch.par ψ p' = z} with hZ
  have hz₀ : Work.BoxShrink.Pinch.par ψ pp ∈ Z := ⟨pp, hp, rfl⟩
  have hZ'fin : (Z \ {Work.BoxShrink.Pinch.par ψ pp}).Finite := hZfin.sdiff
  rcases Set.eq_empty_or_nonempty (Z \ {Work.BoxShrink.Pinch.par ψ pp}) with hempty | hne
  · -- nothing else: any positive radius works
    refine ⟨1, one_pos, ?_⟩
    intro p' hp' _
    by_contra hcontr
    have hmem : Work.BoxShrink.Pinch.par ψ p' ∈ Z \ {Work.BoxShrink.Pinch.par ψ pp} :=
      ⟨⟨p', hp', rfl⟩, by simpa only [Set.mem_singleton_iff] using hcontr⟩
    rw [hempty] at hmem
    exact hmem
  · -- the distance to the remaining finite set attains a positive minimum
    obtain ⟨y₀, hy₀, hmin⟩ := hZ'fin.isCompact.exists_isMinOn hne
      ((continuous_id.sub continuous_const).norm.continuousOn)
    have hy₀ne : y₀ ≠ Work.BoxShrink.Pinch.par ψ pp :=
      fun h => hy₀.2 (by simpa only [Set.mem_singleton_iff] using h)
    have hpos : 0 < ‖y₀ - Work.BoxShrink.Pinch.par ψ pp‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact hy₀ne
    refine ⟨‖y₀ - Work.BoxShrink.Pinch.par ψ pp‖ / 2, half_pos hpos, ?_⟩
    intro p' hp' hle
    by_contra hcontr
    have hmem : Work.BoxShrink.Pinch.par ψ p' ∈ Z \ {Work.BoxShrink.Pinch.par ψ pp} :=
      ⟨⟨p', hp', rfl⟩, by simpa only [Set.mem_singleton_iff] using hcontr⟩
    have h1 : ‖y₀ - Work.BoxShrink.Pinch.par ψ pp‖ ≤
        ‖Work.BoxShrink.Pinch.par ψ p' - Work.BoxShrink.Pinch.par ψ pp‖ := hmin hmem
    linarith

end

end Work.Drive.Final
