import Mathlib
import Submission.Work.Drive.Mono.isEmbeddedSphere_of_twoDiscs
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_eq_caps
import Submission.Work.JordanBrouwer3.sphereSides_boxSphere

/-!
# The pieces of the frontier of a level of the tilted sweep (the "one-sphere window")

Vocabulary and the set-theoretic part of `Work.Drive.Final.tls_twoDiscs_crux`.

The frontier of `Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is, in the window of the
hypotheses of that theorem, the union of two closed pieces glued along a common circle, each of
which is a topologist's disc:

* `tlsSeam` — the circle along which the box sphere meets the boundary of the chunk;
* `tlsOuter` — the part of the box sphere outside the chunk, closed up;
* `tlsTrough` — the boundary of the chunk inside the box (the wall together with the two slab
  faces).

Proved here: `v ≠ 0`, the `SlabCutsBox` and "above the wall" inputs of the caps identity, the
*window* facts (a point of the open box on each slab face at the level *above* the wall), the
identity `frontier = tlsOuter ∪ tlsTrough`, and `tlsOuter ∩ tlsTrough = tlsSeam`.
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Final

noncomputable section

/-- The closed slab of the tilted sweep: `{|⟪v,·⟫ - a| ≤ h}`. -/
abbrev tlsSlab (a h : ℝ) (v : R3) : Set R3 := {y : R3 | |inner ℝ v y - a| ≤ h}

/-- The wall: the sublevel set of the level functional. -/
abbrev tlsWall (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 := {y : R3 | ℓ y ≤ lam}

/-- The boundary of the slab: its two faces. -/
abbrev tlsSlabBdry (a h : ℝ) (v : R3) : Set R3 := {y : R3 | |inner ℝ v y - a| = h}

/-- The **chunk**: the closed convex piece of the box cut out by the slab and the wall. -/
abbrev tlsChunk (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set R3 :=
  closure (Submission.PBox s c σ) ∩ tlsSlab (inner ℝ v c + u) h v ∩ tlsWall ℓ lam

/-- The **seam**: the circle along which the box sphere meets the boundary of the chunk. -/
abbrev tlsSeam (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set R3 :=
  Work.Topology.SphereSlicing.BoxSphere s c σ ∩ tlsChunk s c σ u h lam v ℓ ∩
    (tlsSlabBdry (inner ℝ v c + u) h v ∪ {y : R3 | ℓ y = lam})

/-- The **outer piece**: the part of the box sphere outside the chunk, closed up. -/
abbrev tlsOuter (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set R3 :=
  (Work.Topology.SphereSlicing.BoxSphere s c σ \ tlsChunk s c σ u h lam v ℓ) ∪
    tlsSeam s c σ u h lam v ℓ

/-- The **trough**: the boundary of the chunk inside the box. -/
abbrev tlsTrough (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set R3 :=
  tlsChunk s c σ u h lam v ℓ ∩
    (tlsSlabBdry (inner ℝ v c + u) h v ∪ {y : R3 | ℓ y = lam})

/-- **`v ≠ 0` is forced by the window hypotheses.** -/
theorem tls_v_ne_zero {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h : ℝ} {v : R3}
    (hh : 0 < h)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h) : v ≠ 0 := by
  intro hv
  obtain ⟨y, -, hy⟩ := hwinP
  obtain ⟨y', -, hy'⟩ := hwinM
  rw [hv, inner_zero_left, inner_zero_left] at hy hy'
  linarith

/-- The `SlabCutsBox` input of the caps identity, from the two window hypotheses. -/
theorem tls_slabCutsBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h : ℝ} {v : R3}
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h) :
    Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v :=
  ⟨hwinP, hwinM⟩

/-- The "above the wall" input of the caps identity, from `hwallP`. -/
theorem tls_above {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ} {v : R3}
    {ℓ : R3 →L[ℝ] ℝ}
    (hwallP : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y) :
    ∃ y : R3, y ∈ Submission.PBox s c σ ∧ lam < ℓ y := by
  obtain ⟨y, hy, -, hyl⟩ := hwallP
  exact ⟨y, hy, hyl⟩

/-- **The window fact**: the two wall hypotheses force a point of the open box on the upper slab
face, strictly above the wall. -/
theorem tls_exists_face_above {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ} {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hh : 0 < h)
    (hwallP : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) :
    ∃ z ∈ Submission.PBox s c σ,
      inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z := by
  obtain ⟨y, hy, hyp, hyl⟩ := hwallP
  obtain ⟨y', hy', hy'p, hy'l⟩ := hwallM
  set f : ℝ → R3 := fun t => y' + t • (y - y') with hf
  have hf0 : f 0 = y' := by simp [hf]
  have hf1 : f 1 = y := by simp [hf]
  have hcont : Continuous fun t : ℝ => inner ℝ v (f t) - (inner ℝ v c + u + h) := by
    fun_prop
  have h0 : inner ℝ v (f 0) - (inner ℝ v c + u + h) ≤ 0 := by rw [hf0]; linarith
  have h1 : 0 ≤ inner ℝ v (f 1) - (inner ℝ v c + u + h) := by rw [hf1]; linarith
  obtain ⟨t₀, ht₀_mem, ht₀⟩ :=
    intermediate_value_Icc (le_of_lt zero_lt_one) hcont.continuousOn ⟨h0, h1⟩
  refine ⟨f t₀, ?_, by linarith [ht₀], ?_⟩
  · have hconv : Convex ℝ (Submission.PBox s c σ) := Work.Topology.SphereSlicing.convex_PBox s c σ
    have hft : f t₀ = (1 - t₀) • y' + t₀ • y := by
      simp only [hf]
      module
    rw [hft]
    exact hconv hy' hy (by linarith [ht₀_mem.2]) ht₀_mem.1 (by ring)
  · have haff : ℓ (f t₀) = (1 - t₀) * ℓ y' + t₀ * ℓ y := by
      simp only [hf, map_add, map_sub, map_smul, smul_eq_mul]
      ring
    rw [haff]
    have hA : (1 - t₀) * lam ≤ (1 - t₀) * ℓ y' :=
      mul_le_mul_of_nonneg_left (le_of_lt hy'l) (by linarith [ht₀_mem.2])
    have hB : t₀ * lam ≤ t₀ * ℓ y := mul_le_mul_of_nonneg_left (le_of_lt hyl) ht₀_mem.1
    nlinarith [hA, hB]

/-- The same on the lower slab face. -/
theorem tls_exists_face_above_minus {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ}
    {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hh : 0 < h)
    (hwallP : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) :
    ∃ z ∈ Submission.PBox s c σ,
      inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z := by
  obtain ⟨y, hy, hyp, hyl⟩ := hwallP
  obtain ⟨y', hy', hy'p, hy'l⟩ := hwallM
  set f : ℝ → R3 := fun t => y + t • (y' - y) with hf
  have hf0 : f 0 = y := by simp [hf]
  have hf1 : f 1 = y' := by simp [hf]
  have hcont : Continuous fun t : ℝ => inner ℝ v (f t) - (inner ℝ v c + u - h) := by
    fun_prop
  have h0 : 0 ≤ inner ℝ v (f 0) - (inner ℝ v c + u - h) := by rw [hf0]; linarith
  have h1 : inner ℝ v (f 1) - (inner ℝ v c + u - h) ≤ 0 := by rw [hf1]; linarith
  obtain ⟨t₀, ht₀_mem, ht₀⟩ :=
    intermediate_value_Icc' (le_of_lt zero_lt_one) hcont.continuousOn ⟨h1, h0⟩
  refine ⟨f t₀, ?_, by linarith [ht₀], ?_⟩
  · have hconv : Convex ℝ (Submission.PBox s c σ) := Work.Topology.SphereSlicing.convex_PBox s c σ
    have hft : f t₀ = (1 - t₀) • y + t₀ • y' := by
      simp only [hf]
      module
    rw [hft]
    exact hconv hy hy' (by linarith [ht₀_mem.2]) ht₀_mem.1 (by ring)
  · have haff : ℓ (f t₀) = (1 - t₀) * ℓ y + t₀ * ℓ y' := by
      simp only [hf, map_add, map_sub, map_smul, smul_eq_mul]
      ring
    rw [haff]
    have hA : (1 - t₀) * lam ≤ (1 - t₀) * ℓ y :=
      mul_le_mul_of_nonneg_left (le_of_lt hyl) (by linarith [ht₀_mem.2])
    have hB : t₀ * lam ≤ t₀ * ℓ y' := mul_le_mul_of_nonneg_left (le_of_lt hy'l) ht₀_mem.1
    nlinarith [hA, hB]

/-- The seam is contained in the trough. -/
theorem tls_seam_subset_trough (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ)
    (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    tlsSeam s c σ u h lam v ℓ ⊆ tlsTrough s c σ u h lam v ℓ := by
  intro y hy
  exact ⟨hy.1.2, hy.2⟩

/-- The outer piece together with the trough, in the form in which the caps identity gives the
frontier: the seam is absorbed by the trough. -/
theorem tls_outer_union_trough_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ)
    (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    tlsOuter s c σ u h lam v ℓ ∪ tlsTrough s c σ u h lam v ℓ =
      (Work.Topology.SphereSlicing.BoxSphere s c σ \ tlsChunk s c σ u h lam v ℓ) ∪
        tlsTrough s c σ u h lam v ℓ := by
  have hseam := tls_seam_subset_trough s c σ u h lam v ℓ
  ext y
  constructor
  · intro hy
    rcases hy with hleft | htr
    · rcases hleft with ⟨hyb, hyc⟩ | hys
      · exact Or.inl ⟨hyb, hyc⟩
      · exact Or.inr (hseam hys)
    · exact Or.inr htr
  · intro hy
    rcases hy with ⟨hyb, hyc⟩ | htr
    · exact Or.inl (Or.inl ⟨hyb, hyc⟩)
    · exact Or.inr htr

/-- **The frontier is the union of the outer piece and the trough.**  This is the caps identity
`Work.Drive.Mono.frontier_tiltedLevelRemoved_eq_caps` in the vocabulary of this module. -/
theorem tls_frontier_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hs : 0 < s) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hwallP : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h) :
    frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
      tlsOuter s c σ u h lam v ℓ ∪ tlsTrough s c σ u h lam v ℓ := by
  have hcaps := Work.Drive.Mono.frontier_tiltedLevelRemoved_eq_caps s u h lam c v σ ℓ hs hh
    (tls_v_ne_zero (s := s) (c := c) (σ := σ) (u := u) (h := h) hh hwinP hwinM) hℓv hℓne
    (tls_slabCutsBox hwinP hwinM) (tls_above hwallP)
  have hfront : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
      (Work.Topology.SphereSlicing.BoxSphere s c σ \ tlsChunk s c σ u h lam v ℓ) ∪
        tlsTrough s c σ u h lam v ℓ := by
    rw [hcaps, Work.JordanBrouwer3.frontier_closure_PBox hs c σ]
  exact hfront.trans (tls_outer_union_trough_eq s c σ u h lam v ℓ).symm

/-- **The two pieces meet exactly in the seam.** -/
theorem tls_outer_inter_trough (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ)
    (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    tlsOuter s c σ u h lam v ℓ ∩ tlsTrough s c σ u h lam v ℓ =
      tlsSeam s c σ u h lam v ℓ := by
  ext y
  constructor
  · rintro ⟨hy, htr⟩
    rcases hy with ⟨hyb, hyc⟩ | hys
    · exact absurd htr.1 hyc
    · exact hys
  · intro hy
    exact ⟨Or.inr hy, tls_seam_subset_trough s c σ u h lam v ℓ hy⟩

end

end Work.Drive.Final
