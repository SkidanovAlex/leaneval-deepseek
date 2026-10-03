import Mathlib
import Submission.Work.Pert.RBlock

/-!
# PERT · `Work.Pert.tSat_glue`: gluing `T`-equivariant local maps into one

Suppose a family of open sets `U i ⊆ ℂ` carries holomorphic functions `R i` that are *compatible*
under integers translations: whenever `w ∈ U i` and `w + n ∈ U j` (with `n : ℤ`),

`R j (w + n) = R i w + n`.

Then all the translates `U i + n` fit together into a single open set `D = ⋃ i ⋃ n (U i + n)`
carrying one `T`-equivariant holomorphic map `R'` (`T` acts by `w ↦ w + 1`) which agrees with `R i`
on each `U i`.  The value of `R'` on a translate is forced, and the compatibility hypothesis is
exactly what makes it well defined: if `z = w₁ + n₁ = w₂ + n₂` with `w₁ ∈ U i₁`, `w₂ ∈ U i₂`, then
`w₂ = w₁ + (n₁ - n₂)` and the hypothesis applied to `(i₁, i₂, n₁ - n₂)` gives
`R i₂ w₂ + n₂ = R i₁ w₁ + n₁`.

This is the abstract gluing step behind the construction of the lifted return map `R̃_f` of
Shishikura §4.2: the local charts (gates) are glued along the deck translations `Tt α`.
-/

namespace Work.Pert

open Set

theorem tSat_glue {ι : Type*} (U : ι → Set ℂ) (R : ι → ℂ → ℂ)
    (hU : ∀ i, IsOpen (U i)) (hR : ∀ i, DifferentiableOn ℂ (R i) (U i))
    (hcompat : ∀ i j (n : ℤ) (w : ℂ), w ∈ U i → w + (n : ℂ) ∈ U j →
      R j (w + (n : ℂ)) = R i w + (n : ℂ)) :
    ∃ R' : ℂ → ℂ, IsOpen (⋃ i, ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' U i) ∧
      MandelDim.IsTEquivariantOn R' (⋃ i, ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' U i) ∧
      DifferentiableOn ℂ R' (⋃ i, ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' U i) ∧
      ∀ i, ∀ w ∈ U i, R' w = R i w := by
  classical
  -- the translates of the local domains, and their union
  let V : ι → ℤ → Set ℂ := fun i n => (fun w => w + (n : ℂ)) '' U i
  let D : Set ℂ := ⋃ i, ⋃ n : ℤ, V i n
  -- the "value at `z` coming from the chart `i` at level `n`"
  let P : ℂ → ℂ → Prop := fun z v =>
    ∃ (i : ι) (n : ℤ) (w : ℂ), w ∈ U i ∧ w + (n : ℂ) = z ∧ v = R i w + (n : ℂ)
  have hD : ∀ z : ℂ, z ∈ D ↔ ∃ (i : ι) (n : ℤ) (w : ℂ), w ∈ U i ∧ w + (n : ℂ) = z := by
    intro z
    simp only [D, V, mem_iUnion, mem_image]
  have hP_ex : ∀ z : ℂ, z ∈ D → ∃ v, P z v := by
    intro z hz
    rw [hD] at hz
    obtain ⟨i, n, w, hw, hwz⟩ := hz
    exact ⟨R i w + (n : ℂ), i, n, w, hw, hwz, rfl⟩
  -- the compatibility hypothesis makes the value well defined
  have hwd : ∀ z v v', P z v → P z v' → v = v' := by
    intro z v v' h1 h2
    simp only [P] at h1 h2
    obtain ⟨i₁, n₁, w₁, hw₁, hz₁, hv₁⟩ := h1
    obtain ⟨i₂, n₂, w₂, hw₂, hz₂, hv₂⟩ := h2
    have hw₂' : w₂ = w₁ + ((n₁ - n₂ : ℤ) : ℂ) := by
      have hz2' : w₂ = z - (n₂ : ℂ) := by rw [← hz₂]; ring
      rw [hz2', ← hz₁, Int.cast_sub]; ring
    have hmem : w₁ + ((n₁ - n₂ : ℤ) : ℂ) ∈ U i₂ := by rw [← hw₂']; exact hw₂
    have hc := hcompat i₁ i₂ (n₁ - n₂) w₁ hw₁ hmem
    have hc' : R i₂ w₂ = R i₁ w₁ + ((n₁ - n₂ : ℤ) : ℂ) := by rw [hw₂']; exact hc
    rw [hv₁, hv₂, hc', Int.cast_sub]
    ring
  -- the glued function: pick any chart representing `z`
  let R' : ℂ → ℂ := fun z => if h : z ∈ D then Classical.choose (hP_ex z h) else 0
  have hR'_val : ∀ z (hz : z ∈ D), R' z = Classical.choose (hP_ex z hz) := by
    intro z hz
    dsimp only [R']
    rw [dite_eq_left hz]
  have hR'_spec : ∀ z (hz : z ∈ D), P z (R' z) := by
    intro z hz
    rw [hR'_val z hz]
    exact Classical.choose_spec (hP_ex z hz)
  have hR'_eq : ∀ i (w : ℂ), w ∈ U i → R' w = R i w := by
    intro i w hw
    have hwD : w ∈ D := by rw [hD]; exact ⟨i, 0, w, hw, by simp⟩
    have h1 : P w (R' w) := hR'_spec w hwD
    have h2 : P w (R i w) := ⟨i, 0, w, hw, by simp, by simp⟩
    exact hwd w (R' w) (R i w) h1 h2
  -- `D` is invariant under `T`
  have hT : MandelDim.IsTInvariant D := by
    intro z
    rw [hD, hD]
    constructor
    · rintro ⟨i, n, w, hw, hwz⟩
      exact ⟨i, n + 1, w, hw, by rw [Int.cast_add, Int.cast_one, ← hwz]; ring⟩
    · rintro ⟨i, n, w, hw, hwz⟩
      refine ⟨i, n - 1, w, hw, ?_⟩
      have hz : z = w + (n : ℂ) - 1 := by rw [eq_sub_iff_add_eq, ← hwz]
      rw [hz, Int.cast_sub, Int.cast_one]; ring
  -- `R'` is `T`-equivariant
  have hEq : ∀ z ∈ D, R' (z + 1) = R' z + 1 := by
    intro z hz
    have hz' : P z (R' z) := hR'_spec z hz
    simp only [P] at hz'
    obtain ⟨i, n, w, hw, hwz, hv⟩ := hz'
    have hz1mem : z + 1 ∈ D := by
      rw [hD]
      exact ⟨i, n + 1, w, hw, by rw [Int.cast_add, Int.cast_one, ← hwz]; ring⟩
    have h1 : P (z + 1) (R' (z + 1)) := hR'_spec (z + 1) hz1mem
    have h2 : P (z + 1) (R' z + 1) := by
      refine ⟨i, n + 1, w, hw, ?_, ?_⟩
      · rw [Int.cast_add, Int.cast_one, ← hwz]; ring
      · rw [hv, Int.cast_add, Int.cast_one]; ring
    exact hwd (z + 1) (R' (z + 1)) (R' z + 1) h1 h2
  have hVopen : ∀ i n, IsOpen (V i n) := by
    intro i n
    show IsOpen ((fun w => w + (n : ℂ)) '' U i)
    exact (Homeomorph.addRight (n : ℂ)).isOpen_image.mpr (hU i)
  have hGlue : ∀ (i : ι) (n : ℤ),
      DifferentiableOn ℂ (fun z : ℂ => R i (z - (n : ℂ)) + (n : ℂ)) (V i n) := by
    intro i n
    have hsub : DifferentiableOn ℂ (fun z : ℂ => z - (n : ℂ)) (V i n) :=
      differentiableOn_id.sub_const _
    have hmap : MapsTo (fun z : ℂ => z - (n : ℂ)) (V i n) (U i) := by
      rintro z hz
      simp only [V, mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      simpa using hw
    have hcomp := (hR i).comp hsub hmap
    simpa [Function.comp] using hcomp.add_const (n : ℂ)
  have hDopen : IsOpen D := by
    simp only [D]
    exact isOpen_iUnion (fun i => isOpen_iUnion (fun n => hVopen i n))
  -- local differentiability on each translate, hence on `D`
  have hDiff : DifferentiableOn ℂ R' D := by
    apply differentiableOn_of_locally_differentiableOn
    intro x hx
    rw [hD] at hx
    obtain ⟨i, n, w, hw, hwx⟩ := hx
    refine ⟨V i n, hVopen i n, ⟨w, hw, hwx⟩, ?_⟩
    have hVsubD : V i n ⊆ D := by
      intro z hz
      rw [hD]
      simp only [V, mem_image] at hz
      obtain ⟨w', hw', rfl⟩ := hz
      exact ⟨i, n, w', hw', rfl⟩
    have hcongr : ∀ z ∈ V i n, R' z = (fun z : ℂ => R i (z - (n : ℂ)) + (n : ℂ)) z := by
      intro z hz
      have hzD : z ∈ D := hVsubD hz
      have h1 : P z (R' z) := hR'_spec z hzD
      have h2 : P z (R i (z - (n : ℂ)) + (n : ℂ)) := by
        simp only [V, mem_image] at hz
        obtain ⟨w', hw', rfl⟩ := hz
        refine ⟨i, n, w', hw', rfl, ?_⟩
        simp
      exact hwd z (R' z) _ h1 h2
    have hVdiff : DifferentiableOn ℂ R' (V i n) := (hGlue i n).congr hcongr
    exact hVdiff.mono (inter_subset_right)
  refine ⟨R', ?_, ?_, ?_, ?_⟩
  · exact hDopen
  · exact ⟨hT, hEq⟩
  · exact hDiff
  · exact hR'_eq

end Work.Pert
