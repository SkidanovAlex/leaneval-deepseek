import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Slicing the Minkowski sum `M + S` along the coordinates that `M` does not see

Auxiliary definitions and lemmas for `Work.BW.Minkowski2.slicing_scaleFirst`.

Given `d i : ℕ`, the index set `Fin d` splits into
* `Xidx d i = {j : Fin d // (j : ℕ) < i}`, the coordinates that `Work.BW.scaleFirst i ρ` dilates,
* `Yidx d i = {j : Fin d // ¬ (j : ℕ) < i}`, the coordinates it leaves fixed.
A finite set `M` whose points vanish on `Yidx d i` therefore lives in the `Xidx`-coordinates.

`Phi d i` reindexes `Fin d → ℝ` as the product `(Xidx d i → ℝ) × (Yidx d i → ℝ)`; it is a
measure preserving linear equivalence, additive and `ℝ`-homogeneous.  It turns `M + S` into
`(Phi '' M) + (Phi '' S)` where all points of `Phi '' M` have vanishing second coordinate, and it
turns `scaleFirst i ρ '' S` into the set obtained from `Phi '' S` by dilating the first coordinate
by `ρ` (`scaleX ρ`).
-/

namespace Work.BW.Minkowski2

open MeasureTheory

/-- The coordinates `j` with `(j : ℕ) < i`, i.e. those dilated by `Work.BW.scaleFirst i ρ`. -/
abbrev Xidx (d i : ℕ) : Type := {j : Fin d // (j : ℕ) < i}

/-- The coordinates `j` with `¬ (j : ℕ) < i`, i.e. those kept fixed by `Work.BW.scaleFirst i ρ`.
These are the coordinates on which the points of `M` are known to vanish. -/
abbrev Yidx (d i : ℕ) : Type := {j : Fin d // ¬ (j : ℕ) < i}

/-- The coordinate splitting `(Fin d → ℝ) ≃ (Xidx d i → ℝ) × (Yidx d i → ℝ)`. -/
noncomputable abbrev Phi (d i : ℕ) : (Fin d → ℝ) ≃ᵐ (Xidx d i → ℝ) × (Yidx d i → ℝ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (fun j : Fin d => (j : ℕ) < i)

/-- `Phi d i` preserves Lebesgue measure. -/
theorem measurePreserving_Phi (d i : ℕ) : MeasurePreserving (Phi d i) :=
  volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (fun j : Fin d => (j : ℕ) < i)

@[simp] theorem Phi_fst (d i : ℕ) (x : Fin d → ℝ) : (Phi d i x).1 = fun j => x j.1 := rfl

@[simp] theorem Phi_snd (d i : ℕ) (x : Fin d → ℝ) : (Phi d i x).2 = fun j => x j.1 := rfl

/-- `Phi d i` is additive. -/
theorem Phi_add (d i : ℕ) (x y : Fin d → ℝ) : Phi d i (x + y) = Phi d i x + Phi d i y := by
  rw [Prod.ext_iff]; constructor <;> · ext j; rfl

/-- `Phi d i` is `ℝ`-homogeneous. -/
theorem Phi_smul (d i : ℕ) (c : ℝ) (x : Fin d → ℝ) : Phi d i (c • x) = c • Phi d i x := by
  rw [Prod.ext_iff]; constructor <;> · ext j; rfl

/-- `Phi d i` intertwines `Work.BW.scaleFirst i ρ` with the dilation `scaleX ρ` of the first
coordinate. -/
theorem Phi_scaleFirst (d i : ℕ) (ρ : ℝ) (x : Fin d → ℝ) :
    Phi d i (Work.BW.scaleFirst i ρ x) = (ρ • (Phi d i x).1, (Phi d i x).2) := by
  rw [Prod.ext_iff]; constructor
  · ext j
    simp only [Phi_fst, Phi_snd, Pi.smul_apply, smul_eq_mul]
    exact Work.BW.scaleFirst_apply_lt i ρ x j.2
  · ext j
    simp only [Phi_fst, Phi_snd]
    exact Work.BW.scaleFirst_apply_not i ρ x j.2

/-- The dilation of the first coordinate of a product `(ι → ℝ) × (κ → ℝ)` by `ρ`. -/
def scaleX {ι κ : Type*} (ρ : ℝ) : ((ι → ℝ) × (κ → ℝ)) → ((ι → ℝ) × (κ → ℝ)) :=
  fun p => (ρ • p.1, p.2)

@[simp] theorem scaleX_apply {ι κ : Type*} (ρ : ℝ) (p : (ι → ℝ) × (κ → ℝ)) :
    scaleX ρ p = (ρ • p.1, p.2) := rfl

theorem scaleX_add {ι κ : Type*} (ρ : ℝ) (p q : (ι → ℝ) × (κ → ℝ)) :
    scaleX ρ (p + q) = scaleX ρ p + scaleX ρ q := by
  rw [Prod.ext_iff]; constructor <;> · ext j; simp

/-- If the points of `M` vanish on the `Yidx`-coordinates then so do the points of `Phi d i '' M`. -/
theorem Phi_snd_eq_zero (d i : ℕ) (M : Finset (Fin d → ℝ))
    (hM : ∀ x ∈ M, ∀ j : Fin d, i ≤ (j : ℕ) → x j = 0) :
    ∀ p ∈ M.image (Phi d i), p.2 = 0 := by
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  simp only [Phi_snd]
  funext j
  exact hM x hx j.1 (Nat.le_of_not_lt j.2)

/-- `Phi d i` carries the Minkowski sum `M + S` to `(Phi '' M) + (Phi '' S)`. -/
theorem Phi_image_addSet (d i : ℕ) (M : Finset (Fin d → ℝ)) (S : Set (Fin d → ℝ)) :
    Phi d i '' (Work.BW.addSet (M : Set (Fin d → ℝ)) S)
      = Work.BW.addSet (M.image (Phi d i) : Set _) (Phi d i '' S) := by
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨m, hm, s, hs, rfl⟩
    exact ⟨Phi d i m, by rw [Finset.mem_coe, Finset.mem_image]; exact ⟨m, hm, rfl⟩,
      Phi d i s, ⟨s, hs, rfl⟩, Phi_add d i m s⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨m, hm, rfl⟩ := ha
    obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨m + s, ⟨m, hm, s, hs, rfl⟩, Phi_add d i m s⟩

/-- `Phi d i` carries `scaleFirst i ρ '' S` to `scaleX ρ '' (Phi '' S)`. -/
theorem Phi_image_scaleFirst (d i : ℕ) (ρ : ℝ) (S : Set (Fin d → ℝ)) :
    Phi d i '' (Work.BW.scaleFirst i ρ '' S) = scaleX (ι := Xidx d i) (κ := Yidx d i) ρ '' (Phi d i '' S) := by
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hw
    exact ⟨Phi d i s, ⟨s, hs, rfl⟩, (Phi_scaleFirst d i ρ s).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hw
    exact ⟨Work.BW.scaleFirst i ρ s, ⟨s, hs, rfl⟩, Phi_scaleFirst d i ρ s⟩

/-- `Phi d i` carries convex sets to convex sets. -/
theorem convex_image_Phi (d i : ℕ) {S : Set (Fin d → ℝ)} (hS : Convex ℝ S) :
    Convex ℝ (Phi d i '' S) := by
  rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hS hx hy ha hb hab, ?_⟩
  rw [Phi_add, Phi_smul, Phi_smul]

/-- `Phi d i` carries measurable sets to measurable sets. -/
theorem measurableSet_image_Phi (d i : ℕ) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    MeasurableSet (Phi d i '' S) := by
  have h : Phi d i '' S = (Phi d i).symm ⁻¹' S := by
    ext z; constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨(Phi d i).symm z, hz, (Phi d i).apply_symm_apply z⟩
  rw [h]
  exact hS.preimage (Phi d i).symm.measurable

/-- The volume (as a real number) is preserved by `Phi d i` on measurable sets. -/
theorem measureReal_image_Phi (d i : ℕ) {T : Set (Fin d → ℝ)} (hT : MeasurableSet T) :
    volume.real (Phi d i '' T) = volume.real T := by
  have hmap : Measure.map (Phi d i) volume = volume := (measurePreserving_Phi d i).map_eq
  have hmeas : MeasurableSet (Phi d i '' T) := measurableSet_image_Phi d i hT
  have hpre : (Phi d i) ⁻¹' (Phi d i '' T) = T := by
    ext z; constructor
    · intro hz
      obtain ⟨x, hx, hxz⟩ := hz
      rwa [← (Phi d i).injective hxz]
    · intro hz; exact ⟨z, hz, rfl⟩
  have h := map_measureReal_apply (μ := volume) (Phi d i).measurable hmeas
  rw [hmap, hpre] at h
  exact h

theorem scaleFirst_comp_inv (d i : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (x : Fin d → ℝ) :
    Work.BW.scaleFirst i ρ (Work.BW.scaleFirst i (ρ⁻¹) x) = x := by
  ext j; by_cases h : (j : ℕ) < i <;> simp [Work.BW.scaleFirst, h, hρ]

theorem scaleFirst_inv_comp (d i : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (x : Fin d → ℝ) :
    Work.BW.scaleFirst i (ρ⁻¹) (Work.BW.scaleFirst i ρ x) = x := by
  ext j; by_cases h : (j : ℕ) < i <;> simp [Work.BW.scaleFirst, h, hρ]

/-- `Work.BW.scaleFirst i ρ` with `ρ ≠ 0` sends measurable sets to measurable sets. -/
theorem measurableSet_scaleFirst_image (d i : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    MeasurableSet (Work.BW.scaleFirst i ρ '' S) := by
  have h : Work.BW.scaleFirst i ρ '' S = (Work.BW.scaleFirst i (ρ⁻¹)) ⁻¹' S := by
    ext y; constructor
    · rintro ⟨s, hs, rfl⟩
      show Work.BW.scaleFirst i (ρ⁻¹) (Work.BW.scaleFirst i ρ s) ∈ S
      rwa [scaleFirst_inv_comp d i hρ s]
    · intro hy
      refine ⟨Work.BW.scaleFirst i (ρ⁻¹) y, ?_, scaleFirst_comp_inv d i hρ y⟩
      show Work.BW.scaleFirst i (ρ⁻¹) y ∈ S
      exact hy
  rw [h]
  exact hS.preimage (by measurability)

/-- `Work.BW.addSet M S` is a finite union of translates of `S`, hence measurable when `S` is. -/
theorem measurableSet_addSet (d : ℕ) (M : Finset (Fin d → ℝ)) {S : Set (Fin d → ℝ)}
    (hS : MeasurableSet S) :
    MeasurableSet (Work.BW.addSet (M : Set (Fin d → ℝ)) S) := by
  have h : Work.BW.addSet (M : Set (Fin d → ℝ)) S
      = ⋃ a : ↑(M : Set (Fin d → ℝ)), (fun z : Fin d → ℝ => z - (a : Fin d → ℝ)) ⁻¹' S := by
    ext z; constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, by simpa using hb⟩
    · intro hz
      obtain ⟨a, hm⟩ := Set.mem_iUnion.mp hz
      exact ⟨a, a.2, z - a, show z - (a : Fin d → ℝ) ∈ S from hm, by abel⟩
  rw [h]
  exact MeasurableSet.iUnion (fun a => hS.preimage (by fun_prop))

end Work.BW.Minkowski2
