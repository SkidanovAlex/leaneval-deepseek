import Mathlib
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.conj_entry_bound

/-!
# `Work.EKLC7.isPlaqueAlgebra_smulMS`

`IsPlaqueAlgebra U Z m` is transported along the point transformation `R_u : y ↦ u • y` for
`u ∈ U`:

* the carrier `Z` becomes `smulSt u Z = R_u '' Z`;
* the σ-algebra `m` becomes `smulMS u m = {R_u B : B ∈ m}` (i.e. `comap R_u⁻¹ m`).

All four clauses of `IsPlaqueAlgebra` are transported: `m ≤ borel` (the action is measurable),
countable generation (`comap` of a `generateFrom` is a `generateFrom` of the preimages, and
`Set.Countable` is preserved by images), `MeasurableSet[m] Z` (a `smulMS u m`-measurable set is a
`R_u⁻¹`-preimage and `R_u⁻¹ ⁻¹' Z = smulSt u Z`), and the pointwise clause.

The pointwise clause is where the hypothesis `u ∈ U` is used: at the point `u • x` the atom of the
translated σ-algebra is `R_u '' atom m x` (see `atom_smulMS_apply_c7`), so the translated shape is
the conjugate of `shape m U x` by `u` (`shape_smulMS_conj`); conjugating an open set by `u` gives
an open set (`conj_image_inter_smulMS`), and conjugating an entrywise-bounded subset of `SL₃(ℝ)`
keeps it entrywise bounded (`conj_entry_bound`).
-/

open MeasureTheory Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-! ## Atoms of a pulled-back σ-algebra -/

/-- The atom of a pulled-back σ-algebra is the pull-back of the atom: membership is tested
against the `m`-measurable sets alone, so no measurability of `atom m (f y)` is needed. -/
theorem atom_comap_smulMS (f : X3 → X3) (m : MeasurableSpace X3) (y : X3) :
    atom (MeasurableSpace.comap f m) y = f ⁻¹' atom m (f y) := by
  ext z
  simp only [atom, Set.mem_sInter, Set.mem_preimage]
  constructor
  · rintro hz t ⟨ht, hyt⟩
    exact hz (f ⁻¹' t) ⟨MeasurableSpace.measurableSet_comap.mpr ⟨t, ht, rfl⟩, hyt⟩
  · rintro hz s ⟨hs, hys⟩
    rw [MeasurableSpace.measurableSet_comap] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hz t ⟨ht, hys⟩

/-- The atom of `smulMS u m` at the transported point `u • x` is the translate of the atom of `m`
at `x`. -/
theorem atom_smulMS_apply_c7 (u : SL3) (m : MeasurableSpace X3) (x : X3) :
    atom (smulMS u m) (u • x) = smulSt u (atom m x) := by
  rw [smulMS, atom_comap_smulMS, inv_smul_smul]
  ext z
  rw [smulSt_mem]
  rfl

/-! ## Transport of a shape by conjugation -/

/-- Membership in a shape, by definition. -/
theorem mem_shape_iff_smulMS {m : MeasurableSpace X3} {U : Subgroup SL3} {x : X3} {u : SL3} :
    u ∈ shape m U x ↔ u ∈ U ∧ u • x ∈ atom m x := Iff.rfl

/-- The shape of the translated plaque algebra at `u • x` is the conjugate of the shape at `x`
by `u` (this is where `u ∈ U` is used). -/
theorem shape_smulMS_conj {U : Subgroup SL3} {u : SL3} (hu : u ∈ U) (m : MeasurableSpace X3)
    (x : X3) :
    shape (smulMS u m) U (u • x) = (fun w : SL3 => u * w * u⁻¹) '' shape m U x := by
  ext v
  rw [Set.mem_image]
  constructor
  · intro hv
    rw [mem_shape_iff_smulMS] at hv
    obtain ⟨hvU, hvatom⟩ := hv
    rw [atom_smulMS_apply_c7, smulSt_mem] at hvatom
    refine ⟨u⁻¹ * v * u, ?_, ?_⟩
    · rw [mem_shape_iff_smulMS]
      refine ⟨U.mul_mem (U.mul_mem (U.inv_mem hu) hvU) hu, ?_⟩
      simpa only [← mul_smul, mul_assoc] using hvatom
    · group
  · rintro ⟨w, hw, rfl⟩
    rw [mem_shape_iff_smulMS] at hw ⊢
    obtain ⟨hwU, hwatom⟩ := hw
    refine ⟨U.mul_mem (U.mul_mem hu hwU) (U.inv_mem hu), ?_⟩
    rw [atom_smulMS_apply_c7, smulSt_mem]
    have hw' : u⁻¹ • ((u * w * u⁻¹) • (u • x)) = w • x := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    rw [hw']
    exact hwatom

/-- Conjugation by `u ∈ U` maps `O ∩ U` onto the intersection of `U` with the preimage of `O`
under the inverse conjugation: the conjugated set is again an open piece of `U`. -/
theorem conj_image_inter_smulMS {U : Subgroup SL3} {u : SL3} (hu : u ∈ U) (O : Set SL3) :
    (fun w : SL3 => u * w * u⁻¹) '' (O ∩ (U : Set SL3))
      = (fun v : SL3 => u⁻¹ * v * u) ⁻¹' O ∩ (U : Set SL3) := by
  ext v
  rw [Set.mem_image]
  constructor
  · rintro ⟨w, ⟨hwO, hwU⟩, rfl⟩
    refine ⟨?_, U.mul_mem (U.mul_mem hu hwU) (U.inv_mem hu)⟩
    show u⁻¹ * (u * w * u⁻¹) * u ∈ O
    rwa [show u⁻¹ * (u * w * u⁻¹) * u = w by group]
  · rintro ⟨hvO, hvU⟩
    exact ⟨u⁻¹ * v * u, ⟨hvO, U.mul_mem (U.mul_mem (U.inv_mem hu) hvU) hu⟩, by group⟩

/-! ## The main transport lemma -/

theorem isPlaqueAlgebra_smulMS {U : Subgroup Work.EKLContract.SL3} {Z : Set Work.EKLContract.X3}
    {m : MeasurableSpace Work.EKLContract.X3} {u : Work.EKLContract.SL3} (hu : u ∈ U)
    (h : Work.EKLContract.IsPlaqueAlgebra U Z m) :
    Work.EKLContract.IsPlaqueAlgebra U (Work.EKLC7.smulSt u Z) (Work.EKLC7.smulMS u m) := by
  obtain ⟨hle, hgen, hZ, hpt⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `smulMS u m ≤ borel X3`
    refine le_trans (MeasurableSpace.comap_mono hle) ?_
    exact (measurable_const_smul (u⁻¹ : SL3)).comap_le
  · -- countable generation
    obtain ⟨b, hbc, hbg⟩ := hgen
    refine ⟨Set.preimage (fun y : X3 => u⁻¹ • y) '' b, hbc.image _, ?_⟩
    rw [smulMS, hbg, MeasurableSpace.comap_generateFrom]
  · -- the carrier is measurable
    refine ⟨Z, hZ, ?_⟩
    ext y
    rw [smulSt_mem]
    rfl
  · -- the pointwise clause, transported to `u • x`
    intro x' hx'
    simp only [smulSt, Set.mem_image] at hx'
    obtain ⟨x, hxZ, rfl⟩ := hx'
    obtain ⟨hxZ', hxU, hxshape, hxC⟩ := hpt x hxZ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [atom_smulMS_apply_c7]
      exact Set.image_mono hxZ'
    · rw [atom_smulMS_apply_c7]
      rintro y ⟨a, ha, rfl⟩
      obtain ⟨v, hvU, hvx⟩ := hxU ha
      refine ⟨u * v * u⁻¹, U.mul_mem (U.mul_mem hu hvU) (U.inv_mem hu), ?_⟩
      rw [← hvx]
      show (u * v * u⁻¹) • (u • x) = u • (v • x)
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    · obtain ⟨O, hO, hshape⟩ := hxshape
      refine ⟨(fun v : SL3 => u⁻¹ * v * u) ⁻¹' O, hO.preimage ?_, ?_⟩
      · exact (continuous_const.mul continuous_id).mul continuous_const
      · rw [shape_smulMS_conj hu, hshape, conj_image_inter_smulMS hu O]
    · -- the shape stays entrywise bounded
      obtain ⟨C, hC⟩ := hxC
      refine ⟨C * (∑ a : Fin 3, ∑ b : Fin 3, |u a b|) *
        (∑ a : Fin 3, ∑ b : Fin 3, |(u⁻¹ : SL3) a b|), ?_⟩
      intro w hw i j
      rw [shape_smulMS_conj hu, Set.mem_image] at hw
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      exact conj_entry_bound (u := u) (w := w₀) C (hC w₀ hw₀) i j

end Work.EKLC7
