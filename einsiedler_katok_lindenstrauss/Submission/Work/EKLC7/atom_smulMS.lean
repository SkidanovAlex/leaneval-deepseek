import Mathlib
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.Defs

/-!
# `Work.EKLC7.atom_smulMS` — translating an atom along the action

`smulMS u m` is, by definition (`Work.EKLC7.SmulMS`), the σ-algebra
`MeasurableSpace.comap (fun y ↦ u⁻¹ • y) m` on `X₃`, i.e. the family of translates
`{u • B : B ∈ m}`; and `smulSt u Z = (fun y ↦ u • y) '' Z`.

The main point (`atom_smulMS`) is that the atom of a point in a translated σ-algebra is the
translate of the atom: `[u • x]_{R_u m} = u • [x]_m`.  This is the σ-algebra side of the
"translate the plaque algebra along the point transformation `R_u`" device used to exploit the
`condexp` field of `IsLeafwise` at two points related by `u ∈ U` (see `SmulMS.lean`).

The proof is the general lemma `sInter_comap_atom` below: for *any* map `f` the atoms of the
σ-algebra `comap f m` are the `f`-preimages of the atoms of `m`,
`[y]_{comap f m} = f ⁻¹' [f y]_m`, since
`MeasurableSet[comap f m] s ↔ ∃ t ∈ m, f ⁻¹' t = s` and preimages commute with `⋂₀`.
No injectivity of `f` is needed; the identification of the translate `smulSt u` with the
preimage under `y ↦ u⁻¹ • y` (lemma `preimage_invSmul_eq_smulSt`) uses the group action.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-! ## Generalities on atoms of a comap σ-algebra -/

/-- **Atoms of a `comap` σ-algebra.**  For an arbitrary map `f : α → α`, the atom of the σ-algebra
`MeasurableSpace.comap f m` at a point `y` is the `f`-preimage of the atom of `m` at `f y`. -/
theorem sInter_comap_atom {α : Type*} (f : α → α) (m : MeasurableSpace α) (y : α) :
    (⋂₀ {s : Set α | MeasurableSet[MeasurableSpace.comap f m] s ∧ y ∈ s})
      = f ⁻¹' (⋂₀ {s : Set α | MeasurableSet[m] s ∧ f y ∈ s}) := by
  ext z
  simp only [Set.mem_sInter, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · intro h t ht
    exact h (f ⁻¹' t) ⟨MeasurableSpace.measurableSet_comap.mpr ⟨t, ht.1, rfl⟩, ht.2⟩
  · intro h s hs
    obtain ⟨s', hs'm, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hs.1
    have hy : y ∈ f ⁻¹' s' := hpre.symm ▸ hs.2
    have hz : f z ∈ s' := h s' ⟨hs'm, hy⟩
    rw [← hpre]
    exact hz

/-- **Measurable sets of a translated σ-algebra**, in terms of the pullback along `y ↦ u • y`:
`s` is measurable for `smulMS u m` exactly when `(fun y ↦ u • y) ⁻¹' s` is `m`-measurable
(equivalently, when `s` is `m`-measurable as a set of the form `smulSt u B`, `B ∈ m`, since
`y ↦ u • y` is a bijection). -/
theorem measurableSet_smulMS {u : SL3} {m : MeasurableSpace X3} {s : Set X3} :
    MeasurableSet[smulMS u m] s ↔ MeasurableSet[m] ((fun y : X3 => u • y) ⁻¹' s) := by
  rw [smulMS, MeasurableSpace.measurableSet_comap]
  constructor
  · rintro ⟨s', hs', hpre⟩
    rw [← hpre]
    have hset : (fun y : X3 => u • y) ⁻¹' ((fun y : X3 => u⁻¹ • y) ⁻¹' s') = s' := by
      ext z
      simp only [Set.mem_preimage]
      rw [inv_smul_smul]
    rw [hset]
    exact hs'
  · intro hs
    refine ⟨(fun y : X3 => u • y) ⁻¹' s, hs, ?_⟩
    ext z
    simp only [Set.mem_preimage]
    rw [smul_inv_smul]

/-! ## The translate `smulSt` as a preimage -/

/-- The action by `u` and the action by `u⁻¹` are inverse: the image of `A` under `y ↦ u • y` is
the preimage of `A` under `y ↦ u⁻¹ • y`. -/
theorem preimage_invSmul_eq_smulSt (u : SL3) (A : Set X3) :
    (fun y : X3 => u⁻¹ • y) ⁻¹' A = smulSt u A := by
  ext z
  rw [smulSt, Set.mem_preimage, Set.mem_image]
  constructor
  · intro hz
    exact ⟨u⁻¹ • z, hz, smul_inv_smul u z⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

/-! ## The main lemma -/

/-- **Atom of a translated σ-algebra at a translated point.**  For `u : SL₃(ℝ)`, a σ-algebra `m`
on `X₃ = SL₃(ℝ)/Γ₃` and `x : X₃`,
`[u • x]_{R_u m} = u • [x]_m`,
where `smulMS u m` is the translate of `m` by the point transformation `R_u : y ↦ u • y` and
`smulSt u Z = R_u '' Z`. -/
theorem atom_smulMS (u : Work.EKLContract.SL3) (m : MeasurableSpace Work.EKLContract.X3)
    (x : Work.EKLContract.X3) :
    Work.EKLContract.atom (Work.EKLC7.smulMS u m) (u • x)
      = Work.EKLC7.smulSt u (Work.EKLContract.atom m x) := by
  have h := sInter_comap_atom (fun y : X3 => u⁻¹ • y) m (u • x)
  simp only [inv_smul_smul] at h
  rw [preimage_invSmul_eq_smulSt] at h
  simpa only [Work.EKLContract.atom, smulMS] using h

/-- The main lemma at an arbitrary point: `[y]_{R_u m} = u • [u⁻¹ • y]_m`. -/
theorem atom_smulMS_apply (u : SL3) (m : MeasurableSpace X3) (y : X3) :
    atom (smulMS u m) y = smulSt u (atom m (u⁻¹ • y)) := by
  have h := sInter_comap_atom (fun y : X3 => u⁻¹ • y) m y
  rw [preimage_invSmul_eq_smulSt] at h
  simpa only [Work.EKLContract.atom, smulMS] using h

end Work.EKLC7
