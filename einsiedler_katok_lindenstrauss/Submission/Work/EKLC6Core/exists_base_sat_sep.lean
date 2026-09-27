import Mathlib
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.exists_base_sat_sep`

The existence of a *separating* countable family of open sets of `SL₃(ℝ)` for the
`U`-saturation `sat U ·`: a topological basis `O : ℕ → Set SL3` of `SL₃(ℝ)` such that the
membership pattern `m ↦ (z ∈ sat U (O m))` determines the left `U`-coset of a point.  Precisely,
if `z` and `w` have the same pattern then `w ∈ sat U {z}`, i.e. `w = u * z` for some `u ∈ U`.

The mechanism is that `sat U O` is the set of `h` whose left `U`-coset `U h = {u * h | u ∈ U}`
meets `O` (`mem_sat_iff`).  For a *closed* subgroup `U` two distinct left cosets are disjoint
nonempty closed subsets of the second countable space `SL₃(ℝ)`, hence are separated by a basis
element: if `w ∉ U z` then the coset `U w` is closed, does not contain `z`, and a basis element
`V ∋ z` with `V ∩ U w = ∅` witnesses that the patterns of `z` and `w` differ at `V`.
-/

set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `SL₃(ℝ)` is second countable (it is a subspace of `ℝ³ˣ³`).  Stated as a local instance
because `Matrix.SpecialLinearGroup` is a `def`, so that instance search does not unfold it. -/
theorem secondCountableTopology_SL3 : SecondCountableTopology SL3 :=
  have : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  TopologicalSpace.Subtype.secondCountableTopology (α := Matrix (Fin 3) (Fin 3) ℝ)
    {A | A.det = 1}

/-- `z` lies in the `U`-saturation `sat U O` of `O` iff the left `U`-coset of `z`, i.e.
`{u * z | u ∈ U}`, meets `O`. -/
theorem mem_sat_iff (U : Subgroup SL3) (O : Set SL3) (z : SL3) :
    z ∈ sat U O ↔ ∃ u ∈ U, u * z ∈ O := by
  constructor
  · rintro ⟨u, hu, o, ho, rfl⟩
    exact ⟨u⁻¹, U.inv_mem hu, by simpa using ho⟩
  · rintro ⟨u, hu, huO⟩
    exact ⟨u⁻¹, U.inv_mem hu, u * z, huO, by simp⟩

/-- The left `U`-coset `{u * w | u ∈ U}`, written as a level set of the map `x ↦ x * w⁻¹`. -/
theorem isClosed_coset (U : Subgroup SL3) (hUc : IsClosed (U : Set SL3)) (w : SL3) :
    IsClosed {x : SL3 | x * w⁻¹ ∈ (U : Set SL3)} :=
  hUc.preimage (continuous_mul_const w⁻¹)

theorem exists_base_sat_sep (U : Subgroup Work.EKLContract.SL3)
    (hUc : IsClosed (U : Set Work.EKLContract.SL3)) :
    ∃ O : ℕ → Set Work.EKLContract.SL3,
      (∀ m, IsOpen (O m)) ∧
      (∀ z : Work.EKLContract.SL3, ∃ m, z ∈ Work.EKLC6Core.sat U (O m)) ∧
      (∀ z w : Work.EKLContract.SL3,
        (∀ m, (z ∈ Work.EKLC6Core.sat U (O m) ↔ w ∈ Work.EKLC6Core.sat U (O m))) →
        w ∈ Work.EKLC6Core.sat U ({z} : Set Work.EKLContract.SL3)) := by
  haveI : SecondCountableTopology SL3 := secondCountableTopology_SL3
  obtain ⟨O, hOb⟩ := TopologicalSpace.exists_seq_basis SL3
  refine ⟨O, fun m => hOb.isOpen (Set.mem_range_self m), ?_, ?_⟩
  · -- every point lies in the saturation of some member of the basis
    intro z
    obtain ⟨V, hV, hzV, -⟩ := hOb.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    obtain ⟨m, hm⟩ := hV
    exact ⟨m, by rw [hm, mem_sat_iff]; exact ⟨1, U.one_mem, by simpa using hzV⟩⟩
  · -- the pattern determines the left coset
    intro z w hzw
    rw [mem_sat_iff]
    simp only [Set.mem_singleton_iff]
    by_contra hcon
    -- `B` is the left coset `U w`, a closed set not containing `z`
    set B : Set SL3 := {x : SL3 | x * w⁻¹ ∈ (U : Set SL3)} with hBdef
    have hBclosed : IsClosed B := by
      rw [hBdef]
      exact isClosed_coset U hUc w
    have hzB : z ∉ B := by
      intro hzU
      rw [hBdef, Set.mem_ofPred_eq] at hzU
      exact hcon ⟨z * w⁻¹, hzU, by simp [mul_assoc]⟩
    obtain ⟨V, hV, hzV, hVsub⟩ :=
      hOb.exists_subset_of_mem_open (show z ∈ Bᶜ from hzB) hBclosed.isOpen_compl
    obtain ⟨m, hm⟩ := hV
    have hzm : z ∈ sat U (O m) := by
      rw [hm, mem_sat_iff]
      exact ⟨1, U.one_mem, by simpa using hzV⟩
    have hwm : w ∈ sat U (O m) := (hzw m).mp hzm
    rw [hm, mem_sat_iff] at hwm
    obtain ⟨u, hu, huwV⟩ := hwm
    have huB : u * w ∈ B := by
      rw [hBdef, Set.mem_ofPred_eq]
      simpa [mul_assoc] using hu
    exact (hVsub huwV) huB

end Work.EKLC6Core
