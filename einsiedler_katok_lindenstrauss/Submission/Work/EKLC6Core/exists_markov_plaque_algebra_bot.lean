import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.Gamma3Facts

/-!
# `Work.EKLC6Core.exists_markov_plaque_algebra_bot`

The degenerate case `Uminus t = ⊥` of the Markov plaque algebra
(`Work.EKLC6Core.exists_markov_plaque_algebra`): when the contracted horospherical subgroup
`G⁻(t) = Uminus t` is trivial, the Borel σ-algebra `borel X₃` is itself a plaque algebra for it on
the *whole* space, and one may take `Z = univ`, `C = 1`.

Indeed:
* the atoms of `borel X₃` are singletons (the space is `T₁`, `Γ₃` being closed in `SL₃(ℝ)`),
  hence every point is its own plaque;
* `shape (borel X₃) ⊥ x = {1} = univ ∩ ⊥`, and `{1}` is entrywise bounded by `1`;
* `borel X₃` is countably generated (`X₃` is second countable);
* `borel X₃` is `aDiag t`-decreasing, since the action of `SL₃(ℝ)` on `X₃` is continuous;
* the last conjunct is vacuous, every element of `Uminus t = ⊥` being `1`.

Everything is quantitative-free: the constant `C = 1` bounds the entries of `1 : SL₃(ℝ)`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.EKLC6Core

open Work.EKLContract

set_option linter.style.haveILetI false

/-! ## The two topological instances of `X₃` -/

/-- `X₃ = SL₃(ℝ)/Γ₃` is a `T₁` space, `Γ₃` being closed in `SL₃(ℝ)`. -/
theorem t1Space_X3 : T1Space X3 := by
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  exact QuotientGroup.instT1Space

/-- `X₃ = SL₃(ℝ)/Γ₃` is second countable, being a quotient of the second countable group
`SL₃(ℝ)`. -/
theorem secondCountableTopology_X3 : SecondCountableTopology X3 := by
  haveI : SecondCountableTopology SL3 := Work.EKLContract.Lemmas.SL3Topology.2
  exact QuotientGroup.instSecondCountableTopology (N := Γ3)

/-- In a `T₁` Borel space the atom of the Borel σ-algebra at `x` is the singleton `{x}`. -/
theorem atom_borel_eq_singleton (x : X3) : atom (borel X3) x = {x} := by
  haveI : T1Space X3 := t1Space_X3
  refine Set.Subset.antisymm ?_ ?_
  · exact Set.sInter_subset_of_mem ⟨(isClosed_singleton (x := x)).measurableSet, rfl⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Set.mem_sInter.mpr fun t ht => ht.2

/-- The shape of a point for the trivial subgroup and the Borel σ-algebra is the whole (trivial)
subgroup. -/
theorem shape_bot_borel (x : X3) :
    shape (borel X3) (⊥ : Subgroup SL3) x = ((⊥ : Subgroup SL3) : Set SL3) := by
  have hatom : atom (borel X3) x = {x} := atom_borel_eq_singleton x
  ext u
  simp only [shape, Set.mem_ofPred_eq, SetLike.mem_coe, hatom]
  constructor
  · rintro ⟨hu, -⟩; exact hu
  · intro hu
    exact ⟨hu, by rw [Subgroup.mem_bot.mp hu, one_smul]; exact Set.mem_singleton x⟩

/-! ## The trivial plaque algebra -/

/-- `IsPlaqueAlgebra` holds for the trivial subgroup, with the Borel σ-algebra and the whole
space. -/
theorem isPlaqueAlgebra_bot_univ_borel :
    IsPlaqueAlgebra (⊥ : Subgroup SL3) Set.univ (borel X3) := by
  haveI : SecondCountableTopology X3 := secondCountableTopology_X3
  refine ⟨le_rfl, ?_, MeasurableSet.univ, ?_⟩
  · obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X3
    exact ⟨b, hbc, hb.borel_eq_generateFrom⟩
  · intro x _
    have hatom : atom (borel X3) x = {x} := atom_borel_eq_singleton x
    refine ⟨by rw [hatom]; exact Set.singleton_subset_iff.mpr (Set.mem_univ x), ?_, ?_, ?_⟩
    · rw [hatom]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨1, Subgroup.mem_bot.mpr rfl, one_smul SL3 x⟩
    · refine ⟨Set.univ, isOpen_univ, ?_⟩
      rw [shape_bot_borel x, Set.univ_inter]
    · refine ⟨1, ?_⟩
      intro u hu i j
      rw [shape_bot_borel x] at hu
      have hu1 : u = 1 := Subgroup.mem_bot.mp hu
      rw [hu1]
      rw [show ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 from rfl, Matrix.one_apply]
      split <;> simp

/-! ## The target -/

theorem exists_markov_plaque_algebra_bot {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ) (hbot : Work.EKLC6Core.Uminus t = ⊥) :
    ∃ (M : MeasurableSpace Work.EKLContract.X3) (Z : Set Work.EKLContract.X3) (C : ℝ),
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z M ∧
      μ Zᶜ = 0 ∧
      MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) M ≤ M ∧
      (∀ x : Work.EKLContract.X3, x ∉ Z → Work.EKLContract.atom M x = {x}) ∧
      (∀ x ∈ Z, ∀ u ∈ Work.EKLC6Core.Uminus t,
        u • x ∈ Work.EKLContract.atom M x → ∀ i j, |u i j| ≤ C) := by
  refine ⟨borel Work.EKLContract.X3, Set.univ, 1, ?_, ?_, ?_, ?_, ?_⟩
  · -- the Borel σ-algebra is a plaque algebra for the trivial subgroup
    rw [hbot]
    exact isPlaqueAlgebra_bot_univ_borel
  · -- `univ` is conull
    simp
  · -- the flow preserves the Borel σ-algebra
    exact measurable_iff_comap_le.mp
      ((continuous_const_smul (Work.EKLContract.aDiag t)).measurable)
  · -- off the conull set there is nothing to check
    intro x hx
    exact absurd (Set.mem_univ x) hx
  · -- every element of `Uminus t = ⊥` is `1`, whose entries are bounded by `1`
    intro x _ u hu _ i j
    rw [hbot] at hu
    have hu1 : u = 1 := Subgroup.mem_bot.mp hu
    rw [hu1]
    rw [show ((1 : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 from rfl,
      Matrix.one_apply]
    split <;> simp

end Work.EKLC6Core
