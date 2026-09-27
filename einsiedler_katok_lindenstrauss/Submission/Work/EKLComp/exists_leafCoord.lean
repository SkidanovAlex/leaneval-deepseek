import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.joinAtoms
import Submission.Work.EKLContract.Interfaces

/-!
# A measurable leaf coordinate on an atom of a plaque algebra

Let `U ≤ SL₃(ℝ)` be a closed subgroup, `Z ⊆ X₃`, `𝔪` a plaque algebra on `Z`
(`IsPlaqueAlgebra U Z 𝔪.m`), and `x ∈ Z` a point at which the `U`-action is free
(`u • x = x → u = 1`).  This file proves

`Work.EKLComp.exists_leafCoord`:

there is a **Borel measurable** map `σ : X₃ → SL₃(ℝ)` such that for every `y` in the atom
`[x]_𝔪` of `x` the element `σ y` is the unique `u ∈ U` with `u • x = y`, and `σ y = 1` for
`y ∉ [x]_𝔪`.

This is the "measurable leaf coordinate" used in the construction of leafwise measures: it
turns the conditional measure of `𝔪` at `x` into a measure on the group `U`, via
`ν x := (condExpKernel … x).map σ`.

Mathematically the only content is the standard-Borel fact that an injective continuous map
from a Polish space is a measurable embedding (`Continuous.measurableEmbedding`, using that
`U`, a closed subset of the Polish group `SL₃(ℝ)`, is Polish): the orbit map

`ψ : U → X₃,  u ↦ u • x`

is continuous and injective (injectivity is exactly the freeness of the action at `x`), so it is
a measurable embedding and has a measurable left inverse `ψ⁻¹` on its range.  Since the atom
`[x]_𝔪` is contained in the `U`-orbit of `x` (a field of `IsPlaqueAlgebra`) and is Borel
(`𝔪 ≤ borel X₃` and `𝔪` is countably generated), the piecewise definition

`σ y = ψ⁻¹ y` for `y ∈ [x]_𝔪`,  `σ y = 1` for `y ∉ [x]_𝔪`

is Borel measurable.
-/

open MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLComp

open Work.EKLContract

/-- The atom of a countably generated σ-algebra which is coarser than the Borel σ-algebra of `X₃`
is a Borel set.  (`SigAlg` is used for the σ-algebra so that it is not picked up by instance
search as the ambient `MeasurableSpace X₃`.) -/
lemma measurableSet_atom_of_countablyGen (𝔪 : SigAlg) (hm : 𝔪.m ≤ borel X3)
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ 𝔪.m = MeasurableSpace.generateFrom b) (x : X3) :
    MeasurableSet (atom 𝔪.m x) := by
  obtain ⟨b, hbc, hbm⟩ := hgen
  haveI : Countable b := hbc
  have hm' : MeasurableSpace.generateFrom b ≤ borel X3 := hbm ▸ hm
  have hatom : atom 𝔪.m x = {y | ∀ s ∈ b, y ∈ s ↔ x ∈ s} := by
    rw [hbm]
    exact atomG_generateFrom x
  rw [hatom]
  rw [show {y : X3 | ∀ s ∈ b, y ∈ s ↔ x ∈ s}
      = ⋂ (s : b), {y : X3 | y ∈ (s : Set X3) ↔ x ∈ (s : Set X3)} from by ext y; simp]
  refine MeasurableSet.iInter fun s => ?_
  have hA : MeasurableSet (s : Set X3) := hm' _ (MeasurableSpace.measurableSet_generateFrom s.2)
  by_cases hxs : x ∈ (s : Set X3)
  · have hset : {y : X3 | y ∈ (s : Set X3) ↔ x ∈ (s : Set X3)} = (s : Set X3) := by
      ext y; simp [hxs]
    rw [hset]; exact hA
  · have hset : {y : X3 | y ∈ (s : Set X3) ↔ x ∈ (s : Set X3)} = (s : Set X3)ᶜ := by
      ext y; simp [hxs]
    rw [hset]; exact hA.compl

theorem exists_leafCoord (U : Subgroup Work.EKLContract.SL3)
    (hcl : IsClosed (U : Set Work.EKLContract.SL3))
    (Z : Set Work.EKLContract.X3) (𝔪 : Work.EKLComp.SigAlg)
    (hm : Work.EKLContract.IsPlaqueAlgebra U Z 𝔪.m) (x : Work.EKLContract.X3)
    (hx : x ∈ Z) (hfree : ∀ u ∈ U, u • x = x → u = 1) :
    ∃ σ : Work.EKLContract.X3 → Work.EKLContract.SL3,
      Measurable σ ∧
      (∀ y ∈ Work.EKLContract.atom 𝔪.m x,
        σ y ∈ U ∧ σ y • x = y ∧ ∀ u ∈ U, u • x = y → u = σ y) ∧
      (∀ y ∉ Work.EKLContract.atom 𝔪.m x, σ y = 1) := by
  classical
  obtain ⟨hmle, hgen, -, hatom⟩ := hm
  -- `U` is a Polish space: it is a closed subset of the Polish group `SL₃(ℝ)`
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace U := hcl.polishSpace
  haveI : Nonempty U := ⟨⟨1, U.one_mem⟩⟩
  -- the orbit map of `U` through `x`
  let ψ : U → X3 := fun u => (u : SL3) • x
  have hψinj : Function.Injective ψ := by
    intro u v huv
    have huv' : (u : SL3) • x = (v : SL3) • x := huv
    have hU : (v : SL3)⁻¹ * (u : SL3) ∈ U := U.mul_mem (U.inv_mem v.2) u.2
    have hfix : ((v : SL3)⁻¹ * (u : SL3)) • x = x := by
      rw [mul_smul, huv']
      exact inv_smul_smul _ _
    have h1 := hfree _ hU hfix
    have h2 : (u : SL3) = (v : SL3) := by
      have hh := congrArg (fun t => (v : SL3) * t) h1
      simpa using hh
    exact Subtype.ext h2
  have hψcont : Continuous ψ := by fun_prop
  -- hence `ψ` is a measurable embedding, with measurable left inverse
  have hME : MeasurableEmbedding ψ := Continuous.measurableEmbedding hψcont hψinj
  have hcoord : ∀ y ∈ Set.range ψ, ψ (hME.invFun y) = y := by
    intro y hy
    rw [Set.mem_range] at hy
    obtain ⟨u, rfl⟩ := hy
    exact congrArg ψ (hME.leftInverse_invFun u)
  -- the atom is Borel
  have hAmeas : MeasurableSet (atom 𝔪.m x) := measurableSet_atom_of_countablyGen 𝔪 hmle hgen x
  refine ⟨fun y => if y ∈ atom 𝔪.m x then ((hME.invFun y : U) : SL3) else 1, ?_, ?_, ?_⟩
  · refine Measurable.ite hAmeas ?_ measurable_const
    exact continuous_subtype_val.measurable.comp hME.measurable_invFun
  · intro y hy
    -- every point of the atom lies in the `U`-orbit of `x`, so it has a coordinate
    have hsub : atom 𝔪.m x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) := (hatom x hx).2.1
    have hyimg : y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) := hsub hy
    rw [Set.mem_image] at hyimg
    obtain ⟨u₀, hu₀, huy₀⟩ := hyimg
    have hrange : y ∈ Set.range ψ := ⟨⟨u₀, hu₀⟩, huy₀⟩
    show (if y ∈ atom 𝔪.m x then ((hME.invFun y : U) : SL3) else 1) ∈ U ∧
      (if y ∈ atom 𝔪.m x then ((hME.invFun y : U) : SL3) else 1) • x = y ∧
      ∀ u ∈ U, u • x = y →
        u = (if y ∈ atom 𝔪.m x then ((hME.invFun y : U) : SL3) else 1)
    rw [if_pos hy]
    refine ⟨(hME.invFun y).2, hcoord y hrange, ?_⟩
    intro u hu huy
    have key : ψ ⟨u, hu⟩ = ψ (hME.invFun y) := huy.trans (hcoord y hrange).symm
    exact congrArg Subtype.val (hψinj key)
  · intro y hy
    show (if y ∈ atom 𝔪.m x then ((hME.invFun y : U) : SL3) else 1) = 1
    rw [if_neg hy]

end Work.EKLComp
