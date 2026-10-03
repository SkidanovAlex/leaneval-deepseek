import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.Rat.Weak.A_add_left
import Submission.Work.ORHughesFree.Rat.Weak.Structural

/-!
# Assembling the source theorem from the two `A`-family inputs

The target statement (`Rat.exists_source_subgroup_weak`) is equivalent to: the family
`Rat.F α = {V ≤ U | α ∈ Rat(V)·U}` has a least element, finitely generated.

This file reduces the target statement to two statements about the *one-sided* family
`Weak.FA y = {V | y ∈ Rat(V)}`:

* `IsSource σA` : `σA` is a source function for the `A`-families, i.e. `FA y = Set.Ici (σA y)`
  for every `y` (the least element of `FA y` exists, and is `σA y`);
* `hmin` : for every `α`, the family `{σA (α * φ u) : u : U}` has a least element.

Given these, the least element of `F α` is `σA (α * φ u₀)` for a minimising `u₀`:

* `σA (α φ u₀) ∈ F α`, because `σA (α φ u₀) ∈ FA (α φ u₀) ⊆ F (α φ u₀) = F α`;
* `σA (α φ u₀) ⊆ V` for every `V ∈ F α = ⋃_u FA (α φ u)`: if `V ∈ FA (α φ u)` then
  `σA (α φ u) ⊆ V`, and `σA (α φ u₀) ⊆ σA (α φ u)`;
* it is finitely generated because it is the closure of the support of a term representing
  `α · φ u₀` as an element of `Rat(σA (α φ u₀))` (`Rat.mem_A_iff`).
-/

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel

variable {U : Type} [Group U]

/-- A function `σA` is a **source function for the `A`-families** if each `FA y` is exactly the
family of subgroups containing `σA y`; equivalently `σA y` is the least element of `FA y`. -/
def IsSource (σA : RatU U → Subgroup U) : Prop := ∀ y : RatU U, FA y = Set.Ici (σA y)

/-- **The target statement follows from the two `A`-family inputs.**

If `σA` is a source function for the `A`-families (`IsSource σA`) and for every `α` the family
`{σA (α * φ u) : u : U}` has a least element, then `Rat.exists_source_subgroup_weak` holds for
`α`, with `S := σA (α * φ u₀)`. -/
theorem exists_source_subgroup_weak_of_source (σA : RatU U → Subgroup U) (hσ : IsSource σA)
    (hmin : ∀ α : RatU U, ∃ u₀ : U,
      ∀ u : U, σA (α * RatU.ofGroup u₀) ≤ σA (α * RatU.ofGroup u))
    (α : RatU U) :
    ∃ (S : Subgroup U), S.FG ∧
      (∃ (u : U) (β : RatU ↥S), RatU.ofSubgroup S β * RatU.ofGroup u = α) ∧
      (∀ (V : Subgroup U) (u : U) (β : RatU ↥V),
        RatU.ofSubgroup V β * RatU.ofGroup u = α → S ≤ V) := by
  obtain ⟨u₀, hu₀⟩ := hmin α
  -- `α φ u₀ ∈ Rat(σA (α φ u₀))`
  have hmem : σA (α * RatU.ofGroup u₀) ∈ FA (α * RatU.ofGroup u₀) := by
    rw [hσ, Set.mem_Ici]
  refine ⟨σA (α * RatU.ofGroup u₀), ?_, ?_, ?_⟩
  · -- finite generation: `σA (α φ u₀)` is the closure of the support of a term for `α φ u₀`
    obtain ⟨t, ht, htx⟩ := (Rat.mem_A_iff _ _).mp hmem
    have hgen : Subgroup.closure (RTerm.supp t) = σA (α * RatU.ofGroup u₀) := by
      refine le_antisymm ?_ ?_
      · rw [Subgroup.closure_le]; exact ht
      · have hcl : Subgroup.closure (RTerm.supp t) ∈ FA (α * RatU.ofGroup u₀) :=
          (Rat.mem_A_iff _ _).mpr ⟨t, fun u hu => Subgroup.subset_closure hu, htx⟩
        rw [hσ] at hcl
        exact hcl
    rw [← hgen]
    exact (Subgroup.fg_iff _).mpr ⟨RTerm.supp t, rfl, RTerm.supp_finite t⟩
  · -- the witness `α = ofSubgroup S β * ofGroup u₀⁻¹`
    obtain ⟨β, hβ⟩ := hmem
    refine ⟨u₀⁻¹, β, ?_⟩
    rw [hβ]
    calc (α * RatU.ofGroup u₀) * RatU.ofGroup u₀⁻¹
        = α * (RatU.ofGroup u₀ * RatU.ofGroup u₀⁻¹) := by rw [mul_assoc]
      _ = α := by rw [ofGroup_mul_inv, mul_one]
  · -- minimality
    intro V u β hVu
    have hVF : V ∈ Rat.F α := ⟨β, u, hVu⟩
    rw [F_eq_iUnion_FA] at hVF
    obtain ⟨u', hu'⟩ := Set.mem_iUnion.mp hVF
    have h1 : σA (α * RatU.ofGroup u') ≤ V := by
      rw [hσ] at hu'
      exact hu'
    exact le_trans (hu₀ u') h1

end Work.ORHughesFree.Rat.Weak
