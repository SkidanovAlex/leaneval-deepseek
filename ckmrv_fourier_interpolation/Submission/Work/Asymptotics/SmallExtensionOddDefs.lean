/-
# The finite "small extension" data at odd weight

This file sets up the odd-weight analogue of `Submission/Work/Asymptotics/ExtensionEvenDefs.lean`:
the interface against which the finite check of CKMRV Proposition 3.2(1) (the "small extension
claim") is stated.

For a neighbour `ν` of `𝓕̄` and a row `i`, the carries of `rowDiffOdd ν i` can be taken to be
scalar multiples of single group elements (`Work.Asymptotics.small_decomp_neighbor_odd`).  The
group elements that occur have the property that their translates of `O_F`, and those of their
`T`- (resp. `S T`-) translates, again land in `O`: this is the content of `SafePair`/`SafePairS`
(`Work.Asymptotics.ExtensionEvenDefs`, reused verbatim since the group elements are the same),
and it is what makes the two defect identities applicable at the evaluated points.

## Main definitions

* `Work.Asymptotics.ofOptC` : `none ↦ 0`, `some (c, γ) ↦ c • of γ`.
* `Work.Asymptotics.CarryOkOdd` : `rowDiffOdd ν i - ((T-I)² a + S(T-I)² b) ∈ (1+z)R`.
* `Work.Asymptotics.SafePairOdd`, `Work.Asymptotics.SafePairSOdd` : the corresponding safety.
-/
import Mathlib
import Submission.Work.Asymptotics.OddAssembly
import Submission.Work.Asymptotics.ExtensionEvenDefs
import Submission.Work.Asymptotics.small_decomp_neighbor_odd

noncomputable section

open UpperHalfPlane Work.Kernels
open scoped MatrixGroups ModularForm Modular Manifold

namespace Work.Asymptotics

open Work.Asymptotics

/-- The group algebra element attached to an optional scalar multiple of a group element. -/
def ofOptC : Option (ℂ × X) → R
  | none => 0
  | some p => p.1 • ofSL p.2

@[simp] lemma ofOptC_none : ofOptC (none : Option (ℂ × X)) = 0 := rfl
@[simp] lemma ofOptC_some (c : ℂ) (γ : X) : ofOptC (some (c, γ)) = c • ofSL γ := rfl

/-- The algebraic content of the finite check at odd weight. -/
def CarryOkOdd (ν : X) (i : Fin 6) (a b : Option (ℂ × X)) : Prop :=
  rowDiffOdd ν i - ((R_T - 1) ^ 2 * ofOptC a + R_S * (R_T - 1) ^ 2 * ofOptC b)
    ∈ augIdealOdd

/-- The `(T-I)²`-carry is compatible with the propagation hypothesis: its support consists of group
elements whose `T`-translates map the relevant points of `O_F` into `O`. -/
def SafePairOdd (ν : X) (i : Fin 6) (a : Option (ℂ × X)) : Prop :=
  ∀ (c : ℂ) (γ : X), a = some (c, γ) →
    ({γ, ModularGroup.T * γ, ModularGroup.T * ModularGroup.T * γ} : Finset X) ⊆ SafeThick ν i

/-- The `S(T-I)²`-carry is compatible with the propagation hypothesis. -/
def SafePairSOdd (ν : X) (i : Fin 6) (b : Option (ℂ × X)) : Prop :=
  ∀ (c : ℂ) (γ : X), b = some (c, γ) →
    ({ModularGroup.S * γ, ModularGroup.S * (ModularGroup.T * γ),
      ModularGroup.S * (ModularGroup.T * ModularGroup.T * γ)} : Finset X) ⊆ SafeThick ν i

/-- `-δ` acts on `ℍ` by the same Möbius transformation as `δ`. -/
lemma neg_smul_SL (δ : X) (τ : ℍ) : (-δ) • τ = δ • τ := ModularGroup.SL_neg_smul δ τ

/-- **The geometry of the safe set.**  Every element of `SafeThick ν i` maps `τ` into `O`. -/
lemma smul_mem_of_mem_SafeThick_odd {O O_F : Set ℍ} {ν : X} {i : Fin 6} {τ : ℍ}
    (hMpO : ∀ j : Fin 6, ∀ σ ∈ O_F, (Mp j) • σ ∈ O) (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F)
    {γ : X} (hγ : γ ∈ SafeThick ν i) : γ • τ ∈ O := by
  have hbase : ∀ j : Fin 6, (Mp j) • τ ∈ O := fun j => hMpO j τ hτ
  have hpair : (Mp i * ν) • τ ∈ O := by
    rw [mul_smul]; exact hMpO i (ν • τ) hντ
  simp only [SafeThick, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and] at hγ
  rcases hγ with ((c1 | c2) | c3) | c4
  · obtain ⟨j, rfl⟩ := c1
    exact hbase j
  · obtain ⟨δ, ⟨j, rfl⟩, rfl⟩ := c2
    rw [neg_smul_SL]
    exact hbase j
  · rw [c3]
    exact hpair
  · rw [c4, neg_smul_SL]
    exact hpair

end Work.Asymptotics
