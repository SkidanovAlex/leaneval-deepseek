import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators

set_option backward.isDefEq.respectTransparency false

open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

noncomputable section

/-- The joint weight space of the Serre-constructed `e₈` at an **integral** weight `μ`, i.e. the
set of `x` with `⁅Hᵢ, x⁆ = μᵢ • x` for all `i`, where `Hᵢ` is the image of the `i`-th `H`
generator in `e₈`. -/
private abbrev Wi (μ : Fin 8 → ℤ) : Submodule ℂ (LieAlgebra.e₈ ℂ) :=
  ⨅ i : Fin 8, LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH i) - (μ i : ℂ) • 1)

private lemma mem_Wi_iff {μ : Fin 8 → ℤ} {x : LieAlgebra.e₈ ℂ} :
    x ∈ Wi μ ↔ ∀ i, ⁅SerreH i, x⁆ = (μ i : ℂ) • x := by
  simp only [Wi, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, LieAlgebra.ad_apply, sub_eq_zero]

/-- The bracket of two weight vectors is a weight vector, the weights adding. -/
private lemma bracket_mem_Wi {μ ν : Fin 8 → ℤ} {x y : LieAlgebra.e₈ ℂ}
    (hx : x ∈ Wi μ) (hy : y ∈ Wi ν) : ⁅x, y⁆ ∈ Wi (μ + ν) := by
  rw [mem_Wi_iff] at hx hy ⊢
  intro i
  rw [leibniz_lie, hx i, hy i, smul_lie, lie_smul, Pi.add_apply, Int.cast_add, add_smul]

private lemma SerreH_mem_Wi_zero (i : Fin 8) : SerreH i ∈ Wi (0 : Fin 8 → ℤ) := by
  rw [mem_Wi_iff]
  intro j
  rw [serreLie_HH, Pi.zero_apply, Int.cast_zero, zero_smul]

private lemma SerreE_mem_Wi (i : Fin 8) : SerreE i ∈ Wi (fun j => E8 j i) :=
  mem_Wi_iff.mpr fun j => by rw [serreLie_H_E, Int.cast_smul_eq_zsmul]

private lemma SerreF_mem_Wi (i : Fin 8) : SerreF i ∈ Wi (fun j => -E8 j i) :=
  mem_Wi_iff.mpr fun j =>
    (serreLie_H_F j i).trans (Int.cast_smul_eq_zsmul ℂ (-E8 j i) (SerreF i)).symm

/-- Bracketing with a fixed weight vector preserves the sum of all integral weight spaces. -/
private lemma ad_mem_iSup_Wi {μ : Fin 8 → ℤ} {x : LieAlgebra.e₈ ℂ} (hx : x ∈ Wi μ)
    {y : LieAlgebra.e₈ ℂ} (hy : y ∈ ⨆ ν : Fin 8 → ℤ, Wi ν) :
    ⁅x, y⁆ ∈ ⨆ ν : Fin 8 → ℤ, Wi ν := by
  refine Submodule.iSup_induction (p := fun ν : Fin 8 → ℤ => Wi ν)
    (motive := fun y => ⁅x, y⁆ ∈ ⨆ ν : Fin 8 → ℤ, Wi ν) hy ?_ ?_ ?_
  · intro ν y hyν
    exact Submodule.mem_iSup_of_mem (μ + ν) (bracket_mem_Wi hx hyν)
  · rw [lie_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    rw [lie_add]
    exact Submodule.add_mem _ ha hb

/-- **The sum of all integral weight spaces is closed under the Lie bracket.** -/
private lemma lie_mem_iSup_Wi {x y : LieAlgebra.e₈ ℂ}
    (hx : x ∈ ⨆ μ : Fin 8 → ℤ, Wi μ) (hy : y ∈ ⨆ μ : Fin 8 → ℤ, Wi μ) :
    ⁅x, y⁆ ∈ ⨆ μ : Fin 8 → ℤ, Wi μ := by
  refine (Submodule.iSup_induction (p := fun μ : Fin 8 → ℤ => Wi μ)
    (motive := fun x => ∀ y ∈ ⨆ μ : Fin 8 → ℤ, Wi μ, ⁅x, y⁆ ∈ ⨆ μ : Fin 8 → ℤ, Wi μ)
    hx ?_ ?_ ?_) y hy
  · intro μ x hxμ y hy
    exact ad_mem_iSup_Wi hxμ hy
  · intro y hy
    rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b ha hb y hy
    rw [add_lie]
    exact Submodule.add_mem _ (ha y hy) (hb y hy)

/-- The sum of all integral weight spaces of the Serre-constructed `e₈`, as a Lie subalgebra. -/
private noncomputable def Z : LieSubalgebra ℂ (LieAlgebra.e₈ ℂ) :=
  { toSubmodule := ⨆ μ : Fin 8 → ℤ, Wi μ
    lie_mem' := fun {_ _} hx hy => lie_mem_iSup_Wi hx hy }

private lemma Z_toSubmodule : (Z : Submodule ℂ (LieAlgebra.e₈ ℂ)) = ⨆ μ : Fin 8 → ℤ, Wi μ :=
  rfl

/-- **`e₈` is spanned by its integral weight spaces.**

Each Serre generator is an eigenvector for every `ad H i` with integer eigenvalue (`0` for the
`H`-generators, the entries of the Cartan matrix for the `E`-generators and their negatives for
the `F`-generators), and since brackets of weight vectors are weight vectors, the sum of the
weight spaces is a Lie subalgebra; it contains all the generators, hence is everything. -/
theorem e8_weightSpace_iSup_eq_top :
    (⨆ μ : Fin 8 → ℤ, ⨅ i : Fin 8, LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - (μ i : ℂ) • 1))
    = (⊤ : Submodule ℂ (LieAlgebra.e₈ ℂ)) := by
  have hgen : ∀ g : CartanMatrix.Generators (Fin 8),
      LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ g) ∈ Z := by
    intro g
    cases g with
    | H i => exact Submodule.mem_iSup_of_mem 0 (SerreH_mem_Wi_zero i)
    | E i => exact Submodule.mem_iSup_of_mem (fun j => E8 j i) (SerreE_mem_Wi i)
    | F i => exact Submodule.mem_iSup_of_mem (fun j => -E8 j i) (SerreF_mem_Wi i)
  have htop : Z = ⊤ := eq_top_of_lieSubalgebra_of_generators CartanMatrix.E₈ Z hgen
  rw [Submodule.eq_top_iff']
  intro x
  have hxZ : x ∈ Z := by rw [htop]; trivial
  exact hxZ

end

end Commons.Algebra.Lie.SerreConstruction
