import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.LogLattice

open Module

/-- **A `ℤ`-basis of a full lattice is an `ℝ`-basis of the ambient real vector space.**  If `M` is a
finitely generated additive subgroup of a real vector space `V` which spans `V` over `ℝ`, and `bM`
is a `ℤ`-basis of `M` indexed by `Fin (finrank ℝ V)`, then the images of the `bM i` in `V` form an
`ℝ`-basis of `V`. -/
theorem realBasis_of_full_lattice {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : AddSubgroup V) [Module.Finite ℤ ↥M]
    (hMspan : Submodule.span ℝ (M : Set V) = ⊤)
    (bM : Module.Basis (Fin (Module.finrank ℝ V)) ℤ ↥M) :
    ∃ bMR : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ i, bMR i = ((bM i : ↥M) : V) := by
  classical
  -- the image family in `V`
  let f : Fin (Module.finrank ℝ V) → V := fun i => ((bM i : ↥M) : V)
  -- `f` spans `V`: the `ℤ`-basis `bM` generates `M` as a `ℤ`-module, so its image generates `M`
  -- as an additive subgroup of `V`, whence `M ⊆ span ℝ (range f)` and `span ℝ M = ⊤`.
  have hle : ⊤ ≤ Submodule.span ℝ (Set.range f) := by
    rw [← hMspan, Submodule.span_le]
    intro x hx
    set x' : ↥M := ⟨x, hx⟩ with hx'
    have hrepr : ∑ i, (bM.repr x') i • bM i = x' := bM.sum_repr x'
    have hcoe : (x' : V) = ∑ i, (((bM.repr x') i : ℤ) : ℝ) • f i := by
      conv_lhs => rw [← hrepr]
      rw [show (↑(∑ i, (bM.repr x') i • bM i) : V)
          = ∑ i, (↑((bM.repr x') i • bM i) : V) from
        map_sum (AddSubgroup.subtype M) (fun i => (bM.repr x') i • bM i) Finset.univ]
      apply Finset.sum_congr rfl
      intro i _
      rw [AddSubgroup.coe_zsmul]
      simp only [f, Int.cast_smul_eq_zsmul]
    have : x = ∑ i, (((bM.repr x') i : ℤ) : ℝ) • f i := hcoe
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- a spanning family of `finrank ℝ V` vectors is a basis
  refine ⟨basisOfTopLeSpanOfCardEqFinrank f hle (by simp), fun i => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]

end NK.GlobalCFTdeep.LogLattice
