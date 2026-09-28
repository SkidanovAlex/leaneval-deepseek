import Mathlib
import Submission.Work.HP.Transf.Basic

/-!
# Independent families in a `ℤ`-submodule of `ℝ^ι` (`Work.HP.Transf.indep_of_le_finrank`)

If `L ⊆ ℝ^ι` is a `ℤ`-submodule whose real span has dimension `rkR L ≥ k`, then `L` contains
`k` vectors that are linearly independent over `ℝ`.

The proof takes a maximal `ℝ`-linearly independent subset `b` of `L` (Mathlib's
`exists_linearIndependent`), which is finite because `ℝ^ι` is finite dimensional and which
spans the same real space as `L`.  Hence `b` has exactly `rkR L` elements, and any `k` of them
work.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Transf

theorem indep_of_le_finrank {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) {k : ℕ}
    (hk : k ≤ rkR L) :
    ∃ f : Fin k → (ι → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f := by
  classical
  -- A maximal `ℝ`-linearly independent subset of `L`, spanning the same real space as `L`.
  obtain ⟨b, hbL, hspan, hli⟩ := exists_linearIndependent ℝ (L : Set (ι → ℝ))
  -- It is finite, since `ℝ^ι` is finite dimensional.
  letI : Fintype b := hli.setFinite.fintype
  -- ... and it has exactly `rkR L` elements.
  have hcard : Fintype.card b = rkR L := by
    rw [rkR, ← hspan, ← Set.toFinset_card]
    exact (finrank_span_set_eq_card hli).symm
  have hk' : k ≤ Fintype.card b := hk.trans_eq hcard.symm
  let e := Fintype.equivFin b
  let g : Fin k → b := fun j => e.symm (Fin.castLE hk' j)
  have hg : Function.Injective g := (e.symm.injective).comp (Fin.castLE_injective hk')
  exact ⟨fun j => (g j : ι → ℝ), fun j => hbL (g j).2, hli.comp g hg⟩

end Work.HP.Transf
