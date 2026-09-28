import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_satLat

namespace Work.HP

/-- The saturation `satLat Λ` of an integral lattice has the same rank as `Λ`.
This is the universe-polymorphic form of `numaux.rk_satLat` (whose statement fixes `ι : Type`).
Route: spreading both lattices out over `ℚ` is rank preserving, and saturation does not change
the rational spread (`numaux.finrank_eq_finrank_spread`, `numaux.spread_satLat_eq`). -/
lemma rk_satLat_poly {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ)) :
    rk (satLat Λ) = rk Λ := by
  show Module.finrank ℤ (satLat Λ) = Module.finrank ℤ Λ
  rw [numaux.finrank_eq_finrank_spread (satLat Λ), numaux.finrank_eq_finrank_spread Λ,
      numaux.spread_satLat_eq]

/-- Every sublattice `L ⊆ ℤ^ι` is contained in a **primitive** (saturated, pure) sublattice of the
same rank: its saturation `{v | ∃ 0 ≠ n : ℤ, n • v ∈ L}`.

Route. `Submodule.smithNormalForm (Pi.basisFun ℤ ι) L` gives a basis `bM` of `ℤ^ι`, a basis `bL` of
`L`, an embedding `f : Fin n ↪ ι` and nonzero `a : Fin n → ℤ` with `(bL i : ι → ℤ) = a i • bM (f i)`.
Put `P := Submodule.span ℤ (Set.range fun i => (bM (f i) : ι → ℤ))`. The family `bM ∘ f` is
`ℤ`-independent (subfamily of a basis), so `Module.Basis.span` gives a basis of `P` indexed by
`Fin n`, whence `rk P = n = rk L` by `Module.finrank_eq_card_basis`. `L ≤ P` since each `bL i` lies in
`P` and the `bL i` span `L`. Finally `P` is primitive: its elements are exactly the `w` whose
`bM`-coordinates vanish outside `Set.range f`, so if `0 ≠ m • v ∈ P` then for `j ∉ Set.range f`
one has `m * (bM.repr v) j = (bM.repr (m • v)) j = 0` and hence `(bM.repr v) j = 0`, i.e. `v ∈ P`.
(The conclusion is the purity condition, which is exactly the definition of `IsPrimLat` in
`Submission.Work.HP.PairsAux`.)

We take the second (alternative) route: the saturation `satLat L = {v | ∃ 0 ≠ n, n • v ∈ L}`
of `L` contains `L` (`le_satLat`), is primitive (`isPrimLat_satLat`), and has the same
rank as `L` (`numaux.rk_satLat`, proved by spreading both lattices out over `ℚ`; saturation
does not change the rational span). -/
theorem exists_prim_super {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) :
    ∃ P : Submodule ℤ (ι → ℤ), L ≤ P ∧ IsPrimLat P ∧ rk P = rk L :=
  ⟨satLat L, le_satLat L, isPrimLat_satLat L, rk_satLat_poly L⟩

end Work.HP
