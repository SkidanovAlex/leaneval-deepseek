import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# The coface sum `Φ` squares to zero

`Work.SingMV.phi n = Σᵢ (-1)ⁱ (δᵢ)∗ : C(Δⁿ) ⟶ C(Δⁿ⁺¹)` is the alternating sum of the
pushforwards along the coface inclusions, i.e. the differential of the alternating *coface*
map complex of the cosimplicial object `n ↦ C(Δⁿ)` (singular chains of the standard
simplices, with cofaces given by the topological cofaces). The simplicial identity
`δ_j ∘ δ_i = δ_{j-1} ∘ δ_i` (`i < j`) forces the double sum `Φ n ≫ Φ (n+1)` to cancel
pairwise, which is Mathlib's `AlternatingCofaceMapComplex.d_squared`.

The only content here is the identification `phi = AlternatingCofaceMapComplex.objD`, which is
definitional.
-/

open CategoryTheory

namespace Work.SingMV

/-- The singular chains of the standard simplices, as a cosimplicial object in chain complexes:
the `n`-th term is `C(Δⁿ)`, and the coface `δᵢ` is the pushforward along the topological
coface inclusion `coface n i`. -/
noncomputable abbrev singCcs : CosimplicialObject (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  SimplexCategory.toTop₀ ⋙ Submission.Blueprint.singC

/-- `Work.SingMV.phi n` is the `n`-th differential of the alternating coface map complex of the
cosimplicial object `singCcs`; the two are the same alternating sum of cofaces by definition. -/
lemma phi_eq_objD (n : ℕ) :
    phi n = AlgebraicTopology.AlternatingCofaceMapComplex.objD singCcs n := rfl

theorem phi_comp_phi (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.SingMV.phi n) (Work.SingMV.phi (n+1)) = 0 := by
  rw [phi_eq_objD n, phi_eq_objD (n + 1)]
  exact AlgebraicTopology.AlternatingCofaceMapComplex.d_squared singCcs n

end Work.SingMV
