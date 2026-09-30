import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Finiteness of the cohomology of a space with finitely generated integral homology

If the integral homology `H_i(X;ℤ)` is finitely generated for every `i ≤ M`, then for **every**
field `𝕜` the cohomology `H^s(X;𝕜)` is finite dimensional for every `s ≤ M`.

The two ingredients are the standard ones.

* *Finiteness of homology with field coefficients.*  `Work.Pi6.EMM2.moduleFinite_singularHomology`
  (the universal coefficient theorem read in the Serre class of finite dimensional vector spaces:
  characteristic zero goes through flatness of `ℤ → 𝕜`, characteristic `p` through
  `H_*(X;ℤ/p)` and the flat base change `ℤ/p → 𝕜`) shows that `H_s(X;𝕜)` is a finitely generated
  `𝕜`-module as soon as `H_s(X;ℤ)` and `H_{s-1}(X;ℤ)` are finitely generated.
* *Duality over a field.*  For a field `𝕜` no finiteness hypothesis is needed for the universal
  coefficient theorem (`Work.StemsB.fieldDualUCT`): `H^s(X;𝕜) ≅ Hom_𝕜(H_s(X;𝕜), 𝕜)`.  The
  `𝕜`-dual of a finitely generated module is finitely generated, so `H^s(X;𝕜)` is finite
  dimensional.
-/

namespace Work.Pi6.K2Z

open CategoryTheory

theorem finiteDimCoh {𝕜 : Type} [Field 𝕜] (X : Type) [TopologicalSpace X] (M : ℕ)
    (hfg : ∀ i : ℕ, i ≤ M → Module.Finite ℤ (Work.Pi6.HR ℤ X i)) :
    ∀ s : ℕ, s ≤ M → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 X s) := by
  intro s hs
  haveI hHR : FiniteDimensional 𝕜 (Work.Pi6.HR 𝕜 X s) :=
    Work.Pi6.EMM2.moduleFinite_singularHomology 𝕜 X M hfg s hs
  obtain ⟨e⟩ := Work.StemsB.fieldDualUCT (F := 𝕜)
    (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) s
  exact Module.Finite.equiv (Iso.toLinearEquiv e).symm

end Work.Pi6.K2Z
