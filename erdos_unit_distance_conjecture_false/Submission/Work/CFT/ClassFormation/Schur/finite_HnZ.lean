import Mathlib
import Submission.Work.CFT.ClassFormation.Defs

/-!
# Finiteness of integral group homology

The inhomogeneous chain complex computing the group homology of a `k`-linear `G`-representation
`A` has chain modules `Cₙ(G,A) = (Fin n → G) →₀ A`.  For `A = ℤ` (with trivial `G`-action) and
`G` finite this is a finitely generated free `ℤ`-module, and `ℤ` is a Noetherian ring.  Since
`H_n(G,ℤ)` is a quotient of the `n`-cycles, which in turn form a submodule of `Cₙ(G,ℤ)`, it is
finitely generated as well.
-/

namespace Work.CFT.ClassFormation.Schur

open CategoryTheory

/-- The degree-`n` chain group `Cₙ(G, ℤ) = (Fin n → G) →₀ ℤ` of the inhomogeneous chain complex
computing `H_*(G, ℤ)` is a finitely generated `ℤ`-module when `G` is finite. -/
lemma finite_inhomogeneousChains (G : Type) [Group G] [Fintype G] (n : ℕ) :
    Module.Finite ℤ ((groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).X n : Type) := by
  show Module.Finite ℤ ((Fin n → G) →₀ ℤ)
  infer_instance

/-- **Finiteness of integral group homology.**  For a finite group `G` and every `n`, the
abelian group `H_n(G, ℤ)` is finitely generated.  It is a subquotient of the degree-`n` term of
the inhomogeneous chain complex of `Rep.trivial ℤ G ℤ`, which is `(Fin n → G) →₀ ℤ`, a finitely
generated free `ℤ`-module when `G` is finite; `ℤ` is Noetherian, so submodules and quotients stay
finitely generated.  (The extra fact that `|G|` annihilates `H_n(G,ℤ)` for `n ≥ 1`, hence that it
is actually finite, is not asserted here.) -/
theorem finite_HnZ (G : Type) [Group G] [Fintype G] (n : ℕ) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) n : Type) := by
  classical
  -- `S` is the short complex `Cₙ₊₁(G,ℤ) ⟶ Cₙ(G,ℤ) ⟶ Cₙ₋₁(G,ℤ)`; its middle term is `S.X₂`,
  -- and `H_n(G,ℤ) = (inhomogeneousChains ℤ).homology n = S.homology`.
  set S := (groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).sc n
  -- The `n`-chains `Cₙ(G,ℤ) = (Fin n → G) →₀ ℤ` form a finitely generated `ℤ`-module.
  have hfin : Module.Finite ℤ (S.X₂ : Type) :=
    finite_inhomogeneousChains G n
  -- Hence they are Noetherian (ℤ is a Noetherian ring).
  have hNoeth : IsNoetherian ℤ (S.X₂ : Type) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ _
  -- The `n`-cycles, i.e. the kernel of the differential `Cₙ(G,ℤ) ⟶ Cₙ₋₁(G,ℤ)`, are therefore
  -- finitely generated.
  have hker : Module.Finite ℤ (S.g.hom.ker : Type) :=
    Module.Finite.of_fg (IsNoetherian.noetherian (S.g.hom.ker))
  -- `H_n` is the quotient of the cycles by the `n`-boundaries, so it is finitely generated too;
  -- here `S.moduleCatLeftHomologyData.H` is exactly this quotient of `S.g.hom.ker`.
  have hH : Module.Finite ℤ (S.moduleCatLeftHomologyData.H : Type) := by
    rw [ShortComplex.moduleCatLeftHomologyData_H]
    exact Module.Finite.quotient ℤ _
  -- Finally transport finiteness along the isomorphism `S.homology ≅ S.moduleCatLeftHomologyData.H`.
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

/-- Restatement of `finite_HnZ` for the notation `HnZ G n = H_n(G, ℤ)` of
`Work.CFT.ClassFormation`. -/
lemma finite_HnZ' (G : Type) [Group G] [Fintype G] (n : ℕ) :
    Module.Finite ℤ (HnZ G n : Type) :=
  finite_HnZ G n

end Work.CFT.ClassFormation.Schur
