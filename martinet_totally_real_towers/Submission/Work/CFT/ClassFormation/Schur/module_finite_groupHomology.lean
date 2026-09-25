import Mathlib
import Submission.Work.CFT.ClassFormation.Defs

/-!
# Finiteness of group homology with finitely generated coefficients

The inhomogeneous chain complex computing the group homology of a `k`-linear `G`-representation
`A` has chain modules `Cₙ(G, A) = (Fin n → G) →₀ A`.  When `G` is finite and `A` is a finitely
generated `k`-module (e.g. `A = V` with trivial `G`-action), each chain module is finitely
generated over `k`.  Since `k` is Noetherian, the `n`-cycles form a finitely generated
`k`-module, and `Hₙ(G, A)`, being a quotient of the cycles, is finitely generated as well.

This is the `k`-linear generalisation of `Work.CFT.ClassFormation.Schur.finite_HnZ`.
-/

namespace Work.CFT.ClassFormation.Schur

open CategoryTheory

/-- The degree-`n` chain group `Cₙ(G, V) = (Fin n → G) →₀ V` of the inhomogeneous chain complex
computing `H_*(G, V)` is a finitely generated `k`-module when `G` is finite and `V` is a
finitely generated `k`-module. -/
lemma module_finite_inhomogeneousChains (k : Type) [CommRing k]
    (G : Type) [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) :
    Module.Finite k ((groupHomology.inhomogeneousChains (Rep.trivial k G V)).X n : Type) := by
  show Module.Finite k ((Fin n → G) →₀ V)
  infer_instance

/-- **Finiteness of group homology.**  For a finite group `G`, a Noetherian ring `k` and a
finitely generated `k`-module `V` (with trivial `G`-action), the homology `H_n(G, V)` is a
finitely generated `k`-module for every `n`.  It is a subquotient of the degree-`n` term of the
inhomogeneous chain complex of `Rep.trivial k G V`, which is `(Fin n → G) →₀ V`, a finitely
generated `k`-module; since `k` is Noetherian, submodules and quotients stay finitely
generated. -/
theorem module_finite_groupHomology (k : Type) [CommRing k] [IsNoetherianRing k]
    (G : Type) [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) :
    Module.Finite k (groupHomology (Rep.trivial k G V) n) := by
  classical
  -- `S` is the short complex `Cₙ₊₁(G,V) ⟶ Cₙ(G,V) ⟶ Cₙ₋₁(G,V)`; its middle term is `S.X₂`,
  -- and `H_n(G,V) = (inhomogeneousChains V).homology n = S.homology`.
  set S := (groupHomology.inhomogeneousChains (Rep.trivial k G V)).sc n
  -- The `n`-chains `Cₙ(G,V) = (Fin n → G) →₀ V` form a finitely generated `k`-module.
  have hfin : Module.Finite k (S.X₂ : Type) :=
    module_finite_inhomogeneousChains k G n
  -- Hence they are Noetherian (`k` is a Noetherian ring).
  have hNoeth : IsNoetherian k (S.X₂ : Type) :=
    isNoetherian_of_isNoetherianRing_of_finite k _
  -- The `n`-cycles, i.e. the kernel of the differential `Cₙ(G,V) ⟶ Cₙ₋₁(G,V)`, are therefore
  -- finitely generated.
  have hker : Module.Finite k (S.g.hom.ker : Type) :=
    Module.Finite.of_fg (IsNoetherian.noetherian (S.g.hom.ker))
  -- `H_n` is the quotient of the cycles by the `n`-boundaries, so it is finitely generated too;
  -- here `S.moduleCatLeftHomologyData.H` is exactly this quotient of `S.g.hom.ker`.
  have hH : Module.Finite k (S.moduleCatLeftHomologyData.H : Type) := by
    rw [ShortComplex.moduleCatLeftHomologyData_H]
    exact Module.Finite.quotient k _
  -- Finally transport finiteness along the isomorphism `S.homology ≅ S.moduleCatLeftHomologyData.H`.
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

end Work.CFT.ClassFormation.Schur
