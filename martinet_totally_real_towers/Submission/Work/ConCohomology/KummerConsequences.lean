/-
Copyright: the martinet_totally_real_towers team.

# Consequences of the Kummer sequence

Specialisations of the long exact sequence (`Work.ConCohomology.exact_H0_C`,
`exact_H2_B`, `kummer_H1_surjective`, `kummer_H2_injective`) to the Kummer sequence
`Work.ConCohomology.kummerSES n : 0 → μ_n → B →ⁿ n·B → 0`:

* `kummer_H2_range_eq_ker` : the image of `H²(G,μ_n)` in `H²(G,B)` is exactly the kernel of the
  `n`-th power map (i.e. `H²(G,μ_n)` is the `n`-torsion of `H²(G,B)`), when `H¹(G,B)` and
  `H¹(G,n·B)` vanish -- for `B = Additive Lˣ` these are Hilbert 90 (`hilbert90_infinite_units`);
* `kummer_H1_ker` : the kernel of `δ⁰ : H⁰(G,n·B) → H¹(G,μ_n)` is the image of the `n`-th power
  map on the `G`-invariants, so `H¹(G,μ_n) ≅ H⁰(G,n·B)/im(n·)` (Kummer theory) since `δ⁰` is onto
  when `H¹(G,B) = 0`.

For `B = Additive Lˣ`, `G = Gal(L/K)`: `H⁰(G,B) = Kˣ`, `n·` on it is `x ↦ xⁿ`, and
`H⁰(G,n·B) = K^× ∩ (L^×)ⁿ`, which gives `H¹(Gal(L/K), μ_n) ≅ (K^× ∩ (L^×)ⁿ)/(K^×)ⁿ`, and
`≅ K^×/(K^×)ⁿ` when `L = K^sep` (every element of `K^×` is an `n`-th power in `L`).
-/

import Submission.Work.ConCohomology.Kummer
import Submission.Work.ConCohomology.LongExact
import Submission.Work.ConCohomology.kummer_H1_surjective
import Submission.Work.ConCohomology.kummer_H2_injective

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section Consequences

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {B : Type*} [AddCommGroup B] [DistribMulAction G B] [IsDiscreteGModule G B]

variable (n : ℕ)

/-- **Kummer/Kronecker, degree 2, surjectivity.**  Every class of `H²(G,B)` killed by the `n`-th
power map comes from `H²(G,μ_n)` (via the Kummer sequence `0 → μ_n → B →ⁿ n·B → 0`), provided
`H¹(G,B) = H¹(G,n·B) = 0`.  With `hilbert90_infinite_units` this is the statement that every
`n`-torsion Brauer class of a field comes from a Kummer class. -/
theorem kummer_H2_torsion_range (hB : Subsingleton (H1 G B))
    (hC : Subsingleton (H1 G ↥(nPowers (G := G) (B := B) n))) (y : H2 G B)
    (hy : H2Map (kummerG (G := G) (B := B) n) y = 0) :
    ∃ x : H2 G ↥(nTorsion (G := G) (B := B) n),
      H2Map (kummerF (G := G) (B := B) n) x = y :=
  (exact_H2_B (kummerSES (G := G) (B := B) n) y).mp hy

/-- **Kummer/Kronecker, degree 2, injectivity.**  If `H¹(G,B) = H¹(G,n·B) = 0` then the map
`H²(G,μ_n) → H²(G,B)` is injective, so together with `kummer_H2_torsion_range` it identifies
`H²(G,μ_n)` with the `n`-torsion of `H²(G,B)`. -/
theorem kummer_H2_inj (hB : Subsingleton (H1 G B))
    (hC : Subsingleton (H1 G ↥(nPowers (G := G) (B := B) n))) :
    Function.Injective (H2Map (kummerF (G := G) (B := B) n)) :=
  kummer_H2_injective (kummerSES (G := G) (B := B) n) hB hC

/-- **Kummer theory, degree 1.**  The kernel of `δ⁰ : H⁰(G,n·B) → H¹(G,μ_n)` is the image of the
`n`-th power map on the `G`-invariants. -/
theorem kummer_H1_ker (c : H0 G ↥(nPowers (G := G) (B := B) n)) :
    connecting0 (kummerSES (G := G) (B := B) n) c = 0 ↔
      ∃ b : H0 G B, H0Map (kummerG (G := G) (B := B) n) b = c :=
  exact_H0_C (kummerSES (G := G) (B := B) n) c

end Consequences

end Work.ConCohomology
