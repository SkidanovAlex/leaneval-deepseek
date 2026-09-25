import Mathlib
import Submission.Work.ConCohomology.Extension

namespace Work.ConCohomology

/-- The conjugation action of `G` on `1`-cochains on `N` (see `conjCochain`) carries the
`N`-coboundary of `m` to the `N`-coboundary of `g • m`:

`g · d⁰_N(m) = d⁰_N(g • m)`.

This is the statement that the conjugation action on `H¹(N,M)` is compatible with the action of
`G` on `M`, and it is exactly what makes the coinvariants `H¹(N,M)_Q` (as opposed to invariants)
the right receptacle for the transgression: the transgression `tg` of the extension is defined on
`H¹(N,M)_Q`, and on the coboundaries this identification is the content of the lemma.

Proof: at `n`,
`(g·d⁰m)(n) = g • d⁰m(g⁻¹ n g) = g • ((g⁻¹ n g) • m - m) = g • ((g⁻¹ n g) • m) - g • m`,
and `g • ((g⁻¹ n g) • m) = ((g g⁻¹ n g) • m) = (n g) • m = n • (g • m)`,
where we used `hcompN` to replace the `N`-action by the `G`-action through `E.i` and `E.i_conj`
for `E.i (E.conj g⁻¹ n) = g⁻¹ * E.i n * g`. Thus the result is `n • (g • m) - g • m = d⁰(g • m) n`. -/
lemma conjCochain_coboundary {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] [IsDiscreteGModule N M] (E : GroupExt G Q N)
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m)
    (hcont : ∀ g : G, Continuous (E.conj g)) (g : G) (m : M) :
    (conjCochain E hcont g (d0Hom (G := N) (M := M) m) : N → M) =
      d0Fun (G := N) (g • m) := by
  funext n
  rw [conjCochain_apply]
  show g • ((d0Hom (G := N) (M := M) m : Cochain1 N M) (E.conj g⁻¹ n)) =
      d0Fun (G := N) (g • m) n
  rw [d0Hom_apply, d0Fun_apply, smul_sub]
  congr 1
  rw [hcompN (E.conj g⁻¹ n) m, E.i_conj, ← mul_smul,
    show g * (g⁻¹ * E.i n * (g⁻¹)⁻¹) = E.i n * g from by group, mul_smul,
    ← hcompN n (g • m)]

end Work.ConCohomology
