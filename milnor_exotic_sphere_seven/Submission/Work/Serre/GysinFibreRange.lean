import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The global Thom class of a rational spherical fibration, in the fibre-given range

This module fixes the **crux** of E3(b) (`Work.Serre.SerreE3b`): the *relative* Thom class of the
mapping-cylinder fibration, and the fact that the mixed cup product with it is an isomorphism in the
range given by the *fibre*'s knowledge.

## The mathematical statement

Let `p : E → B` be a Serre fibration with `B` simply connected, `E` rationally acyclic, and strict
fibre `F = p⁻¹{b₀}` a rational `r`-sphere *through degree `N`* (i.e. `H_t(F;ℚ) = 0` for
`0 < t ≤ N`, `t ≠ r`, and `H_r(F;ℚ) ≅ ℚ`).  Let `M_p := cyl p` be the mapping cylinder of `p`, with
the copy `E ⊆ M_p` of the source at the bottom (`cylIncl p`); then the pair `(M_p, E)` is a
"disc-pair fibration" over `B` with fibre pair `(CF, F) ≅ (D^{r+1}, S^r)`, whose rational homology
is `ℚ` in degree `r+1` only.

The **Thom class** is the relative class `U ∈ H^{r+1}(M_p, E;ℚ)` restricting to the generator of the
fibre pair, and the **Thom isomorphism** says that

  `x ↦ p^*(x) ⌣ U : H^m(B;ℚ) ≅ H^{m+r+1}(M_p, E;ℚ)`

is an isomorphism for `m + r + 1 ≤ N + 1` — the range given by the *fibre*, with no connectivity
hypothesis on `B` beyond simple connectivity (which is the orientability of the fibration: without
it the local systems are twisted; cf. `Work.RatHurewicz.FibreRangeGysin`).

This is the missing global Thom statement of the Thom chapter (the local input is
`Work.StemsB.ModelThomRat`, the Thom class of the *trivial* disc pair over an arbitrary base; the
global statement is produced by the cell-by-cell induction over a CW model of `B`, blueprint K5:
over each cell the fibration is fibrewise trivial, so the cell step is the local model, and the
fibre pair being concentrated in one degree makes the induction degenerate in the stated range).

## How it is used

`Work.Serre.serreE3b_of_thomCyl` derives `Work.Serre.SerreE3b` from it: the class
`e := (cylInr p)^*(U|)` (the absolute class induced by `U`) satisfies `x ⌣ e = Φ(x)`, where `Φ` is
the composite of the Thom isomorphism above with the two isomorphisms `relToAbs` (available in
degree `≥ 2` because `H^*(E;ℚ)` vanishes in positive degrees) and `(cylInr p)^*` (available because
`cylRetract p` and `cylInr p` are homotopy inverse).  Hence `⌣ e` is an isomorphism in the range,
which is `Work.Serre.SerreE3b`.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The global Thom class / Thom isomorphism of a rational spherical fibration, in the range given
by the fibre.**  See the module docstring. -/
def ThomIsoCylFibreRange : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (r N : ℕ),
    1 ≤ r → Work.StemsB.IsSerreFibration p → SimplyConnectedSpace B → RatAcyclic E →
      PathConnectedSpace (Work.StemsB.fibre p b₀) →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) t)) →
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∃ U : Work.Thom.RelCoh ℚ (r + 1) (cyl p) (Set.range (cylIncl p)),
        ∀ m : ℕ, m + r + 1 ≤ N + 1 →
          IsIso (ModuleCat.ofHom
            (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U ∘ₗ
              (Work.Thom.CohMap (cylRetract p) ℚ m).hom))

end

end Work.Serre
