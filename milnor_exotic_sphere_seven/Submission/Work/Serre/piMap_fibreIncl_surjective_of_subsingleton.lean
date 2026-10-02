import Mathlib
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.PiMap
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.RelHomotopy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Trivial `π_{m+1}(B)` forces `π_{m+1}(F) → π_{m+1}(E)` onto

For a Serre fibration `p : E → B` with fibre `F = p ⁻¹' {p e₀}`, the long exact homotopy sequence
`⋯ → π_{m+1}(F) →^{i_*} π_{m+1}(E) →^{p_*} π_{m+1}(B) →^{∂} π_m(F) → ⋯` is exact at `π_{m+1}(E)`:
`im(i_*) = ker(p_*)`.  If `π_{m+1}(B)` is trivial then `p_*` is the zero map, so its kernel is
everything and `i_*` is onto.

This is the degree-`m` surjectivity that the stable-stems (Serre) input needs, in the "one degree
up in the base" form: `Subsingleton (π_{m+1}(B))` gives surjectivity of `π_{m+1}(F) → π_{m+1}(E)`.
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- **Surjectivity of `π_{m+1}(F) → π_{m+1}(E)` when `π_{m+1}(B)` vanishes.**

Uses the exactness at `π_{m+1}(E)` of the long exact homotopy sequence of the Serre fibration `p`
(`Work.StemsB.fibrationLES_of_isSerreFibration`), evaluated at `k = m - 1`: writing `m = m' + 1`,
the first exactness clause reads `MulExact (πmap (fibreIncl p (p e₀)) (m'+1) _) (πmap p (m'+1) e₀)`,
i.e. `y ∈ range i_* ↔ p_* y = 1`; and `p_* y = 1` holds because the target `π_{m+1}(B)` is a
subsingleton. -/
theorem piMap_fibreIncl_surjective_of_subsingleton {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (m : ℕ)
    (hm : 1 ≤ m)
    (hB : Subsingleton (HomotopyGroup (Fin (m + 1)) B (p e₀))) :
    Function.Surjective (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) m
      (Work.StemsB.fibrePoint p e₀)) := by
  -- Write `m = m' + 1`, so that the LES clause with `k = m'` is exactly the clause we need.
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨_, h1, -, -⟩ := Work.StemsB.fibrationLES_of_isSerreFibration p hp e₀ m'
  intro y
  -- `h1 y : p_* y = 1 ↔ y ∈ range i_*`; the left side holds since `π_{m+1}(B)` is a subsingleton.
  exact (h1 y).mp (Subsingleton.elim (Work.StemsB.πmap p (m' + 1) e₀ y) 1)

end Work.Serre
