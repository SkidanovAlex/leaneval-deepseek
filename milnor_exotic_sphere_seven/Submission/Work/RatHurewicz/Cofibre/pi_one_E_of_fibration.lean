import Mathlib
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.Excision
import Submission.Work.Serre.piMap_fibreIncl_surjective_pi1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `π₁` of the total space of a fibration with `k`-connected fibre (`k ≥ 2`) and `π₁(B) = 0`

For a Hurewicz fibration `p : E → B` whose fibre over `p e₀` is `k`-connected with `k ≥ 2`, the
total space `E` has trivial `π₁` as soon as `π₁(B)` vanishes.  This is the `J = 1` case of the
connectivity of the total space, which the workspace's fibration long exact sequence
(`Work.StemsB.les_exact_E`, exactness at `π_{k+2}(E)` for `k ≥ 0`) does not cover: it only reaches
degrees `≥ 2`.

The degree-one input is the dedicated lemma `Work.Serre.piMap_fibreIncl_surjective_pi1`: for any
Serre fibration whose base has trivial `π₁`, the fibre inclusion induces a **surjection** on `π₁`
(proved there from the relative homotopy lifting property `Work.StemsB.exists_lift_rel`, by lifting
a null-homotopy of the projected loop with the lateral boundary prescribed).  Since the source
`π₁(F)` is a subsingleton, so is the target, and that target is `π₁(E, e₀)`.

Note that the two descriptions of the fibre,
`Work.StemsB.fibre p (p e₀) = {x // p x = p e₀}` and `↥(p ⁻¹' {p e₀})`, are *definitionally*
equal, as are their base points `Work.StemsB.fibrePoint p e₀` and `⟨e₀, rfl⟩`, so no transport
along `propext` is needed.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz.Cofibre

noncomputable section

/-- **`π_1` of the total space is trivial**, Serre-fibration form: for a Serre fibration `p : E → B`
with `k`-connected fibre over `p e₀` (`k ≥ 2`) and `π_1(B) = 0`.

The hypotheses on the fibre and on the base are used only in degree `1`; the general shape
(`j ≤ k`, `j ≤ 2 * k - 1`, `j ≠ k`) is inherited from the `J = 1` instance of the statement. -/
theorem pi_one_E_of_serreFibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩))
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀))) :
    Subsingleton (HomotopyGroup (Fin 1) E e₀) := by
  -- `π₁(B) = 0`
  have hB : Subsingleton (HomotopyGroup (Fin 1) B (p e₀)) :=
    hmodel 1 (by omega) (by omega)
  -- `π₁` of the fibre over `p e₀` is trivial (`k ≥ 2` in particular `1 ≤ k`)
  have hfibre : Subsingleton (HomotopyGroup (Fin 1) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀)) :=
    hconn 1 (by omega)
  -- the fibre inclusion is surjective on `π₁`; a surjection out of a subsingleton has a
  -- subsingleton target
  exact (Work.Serre.piMap_fibreIncl_surjective_pi1 p hp e₀ hB).subsingleton

/-- **`π_1` of the total space is trivial** for a Hurewicz fibration `p : E → B` with `k`-connected
fibre over `p e₀` (`k ≥ 2`) and `π_1(B) = 0`.

This is the `J = 1` case of the connectivity of the total space, which the workspace's fibration long
exact sequence (`Work.StemsB.les_exact_E`, exactness at `π_{k+2}(E)` for `k ≥ 0`) does not cover: it
only reaches degrees `≥ 2`.

**Route (corrected — the first suggestion was invalid).** `Work.Serre.piMap_fibreIncl_surjective_of_subsingleton`
requires `1 ≤ m` and only reaches degree `m+1 ≥ 2`, so it does *not* apply at `m = 0`.  The degree-one
statement is the dedicated lemma `Work.Serre.piMap_fibreIncl_surjective_pi1`
(equivalently `fibrationPiOne_surjective`): the fibre inclusion is surjective on `π_1` when `π_1` of the
base vanishes.  Together with `hconn 1` (the fibre's `π_1` is trivial) a surjection whose source is a
subsingleton has a subsingleton target.  Alternatively, reprove it directly from the relative homotopy
lifting property `Work.StemsB.exists_lift_rel`: lift a null-homotopy of the projected loop and contract
inside the fibre.  Note `Work.StemsB.fibre p (p e₀) = {x // p x = p e₀}` is only `propext`-equal to
`↥(p ⁻¹' {p e₀})`, so a small transport is needed. -/
theorem pi_one_E_of_fibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩))
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀))) :
    Subsingleton (HomotopyGroup (Fin 1) E e₀) :=
  pi_one_E_of_serreFibration p hp.isSerreFibration e₀ k hk hconn hmodel

end

end Work.RatHurewicz.Cofibre
