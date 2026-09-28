import Mathlib
import Submission.Work.Serre.RangeEMVanDefs

/-!
# The range form of C3 for FINITE coefficient groups

`Work.Serre.RangeEMVanOneFin` / `Work.Serre.RangeEMVanAllFin` are the *finite-group* forms of
`Work.Serre.RangeEMVanOne` / `Work.Serre.RangeEMVanAll` (this directory): the same statements with
the hypothesis "`π_{a+1}(W)` is a torsion group" (`∀ α, ∃ K > 0, α ^ K = 1`) replaced by the
*stronger* hypothesis "`π_{a+1}(W)` is a **finite** group" (`Nonempty (Fintype _)`).

They are the statements that the proved C3-for-finite-groups (`Work.Serre.serreC3Finite`,
`Submission/Work/Serre/serreC3Finite.lean`) discharges **unconditionally**, whereas
`RangeEMVanOne`/`RangeEMVanAll` need the full `SerreC3` (arbitrary torsion coefficient group).  A
torsion group is a filtered union of finite ones, so the finite statement is *strictly* weaker and
does not follow from the torsion one, nor conversely: see `README.md` §5.2.

The definitions are kept separate from the target file so that the modules proving them may import
them without a cycle.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **The `1`-type case of the range form of C3 for a finite coefficient group.**  Let `W` be a
connected space whose `π₁` is a *finite* abelian group and whose homotopy groups vanish in degrees
`2 ≤ i ≤ N`.  Then `H_t(W;ℚ) = 0` for `0 < t ≤ N-1`.

Same statement as `Work.Serre.RangeEMVanOne` with `Nonempty (Fintype (π₁ W w₀))` in place of the
torsion hypothesis; proved unconditionally from `Work.Serre.SerreC0` and
`Work.Serre.SerreC3Finite` in `Submission/Work/Serre/serreRangeEMVanOneFin.lean`. -/
def RangeEMVanOneFin : Prop :=
  ∀ (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    Nonempty (Fintype (HomotopyGroup (Fin 1) W w₀)) →
    (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 → IsZero (ratH (TopCat.of W) t)

/-- The degree-`a` case, as in `Work.Serre.RangeEMVanAllAux` but with `Nonempty (Fintype π_{a+1})`
in place of the torsion hypothesis. -/
def RangeEMVanAllAuxFin (a N : ℕ) : Prop :=
  ∀ (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    (∀ i : ℕ, 1 ≤ i → i ≤ N → i ≠ a + 1 → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    Nonempty (Fintype (HomotopyGroup (Fin (a + 1)) W w₀)) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 - 2 * a → IsZero (ratH (TopCat.of W) t)

/-- **The range form of C3 for a finite coefficient group, all degrees.**  Same statement as
`Work.Serre.RangeEMVanAll` with the torsion hypothesis on `π_{a+1}(W)` replaced by its finiteness. -/
def RangeEMVanAllFin : Prop :=
  ∀ (a N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    (∀ i : ℕ, 1 ≤ i → i ≤ N → i ≠ a + 1 → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    Nonempty (Fintype (HomotopyGroup (Fin (a + 1)) W w₀)) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 - 2 * a → IsZero (ratH (TopCat.of W) t)

end

end Work.Serre
