/-
  WilC4 : area C4 of `annals_wilkies_conjecture` (Wilkie's valuation inequality for `TR`).

  Every definable closure of a value base is again a value base.  Recall

    `IsValBase S  :⇔  1 ∈ S ∧ (∀ x ∈ S, x ≠ 0 → x⁻¹ ∈ S) ∧ (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)`,

  i.e. `Γ S = {ν c : c ∈ S, c ≠ 0}` is a subgroup of the value group.  For `Dcl S A` the three
  components are:

  * `1 ∈ Dcl S A`, because `S ⊆ Dcl S A`: an element of the parameter set is definable from it
    (`definableElt_of_mem_left`);
  * closure under `⁻¹` (`dcl_inv`): `Dcl` is closed under `LRc`-definable functions, and
    inversion is definable over the parameter `x` by the atomic formula `x * y = 1` (the language
    of rings has no inversion symbol, but `x ≠ 0` makes `{y | x * y = 1}` the singleton `{x⁻¹}`);
  * closure under `*` (`dcl_mul`): multiplication *is* a function symbol of the ring part of
    `LRc`, so the graph of `(x, y) ↦ x * y` is definable without parameters.

  The three ingredients are proved in the sibling files of this area and are imported here; this
  file only assembles them into the value-base statement used by `Work.WilC4.Assembly`
  (`valSpans_dcl_range` applies the preparation step to the value base `Dcl S (range a ∘ castSucc)`).
-/
import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.definableElt_of_mem_left
import Submission.Work.WilC4.dcl_mul
import Submission.Work.WilC4.dcl_inv

namespace Work.WilC4

theorem dcl_valBase {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {S A : Set M} (hS : IsValBase S) : IsValBase (Dcl S A) := by
  obtain ⟨hone, hinv, hmul⟩ := hS
  refine ⟨definableElt_of_mem_left S A hone, fun x hx hx0 => dcl_inv hx hx0, ?_⟩
  intro x hx y hy
  exact dcl_mul hx hy

end Work.WilC4
