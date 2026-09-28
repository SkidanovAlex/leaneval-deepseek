import Mathlib
import Submission.Work.Rat.s1Full
import Submission.Work.Rat.U.Main

/-!
# The rational vanishing Hurewicz theorem, all degrees, unconditional

Combining `Work.Rat.piTorsion_of_ratH_vanishing_full` with the reconstructed C3 chain
(`Work.Rat.rangeEMVanAllFin_reproved`) gives the rational Hurewicz theorem for finitely generated
homotopy in **all** degrees, from `SerreE3a` alone.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Rat

noncomputable section

/-- **Rational vanishing Hurewicz, all degrees, for finitely generated homotopy.**  If `X` is
`(k-1)`-connected (`k ≥ 3`) with finitely generated homotopy groups and `H̃_i(X;ℚ) = 0` for
`k ≤ i ≤ M`, then `π_j(X)` is torsion for `k ≤ j ≤ M`. -/
theorem piTorsion_of_ratH_vanishing_full' (hE3a : Work.Serre.SerreE3a)
    (k : ℕ) (hk : 3 ≤ k) (X : Type) [TopologicalSpace X] (x₀ : X)
    (M : ℕ) (hconn : ∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hfg : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a) X x₀))
    (hhom : ∀ i, k ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of X) i)) :
    ∀ j : ℕ, k ≤ j → j ≤ M → Work.Serre.PiTorsion X x₀ (j - 1) :=
  piTorsion_of_ratH_vanishing_full hE3a (rangeEMVanAllFin_reproved hE3a) k hk X x₀ M hconn hfg hhom

end

end Work.Rat
