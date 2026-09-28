import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.Defs

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

open scoped Topology

noncomputable section

/-- **The torsion case of the Eilenberg–MacLane computation** (Serre's theorem for the Serre class
of torsion groups): a space which is connected, simply connected and whose homotopy groups in
degrees `2, …, N+2` are all *torsion* groups has rationally trivial homology in those degrees.

This is the content of `ratVanishing_of_torsion_homotopy`
(`Submission/Work/RatHurewicz/ratVanishing_of_torsion_homotopy.lean`), restated here only to fix
the indexing used below. -/
def TorsionHomotopyVanishing : Prop :=
  ∀ (N : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X),
    Subsingleton (HomotopyGroup (Fin 0) X x₀) →
    Subsingleton (HomotopyGroup (Fin 1) X x₀) →
    (∀ j : ℕ, j ≤ N → IsTorsionGroup (HomotopyGroup (Fin (j + 2)) X x₀)) →
    Work.Serre.RatVanishingBelow X (N + 3)

/-- **The reduction of a range model to a torsion model**: killing the free part of `π_k` by
attaching `(k+1)`-cells along a `ℤ`-independent spanning family produces a space with the same
rational homology in the range `k < j ≤ N` and with torsion homotopy groups below `N`.

This is `rangeModel_reduce_torsion`
(`Submission/Work/RatHurewicz/rangeModel_reduce_torsion.lean`), restated here only to fix the
indexing used below. -/
def RangeModelReduction : Prop :=
  ∀ (k N : ℕ), 2 ≤ k → N ≤ 2 * k - 1 → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ j : ℕ, j ≤ N → j ≠ k → Subsingleton (HomotopyGroup (Fin j) X x₀)) →
    ∃ (X' : Type) (_ : TopologicalSpace X') (c : C(X, X')),
      Subsingleton (HomotopyGroup (Fin 0) X' (c x₀)) ∧
      Subsingleton (HomotopyGroup (Fin 1) X' (c x₀)) ∧
      (∀ j : ℕ, j + 2 ≤ N → IsTorsionGroup (HomotopyGroup (Fin (j + 2)) X' (c x₀))) ∧
      ∀ j : ℕ, k < j → j ≤ N →
        Nonempty ((Work.Serre.ratH (TopCat.of X) j) ≅ (Work.Serre.ratH (TopCat.of X') j))

/-- **The rational homology of a range model of `K(A,k)` vanishes below `2k`** from the two
ingredients above. -/
theorem rangeModelRatAcyclic_of (hγ : TorsionHomotopyVanishing) (hβ : RangeModelReduction) :
    Work.RatHurewicz.RangeModelRatAcyclic := by
  intro k hk Z _ z₀ hmodel j hkj hjN
  obtain ⟨X', _, c, h0, h1, htors, hiso⟩ :=
    hβ k (2 * k - 1) hk le_rfl Z z₀ (fun j hj => hmodel j hj)
  have hvan : Work.Serre.RatVanishingBelow X' (2 * k - 3 + 3) :=
    hγ (2 * k - 3) X' (c z₀) h0 h1 (fun j hj => htors j (by omega))
  have hX' : IsZero (Work.Serre.ratH (TopCat.of X') j) :=
    hvan j (by omega) (by omega)
  have hZ : IsZero (Work.Serre.ratH (TopCat.of Z) j) :=
    IsZero.of_iso hX' (hiso j hkj hjN).some
  exact hZ

-- (pi_sphere: the sorry-d milnor contract theorem rangeModelRatAcyclic was removed; only the definitions and
-- rangeModelRatAcyclic_of are used. Backup: .)


end

end Work.RatHurewicz
