import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

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

/-- **The rational homology of a range model of `K(A,k)` vanishes below `2k`** (C2/C3 of `Submission/Work/Drive/SERRE_BLUEPRINT.md`). For `k ≥ 2` and a space `Z` with `π_j(Z) = 0` for `j ≤ 2k-1`, `j ≠ k`, the rational homology of `Z` vanishes in degrees `k < j ≤ 2k-1`. The free case is the classical statement that `K(A,k)` is rationally a wedge of `k`-spheres below `2k`; the torsion case is C3. -/
theorem rangeModelRatAcyclic : Work.RatHurewicz.RangeModelRatAcyclic := by
  -- Once the two delegated modules have landed, this is
  --   `rangeModelRatAcyclic_of ratVanishing_of_torsion_homotopy rangeModel_reduce_torsion`
  -- after
  --   `import Submission.Work.RatHurewicz.ratVanishing_of_torsion_homotopy`
  --   `import Submission.Work.RatHurewicz.rangeModel_reduce_torsion`.
  sorry

end

end Work.RatHurewicz
