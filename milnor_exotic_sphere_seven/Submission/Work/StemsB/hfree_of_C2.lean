import Mathlib
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.Serre.serreC0Range
import Submission.Work.RatHurewicz.fin_prod_ratH_vanishing_rat
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The free finitely generated case of `RangeModelRatAcyclic` from `C2RatSphereRange`

`Work.StemsB.rangeModelRatAcyclic_of_serre` reduces `Work.RatHurewicz.RangeModelRatAcyclic` to
subproject SERRE's `SerreC0`/`SerreC3` **and** the *free finitely generated* case

  `hfree` — a range model of `K(ℤ^r, k)` through degree `N ≥ 2k-1` has vanishing rational homology
  in degrees `k < i ≤ 2k-1`.

This is the assignment of area STEMS/H5 phrased for the group `ℤ^r`.  The classical input, however,
is the case `r = 1` — the computation of the rational homology of `K(ℤ,k)` below the doubled degree
— which is exactly the interface `Work.StemsB.C2RatSphereRange` of
`Submission/Work/StemsB/RangeModelPlan.lean`:

  `C2RatSphereRange` — for `k ≥ 1` and a range model of `K(ℤ,k)` through `N ≥ 2k-1`, one has
  `H_k ≅ ℚ` and `H_i = 0` for `0 < i ≤ 2k-1`, `i ≠ k`
  (**the range hypothesis `2k-1 ≤ N` is essential** — see the warning at `Work.StemsB.C2RatSphere`).

This file proves that **the `r`-fold case follows from the `r = 1` case**, so that a prover only has
to establish `C2RatSphereRange`, and the `ℤ^r` statement — hence
`Work.StemsB.rangeModelRatAcyclic_of_serre` — follows.  The computation is Künneth in the vanishing
range, which is available *over `ℚ`* without any integral Serre exact sequence
(`Work.RatHurewicz.fin_prod_ratH_vanishing_rat`, built on the rational pair comparison).

The proof is three lines of mathematics:

* take a range model `L` of `K(ℤ,k)` through `N` (`Work.Serre.serreC0Range`, proved);
* `Fin r → L` is a range model of `K(Fin r → ℤ, k)` through `N` (`isEMSpaceUpTo_pi_fin`), and its
  rational homology vanishes in the range by `C2RatSphereRange` for `L` plus the `r`-fold product
  step `Work.RatHurewicz.fin_prod_ratH_vanishing_rat`;
* transport along the comparison of two range models (`Work.StemsB.rangeModel_ratH_iso`, proved).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **The free finitely generated case follows from the *range* form of `C2`.**  This is the form
that should be used: `C2RatSphereRange` (unlike `C2RatSphere`) is true — see the warning at
`C2RatSphere` — and it is what the Eilenberg–MacLane computation proves. -/
theorem hfree_of_C2RatSphereRange (h : C2RatSphereRange) :
    ∀ (r : ℕ) (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
      (Y : Type) [TopologicalSpace Y] (y : Y),
        Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) k (by omega) N Y y →
        ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
          CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Y) i) := by
  intro r k N hk hN Y _ y hY i hi1 hi2
  have hk0 : 0 < k := by omega
  have hkN : k ≤ N := by omega
  obtain ⟨L, tL, l₀, hL⟩ := Work.Serre.serreC0Range ℤ k N (by omega) hkN
  letI : TopologicalSpace L := tL
  have hLc : Work.Serre.Conn L l₀ k := fun i hi => hL.2 i (by omega) (Or.inl hi)
  have hLvan : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of L) j) :=
    fun j hj1 hj2 => (h k (by omega) N hN L l₀ hL).2 j (by omega) hj2 (by omega)
  have hFL : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Fin r → L)) j) :=
    Work.RatHurewicz.fin_prod_ratH_vanishing_rat k hk r l₀ hLc hLvan
  have hPEM : Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) k (by omega) N (Fin r → L)
      (fun _ => l₀) :=
    Work.RatHurewicz.isEMSpaceUpTo_pi_fin (A := ℤ) (k := k) (N := N) hk0 r l₀ hL
  obtain ⟨e⟩ := rangeModel_ratH_iso (Fin r → ℤ) k N hk Y y hY (Fin r → L) (fun _ => l₀) hPEM i
    (by omega)
  exact CategoryTheory.Limits.IsZero.of_iso (hFL i hi1 hi2) e

end

end Work.StemsB
