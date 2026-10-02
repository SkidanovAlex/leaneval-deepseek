import Mathlib
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.Serre.serreC0Range
import Submission.Work.Serre.RangeEMVanDefs
import Submission.Work.RatHurewicz.torsionVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `C3FiniteTwo` from SERRE's range-form C3, **without `SerreC0`**

`Work.StemsB.C3FiniteTwo` — the range models of `K(A,k)` with `A` finite and `k ≥ 2` are rationally
acyclic in the range — is the third input of this area's reduction of
`Work.RatHurewicz.RangeModelRatAcyclic` (see `Submission/Work/StemsB/contractInputs.lean`).  The
route recorded in `Submission/Work/StemsB/C3Finite_of_serre_two.lean` obtains it from subproject
SERRE's `SerreC0` (existence of *genuine* models of `K(A,k)`) and `SerreC3` (their rational
acyclicity).  But **`SerreC0` has no producer in the tree**: it asks for a space with
`π_m ≅ A` and *all* other homotopy groups trivial, i.e. an infinite cell attachment (compare
`Submission/Work/RatHurewicz/coverRouteFreeTop.lean`, `sphere_stem_torsion.lean`:
"unbounded model-existence contract `Work.Serre.SerreC0`, which has no producer").

This file removes that input.  The replacement is SERRE's **range-form** C3

  `Work.Serre.RangeEMVanAll` — `W` connected, `π_i(W) = 0` for `1 ≤ i ≤ N`, `i ≠ a+1`, and
  `π_{a+1}(W)` a torsion group ⟹ `H_t(W;ℚ) = 0` for `0 < t ≤ N - 1 - 2a`,

which is a *theorem* of the tree: `Work.RatHurewicz.rangeEMVanAll_of_C3 (SerreE3a) (SerreC3)`
(`Submission/Work/RatHurewicz/torsionVanishing.lean`), built from the colimit model
`Work.Serre.RangeOne.colimModel` (proved) and the loop-space step
`Work.Serre.rangeEMVanAllAux_succ` (proved).  So

  `SerreE3a + SerreC3 ⟹ C3FiniteTwo`,

with no `SerreC0`.

The proof is bookkeeping: take a range model `P` of `K(A,k)` with the *large* top `N + 2k`
(`Work.Serre.SerreC0Range`, proved), apply `RangeEMVanAll` at `a = k-1` (the only finite input is
`Nat.card A • α = 0`, i.e. `pow_card_eq_one'`), and transport the vanishing back to the given range
model `X` through the comparison of two range models (`Work.StemsB.rangeModel_ratH_iso`, proved).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **`C3FiniteTwo` from the range form of C3.**  Only the *range* statements are used: no genuine
model of `K(A,k)` is ever built (the range models come from `Work.Serre.serreC0Range`, which is
proved), so the unbounded contract `Work.Serre.SerreC0` is not needed. -/
theorem C3FiniteTwo_of_rangeEMVanAll (h : Work.Serre.RangeEMVanAll) : C3FiniteTwo := by
  intro A _ hfA k hk N X _ pt hX i hi1 hiN
  have hidx : (k - 1) + 1 = k := by omega
  -- a range model of `K(A,k)` with the large top `N + 2k`
  obtain ⟨P, tP, p₀, hP⟩ := Work.Serre.serreC0Range A k (N + 2 * k) (by omega) (by omega)
  letI : TopologicalSpace P := tP
  -- the same hypothesis, read at the index `(k-1)+1` (the index of `RangeEMVanAll` at `a = k-1`)
  have hPa : Work.Serre.IsEMSpaceUpTo A ((k - 1) + 1) (by omega) (N + 2 * k) P p₀ := by
    convert hP using 1
  -- `RangeEMVanAll` at `a = k-1`, `N = N + 2k`
  have hvan : IsZero (Work.Serre.ratH (TopCat.of P) i) := by
    refine h (k - 1) (N + 2 * k) P p₀ ?_ ?_ ?_ ?_ i hi1 ?_
    · -- `π₀(P) = 0`
      exact hPa.2 0 (by omega) (Or.inl (by omega))
    · -- `π₁(P)` is abelian (it is trivial, as `k ≥ 2`)
      intro a b
      haveI : Subsingleton (HomotopyGroup (Fin 1) P p₀) :=
        hPa.2 1 (by omega) (Or.inl (by omega))
      exact Subsingleton.elim (a * b) (b * a)
    · -- the vanishing of `π_i(P)` in the range
      intro j hj1 hjN hjne
      exact hPa.2 j hjne (Or.inr hjN)
    · -- `π_k(P) ≅ A` is a torsion group, `A` being finite
      intro α
      obtain ⟨e⟩ := hPa.1
      refine ⟨Nat.card A, Nat.card_pos_iff.mpr ⟨⟨0⟩, hfA⟩, ?_⟩
      -- `e α` is an element of the finite group `Multiplicative A`
      apply e.injective
      rw [map_pow, map_one]
      have h2 : (e α) ^ Nat.card (Multiplicative A) = 1 := pow_card_eq_one'
      rw [Nat.card_congr Multiplicative.toAdd] at h2
      exact h2
    · omega
  -- the vanishing of the large model transfers to the given range model
  have hPQ : Work.Serre.IsEMSpaceUpTo A k (by omega) N P p₀ :=
    ⟨hP.1, fun j hj hc => hP.2 j hj (hc.imp id (fun h => by omega))⟩
  obtain ⟨e⟩ := rangeModel_ratH_iso A k N hk X pt hX P p₀ hPQ i hiN
  exact IsZero.of_iso hvan e

/-- **`C3FiniteTwo` from SERRE's two contracts `SerreE3a` and `SerreC3`** (no `SerreC0`). -/
theorem C3FiniteTwo_of_serre (hE3a : Work.Serre.SerreE3a) (hC3 : Work.Serre.SerreC3) :
    C3FiniteTwo :=
  C3FiniteTwo_of_rangeEMVanAll (Work.RatHurewicz.rangeEMVanAll_of_C3 hE3a hC3)

end

end Work.StemsB
