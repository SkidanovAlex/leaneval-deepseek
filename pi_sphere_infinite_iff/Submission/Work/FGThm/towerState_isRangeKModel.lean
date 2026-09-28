import Mathlib
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.towerStepData

/-!
# A truncation tower is a range model of `K(π_k X, k)` up to degree `k + s`

A `Work.RatHurewicz.TowerState X x₀ k s` records a space `Y` together with an embedding
`incl : X → Y`, the compression property of the pair `(Y, range incl)` in dimensions `≤ k+1`, and
the killing of the homotopy groups `π_j(Y)` for `k < j ≤ k + s`.  This file shows that these data
alone yield the range-model condition `Work.RatHurewicz.IsRangeKModel k M (st.incl x₀)` for every
`M ≤ k + s`, provided `X` is `(k-1)`-connected:

* for `j > k` the vanishing is exactly the record `st.killed` of the tower;
* for `0 < j < k` compression pushes based `j`-cubes of `Y` into the range of `incl` — which is
  homeomorphic to `X`, where `π_j` vanishes by hypothesis — and
  `Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel` transfers this to `π_j(Y)`;
* for `j = 0` the same compression (in dimension zero) joins every point of `Y` to the image of the
  connected space `X`.

This is the generalisation of the range-model clause of `Work.RatHurewicz.towerStepData` from the
single degree `M = 2k-1` to an arbitrary `M ≤ k+s`; in particular `k` need not satisfy `k ≥ 2`,
only the `j = 0` case needs `k ≥ 1` (which is automatic in the branch `j < k`).
-/

open scoped Topology

namespace Work.FGThm

/-- **A tower state is a range model up to degree `k + s`.**  If `X` is `(k-1)`-connected and
`st : TowerState X x₀ k s` is a stage of the truncation tower, then `π_j(Y, incl x₀)` is trivial for
every `j ≤ M` with `j ≠ k`, as soon as `M ≤ k + s`. -/
theorem towerState_isRangeKModel {X : Type} [TopologicalSpace X] {x₀ : X} {k s M : ℕ}
    (hconn : ∀ j : ℕ, j < k → Subsingleton (HomotopyGroup (Fin j) X x₀))
    (st : Work.RatHurewicz.TowerState X x₀ k s) (hM : M ≤ k + s) :
    Work.RatHurewicz.IsRangeKModel k M (st.incl x₀) := by
  intro j hj hjne
  rcases lt_or_gt_of_ne hjne with hlt | hgt
  · -- `j < k`: compression pushes cubes of `Y` into the range of `incl`, which is `X`
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- `j = 0`: `Y` is connected
      subst hj0
      haveI hπ0 : Subsingleton (HomotopyGroup (Fin 0) X x₀) := hconn 0 (by omega)
      haveI hXZ : Subsingleton (ZerothHomotopy X) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).surjective.subsingleton
      have hAZ : Subsingleton (ZerothHomotopy ↥(Set.range (st.incl : X → st.Y))) := by
        have key : ∀ a : Set.range (st.incl : X → st.Y),
            ZerothHomotopy.mk a = ZerothHomotopy.mk
              (⟨st.incl x₀, x₀, rfl⟩ : Set.range (st.incl : X → st.Y)) := by
          intro a
          have hj : Joined a.2.choose x₀ :=
            Quotient.exact (Subsingleton.elim (ZerothHomotopy.mk a.2.choose)
              (ZerothHomotopy.mk x₀))
          have h1 : Joined (⟨st.incl a.2.choose, a.2.choose, rfl⟩ : Set.range (st.incl : X → st.Y))
              ⟨st.incl x₀, x₀, rfl⟩ :=
            hj.map (f := fun x => (⟨st.incl x, x, rfl⟩ : Set.range (st.incl : X → st.Y)))
              (by fun_prop)
          have h2 : a = (⟨st.incl a.2.choose, a.2.choose, rfl⟩ : Set.range (st.incl : X → st.Y)) :=
            Subtype.ext a.2.choose_spec.symm
          rw [h2]
          exact ZerothHomotopy.sound h1.somePath
        refine ⟨fun u v => ?_⟩
        induction u using ZerothHomotopy.rec with
        | mk a =>
          induction v using ZerothHomotopy.rec with
          | mk b => rw [key a, key b]
      haveI hYZ : Subsingleton (ZerothHomotopy st.Y) :=
        Work.RatHurewicz.subsingleton_zerothHomotopy_of_compressRel_zero
          (st.compress 0 (by omega)) hAZ
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := st.Y)
        (x := st.incl x₀)).symm.surjective.subsingleton
    · -- `1 ≤ j < k`
      have hA : Subsingleton (HomotopyGroup (Fin (j - 1 + 1))
          ↥(Set.range (st.incl : X → st.Y)) ⟨st.incl x₀, x₀, rfl⟩) :=
        Work.RatHurewicz.subsingleton_homotopyGroup_range_of_isEmbedding (j := j - 1 + 1)
          st.incl x₀ st.emb (hconn (j - 1 + 1) (by omega))
      have hbij := Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel
        (A := Set.range (st.incl : X → st.Y)) ⟨st.incl x₀, x₀, rfl⟩ (k + 1)
        (fun d hd => st.compress d (by omega)) (j - 1) (by omega)
      have hS : Subsingleton (HomotopyGroup (Fin (j - 1 + 1)) st.Y (st.incl x₀)) := by
        haveI := hA
        exact hbij.2.subsingleton
      rwa [show j - 1 + 1 = j from by omega] at hS
  · -- `k < j`: the killing recorded by the tower
    exact st.killed j hgt (by omega)

end Work.FGThm
