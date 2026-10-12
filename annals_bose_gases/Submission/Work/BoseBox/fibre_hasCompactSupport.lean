import ChallengeDeps
import Submission.Work.BoseBox.CNodeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.fibre_hasCompactSupport`

The slot-`i` fibre `z ↦ Ψ (kcInsN n i (z, r))` of a state whose topological support lies
in the *corner* box `[0,L]³` (the `_root_.BoseGases.box (n+1) L` of the bridge, in
contrast to the *centred* box `abox` used by `Work.BoseKinLoc.Kinetic.liftFibre`) has
compact support.

The argument is purely support-theoretic and needs no regularity of `Ψ`:

* if the fibre does not vanish at `z`, then the configuration `kcInsN n i (z,r)` lies in
  `Function.support Ψ ⊆ tsupport Ψ ⊆ box (n+1) L`;
* in the corner box the `i`-th coordinate is subject to the corner bounds, and inserting
  at slot `i` is the identity there (`kc_insN_apply_same`), so `z` itself lies in the
  coordinate cube `cube L = {y : ℝ³ | ∀ k, (y k) ∈ Icc 0 L}`;
* hence the support of the fibre is contained in `cube L`, which is closed, so its
  topological support is too, and `cube L` is compact.

(For `L ≤ 0` the cube `cube L` is `{0}` resp. empty and the statement is trivial; the
general compactness of `cube L` for every real `L` is `cube_isCompact`.)
-/

namespace Work.BoseBox

set_option autoImplicit false

/-- The coordinate cube `[0,L]³ ⊆ ℝ³` is compact for **every** real `L`; note that
`Submission.BoseGases.cube_compact` requires `0 < L`.  For `0 ≤ L` it is closed and
bounded (`Metric.isCompact_iff_isClosed_bounded`), for `L < 0` it is empty. -/
lemma cube_isCompact (L : ℝ) : IsCompact (Submission.BoseGases.cube L) := by
  by_cases hL : 0 ≤ L
  · exact (Metric.isCompact_iff_isClosed_bounded).mpr
      ⟨Submission.BoseGases.cube_isClosed L, Submission.BoseGases.cube_isBounded L hL⟩
  · have hne : Submission.BoseGases.cube L = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have h0 := hz 0
      rw [Set.mem_Icc] at h0
      exact absurd h0.1 (not_le.mpr (by linarith [h0.2, not_le.mp hL]))
    rw [hne]
    exact isCompact_empty

theorem fibre_hasCompactSupport {n : ℕ} {L : ℝ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box (n + 1) L)
    (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
      Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
  have hsub : tsupport (fun z : EuclideanSpace ℝ (Fin 3) =>
        Ψ (Submission.BoseGases.kcInsN n i (z, r))) ⊆ Submission.BoseGases.cube L := by
    refine closure_minimal ?_ (Submission.BoseGases.cube_isClosed L)
    intro z hz
    have hz' : Ψ (Submission.BoseGases.kcInsN n i (z, r)) ≠ 0 := Function.mem_support.mp hz
    have hsupp' : Submission.BoseGases.kcInsN n i (z, r) ∈ tsupport Ψ :=
      subset_tsupport Ψ (Function.mem_support.mpr hz')
    have hbox := hsupp hsupp'
    have hcoord : Submission.BoseGases.kcInsN n i (z, r) i = z :=
      Submission.BoseGases.kc_insN_apply_same n i z r
    intro k
    have h := hbox i k
    rwa [hcoord] at h
  exact IsCompact.of_isClosed_subset (cube_isCompact L) (isClosed_tsupport _) hsub

end Work.BoseBox
