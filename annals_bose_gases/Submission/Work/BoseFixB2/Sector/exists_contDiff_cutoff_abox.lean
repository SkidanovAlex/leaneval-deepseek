import Mathlib.Order.CompletePartialOrder
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `exists_contDiff_cutoff_abox`: cutting a smooth function down to the centred box

Given a smooth `Φ : X n → ℝ` (`X n = (ℝ³)ⁿ`) and a scale `ℓ > 0`, there is a larger
scale `L > ℓ` and a smooth `Ψ` which agrees with `Φ` on the centred `n`-particle box
`abox n ℓ` and whose (topological) support is contained in the larger box
`abox n L`.  Concretely `Ψ = η * Φ` where `η` is a smooth cutoff equal to `1` on
`abox n ℓ` and vanishing outside `abox n L`.

## Proof

* `L := 2ℓ`, so that `ℓ < L` and `abox n ℓ ⊆ abox n L` with room to spare; in fact
  the whole box `abox n ℓ` lies in the *open* interior of `abox n L`
  (`abox_subset_interior_abox`, proved by an elementary ball argument: the
  coordinatewise slack is `(L - ℓ)/2 = ℓ/2 > 0`).
* Consequently the closed set `s := (interior (abox n L))ᶜ` — which is the closure of
  the complement of `abox n L`, cf. `closure_compl` — is disjoint from the closed set
  `t := abox n ℓ`.
* Mathlib's smooth Urysohn lemma for finite-dimensional manifolds
  (`exists_contMDiffMap_zero_one_of_isClosed`) applied to `s` and `t` produces a smooth
  `f` equal to `1` on `abox n ℓ` and to `0` on all of `(interior (abox n L))ᶜ`.
* Hence `Ψ := f * Φ` is smooth, agrees with `Φ` on `abox n ℓ`
  (where the factor `f` is `1`), and its support lies in
  `interior (abox n L) ⊆ abox n L`, so its topological support lies in
  `closure (abox n L) = abox n L`.
-/

namespace Work.BoseFixB2.Sector

open MeasureTheory
open scoped ContDiff Topology

open Submission.BoseGases

/-- The `n`-particle box of side `a` lies in the *interior* of the box of side `b`
whenever `a < b`: the coordinatewise slack is `(b - a)/2 > 0`. -/
lemma abox_subset_interior_abox {n : ℕ} {a b : ℝ} (hab : a < b) :
    Submission.BoseGases.abox n a ⊆ interior (Submission.BoseGases.abox n b) := by
  intro x hx
  rw [mem_interior_iff_mem_nhds]
  have hδ : 0 < (b - a) / 2 := by linarith
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hδ) ?_
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  rw [Submission.BoseGases.mem_abox_iff_coord] at hx ⊢
  intro i m
  have hxi := hx i m
  rw [Set.mem_Icc] at hxi ⊢
  -- the `m`-th coordinate of the `i`-th particle moves by at most `‖y - x‖`
  have hcoord : |(y i).ofLp m - (x i).ofLp m| ≤ ‖y - x‖ := by
    calc |(y i).ofLp m - (x i).ofLp m| = |((y - x) i).ofLp m| := by simp
      _ ≤ ‖(y - x) i‖ := Submission.BoseGases.abs_coord_le_norm _ m
      _ ≤ ‖y - x‖ := norm_le_pi_norm _ i
  have hcoord' : |(y i).ofLp m - (x i).ofLp m| < (b - a) / 2 := lt_of_le_of_lt hcoord hy
  obtain ⟨h1, h2⟩ := abs_le.mp hcoord'.le
  exact ⟨by linarith, by linarith⟩

/-- A smooth function can be cut off to the centred box `abox n ℓ`: there is a larger
box `abox n L` and a smooth modification of `Φ`, supported in `abox n L`, agreeing with
`Φ` on `abox n ℓ`. -/
theorem exists_contDiff_cutoff_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : ∃ (L : ℝ) (Ψ : Submission.BoseGases.X n → ℝ), ℓ < L ∧ ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ tsupport Ψ ⊆ Submission.BoseGases.abox n L ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ, Ψ x = Φ x := by
  classical
  set L : ℝ := 2 * ℓ with hL
  have hℓL : ℓ < L := by rw [hL]; linarith
  -- the cutoff to be produced by smooth Urysohn vanishes on `(interior (abox n L))ᶜ`,
  -- which is the closure of the complement of `abox n L` and hence closed
  have hs : IsClosed ((interior (Submission.BoseGases.abox n L))ᶜ) :=
    isClosed_compl_iff.mpr isOpen_interior
  have ht : IsClosed (Submission.BoseGases.abox n ℓ) := Submission.BoseGases.abox_isClosed n ℓ
  have hd : Disjoint ((interior (Submission.BoseGases.abox n L))ᶜ)
      (Submission.BoseGases.abox n ℓ) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_compl_iff] at hx
    exact hx (abox_subset_interior_abox hℓL hx')
  obtain ⟨f, hf0, hf1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (modelWithCornersSelf ℝ (Submission.BoseGases.X n))
      hs ht hd
  refine ⟨L, fun x => f x * Φ x, hℓL, ?_, ?_, ?_⟩
  · -- smoothness: `f` is smooth and `Φ` is smooth
    exact (contMDiff_iff_contDiff.mp f.contMDiff).mul hΦ
  · -- support: `f` vanishes off `interior (abox n L)`
    have h1 : Function.support (fun x : Submission.BoseGases.X n => f x * Φ x) ⊆
        interior (Submission.BoseGases.abox n L) := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hxc
      exact hx (by simp [hf0 hxc])
    rw [tsupport]
    exact (closure_mono h1).trans ((closure_mono interior_subset).trans
      (le_of_eq (Submission.BoseGases.abox_isClosed n L).closure_eq))
  · -- equality on the smaller box, where the cutoff is `1`
    intro x hx
    have h1 : f x = 1 := hf1 hx
    simp [h1]

end Work.BoseFixB2.Sector
