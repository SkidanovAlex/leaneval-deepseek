import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.JuliaBasics
import Submission.Work.Normal.JuliaIterate
import Submission.Work.Normal.Preimages
import Submission.Work.Normal.juliaSet_infinite
import Submission.Work.Normal.unique_preimage_mem_fatou
import Submission.Work.Normal.poly_eval_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Julia set of a polynomial map is perfect

For a polynomial map `f` of degree `d ≥ 2`, `JuliaSet f` is closed and has no isolated points.

The proof is the classical one.  Let `z ∈ JuliaSet f` and let `U` be a neighbourhood of `z`; we
must find another point of the Julia set in `U`.  Shrinking `U` to a ball `B` around `z`, suppose
`B ∩ JuliaSet f = {z}`.

* If `JuliaSet f = {z}`, then `z` is the unique preimage of itself (every preimage lies in the
  Julia set) and `unique_preimage_mem_fatou` puts `z` in the Fatou set, a contradiction.
* Otherwise take `y ∈ JuliaSet f`, `y ≠ z`.  By density of iterated preimages
  (`subset_closure_iUnion_preimage`) some iterate of `z` equals `y`.  Hence every point of the
  Julia set other than `z` is an iterate of `z`.  A preimage `b ≠ z` of `z` (which exists, again by
  `unique_preimage_mem_fatou`) is then itself an iterate of `z`, so `z` is periodic.  Consequently
  `JuliaSet f` is contained in the finite set of points of the cycle of `z`, contradicting
  `juliaSet_infinite`.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- **The Julia set of a polynomial map of degree at least two is perfect.** -/
theorem juliaSet_perfect {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : Perfect (JuliaSet f) := by
  refine ⟨isClosed_juliaSet f, ?_⟩
  rw [preperfect_iff_nhds]
  intro z hz U hU
  by_contra hcon
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hballJ : ∀ y ∈ Metric.ball z r, y ∈ JuliaSet f → y = z := by
    intro y hyB hyJ
    by_contra hyz
    exact hcon ⟨y, ⟨hrU hyB, hyJ⟩, hyz⟩
  by_cases hsing : (JuliaSet f) = {z}
  · -- `z` is the unique preimage of itself
    have hpre : ∀ w : ℂ, f w = z ↔ w = z := by
      intro w
      constructor
      · intro hw
        have hwJ : w ∈ JuliaSet f :=
          preimage_juliaSet_subset hd hf (show f w ∈ JuliaSet f from by rw [hw]; exact hz)
        simpa [hsing] using hwJ
      · intro hw
        rw [hw]
        have : f z ∈ JuliaSet f := mapsTo_juliaSet hd hf hz
        simpa [hsing] using this
    exact hz (unique_preimage_mem_fatou hd hf hpre)
  · -- there is another point of the Julia set
    obtain ⟨y, hyJ, hyz⟩ : ∃ y ∈ JuliaSet f, y ≠ z := by
      by_contra h'
      push_neg at h'
      exact hsing (Subset.antisymm (fun w hw => by simpa using h' w hw)
        (fun w hw => by rw [mem_singleton_iff] at hw; rw [hw]; exact hz))
    -- every point of `J \ {z}` is an iterate of `z`
    have hiter : ∀ y ∈ JuliaSet f, y ≠ z → ∃ m : ℕ, f^[m] z = y := by
      intro y hyJ _
      have hcl := subset_closure_iUnion_preimage hd hf hyJ hz
      rw [mem_closure_iff_nhds] at hcl
      obtain ⟨w, hwB, hw⟩ := hcl (Metric.ball z r) (Metric.ball_mem_nhds z hr)
      obtain ⟨m, hw'⟩ := mem_iUnion.mp hw
      have hwJ : w ∈ JuliaSet f := by
        refine preimage_iterate_juliaSet_subset hd hf m ?_
        show f^[m] w ∈ JuliaSet f
        rw [hw']
        exact hyJ
      exact ⟨m, by rw [← hballJ w hwB hwJ]; simpa using hw'⟩
    -- a preimage of `z` different from `z`
    have hpre : ∃ b : ℂ, f b = z ∧ b ≠ z := by
      by_contra h'
      push_neg at h'
      have hfz : f z = z := by
        obtain ⟨w, hw⟩ := poly_eval_surjective (by omega : 1 ≤ d) hf z
        have hwz : w = z := h' w hw
        calc f z = f w := by rw [hwz]
          _ = z := hw
      exact hz (unique_preimage_mem_fatou hd hf
        fun w => ⟨fun hw => h' w hw, fun hw => by rw [hw]; exact hfz⟩)
    obtain ⟨b, hb, hbz⟩ := hpre
    obtain ⟨m, hm⟩ := hiter b
      (preimage_juliaSet_subset hd hf (show f b ∈ JuliaSet f from by rw [hb]; exact hz)) hbz
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, Function.iterate_zero_apply] at hm
        exact absurd hm.symm hbz
      · exact hpos
    have hper : f^[m + 1] z = z := by
      rw [Function.iterate_succ_apply', hm, hb]
    -- hence the Julia set is finite
    have hfin : Set.Finite (Set.range (fun i : Fin (m + 1) => f^[i.1] z) ∪ {z}) :=
      (Set.finite_range _).union (Set.finite_singleton z)
    have hj : ∀ j : ℕ, (f^[m + 1])^[j] z = z := by
      intro j
      induction j with
      | zero => rfl
      | succ i ih => rw [Function.iterate_succ_apply', ih, hper]
    have hperiodic : ∀ k : ℕ, f^[k] z = f^[k % (m + 1)] z := by
      intro k
      conv_lhs => rw [← Nat.mod_add_div k (m + 1)]
      rw [Function.iterate_add_apply, Function.iterate_mul, hj]
    have hsub : JuliaSet f ⊆ Set.range (fun i : Fin (m + 1) => f^[i.1] z) ∪ {z} := by
      intro w hwJ
      by_cases hwz : w = z
      · exact Or.inr (by simpa using hwz)
      · obtain ⟨k, hk⟩ := hiter w hwJ hwz
        refine Or.inl ⟨⟨k % (m + 1), Nat.mod_lt k (by omega)⟩, ?_⟩
        rw [← hk, hperiodic k]
    exact (juliaSet_infinite hd hf) (hfin.subset hsub)

end Work.Normal
