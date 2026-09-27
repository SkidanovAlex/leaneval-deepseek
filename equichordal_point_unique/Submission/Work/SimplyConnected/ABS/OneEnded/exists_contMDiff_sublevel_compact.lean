import Mathlib
import Submission.Work.SimplyConnected.ABS.manifold_smooth_upgrade
import Submission.Work.SimplyConnected.ABS.OneEnded.exists_isOpen_isCompact_closure_cover
import Submission.Work.SimplyConnected.ABS.OneEnded.exists_locallyFinite_isOpen_isCompact_closure_cover
import Submission.Work.SimplyConnected.ABS.OneEnded.contMDiff_finsum_mul_of_locallyFinite

/-!
# The smooth exhaustion function of the ABS argument (step 1 of Theorem 12)

Anghel--Bruin--Stan, *Uniformization of Riemann surfaces revisited* (arXiv:2008.12189), Theorem 12
("exhaustion by compact simply-connected submanifolds") starts from a **proper** smooth function
`g : X → [0,∞)`, produced there from a countable locally finite cover `(U_m)` of `X` and a
subordinate partition of unity `(φ_m)` by

  `g(x) = ∑_m m · φ_m(x)`,

whose sublevel sets `g⁻¹ [0,m] ⊆ ⋃_{k ≤ m} supp φ_k` are compact.

This module is that step, in the form the rest of the ABS assembly consumes: a `C^∞` function with
compact sublevel sets (equivalently, a proper smooth function).  It is `D3` of
`Submission/Work/SimplyConnected/ABS/NOTES_frontierConnected_superset_ROUTE_ANALYSIS.md` §46--§53.

## The construction, and where each piece is proved

* an increasing open cover `V n` with `IsCompact (closure (V n))` and `⋃ V n = univ`, together with
  the *monotonicity* `V n ⊆ V (n+1)`: `OneEnded/exists_isOpen_isCompact_closure_cover.lean`
  (`exists_isOpen_isCompact_closure_cover`), built from the workspace's closed-ball cover of a
  non-compact surface;
* a *locally finite* open cover `U n` with the same compactness property:
  `OneEnded/exists_locallyFinite_isOpen_isCompact_closure_cover.lean`
  (`exists_locallyFinite_isOpen_isCompact_closure_cover`), via
  `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`;
* a level function `lvl : ℕ → ℕ` with `closure (U n) ⊆ V (lvl n)`:
  `exists_level_function` (same first module);
* a smooth partition of unity subordinate to `U`: Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate` for the real-smooth structure on `X`
  (`isManifold_self_model_real_infty`, `manifold_smooth_improve`);
* the smoothness of the finitary sum: `contMDiff_finsum_mul_of_locallyFinite`;
* the comparison `∑ᶠ n, χ n x * c n ≥ N + 2` whenever `x ∉ V N`:
  `le_finsum_mul_of_locallyFinite`.

The only input that the ABS construction still needs on top of this module -- and the reason the
function here is *smooth* rather than merely continuous -- is a **regular value** of `g` (Sard's
lemma, absent from Mathlib): see
`Submission/Work/SimplyConnected/ABS/sard_substitute_dense_regular_values.lean` and
`sublevel_frontier_of_proper_regular.lean` for the point-set part of what it feeds.
-/

open Set Filter
open scoped Topology ContDiff

namespace Work.SimplyConnected.ABS.OneEnded

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The data of the ABS exhaustion function.**  Two open covers, one of them locally finite, a
level function relating them, and a smooth partition of unity subordinate to the second cover. -/
theorem exists_contMDiff_sublevel_compact_setup (hX : ¬ CompactSpace X) :
    ∃ (V U : ℕ → Set X) (lvl : ℕ → ℕ)
      (χ : SmoothPartitionOfUnity ℕ (modelWithCornersSelf ℝ ℂ) X),
      (∀ n, IsOpen (V n)) ∧ Monotone V ∧ (⋃ n, V n) = Set.univ ∧
      (∀ n, IsCompact (closure (V n))) ∧ (∀ n, IsCompact (closure (U n))) ∧
      (∀ n, closure (U n) ⊆ V (lvl n)) ∧ χ.IsSubordinate U := by
  obtain ⟨V, hVo, hVc, hVcov, hVmono⟩ := exists_isOpen_isCompact_closure_cover (X := X) hX
  have hVmono' : Monotone V := monotone_nat_of_le_succ hVmono
  obtain ⟨U, hUo, hUc, hUcov, -⟩ :=
    exists_locallyFinite_isOpen_isCompact_closure_cover (X := X) hX
  obtain ⟨lvl, hlvl⟩ := exists_level_function (U := U) (V := V) hVo hVmono' hVcov hUc
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X := isManifold_self_model_real_infty (X := X)
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ ℂ)
    (s := Set.univ) isClosed_univ U hUo (by rw [hUcov])
  exact ⟨V, U, lvl, χ, hVo, hVmono', hVcov, hVc, hUc, hlvl, hχ⟩

/-- **The ABS exhaustion function.**  On a non-compact `ℂ`-charted `T2` second countable surface
there is a nonnegative `C^∞` function whose sublevel sets are all compact; equivalently a proper
`C^∞` function `X → [0,∞)`.

The proof is the ABS construction: with `χ` a smooth partition of unity subordinate to the locally
finite cover `U n` and `lvl` a level function with `closure (U n) ⊆ V (lvl n)`,

  `g x = ∑ᶠ n, χ n x * ((lvl n : ℝ) + 1)`.

`g` is smooth by `contMDiff_finsum_mul_of_locallyFinite`.  For `x ∉ V N` (`N = ⌈a⌉₊`) every
`n` with `χ n x ≠ 0` has `x ∈ U n ⊆ closure (U n) ⊆ V (lvl n)`, so `lvl n > N` (else `V (lvl n) ⊆
V N`), hence `(lvl n : ℝ) + 1 ≥ N + 2`; the weighted-sum comparison
`le_finsum_mul_of_locallyFinite` with `∑ᶠ χ n x = 1` then gives `g x ≥ N + 2 > a`.  So
`{g ≤ a} ⊆ V N ⊆ closure (V N)`, and `{g ≤ a}` is closed, whence compact. -/
theorem exists_contMDiff_sublevel_compact (hX : ¬ CompactSpace X) :
    ∃ g : X → ℝ, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ g ∧
      (∀ x, 0 ≤ g x) ∧ ∀ a : ℝ, IsCompact {x : X | g x ≤ a} := by
  obtain ⟨V, U, lvl, χ, hVo, hVmono, hVcov, hVc, hUc, hlvl, hχ⟩ :=
    exists_contMDiff_sublevel_compact_setup (X := X) hX
  set g : X → ℝ := fun x => ∑ᶠ n, χ n x * ((lvl n : ℝ) + 1) with hg
  have hgsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ g :=
    contMDiff_finsum_mul_of_locallyFinite (fun n => (lvl n : ℝ) + 1) χ.locallyFinite
      (fun n => (χ n).contMDiff)
  have hgnn : ∀ x, 0 ≤ g x := fun x =>
    finsum_nonneg fun n => mul_nonneg (χ.nonneg n x) (by positivity)
  refine ⟨g, hgsm, hgnn, ?_⟩
  intro a
  by_cases ha : a < 0
  · have hempty : {x : X | g x ≤ a} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have h0 := hgnn x
      simp only [Set.mem_ofPred_eq] at hx
      linarith
    rw [hempty]; exact isCompact_empty
  · push Not at ha
    set N : ℕ := ⌈a⌉₊ with hN
    have haN : a ≤ (N : ℝ) := by
      have := Nat.le_ceil a
      simpa [hN] using this
    have hsub : {x : X | g x ≤ a} ⊆ V N := by
      intro x hx
      by_contra hxN
      have hge : (N : ℝ) + 2 ≤ g x := by
        rw [hg]
        refine le_finsum_mul_of_locallyFinite (f := fun n => ⇑(χ n))
          (c := fun n => (lvl n : ℝ) + 1) χ.locallyFinite (fun n => χ.nonneg n x)
          (χ.sum_eq_one (mem_univ x)) ?_
        intro n hn
        have hxU : x ∈ U n := hχ n (subset_closure (Function.mem_support.mpr hn))
        have hxV : x ∈ V (lvl n) := hlvl n (subset_closure hxU)
        have hlvlN : N + 1 ≤ lvl n := by
          by_contra hc
          have hc' : lvl n ≤ N := Nat.lt_succ_iff.mp (not_le.mp hc)
          exact hxN (hVmono hc' hxV)
        have hcast : (N : ℝ) + 1 ≤ (lvl n : ℝ) := by exact_mod_cast hlvlN
        linarith
      have hxa : g x ≤ a := hx
      linarith
    exact (hVc N).of_isClosed_subset (isClosed_le hgsm.continuous continuous_const)
      (hsub.trans subset_closure)

end Work.SimplyConnected.ABS.OneEnded
