import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances

namespace Work.EKLRelCross

/-!
# A countable, level-controlled dense family of compactly supported functions on `SL₃(ℝ)`

Counting input for `Work.EKLRelCross.leafwise_luzin`: on `G = SL₃(ℝ)` we need a countable family
`Fam n j` of compactly supported continuous functions which is, levelwise, sup-norm dense (`Fam n ·`
is dense among functions supported in the compact set `L n`), with the extra property that
`Fam n j` is supported in the next compact set `L (n+1)` — this is what makes the local uniform
boundedness of the leafwise measures usable.  Here `L` is a compact exhaustion of `G` and `χ n`
are bump functions cutting off the level.

Route. Take `L := CompactExhaustion.choice SL3` (or `SigmaCompactSpace.exists_compact_covering`
plus accumulation), so `L n` is compact, `L n ⊆ interior (L (n+1))`, `⋃ n, L n = univ`.  For each
`n`, let `d : ℕ → C(↥(L (n+1)), ℝ)` be a dense sequence of the separable metric space
`C(↥(L (n+1)), ℝ)` (`TopologicalSpace.denseSeq`; `ContinuousMap.instMetricSpace` for compact
domain, separability from `ContinuousMap.instSeparableSpace`); extend `d j` to a continuous
`g j : G → ℝ` by Tietze (`ContinuousMap.exists_restrict_eq`; `↥(L (n+1))` is closed and `ℝ` is a
`TietzeExtension` space), and set `Fam n j := g j * χ n`, a compactly supported continuous
function with support in `L (n+1)` (note: the Tietze extension itself need not have compact
support, only the product does).
Bumps: `exists_continuous_one_zero_of_isCompact` applied to the compact `L n` and the closed set
`(interior (L (n+1)))ᶜ` (disjoint since `L n ⊆ interior (L (n+1))`) gives `χ n` with `χ n = 1` on
`L n`, `χ n = 0` off `interior (L (n+1))`, values in `[0,1]`, compact support inside `L (n+1)`.
Density: given `u` supported in `L n` and `η > 0`, choose `j` with
`dist (d j) (u|L (n+1)) < η/2` (`Metric.denseRange_iff`, `ContinuousMap.dist_apply_le_dist`).
For `x ∈ L n`, `χ n x = 1` so `|u x - Fam n j x| = |u x - g j x| ≤ η/2`; for `x ∈ L (n+1) \ L n`,
`u x = 0` and `|g j x| ≤ |u x| + η/2 = η/2` so `|u x - g j x χ n x| ≤ η/2`; outside `L (n+1)`
both sides vanish.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.style.haveILetI false

noncomputable section

open Work.EKLContract

/-- A fixed dense sequence in the (separable, compactly-based) space `C(↥(K (n+1)), ℝ)` of
continuous functions on the `(n+1)`-st member of a compact exhaustion `K`. -/
noncomputable def denseSeqOn (K : CompactExhaustion SL3) (n : ℕ) : ℕ → C(↥(K (n+1)), ℝ) :=
  haveI : CompactSpace ↥(K (n+1)) := isCompact_iff_compactSpace.mp (K.isCompact (n+1))
  TopologicalSpace.denseSeq (C(↥(K (n+1)), ℝ))

/-- `denseSeqOn K n` has dense range. -/
theorem denseRange_denseSeqOn (K : CompactExhaustion SL3) (n : ℕ) : DenseRange (denseSeqOn K n) := by
  haveI : CompactSpace ↥(K (n+1)) := isCompact_iff_compactSpace.mp (K.isCompact (n+1))
  show DenseRange (TopologicalSpace.denseSeq (C(↥(K (n+1)), ℝ)))
  exact TopologicalSpace.denseRange_denseSeq (C(↥(K (n+1)), ℝ))

/-- **Bump functions for a compact exhaustion.**  For every `n` there is a compactly supported
continuous `χ n` that equals `1` on `K n`, vanishes off `interior (K (n+1))` and takes values in
`[0,1]`.  (Consequently its support is contained in `K (n+1)`.) -/
theorem bump_family_aux (K : CompactExhaustion SL3) :
    ∃ χ : ℕ → CompactlySupportedContinuousMap SL3 ℝ,
      (∀ n x, x ∈ K n → χ n x = 1) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ n x, x ∉ interior (K (n+1)) → χ n x = 0) ∧
      (∀ n, Function.support (χ n) ⊆ K (n+1)) := by
  have hs : ∀ n, IsCompact (K n) := K.isCompact
  have ht : ∀ n, IsClosed ((interior (K (n+1)))ᶜ) := fun n =>
    isClosed_compl_iff.mpr isOpen_interior
  have hd : ∀ n, Disjoint (K n) ((interior (K (n+1)))ᶜ) := fun n =>
    disjoint_compl_right_iff_subset.mpr (K.subset_interior_succ n)
  let χ : ℕ → CompactlySupportedContinuousMap SL3 ℝ := fun n =>
    ⟨(exists_continuous_one_zero_of_isCompact (hs n) (ht n) (hd n)).choose,
     (exists_continuous_one_zero_of_isCompact (hs n) (ht n) (hd n)).choose_spec.2.2.1⟩
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · intro n x hx
    exact (exists_continuous_one_zero_of_isCompact (hs n) (ht n) (hd n)).choose_spec.1 hx
  · intro n x
    exact (exists_continuous_one_zero_of_isCompact (hs n) (ht n) (hd n)).choose_spec.2.2.2 x
  · intro n x hx
    exact (exists_continuous_one_zero_of_isCompact (hs n) (ht n) (hd n)).choose_spec.2.1 hx
  · intro n
    apply Function.support_subset_iff.mpr
    intro x hx
    by_contra hxK
    exact hx ((exists_continuous_one_zero_of_isCompact (hs n) (ht n) (hd n)).choose_spec.2.1
      (fun hmem => hxK (interior_subset hmem)))

/-- **Tietze extensions of a dense sequence.**  The dense sequence `denseSeqOn K n` on the compact
set `K (n+1)` extends to a continuous function on all of `SL₃(ℝ)`. -/
theorem tietze_family_aux (K : CompactExhaustion SL3) :
    ∃ g : ℕ → ℕ → C(SL3, ℝ), ∀ n j, (g n j).restrict (K (n+1)) = denseSeqOn K n j := by
  refine ⟨fun n j => ?_, ?_⟩
  · exact (ContinuousMap.exists_restrict_eq (K.isCompact (n+1)).isClosed (denseSeqOn K n j)).choose
  · intro n j
    exact (ContinuousMap.exists_restrict_eq (K.isCompact (n+1)).isClosed (denseSeqOn K n j)).choose_spec

/-- **The density estimate.**  Given bumps `χ` and Tietze extensions `g` of a dense sequence as
above, every compactly supported `u` with support in `K n` is uniformly approximated on all of
`SL₃(ℝ)` by `g n j · χ n` — this is the levelwise density of the family, and the reason we can
allow `χ` to be supported only in `K (n+1)`. -/
theorem cc_density_estimate (K : CompactExhaustion SL3)
    (χ : ℕ → CompactlySupportedContinuousMap SL3 ℝ) (g : ℕ → ℕ → C(SL3, ℝ))
    (hχ1 : ∀ n x, x ∈ K n → χ n x = 1)
    (hχ01 : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχ0 : ∀ n x, x ∉ interior (K (n+1)) → χ n x = 0)
    (hg : ∀ n j, (g n j).restrict (K (n+1)) = denseSeqOn K n j)
    (u : CompactlySupportedContinuousMap SL3 ℝ) (n : ℕ)
    (hu : Function.support u ⊆ K n) (η : ℝ) (hη : 0 < η) :
    ∃ j, ∀ x, |u x - g n j x * χ n x| ≤ η := by
  haveI : CompactSpace ↥(K (n+1)) := isCompact_iff_compactSpace.mp (K.isCompact (n+1))
  obtain ⟨j, hj⟩ :=
    (Metric.denseRange_iff.mp (denseRange_denseSeqOn K n))
      ((u.toContinuousMap).restrict (K (n+1))) (η/2) (by linarith)
  -- `u` is uniformly `η/2`-close to `g n j` on `K (n+1)`
  have hmain : ∀ x, x ∈ K (n+1) → |u x - g n j x| ≤ η/2 := by
    intro x hx
    have h1 : dist ((u.toContinuousMap).restrict (K (n+1)) ⟨x, hx⟩)
        ((denseSeqOn K n j) ⟨x, hx⟩) ≤
        dist ((u.toContinuousMap).restrict (K (n+1))) (denseSeqOn K n j) :=
      ContinuousMap.dist_apply_le_dist (⟨x, hx⟩ : ↥(K (n+1)))
    have h2 : dist ((u.toContinuousMap).restrict (K (n+1))) (denseSeqOn K n j) < η/2 := hj
    have h3 : dist ((u.toContinuousMap).restrict (K (n+1)) ⟨x, hx⟩)
        ((denseSeqOn K n j) ⟨x, hx⟩) < η/2 := lt_of_le_of_lt h1 h2
    have e1 : ((u.toContinuousMap).restrict (K (n+1)) ⟨x, hx⟩) = u x := by
      simp [ContinuousMap.restrict_apply]
    have e2 : (denseSeqOn K n j) ⟨x, hx⟩ = g n j x := by
      have := congrArg (fun f : C(↥(K (n+1)), ℝ) => f ⟨x, hx⟩) (hg n j)
      simpa [ContinuousMap.restrict_apply] using this.symm
    rw [e1, e2, Real.dist_eq] at h3
    exact le_of_lt h3
  refine ⟨j, fun x => ?_⟩
  by_cases hx : x ∈ K (n+1)
  · have hbound := hmain x hx
    by_cases hxK : x ∈ K n
    · have hχx : χ n x = 1 := hχ1 n x hxK
      calc |u x - g n j x * χ n x| = |u x - g n j x| := by rw [hχx, mul_one]
        _ ≤ η := by linarith
    · have hu0 : u x = 0 := by
        by_contra h
        exact hxK (Function.support_subset_iff.mp hu x h)
      have hgx : |g n j x| ≤ η/2 := by
        rw [hu0, zero_sub, abs_neg] at hbound
        exact hbound
      have hχle : |χ n x| ≤ 1 := by
        rw [abs_of_nonneg (hχ01 n x).1]
        exact (hχ01 n x).2
      calc |u x - g n j x * χ n x| = |g n j x * χ n x| := by rw [hu0, zero_sub, abs_neg]
        _ = |g n j x| * |χ n x| := abs_mul _ _
        _ ≤ (η/2) * 1 := mul_le_mul hgx hχle (abs_nonneg _) (by linarith)
        _ ≤ η := by linarith
  · have hχx : χ n x = 0 := hχ0 n x (fun h => hx (interior_subset h))
    have hu0 : u x = 0 := by
      by_contra h
      exact hx (K.subset (Nat.le_succ n) (Function.support_subset_iff.mp hu x h))
    rw [hu0, hχx]
    simp only [mul_zero, sub_zero, abs_zero]
    exact le_of_lt hη

theorem cc_dense_family :
    ∃ (L : ℕ → Set Work.EKLContract.SL3) (χ : ℕ → CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ)
      (Fam : ℕ → ℕ → CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ),
      (∀ n, IsCompact (L n)) ∧ Monotone L ∧ (⋃ n, L n = Set.univ) ∧
      (∀ n, L n ⊆ interior (L (n+1))) ∧
      (∀ n x, x ∈ L n → χ n x = 1) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ n, Function.support (χ n) ⊆ L (n+1)) ∧
      (∀ n j, Function.support (Fam n j) ⊆ L (n+1)) ∧
      (∀ (u : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) (n : ℕ),
        Function.support u ⊆ L n → ∀ η > 0, ∃ j, ∀ x, |u x - Fam n j x| ≤ η) := by
  obtain ⟨χ, hχ1, hχ01, hχ0, hχsupp⟩ := bump_family_aux (CompactExhaustion.choice SL3)
  obtain ⟨g, hg⟩ := tietze_family_aux (CompactExhaustion.choice SL3)
  refine ⟨fun n => (CompactExhaustion.choice SL3) n, χ, fun n j => (g n j) • (χ n),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (CompactExhaustion.choice SL3).isCompact
  · intro a b hab
    exact (CompactExhaustion.choice SL3).subset hab
  · exact (CompactExhaustion.choice SL3).iUnion_eq
  · exact (CompactExhaustion.choice SL3).subset_interior_succ
  · exact hχ1
  · exact hχ01
  · exact hχsupp
  · intro n j
    apply Function.support_subset_iff.mpr
    intro x hx
    by_contra hxK
    have hχ0x : χ n x = 0 := hχ0 n x (fun h => hxK (interior_subset h))
    rw [CompactlySupportedContinuousMap.smulc_apply, hχ0x, smul_zero] at hx
    exact hx rfl
  · intro u n hu η hη
    have h := cc_density_estimate (CompactExhaustion.choice SL3) χ g hχ1 hχ01 hχ0 hg u n hu η hη
    simpa only [CompactlySupportedContinuousMap.smulc_apply, smul_eq_mul] using h

end

end Work.EKLRelCross
