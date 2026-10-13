import Mathlib
import Submission.Work.DSM5b.CycleDefs
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.chartCech_cycle_iff_pairwise
import Submission.Work.DSM5b.integrality_valuative_criterion
import Submission.Work.DSM5b.chartRing_phi_j_range_mem
import Submission.Work.DSM5b.chartRing_overlap_isLocalization
import Submission.Work.DSM5b.isIntegral_ccC0_iff_isIntegral_e0
import Submission.Work.DSM5b.chartRing_gen_mul_eq
import Submission.Work.DSM5b.chartRing_mem_pow

namespace Work.DSM5b

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-!
# DSM5b — the coordinate form of the integrality of the components of a `0`-cycle

`Work.DSM5b.cycle_component_isIntegral` (file `Submission/Work/DSM5b/cycle_component_isIntegral.lean`)
proves that every component of every `0`-cycle of the honest chart Čech complex is integral over
`R`, and its proof uses the library lemmas `exists_maximiser`, `exists_chartRing_gen_family`,
`chartRing_overlap_extension` which live *in that same file*.  That file imports
`Submission.Work.DSM5b.chartCechH0_root_killing`, so it cannot be imported back from
`component_isIntegral_pairwise.lean` (import cycle), and the three helpers are therefore not
available here.

The three helpers are re-proved, under distinct names, below (they are short and self-contained:
the `i`-chart generator family with `u i = 1`, the value-maximising index of the valuative
criterion of properness of the blowup, and the extension of a `K`-point from a chart to the
overlap, the latter two from `Work.DSM5b.chartRing_overlap_isLocalization`).
-/

/-- **A family of generators of the `i`-th chart, with the `i`-th member equal to `1`.**  For every
`l` the chart ring `chartRing t {i}` contains an element `u l` with
`(u l) * algebraMap (t i) = algebraMap (t l)` (`Work.DSM5b.chartRing_gen_mul_eq`); since `t i` is
a nonzerodivisor in the localisation, this element is unique, so the chosen family can be modified
to have `u i = 1`.

Local copy of `Work.DSM5b.exists_chartRing_gen_family` (which lives in
`cycle_component_isIntegral.lean` and hence cannot be imported here). -/
lemma exists_chartRing_gen_family_pairwise_aux {R : Type a} [CommRing R] {ι : Type a}
    [DecidableEq ι] (t : ι → R) (i : ι) :
    ∃ u : ι → ↥(chartRing t {i}),
      u i = 1 ∧ ∀ l : ι,
        (u l : Localization.Away (tS t {i}))
          * algebraMap R (Localization.Away (tS t {i})) (t i)
        = algebraMap R (Localization.Away (tS t {i})) (t l) := by
  classical
  choose v hv using fun l : ι => chartRing_gen_mul_eq t i l
  refine ⟨fun l => if h : l = i then 1 else v l, by simp, fun l => ?_⟩
  by_cases h : l = i
  · subst h; simp
  · simp only [dif_neg h]; exact hv l

/-- **The value-maximising index.**  Let `A ⊆ K` be a valuation ring, `ψ : chartRing t {i} →+* K`
and `u` a family of generators of the `i`-th chart with `u i = 1`.  Then there is an index `j`
such that every value `ψ (u l)` is an `A`-multiple of `ψ (u j)` and `ψ (u j) ≠ 0`.

Local copy of `Work.DSM5b.exists_maximiser` (which lives in `cycle_component_isIntegral.lean` and
hence cannot be imported here).  Since `ψ (u i) = 1 ≠ 0`, the relation
`y l = a * y j` (`a ∈ A`) is a total preorder on the (finite) index set, and a total preorder on a
finite set has a greatest element. -/
lemma exists_maximiser_pairwise_aux {R : Type a} [CommRing R] {ι : Type a} [Finite ι]
    [DecidableEq ι] (t : ι → R) (i : ι) (u : ι → ↥(chartRing t {i})) (hui : u i = 1)
    {A K : Type a} [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] (ψ : ↥(chartRing t {i}) →+* K) :
    ∃ j : ι, (∀ l : ι, ∃ a : A, ψ (u l) = algebraMap A K a * ψ (u j)) ∧ ψ (u j) ≠ 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  -- the total preorder `y l ≤ y m :⟺ ∃ a : A, y l = a * y m`, where `y l = ψ (u l)`
  let r : ι → ι → Prop := fun l m => ∃ a : A, ψ (u l) = algebraMap A K a * ψ (u m)
  have hrefl : ∀ l, r l l := fun l => ⟨1, by simp [r]⟩
  have htrans : ∀ l m n, r l m → r m n → r l n := by
    intro l m n ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [ha, hb, map_mul, mul_assoc]⟩
  have htot : ∀ l m, r l m ∨ r m l := by
    intro l m
    by_cases hm : ψ (u m) = 0
    · exact Or.inr ⟨0, by rw [hm, map_zero, zero_mul]⟩
    · by_cases hl : ψ (u l) = 0
      · exact Or.inl ⟨0, by rw [hl, map_zero, zero_mul]⟩
      · rcases ValuationRing.isInteger_or_isInteger A (K := K) (ψ (u l) / ψ (u m)) with
          ⟨a, ha⟩ | ⟨a, ha⟩
        · exact Or.inl ⟨a, by rw [ha, div_mul_cancel₀ _ hm]⟩
        · refine Or.inr ⟨a, ?_⟩
          rw [inv_div] at ha
          rw [ha, div_mul_cancel₀ _ hl]
  -- a maximum of a total preorder on a finite set
  have hmax : ∀ s : Finset ι, s.Nonempty → ∃ j ∈ s, ∀ l ∈ s, r l j := by
    intro s
    induction s using Finset.induction with
    | empty => intro h; exact absurd h Finset.not_nonempty_empty
    | insert a s ha ih =>
      intro _
      rcases s.eq_empty_or_nonempty with hs | hs
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro l hl
        simp only [hs, Finset.mem_insert, Finset.notMem_empty, or_false] at hl
        rw [hl]
        exact hrefl a
      · obtain ⟨j, hjs, hj⟩ := ih hs
        by_cases hcase : r a j
        · refine ⟨j, Finset.mem_insert_of_mem hjs, ?_⟩
          intro l hl
          rcases Finset.mem_insert.mp hl with hEq | hl
          · rw [hEq]; exact hcase
          · exact hj l hl
        · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
          intro l hl
          rcases Finset.mem_insert.mp hl with hEq | hl
          · rw [hEq]; exact hrefl a
          · rcases htot l a with h | h
            · exact h
            · exact absurd (htrans a l j h (hj l hl)) hcase
  obtain ⟨j, -, hj⟩ := hmax Finset.univ ⟨i, Finset.mem_univ i⟩
  refine ⟨j, fun l => hj l (Finset.mem_univ l), ?_⟩
  rcases hj i (Finset.mem_univ i) with ⟨a, ha⟩
  intro h0
  rw [hui, map_one, h0, mul_zero] at ha
  exact one_ne_zero ha

/-- The underlying ring homomorphism of `ccRestr` is `ccRestr` itself (so that the `.toRingHom`
decorations produced by `IsLocalization.Away.lift` can be removed). -/
lemma ccRestr_toRingHom_apply {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) {S T : Finset ι} (h : S ⊆ T) (x : ↥(chartRing t S)) :
    (ccRestr t h).toRingHom x = ccRestr t h x := rfl

/-- **Extension of a `K`-valued point from the `i`-chart to the overlap.**  If `u ∈ chartRing t {i}`
satisfies `u * algebraMap (t i) = algebraMap (t j)` (`u = t j / t i`) and `ψ u` is a unit, then `ψ`
extends to the overlap chart `chartRing t ({i} ∪ {j})` along `ccRestr t (Finset.subset_union_left)`.

Local copy of `Work.DSM5b.chartRing_overlap_extension` (which lives in
`cycle_component_isIntegral.lean`); it is a direct consequence of
`Work.DSM5b.chartRing_overlap_isLocalization` (the overlap is the localisation of the `i`-chart at
`u`) and `IsLocalization.Away.lift`. -/
lemma chartRing_overlap_extension_pairwise_aux {R : Type a} [CommRing R] {ι : Type a}
    [DecidableEq ι] (t : ι → R) (i j : ι) (u : ↥(chartRing t {i}))
    (hu : (u : Localization.Away (tS t {i}))
        * algebraMap R (Localization.Away (tS t {i})) (t i)
      = algebraMap R (Localization.Away (tS t {i})) (t j))
    {K : Type a} [CommRing K] (ψ : ↥(chartRing t {i}) →+* K) (hunit : IsUnit (ψ u)) :
    ∃ χ : ↥(chartRing t ({i} ∪ {j})) →+* K,
      χ.comp (ccRestr t (Finset.subset_union_left)).toRingHom = ψ := by
  letI : Algebra ↥(chartRing t {i}) ↥(chartRing t ({i} ∪ {j})) :=
    (ccRestr t (Finset.subset_union_left)).toAlgebra
  haveI := chartRing_overlap_isLocalization t i j u hu
  exact ⟨IsLocalization.Away.lift u hunit, IsLocalization.Away.lift_comp u hunit⟩

/-- **The coordinate form of the integrality of the components of a `0`-cycle.** `R` is perfect of characteristic `p`, `t : ι → R` finite, `T ∈ R`, `t j₀ = T ^ e`, and `y` is a compatible family of chart rings (the coordinates of a `0`-cycle of `chartCech t`, i.e. the pairwise gluing holds on the overlaps). Then every `y i` is integral over `R`.

This is `Work.DSM5b.cycle_component_isIntegral` re-stated in the coordinates of `Work.DSM5b.e0`. It is needed because the target `Work.DSM5b.chartCechH0_root_killing` cannot import `cycle_component_isIntegral.lean`: that file imports `chartCechH0_root_killing.lean`, so importing it back would be an import cycle. Consequently `Work.DSM5b.exists_maximiser` and `Work.DSM5b.chartRing_overlap_extension` (which live in that file) are *not* available here and the valuative-criterion argument must be re-run from the pieces listed in `depends_on` (`integrality_valuative_criterion`, `chartRing_mem_pow`, `mem_pow_ideal_sum_prod`, `chartRing_phi_j_range_mem`, `chartRing_overlap_isLocalization`, `chartCech_cycle_iff_pairwise`, `isIntegral_ccC0_iff_isIntegral_e0`), or else via the `e0`-form transfer. -/
theorem component_isIntegral_pairwise (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R)
    (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = T ^ e) (y : ∀ i : ι, ↥(chartRing t {i}))
    (hy : ∀ i j : ι,
      locRes t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j})
          ((y i : chartRing t {i}) : Localization.Away (tS t {i}))
        = locRes t (Finset.subset_union_right : ({j} : Finset ι) ⊆ {i} ∪ {j})
          ((y j : chartRing t {j}) : Localization.Away (tS t {j})))
    (i : ι) : IsIntegral R (y i) := by
  classical
  -- the valuative criterion for integrality of an element
  rw [integrality_valuative_criterion]
  intro A _ _ _ K _ _ _ φ ψ hcompat
  -- 1. a family of generators of the `i`-th chart (with `u i = 1`)
  obtain ⟨u, hui, hu⟩ := exists_chartRing_gen_family_pairwise_aux t i
  -- 2. the value-maximising index `j`
  obtain ⟨j, hjmax, hjne⟩ := exists_maximiser_pairwise_aux (A := A) (K := K) t i u hui ψ
  -- 3. the extension of `ψ` to the overlap chart
  obtain ⟨χ, hχ⟩ :=
    chartRing_overlap_extension_pairwise_aux t i j (u j) (hu j) ψ (isUnit_iff_ne_zero.mpr hjne)
  -- 4. the estimate: the whole `j`-chart lands in the image of `A`
  have hest := chartRing_phi_j_range_mem t φ i j u hu ψ hcompat hjmax hjne χ hχ
  -- 5. the gluing condition of the compatible family, read in the overlap
  obtain ⟨b, hb⟩ := hest (y j)
  refine ⟨b, ?_⟩
  rw [hb, ← RingHom.congr_fun hχ (y i)]
  refine congrArg χ (Subtype.ext ?_)
  rw [ccRestr_toRingHom_apply, ccRestr_coe, ccRestr_coe]
  exact hy i j

end Work.DSM5b
