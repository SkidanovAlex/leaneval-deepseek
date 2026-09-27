import Mathlib
import Submission.Work.Whitney.CutPush.local_graph_data

/-!
# A smooth bump that is identically one on a prescribed compact set

`exists_contDiffBump_one_on_compact`: for a compact `K` inside an open `U` (in a normed space with
bump functions, e.g. a finite-dimensional Euclidean space) there is a smooth `χ` with `χ = 1` on `K`
and `tsupport χ ⊆ U`.

This is the tool with which each chart-local family of the M1 construction
(`CutPush/NOTES_STATE_S59.md` §2.1) is cut off: the bump is built as `1 - ∏ (1 - β j)` from the bumps
`β j` of `exists_contDiffBump_near` (`CutPush/local_graph_data.lean`) over a finite subcover of `K` by
balls, so its support is the finite union of theirs.
-/

namespace Work.Whitney.CutPush

open scoped ContDiff
open Topology

/-- **A smooth bump equal to one on an *open* neighbourhood of a compact set.**

This is the form the M1 construction consumes (`CutPush/NOTES_STATE_S59.md` §2.1): the bump must be
identically `1` on a *neighbourhood* of the relevant compact set, so that the bumped map agrees with
the unbumped one on a neighbourhood of each point of that set (an eventual equality is what the
derivative computation needs). -/
theorem exists_contDiffBump_one_on_open_of_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ (χ : E → ℝ) (V : Set E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ IsOpen V ∧ K ⊆ V ∧
      V ⊆ U ∧ (∀ x ∈ V, χ x = 1) ∧ tsupport χ ⊆ U := by
  classical
  have hex : ∀ x : K, ∃ (χ : E → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ y, dist y (x : E) ≤ r → χ y = 1) ∧ (∀ y, 0 ≤ χ y) ∧ tsupport χ ⊆ U :=
    fun x => exists_contDiffBump_near hU (hKU x.2)
  choose χ r hr hχc hχ1 hχ0 hχs using hex
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : E) (r x) := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨(⟨y, hy⟩ : K), ?_⟩
    rw [Metric.mem_ball]
    simpa using hr ⟨y, hy⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (x : E) (r x))
    (fun x => Metric.isOpen_ball) hcov
  set V : Set E := ⋃ x ∈ t, Metric.ball (x : E) (r x) with hVdef
  have hVo : IsOpen V := isOpen_biUnion fun x _ => Metric.isOpen_ball
  have hKV : K ⊆ V := by
    intro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht hy)
    obtain ⟨hxt, hxball⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion₂.mpr ⟨x, hxt, hxball⟩
  set χ' : E → ℝ := fun y => 1 - ∏ x ∈ t, (1 - χ x y) with hχ'def
  have hχ'c : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ' := by
    rw [hχ'def]
    refine contDiff_const.sub ?_
    exact contDiff_prod fun x _ => contDiff_const.sub (hχc x)
  have hone : ∀ y ∈ V, χ' y = 1 := by
    intro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hxt, hxball⟩ := Set.mem_iUnion.mp hx
    have hxy : dist y (x : E) < r x := by simpa [Metric.mem_ball] using hxball
    have h1 : χ x y = 1 := hχ1 x y (le_of_lt hxy)
    rw [hχ'def]
    simp only
    rw [Finset.prod_eq_zero hxt (by simp [h1])]
    ring
  have hvan : ∀ y, (∀ x ∈ t, χ x y = 0) → χ' y = 0 := by
    intro y hy
    rw [hχ'def]
    simp only
    have h1 : (∏ x ∈ t, (1 - χ x y)) = 1 :=
      Finset.prod_eq_one fun x hx => by rw [hy x hx]; ring
    rw [h1]
    ring
  have hsupp : Function.support χ' ⊆ ⋃ x ∈ t, Function.support (χ x) := by
    intro y hy
    by_contra hcon
    apply hy
    refine hvan y fun x hx => ?_
    by_contra hne
    exact hcon (Set.mem_iUnion₂.mpr ⟨x, hx, Function.mem_support.mpr hne⟩)
  have hVU : V ⊆ U := by
    intro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hxt, hxball⟩ := Set.mem_iUnion.mp hx
    have hxy : dist y (x : E) < r x := by simpa [Metric.mem_ball] using hxball
    have h1 : χ x y = 1 := hχ1 x y (le_of_lt hxy)
    have : y ∈ tsupport (χ x) := subset_tsupport _ (Function.mem_support.mpr (by rw [h1]; norm_num))
    exact hχs x this
  have hts : tsupport χ' ⊆ U := by
    have hclosed : IsClosed (⋃ x ∈ t, tsupport (χ x)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    have hsub : tsupport χ' ⊆ ⋃ x ∈ t, tsupport (χ x) :=
      (hclosed.closure_subset_iff).mpr (hsupp.trans fun z hz => by
        obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hxt, hzx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, subset_tsupport _ hzx⟩)
    exact hsub.trans fun z hz => by
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hxt, hzx⟩ := Set.mem_iUnion.mp hx
      exact hχs x hzx
  exact ⟨χ', V, hχ'c, hVo, hKV, hVU, hone, hts⟩

/-- **A smooth bump equal to one on a compact set.**  The weaker form in which the conclusion is the
value clause only on `K` itself. -/
theorem exists_contDiffBump_one_on_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ x ∈ K, χ x = 1) ∧
      tsupport χ ⊆ U := by
  obtain ⟨χ, V, hχc, -, hKV, -, hV1, hts⟩ :=
    exists_contDiffBump_one_on_open_of_compact hU hK hKU
  exact ⟨χ, hχc, fun x hx => hV1 x (hKV hx), hts⟩

end Work.Whitney.CutPush
