import Mathlib
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLComp.exists_isCompact_cover_subgroup

/-!
# `Work.EKLC6Core.measurableSet_avoid`

The "avoidance set"

  `{y : X₃ | ∀ u ∈ U, u ∈ V δ → u • y ∉ C}`

is Borel, for `U ≤ SL₃(ℝ)` a **closed** subgroup, `δ > 0` and `C ⊆ X₃` a countable union of
compact sets.

## Why this is not immediate

The quantifier `∀ u ∈ U` ranges over an uncountable set, so the usual "countable intersection of
measurable sets" argument does not apply directly: one has to replace `U ∩ V δ` by a *countable*
union of compacta.  This is where closedness of `U` is used: `U` is a closed subspace of the
second countable locally compact group `SL₃(ℝ)`, hence locally compact and second countable, so
its open subset `U ∩ V δ` is σ-compact
(`Work.EKLComp.exists_isCompact_cover_subgroup`).

With `U ∩ V δ = ⋃ n, A n` (`A n` compact) and `C = ⋃ m, K m` (`K m` compact) the avoidance set is
the complement of the countable union of the sets `{y | ∃ u ∈ A n, u • y ∈ K m}`, and each of
these is closed: it is the image of the compact set `A n × K m` under the continuous map
`(u, c) ↦ u⁻¹ • c`, and `X₃` is Hausdorff.
-/

open MeasureTheory Set Topology

namespace Work.EKLC6Core

open Work.EKLContract

set_option linter.style.haveILetI false

/-- For `A ⊆ SL₃(ℝ)` and `K ⊆ X₃` compact, the set of `y` whose `A`-orbit meets `K` is closed:
it is the image of the compact set `A × K` under the continuous map `(u, c) ↦ u⁻¹ • c`. -/
lemma isClosed_exists_smul_mem_of_isCompact {A : Set SL3} (hA : IsCompact A) {K : Set X3}
    (hK : IsCompact K) : IsClosed {y : X3 | ∃ g ∈ A, g • y ∈ K} := by
  haveI : T2Space X3 := Work.EKLComp.X3Background.1
  haveI : CompactSpace ↥(A ×ˢ K) := isCompact_iff_compactSpace.mp (hA.prod hK)
  have hcont : Continuous (fun q : ↥(A ×ˢ K) => (q.1.1 : SL3)⁻¹ • (q.1.2 : X3)) := by fun_prop
  have hset : {y : X3 | ∃ g ∈ A, g • y ∈ K} =
      (fun q : ↥(A ×ˢ K) => (q.1.1 : SL3)⁻¹ • (q.1.2 : X3)) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨g, hg, hgy⟩
      exact ⟨⟨(g, g • y), Set.mem_prod.mpr ⟨hg, hgy⟩⟩, Set.mem_univ _, inv_smul_smul g y⟩
    · rintro ⟨q, -, rfl⟩
      refine ⟨q.1.1, (Set.mem_prod.mp q.2).1, ?_⟩
      rw [smul_inv_smul]
      exact (Set.mem_prod.mp q.2).2
  rw [hset]
  exact (isCompact_univ.image hcont).isClosed

theorem measurableSet_avoid {U : Subgroup Work.EKLContract.SL3}
    (hU : IsClosed (U : Set Work.EKLContract.SL3)) {C : Set Work.EKLContract.X3}
    (hC : ∃ K : ℕ → Set Work.EKLContract.X3, (∀ m, IsCompact (K m)) ∧ C = ⋃ m, K m)
    {δ : ℝ} (hδ : 0 < δ) :
    MeasurableSet {y : Work.EKLContract.X3 |
      ∀ u ∈ U, u ∈ Work.EKLContract.V δ → u • y ∉ C} := by
  obtain ⟨K, hKc, hCeq⟩ := hC
  rw [hCeq]
  have hVopen : IsOpen (V δ) := (Work.EKLContract.Lemmas.V_open_one δ hδ).1
  obtain ⟨A, hAc, hAcov⟩ := Work.EKLComp.exists_isCompact_cover_subgroup U hU (V δ) hVopen
  -- `U ∩ V δ` is the union of the compacta `A n`
  have hmem : ∀ u : SL3, u ∈ (⋃ n : ℕ, A n) ↔ u ∈ U ∧ u ∈ V δ := by
    intro u
    rw [hAcov, Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  -- the avoidance set, as a countable intersection of complements of closed sets
  have hset : {y : X3 | ∀ u ∈ U, u ∈ V δ → u • y ∉ ⋃ m : ℕ, K m}
      = ⋂ n : ℕ, ⋂ m : ℕ, {y : X3 | ∃ u ∈ A n, u • y ∈ K m}ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff]
    constructor
    · intro h n m hu
      obtain ⟨u, huA, huy⟩ := hu
      obtain ⟨huU, huV⟩ := (hmem u).mp (Set.mem_iUnion.mpr ⟨n, huA⟩)
      exact h u huU huV ⟨m, huy⟩
    · intro h u huU huV hm
      obtain ⟨m, hm'⟩ := hm
      obtain ⟨n, hnA⟩ := Set.mem_iUnion.mp ((hmem u).mpr ⟨huU, huV⟩)
      exact h n m ⟨u, hnA, hm'⟩
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => ?_
  exact (isClosed_exists_smul_mem_of_isCompact (hAc n) (hKc m)).measurableSet.compl

end Work.EKLC6Core
