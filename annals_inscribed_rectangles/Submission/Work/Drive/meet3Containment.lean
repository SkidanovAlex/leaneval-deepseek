import Mathlib
import Submission.Work.Drive.hVStability
import Submission.Work.Drive.TParity.Basic

/-!
# Containment of the perturbed triple locus (`faceHyp`/`hcontain` bookkeeping of the Sard route)

The parametric-Sard route to the counting engine's transversality hypothesis
(`Work.Drive.transHyp_of_good_family`, `Submission/Work/Drive/HV_GENERICITY_STATUS.md` §5–§9) needs one
piece of bookkeeping beyond the Sard result itself: the *perturbed* triple locus of a smooth family of
triples of chains must stay inside the compact region `K` on which the chart and the Sard conclusion are
available.  This file proves exactly that, as an instance of the tube lemma
`Work.Drive.exists_prod_nhds_subset_of_isCompact`:

> if every triple point of the *base* configuration `G 0` inside the nine-box lies in an open set `U`,
> then — for all parameters sufficiently close to `0` — every triple point of `G t` inside the nine-box
> lies in `U`.

(For the route one takes `U := Kᵒ`; the statement is the "stays inside `K`" condition recorded as
`hcontain` in the delegated assembly.  Note that the conclusion is *not* that the triple locus is close
to the base one as a set, but the weaker and precisely sufficient statement that no triple point
escapes `U`.)
-/

namespace Work.Drive

open Set Filter

/-- **The triple condition of a smooth family is closed.** -/
theorem isClosed_meet3Set {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, Continuous (fun q : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin 3) => G q.1 k q.2)) :
    IsClosed {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      q.2 ∈ Submission.Drive.unitBox 8 ∧ Work.Drive.TParity.meet3 (G q.1) q.2} := by
  have h0 : Continuous (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
      G q.1 0 (Work.Drive.TParity.bPartC 0 q.2)) :=
    (hG 0).comp (((continuous_fst).prodMk ((Work.Drive.TParity.bPartC 0).continuous.comp
      continuous_snd)))
  have h1 : Continuous (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
      G q.1 1 (Work.Drive.TParity.bPartC 1 q.2)) :=
    (hG 1).comp (((continuous_fst).prodMk ((Work.Drive.TParity.bPartC 1).continuous.comp
      continuous_snd)))
  have h2 : Continuous (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
      G q.1 2 (Work.Drive.TParity.bPartC 2 q.2)) :=
    (hG 2).comp (((continuous_fst).prodMk ((Work.Drive.TParity.bPartC 2).continuous.comp
      continuous_snd)))
  have hbox : IsClosed {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      q.2 ∈ Submission.Drive.unitBox 8} :=
    (isClosed_unitBox 8).preimage continuous_snd
  have hmeet : IsClosed {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      Work.Drive.TParity.meet3 (G q.1) q.2} := by
    have : {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
        Work.Drive.TParity.meet3 (G q.1) q.2} =
        {q | G q.1 0 (Work.Drive.TParity.bPartC 0 q.2) =
          G q.1 1 (Work.Drive.TParity.bPartC 1 q.2)} ∩
        {q | G q.1 0 (Work.Drive.TParity.bPartC 0 q.2) =
          G q.1 2 (Work.Drive.TParity.bPartC 2 q.2)} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Work.Drive.TParity.meet3]
    rw [this]
    exact (isClosed_eq h0 h1).inter (isClosed_eq h0 h2)
  have : {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      q.2 ∈ Submission.Drive.unitBox 8 ∧ Work.Drive.TParity.meet3 (G q.1) q.2} =
      {q | q.2 ∈ Submission.Drive.unitBox 8} ∩
      {q | Work.Drive.TParity.meet3 (G q.1) q.2} := by
    ext q; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [this]
  exact hbox.inter hmeet

/-- **The perturbed triple locus stays inside a prescribed open set.**  If every triple point of the
base configuration `G 0` in the nine-box lies in the open set `U`, then all parameters near `0` have
their triple points in the nine-box inside `U` as well. -/
theorem eventually_meet3_subset_of_isOpen {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, Continuous (fun q : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    {U : Set (EuclideanSpace ℝ (Fin 9))} (hU : IsOpen U)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (G 0) y → y ∈ U) :
    ∀ᶠ t in nhds (0 : EuclideanSpace ℝ (Fin m)),
      ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
        Work.Drive.TParity.meet3 (G t) y → y ∈ U := by
  set Z : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9)) :=
    {q | q.2 ∈ Submission.Drive.unitBox 8 ∧ Work.Drive.TParity.meet3 (G q.1) q.2} with hZ
  have hZcl : IsClosed Z := isClosed_meet3Set G hG
  have hUopen : IsOpen ((Set.univ : Set (EuclideanSpace ℝ (Fin m))) ×ˢ U) :=
    isOpen_univ.prod hU
  have hsub : Z ∩ ({(0 : EuclideanSpace ℝ (Fin m))} ×ˢ Submission.Drive.unitBox 8) ⊆
      (Set.univ : Set (EuclideanSpace ℝ (Fin m))) ×ˢ U := by
    rintro ⟨t, y⟩ ⟨⟨hy, hmeet⟩, ht0, -⟩
    have ht0' : t = 0 := Set.mem_singleton_iff.mp ht0
    subst ht0'
    exact ⟨trivial, hbase y hy hmeet⟩
  obtain ⟨W, hW0, hWopen, hWsub⟩ := exists_prod_nhds_subset_of_isCompact_set hZcl hUopen
    (isCompact_singleton (x := (0 : EuclideanSpace ℝ (Fin m)))) (isCompact_unitBox 8) hsub
  filter_upwards [hWopen.mem_nhds (hW0 (Set.mem_singleton 0))] with t ht y hy hmeet
  have hmem : ((t, y) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9)) ∈
      Z ∩ (W ×ˢ Submission.Drive.unitBox 8) := ⟨⟨hy, hmeet⟩, ⟨ht, hy⟩⟩
  exact (hWsub hmem).2

end Work.Drive
