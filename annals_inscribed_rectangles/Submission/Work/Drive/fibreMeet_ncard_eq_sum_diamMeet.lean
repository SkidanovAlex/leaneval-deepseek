import Mathlib
import Submission.Work.Drive.collapseT4defs
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.collapseTransport

/-!
# The fibre decomposition of the `s = 1` collapsed meet count

`Work.Drive.fibreMeet Q V W` is the set of quadruples `(t, σ, y, z)` with `t ∈ [0,1)`, `σ ∈ [0,1]`,
`y, z` in the parameter cube of `W`, at which the core loop of the chart at the direction `t` meets
the chain `V` at `y` and the diameter loop at the direction `t` meets `W` at `z`.

Since the two conditions involve **disjoint sets of coordinates** — `(t, y)` occur only in the first
one and `(σ, z)` only in the second — the set is the disjoint union, over the *core meets*
`q = (t, y) ∈ Work.Drive.coreMeet Q c P₁` (with `V = Work.Drive.clampedSweep c (1 - ·) P₁`), of the
copies of the diameter meet `Work.Drive.diamMeet Q q.1 W` at the direction `q.1`, placed at the
direction `q.1` and the chain parameter `q.2`:

> `Work.Drive.fibreMeet Q (clampedSweep c (1 - ·) P₁) W`
>   `= ⋃ q ∈ coreMeet Q c P₁, {(q.1, σ, q.2, z) | (σ, z) ∈ diamMeet Q q.1 W}`.

Consequently (`Work.Drive.fibreMeet_ncard_eq_sum_diamMeet`)

> `#fibreMeet = ∑_{q ∈ coreMeet} #(diamMeet Q q.1 W)`,

which is the form in which the transport consumes the count: it turns the count of the fibre
presentation into the *sum of the diameter-meet counts over the core meets*.

The only hypothesis that is not bookkeeping is `hbase`: the chart's core loop at `t = 1` misses the
chain `V` entirely.  Without it the direction `t = 1` would contribute to `coreMeet` (which is
parametrised on the *closed* interval `[0,1]`) but not to `fibreMeet` (which uses `[0,1)`), and the
two sides would differ.  With it, every core meet has `t < 1`, and the fibre description is exact.

Everything here is `Set`-level bookkeeping: the count of a disjoint union of the fibres
(`Set.Finite.ncard_biUnion`), with the bijection `(σ, z) ↦ (q.1, σ, q.2, z)` on each fibre.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

theorem fibreMeet_ncard_eq_sum_diamMeet (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (P₁ : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (W : EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace)
    (hfin : (Work.Drive.coreMeet Q c P₁).Finite)
    (hfind : ∀ q ∈ Work.Drive.coreMeet Q c P₁,
      (Work.Drive.diamMeet Q q.1 W).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      Work.Drive.coreLoop Q 1 ≠ Work.Drive.clampedSweep c (fun t => 1 - t) P₁ y) :
    (Work.Drive.fibreMeet Q (Work.Drive.clampedSweep c (fun t => 1 - t) P₁) W).ncard
      = Finset.sum hfin.toFinset (fun q => (Work.Drive.diamMeet Q q.1 W).ncard) := by
  classical
  -- The fibre over the core meet `q = (t, y)`: the diameter meet at the direction `t`, placed at the
  -- direction `t` and the chain parameter `y`.
  let F : ℝ × Work.Drive.Amb 2 → Set (ℝ × ℝ × Work.Drive.Amb 2 × Work.Drive.Amb 2) :=
    fun q => (fun r : ℝ × Work.Drive.Amb 2 => (q.1, r.1, q.2, r.2)) ''
      (Work.Drive.diamMeet Q q.1 W)
  -- Membership in a fibre, unwound.
  have hmemF : ∀ (q : ℝ × Work.Drive.Amb 2)
      (p : ℝ × ℝ × Work.Drive.Amb 2 × Work.Drive.Amb 2),
      p ∈ F q ↔ p.1 = q.1 ∧ p.2.2.1 = q.2 ∧
        (p.2.1, p.2.2.2) ∈ Work.Drive.diamMeet Q q.1 W := by
    intro q p
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨rfl, rfl, hr⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(p.2.1, p.2.2.2), h3, by rw [← h1, ← h2]⟩
  -- The base hypothesis excludes the direction `t = 1` from the core meet.
  have hlt : ∀ q ∈ Work.Drive.coreMeet Q c P₁, q.1 < 1 := by
    intro q hq
    rw [Work.Drive.coreMeet, Set.mem_ofPred_eq] at hq
    obtain ⟨h1, h2, hloop⟩ := hq
    rcases lt_or_eq_of_le h1.2 with h | h
    · exact h
    · exact absurd (h ▸ hloop) (hbase q.2 h2)
  -- The fibre decomposition.
  have hunion : Work.Drive.fibreMeet Q (Work.Drive.clampedSweep c (fun t => 1 - t) P₁) W
      = ⋃ q ∈ Work.Drive.coreMeet Q c P₁, F q := by
    ext p
    constructor
    · intro hp
      rw [Work.Drive.fibreMeet, Set.mem_ofPred_eq] at hp
      obtain ⟨h1, h2, h3, h4, hcore, hdiam⟩ := hp
      have hq : (p.1, p.2.2.1) ∈ Work.Drive.coreMeet Q c P₁ := by
        rw [Work.Drive.coreMeet, Set.mem_ofPred_eq]
        exact ⟨⟨h1.1, le_of_lt h1.2⟩, h3, hcore⟩
      refine Set.mem_iUnion₂.mpr ⟨(p.1, p.2.2.1), hq, ?_⟩
      rw [hmemF]
      exact ⟨rfl, rfl, h2, h4, hdiam⟩
    · intro hp
      rw [Set.mem_iUnion₂] at hp
      obtain ⟨q, hq, hpq⟩ := hp
      rw [hmemF] at hpq
      obtain ⟨e1, e2, hd⟩ := hpq
      rw [Work.Drive.diamMeet, Set.mem_ofPred_eq] at hd
      obtain ⟨hd1, hd2, hd3⟩ := hd
      have hqc := hq
      rw [Work.Drive.coreMeet, Set.mem_ofPred_eq] at hqc
      obtain ⟨hc1, hc2, hcore⟩ := hqc
      have hqlt := hlt q hq
      rw [Work.Drive.fibreMeet, Set.mem_ofPred_eq]
      exact ⟨⟨by rw [e1]; exact hc1.1, by rw [e1]; exact hqlt⟩, hd1,
        by rw [e2]; exact hc2, hd2,
        by rw [e1, e2]; exact hcore, by rw [e1]; exact hd3⟩
  -- Each fibre is finite.
  have hFfin : ∀ q ∈ Work.Drive.coreMeet Q c P₁, (F q).Finite := by
    intro q hq
    exact (hfind q hq).image (fun r : ℝ × Work.Drive.Amb 2 => (q.1, r.1, q.2, r.2))
  -- Distinct core meets have disjoint fibres.
  have hpd : (Work.Drive.coreMeet Q c P₁).PairwiseDisjoint F := by
    rw [Set.pairwiseDisjoint_iff]
    intro a ha b hb hne
    obtain ⟨p, hp⟩ := hne
    rw [Set.mem_inter_iff, hmemF, hmemF] at hp
    obtain ⟨⟨ha1, ha2, -⟩, hb1, hb2, -⟩ := hp
    exact Prod.ext (ha1.symm.trans hb1) (ha2.symm.trans hb2)
  -- The fibre's count is the diameter meet's count.
  have hFcard : ∀ q : ℝ × Work.Drive.Amb 2, (F q).ncard
      = (Work.Drive.diamMeet Q q.1 W).ncard := by
    intro q
    refine Set.ncard_image_of_injective _ (fun r r' h => ?_)
    have h1 : r.1 = r'.1 := by
      simpa using congrArg (fun z : ℝ × ℝ × Work.Drive.Amb 2 × Work.Drive.Amb 2 => z.2.1) h
    have h2 : r.2 = r'.2 := by
      simpa using congrArg (fun z : ℝ × ℝ × Work.Drive.Amb 2 × Work.Drive.Amb 2 => z.2.2.2) h
    exact Prod.ext h1 h2
  rw [hunion]
  rw [Set.Finite.ncard_biUnion hfin hFfin hpd]
  rw [finsum_mem_eq_finite_toFinset_sum (fun i => (F i).ncard) hfin]
  exact Finset.sum_congr rfl (fun q _ => hFcard q)

end

end Work.Drive
