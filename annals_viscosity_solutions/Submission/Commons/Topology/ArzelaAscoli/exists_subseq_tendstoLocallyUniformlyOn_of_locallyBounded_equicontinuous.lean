import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Commons.Topology.ArzelaAscoli

open Filter Set
open scoped _root_.Topology

/-- Auxiliary form of Ascoli's theorem: if a sequence of functions on a locally compact space is
equicontinuous on every compact set and converges pointwise (to a Cauchy sequence) on a dense
subset, then it is uniformly Cauchy on every compact set.

The proof covers a compact set `K` by finitely many neighbourhoods coming from equicontinuity on a
slightly larger compact set `K'` (which exists because `X` is locally compact), picks a point of
the dense set inside each of these neighbourhoods and inside `K'`, and combines the pointwise
Cauchy property at those points with equicontinuity. -/
theorem uniform_cauchy_of_dense_cauchy {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {E : Type*} [PseudoMetricSpace E] {f : ℕ → X → E} {φ : ℕ → ℕ} {D : Set X}
    (hDense : Dense D) (hconv : ∀ d ∈ D, CauchySeq (fun k => f (φ k) d))
    (heq : ∀ K : Set X, IsCompact K → Equicontinuous (fun n : ℕ => fun x : K => f n x)) :
    ∀ K : Set X, IsCompact K → ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ K,
      dist (f (φ k) x) (f (φ l) x) < ε := by
  classical
  intro K hK ε hε
  have hε4 : 0 < ε / 4 := by linarith
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨K', hK'cpt, hK'K⟩ := exists_compact_superset hK
  have hF : Equicontinuous (fun n : ℕ => fun x : K' => f n x) := heq K' hK'cpt
  have hW : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      (x ∈ K' → ∀ i, ∀ a ∈ W ∩ (K' : Set X), ∀ b ∈ W ∩ (K' : Set X),
        dist (f i a) (f i b) < ε / 4) := by
    intro x
    by_cases hx : x ∈ K'
    · obtain ⟨U, hU, hUprop⟩ :=
        Metric.equicontinuousAt_iff_pair.mp (hF ⟨x, hx⟩) (ε / 4) hε4
      obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
      obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp hVopen
      refine ⟨W, hWopen, ?_, ?_⟩
      · have : (⟨x, hx⟩ : K') ∈ Subtype.val ⁻¹' W := hWeq ▸ hxV
        exact this
      · intro _ i a ha b hb
        have haU : (⟨a, ha.2⟩ : K') ∈ U := hVU (by rw [← hWeq]; exact ha.1)
        have hbU : (⟨b, hb.2⟩ : K') ∈ U := hVU (by rw [← hWeq]; exact hb.1)
        exact hUprop ⟨a, ha.2⟩ haU ⟨b, hb.2⟩ hbU i
    · exact ⟨univ, isOpen_univ, mem_univ x, fun h => absurd h hx⟩
  choose W hWopen hWmem hWprop using hW
  obtain ⟨t, htK, htcover⟩ := hK.elim_nhds_subcover W (fun y hy => (hWopen y).mem_nhds (hWmem y))
  have hw : ∀ y, y ∈ t → ∃ w : X, w ∈ D ∧ w ∈ W y ∩ interior K' := by
    intro y hy
    exact hDense.exists_mem_open ((hWopen y).inter isOpen_interior)
      ⟨y, hWmem y, hK'K (htK y hy)⟩
  let w : X → X := fun y => if hy : y ∈ t then Classical.choose (hw y hy) else y
  have hw_eq : ∀ (y : X) (hy : y ∈ t), w y = Classical.choose (hw y hy) := fun y hy => dif_pos hy
  have hwD : ∀ (y : X) (hy : y ∈ t), w y ∈ D := by
    intro y hy; rw [hw_eq y hy]; exact (Classical.choose_spec (hw y hy)).1
  have hwW : ∀ (y : X) (hy : y ∈ t), w y ∈ W y := by
    intro y hy; rw [hw_eq y hy]; exact (Classical.choose_spec (hw y hy)).2.1
  have hwK' : ∀ (y : X) (hy : y ∈ t), w y ∈ K' := by
    intro y hy; rw [hw_eq y hy]
    exact interior_subset (Classical.choose_spec (hw y hy)).2.2
  have hCau : ∀ y, y ∈ t → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
      dist (f (φ k) (w y)) (f (φ l) (w y)) < ε / 2 := by
    intro y hy
    have hc := hconv (w y) (hwD y hy)
    rw [Metric.cauchySeq_iff] at hc
    exact hc (ε / 2) hε2
  let Nb : X → ℕ := fun y => if hy : y ∈ t then Classical.choose (hCau y hy) else 0
  have hNb_eq : ∀ (y : X) (hy : y ∈ t), Nb y = Classical.choose (hCau y hy) := fun y hy => dif_pos hy
  let N : ℕ := t.sup Nb
  refine ⟨N, fun k hk l hl x hx => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (htcover hx)
  have hyK : y ∈ K := htK y hyt
  have hyK' : y ∈ K' := interior_subset (hK'K hyK)
  have hNb_le : Nb y ≤ N := Finset.le_sup (f := Nb) hyt
  have hCaub : ∀ k ≥ Nb y, ∀ l ≥ Nb y,
      dist (f (φ k) (w y)) (f (φ l) (w y)) < ε / 2 := by
    rw [hNb_eq y hyt]; exact Classical.choose_spec (hCau y hyt)
  have hk' : k ≥ Nb y := le_trans hNb_le hk
  have hl' : l ≥ Nb y := le_trans hNb_le hl
  have hxK' : x ∈ K' := interior_subset (hK'K hx)
  have hwyW : w y ∈ W y := hwW y hyt
  have hwyK' : w y ∈ K' := hwK' y hyt
  have h1 : dist (f (φ k) x) (f (φ k) (w y)) < ε / 4 :=
    hWprop y hyK' (φ k) x ⟨hxy, hxK'⟩ (w y) ⟨hwyW, hwyK'⟩
  have h2 : dist (f (φ l) (w y)) (f (φ l) x) < ε / 4 :=
    hWprop y hyK' (φ l) (w y) ⟨hwyW, hwyK'⟩ x ⟨hxy, hxK'⟩
  have h3 : dist (f (φ k) (w y)) (f (φ l) (w y)) < ε / 2 := hCaub k hk' l hl'
  calc dist (f (φ k) x) (f (φ l) x)
      ≤ dist (f (φ k) x) (f (φ k) (w y)) + dist (f (φ k) (w y)) (f (φ l) x) :=
        dist_triangle _ _ _
    _ ≤ dist (f (φ k) x) (f (φ k) (w y))
        + (dist (f (φ k) (w y)) (f (φ l) (w y)) + dist (f (φ l) (w y)) (f (φ l) x)) := by
        gcongr; exact dist_triangle _ _ _
    _ < ε / 4 + (ε / 2 + ε / 4) := add_lt_add h1 (add_lt_add h3 h2)
    _ = ε := by ring

theorem exists_subseq_tendstoLocallyUniformlyOn_of_locallyBounded_equicontinuous
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℕ → X → E}
    (hbdd : ∀ K : Set X, IsCompact K → ∃ C : ℝ, ∀ n : ℕ, ∀ x ∈ K, ‖f n x‖ ≤ C)
    (heq : ∀ K : Set X, IsCompact K → Equicontinuous (fun n : ℕ => fun x : K => f n x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → E,
      TendstoLocallyUniformlyOn (fun n : ℕ => f (φ n)) g Filter.atTop Set.univ := by
  classical
  have hproper : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcomplete : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨D, hDcount, hDense⟩ := TopologicalSpace.exists_countable_dense X
  have hDcnt : Countable D := Set.countable_coe_iff.mpr hDcount
  choose C hC using fun d : D => hbdd ({↑d} : Set X) isCompact_singleton
  let Φ : ℕ → (d : D) → Metric.closedBall (0 : E) (C d) := fun n d =>
    ⟨f n (d : X), by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hC d n (d : X) (Set.mem_singleton (d : X))⟩
  obtain ⟨z, φ, hφmono, hΦtend⟩ := CompactSpace.tendsto_subseq Φ
  have hz : ∀ d : D, Tendsto (fun k => f (φ k) (d : X)) atTop
      (𝓝 ((z d : Metric.closedBall (0 : E) (C d)) : E)) := by
    intro d
    have h1 : Tendsto (fun k => (Φ ∘ φ) k d) atTop (𝓝 (z d)) := (tendsto_pi_nhds.mp hΦtend) d
    have h2 := tendsto_subtype_rng.mp h1
    simpa [Φ, Function.comp_def] using h2
  have hconv : ∀ d ∈ D, CauchySeq (fun k => f (φ k) d) := fun d hd => (hz ⟨d, hd⟩).cauchySeq
  have hUnifCau := uniform_cauchy_of_dense_cauchy hDense hconv heq
  have hcauchy : ∀ x : X, CauchySeq (fun k => f (φ k) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hUnifCau {x} isCompact_singleton ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn x (Set.mem_singleton x)⟩
  let g : X → E := fun x => Classical.choose (cauchySeq_tendsto_of_complete (hcauchy x))
  have hg : ∀ x : X, Tendsto (fun k => f (φ k) x) atTop (𝓝 (g x)) := fun x =>
    Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy x))
  refine ⟨φ, hφmono, g, ?_⟩
  rw [tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hUnifCau K hK (ε / 2) (by linarith)
  rw [eventually_atTop]
  refine ⟨N, fun k hk x hx => ?_⟩
  have htend : Tendsto (fun l => dist (f (φ l) x) (f (φ k) x)) atTop
      (𝓝 (dist (g x) (f (φ k) x))) := (hg x).dist tendsto_const_nhds
  have hle : dist (g x) (f (φ k) x) ≤ ε / 2 := by
    refine le_of_tendsto htend ?_
    rw [eventually_atTop]
    exact ⟨N, fun l hl => le_of_lt (hN l hl k hk x hx)⟩
  linarith

end Commons.Topology.ArzelaAscoli