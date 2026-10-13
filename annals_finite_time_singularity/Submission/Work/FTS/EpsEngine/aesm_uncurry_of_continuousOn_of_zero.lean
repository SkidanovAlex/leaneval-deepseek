import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Metric Filter
open scoped Real Topology
open Classical

noncomputable section

/-- The open quadrant `(0,∞) × (0,π/2)` on which the `s`-slices are continuous. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-- The mesh `1/(n+1)` of the `n`-th approximation. -/
private def eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private lemma eps_pos (n : ℕ) : 0 < eps n := by rw [eps]; positivity

/-- The `k`-th cell of the `n`-th approximation: the ball of radius `1/(n+1)` about `c k`,
intersected with the quadrant `Qd`, minus the union of the previous such balls.  These cells
are a measurable partition of `Qd` into pieces of radius `< 1/(n+1)`. -/
private def cells (c : ℕ → ℝ × ℝ) (n k : ℕ) : Set (ℝ × ℝ) :=
  (Metric.ball (c k) (eps n) ∩ Qd) \ (⋃ j ∈ Finset.range k, Metric.ball (c j) (eps n))

private lemma cells_subset_Qd (c : ℕ → ℝ × ℝ) (n k : ℕ) : cells c n k ⊆ Qd :=
  Set.sdiff_subset.trans Set.inter_subset_right

private lemma cells_subset_ball {c : ℕ → ℝ × ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hq : q ∈ cells c n k) : dist q (c k) < eps n := hq.1.1

private lemma measurableSet_cells (c : ℕ → ℝ × ℝ) (n k : ℕ) : MeasurableSet (cells c n k) := by
  refine (Metric.isOpen_ball.measurableSet.inter isOpen_Qd.measurableSet).diff ?_
  exact MeasurableSet.biUnion (Finset.countable_toSet (Finset.range k))
    (fun j _ => Metric.isOpen_ball.measurableSet)

/-- Every point of the quadrant lies in some cell of the `n`-th approximation. -/
private lemma exists_mem_cells {c : ℕ → ℝ × ℝ}
    (hc : ∀ q : ℝ × ℝ, ∀ ε > 0, ∃ k, dist q (c k) < ε) (n : ℕ) {q : ℝ × ℝ} (hq : q ∈ Qd) :
    ∃ k, q ∈ cells c n k := by
  obtain ⟨k, hk⟩ := hc q (eps n) (eps_pos n)
  have hex : ∃ j, dist q (c j) < eps n := ⟨k, hk⟩
  refine ⟨Nat.find hex, ⟨⟨Nat.find_spec hex, hq⟩, ?_⟩⟩
  intro hmem
  simp only [Set.mem_iUnion, Finset.mem_range] at hmem
  obtain ⟨j, hjlt, hjball⟩ := hmem
  exact Nat.find_min hex hjlt hjball

/-- Distinct cells of the same approximation are disjoint. -/
private lemma cells_disjoint {c : ℕ → ℝ × ℝ} {n k l : ℕ} (hkl : k ≠ l) :
    Disjoint (cells c n k) (cells c n l) := by
  rw [Set.disjoint_left]
  intro q hqk hql
  rcases lt_or_gt_of_ne hkl with h | h
  · have hmem : q ∈ ⋃ j ∈ Finset.range l, Metric.ball (c j) (eps n) :=
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr h, hqk.1.1⟩⟩
    exact hql.2 hmem
  · have hmem : q ∈ ⋃ j ∈ Finset.range k, Metric.ball (c j) (eps n) :=
      Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr h, hql.1.1⟩⟩
    exact hqk.2 hmem

/-- The `m`-th partial sum of the `n`-th locally constant approximation of `g`. -/
private def partialSum (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n m : ℕ) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => ∑ k ∈ Finset.range m,
    (cells c n k).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p.2 * g p.1 (c k).1 (c k).2

private lemma partialSum_apply (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n m : ℕ)
    (p : ℝ × (ℝ × ℝ)) :
    partialSum g c n m p = ∑ k ∈ Finset.range m,
      (cells c n k).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p.2 * g p.1 (c k).1 (c k).2 := rfl

/-- The `n`-th locally constant approximation of `g`. -/
private def approx (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => if h : ∃ k, p.2 ∈ cells c n k then g p.1 (c (Nat.find h)).1 (c (Nat.find h)).2 else 0

private lemma approx_apply (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ)
    (p : ℝ × (ℝ × ℝ)) :
    approx g c n p = (if h : ∃ k, p.2 ∈ cells c n k then
      g p.1 (c (Nat.find h)).1 (c (Nat.find h)).2 else 0) := rfl

private lemma approx_eq_of_pos (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ)
    (p : ℝ × (ℝ × ℝ)) (h : ∃ k, p.2 ∈ cells c n k) :
    approx g c n p = g p.1 (c (Nat.find h)).1 (c (Nat.find h)).2 := by
  rw [approx_apply]; exact dif_pos h

private lemma approx_eq_of_neg (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ)
    (p : ℝ × (ℝ × ℝ)) (h : ¬ ∃ k, p.2 ∈ cells c n k) : approx g c n p = 0 := by
  rw [approx_apply]; exact dif_neg h

/-- Finite sums of a.e. strongly measurable functions are a.e. strongly measurable. -/
private lemma ae_finset_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∑ i ∈ s, f i a) μ := by
  induction s using Finset.induction with
  | empty => simpa using (aestronglyMeasurable_const (b := (0 : ℝ)) (μ := μ))
  | insert i s hi ih =>
      have h1 : AEStronglyMeasurable (f i) μ := hf i (Finset.mem_insert_self i s)
      have h2 : AEStronglyMeasurable (fun a => ∑ x ∈ s, f x a) μ :=
        ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun a => ?_)
      simp only [Pi.add_apply, Finset.sum_insert hi]

/-- A.e. strong measurability is preserved by viewing a function of the first coordinate as a
function on a product. -/
private lemma ae_comp_fst {h : ℝ → ℝ} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => h p.1) volume := by
  have h := hh.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (ℝ × ℝ))))
  exact h

/-- Each summand of the approximation is a.e. strongly measurable. -/
private lemma ae_term {g : ℝ → ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2) volume)
    (c : ℕ → ℝ × ℝ) (n k : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        (cells c n k).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p.2 * g p.1 (c k).1 (c k).2)
      volume := by
  refine (Measurable.aestronglyMeasurable ?_).mul ?_
  · exact (Measurable.indicator measurable_const (measurableSet_cells c n k)).comp measurable_snd
  · exact ae_comp_fst (hmeas (c k))

private lemma ae_partialSum {g : ℝ → ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2) volume)
    (c : ℕ → ℝ × ℝ) (n m : ℕ) :
    AEStronglyMeasurable (partialSum g c n m) volume :=
  (ae_finset_sum (Finset.range m) (fun k _ => ae_term hmeas c n k)).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The partial sums converge (pointwise, in fact eventually constantly) to the approximant. -/
private lemma partialSum_tendsto {g : ℝ → ℝ → ℝ → ℝ} {c : ℕ → ℝ × ℝ} {n : ℕ}
    (hd : ∀ k l : ℕ, k ≠ l → Disjoint (cells c n k) (cells c n l)) (p : ℝ × (ℝ × ℝ)) :
    Tendsto (fun m => partialSum g c n m p) atTop (𝓝 (approx g c n p)) := by
  by_cases h : ∃ k, p.2 ∈ cells c n k
  · have hfind : p.2 ∈ cells c n (Nat.find h) := Nat.find_spec h
    rw [approx_eq_of_pos g c n p h]
    refine tendsto_atTop_of_eventually_const (i₀ := Nat.find h + 1) fun m hm => ?_
    rw [partialSum_apply, Finset.sum_eq_single (Nat.find h)]
    · rw [Set.indicator_of_mem hfind]; simp
    · intro k _ hne
      have hnk : p.2 ∉ cells c n k :=
        fun hmem => (Set.disjoint_left.mp (hd k (Nat.find h) hne)) hmem hfind
      rw [Set.indicator_of_notMem hnk]; simp
    · intro hnot
      exact absurd (Finset.mem_range.mpr hm) hnot
  · rw [approx_eq_of_neg g c n p h]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun m => ?_)
    show (0 : ℝ) = partialSum g c n m p
    rw [partialSum_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    have hnk : p.2 ∉ cells c n k := fun hmem => h ⟨k, hmem⟩
    rw [Set.indicator_of_notMem hnk]; simp

private lemma ae_approx {g : ℝ → ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2) volume)
    (c : ℕ → ℝ × ℝ) (n : ℕ) :
    AEStronglyMeasurable (approx g c n) volume :=
  aestronglyMeasurable_of_tendsto_ae atTop (fun m => ae_partialSum hmeas c n m)
    (Filter.Eventually.of_forall fun p => partialSum_tendsto (fun k l hkl => cells_disjoint hkl) p)

/-- The approximants converge pointwise to `g`, using continuity on the open quadrant (and the
fact that the approximants are `0` off it). -/
private lemma approx_tendsto {g : ℝ → ℝ → ℝ → ℝ} {c : ℕ → ℝ × ℝ}
    (hcont : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => g s q.1 q.2) Qd)
    (hzero : ∀ s : ℝ, ∀ q : ℝ × ℝ, q ∉ Qd → g s q.1 q.2 = 0)
    (hc : ∀ q : ℝ × ℝ, ∀ ε > 0, ∃ k, dist q (c k) < ε) (p : ℝ × (ℝ × ℝ)) :
    Tendsto (fun n => approx g c n p) atTop (𝓝 (g p.1 p.2.1 p.2.2)) := by
  by_cases hp : p.2 ∈ Qd
  · have hex : ∀ n, ∃ k, p.2 ∈ cells c n k := fun n => exists_mem_cells hc n hp
    have hdist : ∀ n, dist (c (Nat.find (hex n))) p.2 < eps n := by
      intro n
      have h := cells_subset_ball (c := c) (n := n) (k := Nat.find (hex n))
        (Nat.find_spec (hex n))
      rwa [dist_comm] at h
    have htend : Tendsto (fun n => c (Nat.find (hex n))) atTop (𝓝 p.2) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hdist n)) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hct : ContinuousAt (fun q : ℝ × ℝ => g p.1 q.1 q.2) p.2 :=
      (hcont p.1).continuousAt (isOpen_Qd.mem_nhds hp)
    have hcomp := hct.tendsto.comp htend
    refine hcomp.congr' (Filter.Eventually.of_forall fun n => ?_)
    show g p.1 (c (Nat.find (hex n))).1 (c (Nat.find (hex n))).2 = approx g c n p
    exact (approx_eq_of_pos g c n p (hex n)).symm
  · have hno : ∀ n, ¬ ∃ k, p.2 ∈ cells c n k := fun n ⟨k, hk⟩ => hp (cells_subset_Qd c n k hk)
    have hz : g p.1 p.2.1 p.2.2 = 0 := hzero p.1 p.2 hp
    rw [hz]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    show (0 : ℝ) = approx g c n p
    exact (approx_eq_of_neg g c n p (hno n)).symm

/-- **Carathéodory measurability, in the shape needed by the local step of the `ε`-scheme.**  If
`g : ℝ → ℝ → ℝ → ℝ` is, for every `s`, continuous on the open quadrant `Q0` and zero off it, and if
for every `(z,θ)` the map `s ↦ g s z θ` is a.e. strongly measurable, then `(s,z,θ) ↦ g s z θ` is
a.e. strongly measurable for the product measure.  (Proof: cover `Q0` by countably many balls of
radius `1/k` **intersected with `Q0`**, disjointify, and approximate `g` in the second variable by
the locally constant family; each approximant is measurable and converges pointwise to `g`.) -/
theorem aesm_uncurry_of_continuousOn_of_zero {g : ℝ → ℝ → ℝ → ℝ}
    (hcont : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => g s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ s : ℝ, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → g s q.1 q.2 = 0)
    (hmeas : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2)
      MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      MeasureTheory.volume := by
  obtain ⟨t, ht_count, ht_dense⟩ := TopologicalSpace.exists_countable_dense (ℝ × ℝ)
  obtain ⟨c, hc_range⟩ := ht_count.exists_eq_range ht_dense.nonempty
  have hdense : Dense (Set.range c) := hc_range ▸ ht_dense
  have hc : ∀ q : ℝ × ℝ, ∀ ε > 0, ∃ k, dist q (c k) < ε := by
    intro q ε hε
    have hx : q ∈ closure (Set.range c) := by
      rw [hdense.closure_eq]; exact Set.mem_univ q
    obtain ⟨b, hb, hbd⟩ := Metric.mem_closure_iff.mp hx ε hε
    obtain ⟨k, rfl⟩ := hb
    exact ⟨k, hbd⟩
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => ae_approx hmeas c n)
    (Filter.Eventually.of_forall fun p => approx_tendsto hcont hzero hc p)

end

end Work.FTS.EpsEngine
