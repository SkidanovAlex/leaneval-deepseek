import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.PerzTools

open MeasureTheory Set Metric Filter
open scoped Real Topology
open Classical

noncomputable section

/-!
## Carathéodory measurability, one-dimensional in the second variable

If `g : ℝ → ℝ → ℝ` is, for every `s`, continuous on the open interval `(0, π/2)` and zero off
it, and if for every `θ` the slice `s ↦ g s θ` is a.e. strongly measurable, then the uncurried
map `(s, θ) ↦ g s θ` is a.e. strongly measurable for the product measure.

This is the plane version of `Work.FTS.EpsEngine.aesm_uncurry_of_continuousOn_of_zero` (which
treats `g : ℝ → ℝ → ℝ → ℝ` continuous on the open quadrant), with the same proof: cover
`(0, π/2)` by countably many balls of radius `1/(n+1)` cut down to the interval, disjointify
them, approximate `g` in `θ` by the resulting locally constant family, and pass to the limit.
-/

/-- The open interval on which the `s`-slices are continuous. -/
private def Q1 : Set ℝ := Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_Q1 : IsOpen Q1 := isOpen_Ioo

/-- The mesh `1/(n+1)` of the `n`-th approximation. -/
private def eps1 (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private lemma eps1_pos (n : ℕ) : 0 < eps1 n := by rw [eps1]; positivity

/-- The `k`-th cell of the `n`-th approximation: the ball of radius `1/(n+1)` about `c k`,
intersected with the interval `Q1`, minus the union of the previous such balls.  These cells are
a measurable partition of `Q1` into pieces of radius `< 1/(n+1)`. -/
private def cells1 (c : ℕ → ℝ) (n k : ℕ) : Set ℝ :=
  (Metric.ball (c k) (eps1 n) ∩ Q1) \ (⋃ j ∈ Finset.range k, Metric.ball (c j) (eps1 n))

private lemma cells1_subset_Q1 (c : ℕ → ℝ) (n k : ℕ) : cells1 c n k ⊆ Q1 :=
  Set.sdiff_subset.trans Set.inter_subset_right

private lemma cells1_subset_ball {c : ℕ → ℝ} {n k : ℕ} {θ : ℝ}
    (hθ : θ ∈ cells1 c n k) : dist θ (c k) < eps1 n := hθ.1.1

private lemma measurableSet_cells1 (c : ℕ → ℝ) (n k : ℕ) : MeasurableSet (cells1 c n k) := by
  refine (Metric.isOpen_ball.measurableSet.inter isOpen_Q1.measurableSet).diff ?_
  exact MeasurableSet.biUnion (Finset.countable_toSet (Finset.range k))
    (fun j _ => Metric.isOpen_ball.measurableSet)

/-- Every point of the interval lies in some cell of the `n`-th approximation. -/
private lemma exists_mem_cells1 {c : ℕ → ℝ}
    (hc : ∀ θ : ℝ, ∀ ε > 0, ∃ k, dist θ (c k) < ε) (n : ℕ) {θ : ℝ} (hθ : θ ∈ Q1) :
    ∃ k, θ ∈ cells1 c n k := by
  obtain ⟨k, hk⟩ := hc θ (eps1 n) (eps1_pos n)
  have hex : ∃ j, dist θ (c j) < eps1 n := ⟨k, hk⟩
  refine ⟨Nat.find hex, ⟨⟨Nat.find_spec hex, hθ⟩, ?_⟩⟩
  intro hmem
  simp only [Set.mem_iUnion, Finset.mem_range] at hmem
  obtain ⟨j, hjlt, hjball⟩ := hmem
  exact Nat.find_min hex hjlt hjball

/-- Distinct cells of the same approximation are disjoint. -/
private lemma cells1_disjoint {c : ℕ → ℝ} {n k l : ℕ} (hkl : k ≠ l) :
    Disjoint (cells1 c n k) (cells1 c n l) := by
  rw [Set.disjoint_left]
  intro θ hθk hθl
  rcases lt_or_gt_of_ne hkl with h | h
  · have hmem : θ ∈ ⋃ j ∈ Finset.range l, Metric.ball (c j) (eps1 n) :=
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr h, hθk.1.1⟩⟩
    exact hθl.2 hmem
  · have hmem : θ ∈ ⋃ j ∈ Finset.range k, Metric.ball (c j) (eps1 n) :=
      Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr h, hθl.1.1⟩⟩
    exact hθk.2 hmem

/-- The `m`-th partial sum of the `n`-th locally constant approximation of `g`. -/
private def partialSum1 (g : ℝ → ℝ → ℝ) (c : ℕ → ℝ) (n m : ℕ) : ℝ × ℝ → ℝ :=
  fun p => ∑ k ∈ Finset.range m,
    (cells1 c n k).indicator (fun _ : ℝ => (1 : ℝ)) p.2 * g p.1 (c k)

/-- The `n`-th locally constant approximation of `g`. -/
private def approx1 (g : ℝ → ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun p => if h : ∃ k, p.2 ∈ cells1 c n k then g p.1 (c (Nat.find h)) else 0

private lemma approx1_eq_of_pos (g : ℝ → ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ)
    (p : ℝ × ℝ) (h : ∃ k, p.2 ∈ cells1 c n k) :
    approx1 g c n p = g p.1 (c (Nat.find h)) := by
  rw [approx1]; exact dif_pos h

private lemma approx1_eq_of_neg (g : ℝ → ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ)
    (p : ℝ × ℝ) (h : ¬ ∃ k, p.2 ∈ cells1 c n k) : approx1 g c n p = 0 := by
  rw [approx1]; exact dif_neg h

/-- Finite sums of a.e. strongly measurable functions are a.e. strongly measurable. -/
private lemma ae_finset_sum1 {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
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
private lemma ae_comp_fst1 {h : ℝ → ℝ} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1) (volume.prod volume) := by
  have h := hh.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  exact h

/-- Each summand of the approximation is a.e. strongly measurable. -/
private lemma ae_term1 {g : ℝ → ℝ → ℝ}
    (hmeas : ∀ θ : ℝ, AEStronglyMeasurable (fun s : ℝ => g s θ) volume)
    (c : ℕ → ℝ) (n k : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (cells1 c n k).indicator (fun _ : ℝ => (1 : ℝ)) p.2 * g p.1 (c k))
      (volume.prod volume) := by
  refine (Measurable.aestronglyMeasurable ?_).mul ?_
  · exact (Measurable.indicator measurable_const (measurableSet_cells1 c n k)).comp measurable_snd
  · exact ae_comp_fst1 (hmeas (c k))

private lemma ae_partialSum1 {g : ℝ → ℝ → ℝ}
    (hmeas : ∀ θ : ℝ, AEStronglyMeasurable (fun s : ℝ => g s θ) volume)
    (c : ℕ → ℝ) (n m : ℕ) :
    AEStronglyMeasurable (partialSum1 g c n m) (volume.prod volume) :=
  (ae_finset_sum1 (Finset.range m) (fun k _ => ae_term1 hmeas c n k)).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The partial sums converge (pointwise, in fact eventually constantly) to the approximant. -/
private lemma partialSum1_tendsto {g : ℝ → ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ}
    (hd : ∀ k l : ℕ, k ≠ l → Disjoint (cells1 c n k) (cells1 c n l)) (p : ℝ × ℝ) :
    Tendsto (fun m => partialSum1 g c n m p) atTop (𝓝 (approx1 g c n p)) := by
  by_cases h : ∃ k, p.2 ∈ cells1 c n k
  · have hfind : p.2 ∈ cells1 c n (Nat.find h) := Nat.find_spec h
    rw [approx1_eq_of_pos g c n p h]
    refine tendsto_atTop_of_eventually_const (i₀ := Nat.find h + 1) fun m hm => ?_
    rw [partialSum1, Finset.sum_eq_single (Nat.find h)]
    · rw [Set.indicator_of_mem hfind]; simp
    · intro k _ hne
      have hnk : p.2 ∉ cells1 c n k :=
        fun hmem => (Set.disjoint_left.mp (hd k (Nat.find h) hne)) hmem hfind
      rw [Set.indicator_of_notMem hnk]; simp
    · intro hnot
      exact absurd (Finset.mem_range.mpr hm) hnot
  · rw [approx1_eq_of_neg g c n p h]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun m => ?_)
    show (0 : ℝ) = partialSum1 g c n m p
    rw [partialSum1]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    have hnk : p.2 ∉ cells1 c n k := fun hmem => h ⟨k, hmem⟩
    rw [Set.indicator_of_notMem hnk]; simp

private lemma ae_approx1 {g : ℝ → ℝ → ℝ}
    (hmeas : ∀ θ : ℝ, AEStronglyMeasurable (fun s : ℝ => g s θ) volume)
    (c : ℕ → ℝ) (n : ℕ) :
    AEStronglyMeasurable (approx1 g c n) (volume.prod volume) :=
  aestronglyMeasurable_of_tendsto_ae atTop (fun m => ae_partialSum1 hmeas c n m)
    (Filter.Eventually.of_forall fun p => partialSum1_tendsto (fun k l hkl => cells1_disjoint hkl) p)

/-- The approximants converge pointwise to `g`, using continuity on the open interval (and the
fact that the approximants are `0` off it). -/
private lemma approx1_tendsto {g : ℝ → ℝ → ℝ} {c : ℕ → ℝ}
    (hcont : ∀ s : ℝ, ContinuousOn (fun θ : ℝ => g s θ) Q1)
    (hzero : ∀ s : ℝ, ∀ θ : ℝ, θ ∉ Q1 → g s θ = 0)
    (hc : ∀ θ : ℝ, ∀ ε > 0, ∃ k, dist θ (c k) < ε) (p : ℝ × ℝ) :
    Tendsto (fun n => approx1 g c n p) atTop (𝓝 (g p.1 p.2)) := by
  by_cases hp : p.2 ∈ Q1
  · have hex : ∀ n, ∃ k, p.2 ∈ cells1 c n k := fun n => exists_mem_cells1 hc n hp
    have hdist : ∀ n, dist (c (Nat.find (hex n))) p.2 < eps1 n := by
      intro n
      have h := cells1_subset_ball (c := c) (n := n) (k := Nat.find (hex n))
        (Nat.find_spec (hex n))
      rwa [dist_comm] at h
    have htend : Tendsto (fun n => c (Nat.find (hex n))) atTop (𝓝 p.2) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hdist n)) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hct : ContinuousAt (fun θ : ℝ => g p.1 θ) p.2 :=
      (hcont p.1).continuousAt (isOpen_Q1.mem_nhds hp)
    have hcomp := hct.tendsto.comp htend
    refine hcomp.congr' (Filter.Eventually.of_forall fun n => ?_)
    show g p.1 (c (Nat.find (hex n))) = approx1 g c n p
    exact (approx1_eq_of_pos g c n p (hex n)).symm
  · have hno : ∀ n, ¬ ∃ k, p.2 ∈ cells1 c n k := fun n ⟨k, hk⟩ => hp (cells1_subset_Q1 c n k hk)
    have hz : g p.1 p.2 = 0 := hzero p.1 p.2 hp
    rw [hz]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    show (0 : ℝ) = approx1 g c n p
    exact (approx1_eq_of_neg g c n p (hno n)).symm

/-- **Carathéodory measurability in the second variable, one-dimensional.**  If `g : ℝ → ℝ → ℝ`
is, for every `s`, continuous on the open interval `(0, π/2)` and zero off it, and if for every
`θ` the map `s ↦ g s θ` is a.e. strongly measurable, then `(s,θ) ↦ g s θ` is a.e. strongly
measurable for the product measure. -/
theorem aesm_uncurry_of_continuousOn_of_zero_1d {g : ℝ → ℝ → ℝ}
    (hcont : ∀ s : ℝ, ContinuousOn (fun θ : ℝ => g s θ) (Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ s : ℝ, ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → g s θ = 0)
    (hmeas : ∀ θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s θ)
      MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  obtain ⟨t, ht_count, ht_dense⟩ := TopologicalSpace.exists_countable_dense ℝ
  obtain ⟨c, hc_range⟩ := ht_count.exists_eq_range ht_dense.nonempty
  have hdense : Dense (Set.range c) := hc_range ▸ ht_dense
  have hc : ∀ θ : ℝ, ∀ ε > 0, ∃ k, dist θ (c k) < ε := by
    intro θ ε hε
    have hx : θ ∈ closure (Set.range c) := by
      rw [hdense.closure_eq]; exact Set.mem_univ θ
    obtain ⟨b, hb, hbd⟩ := Metric.mem_closure_iff.mp hx ε hε
    obtain ⟨k, rfl⟩ := hb
    exact ⟨k, hbd⟩
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => ae_approx1 hmeas c n)
    (Filter.Eventually.of_forall fun p => approx1_tendsto hcont hzero hc p)

end

end Work.FTS.EpsEngine.PerzTools
