import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.cut_defs
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.thin_boundary_partition

/-!
# `Work.EKLC6Core.cut_cells` — open cells with thin boundary (Pisa 7.38, step 1)

The "cut" construction of Pisa 7.37/7.38 needs a finite family of pairwise disjoint **open**
subsets of `X₃` of small `V`-diameter covering almost all of the mass, whose boundaries are
"thin" in the quantitative sense `μ ((V η) • frontier (Q i)) ≤ c η`.

This module derives that statement from the thin-boundary partition `thin_boundary_partition`
(colleague's, same directory), which produces a finite *measurable* partition of all of `X₃`
with

* one exceptional piece `P i₀` of measure `< ε` (all other pieces lie in a `V ρ`-ball), and
* thin boundaries, `μ (⋃ i, (V η) • frontier (P i)) ≤ c η`.

The passage from measurable pieces to open ones is the standard one: put `Q i := interior (P i)`
(for `i ≠ i₀`, and `Q i₀ := ∅`).  Since the union of the frontiers is `μ`-null (a consequence of
thinness: `μ (frontier) ≤ μ ((V η) • frontier) ≤ c η` for every `η > 0`), the interiors still
cover all but the exceptional piece, and `frontier (interior (P i)) ⊆ frontier (P i)` keeps the
thinness.
-/

open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The union of the frontiers is null.**  If the `V η`-collar of the union of the frontiers of
a finite family has measure at most `c η` for every `η > 0`, then the union of the frontiers
itself is `μ`-null (take `η → 0`). -/
theorem measure_iUnion_frontier_eq_zero {N : ℕ} {μ : Measure X3} [IsFiniteMeasure μ]
    (P : Fin N → Set X3) {c : ℝ} (hc : 0 < c)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ i, VThick η (frontier (P i))) ≤ ENNReal.ofReal (c * η)) :
    μ (⋃ i, frontier (P i)) = 0 := by
  -- the real-valued measure of the frontier union is at most `c η`, for every `η > 0`
  have hle : ∀ η : ℝ, 0 < η → (μ (⋃ i, frontier (P i))).toReal ≤ c * η := by
    intro η hη
    have h1 : μ (⋃ i, frontier (P i)) ≤ μ (⋃ i, VThick η (frontier (P i))) := by
      refine measure_mono fun x hx => ?_
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, subset_VThick hη _ hi⟩
    have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_trans h1 (hthin η hη))
    rwa [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ c * η)] at h3
  have hzero : (μ (⋃ i, frontier (P i))).toReal = 0 := by
    refine le_antisymm ?_ ENNReal.toReal_nonneg
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hcne : c ≠ 0 := ne_of_gt hc
    have h := hle (ε / (2 * c)) (by positivity)
    have heq : c * (ε / (2 * c)) = ε / 2 := by field_simp
    linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), hzero, ENNReal.ofReal_zero]

/-- **Open cells with thin boundary** (Pisa 7.38, step 1).  For every probability measure `μ` on
`X₃`, every `ε > 0` and every `ρ > 0` there are a finite family `Q i` of pairwise disjoint open
subsets of `X₃`, points `mkX (g i)`, and a constant `c > 0` such that

* `μ ((⋃ i, Q i)ᶜ) < ε` (the cells cover all but `ε` of the mass),
* `Q i ⊆ (V ρ) • mkX (g i)` (each cell sits in a `V ρ`-ball), and
* `μ (⋃ i, (V η) • frontier (Q i)) ≤ c η` for every `η > 0` (thin boundaries). -/
theorem cut_cells (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ (N : ℕ) (Q : Fin N → Set Work.EKLContract.X3) (g : Fin N → Work.EKLContract.SL3)
      (c : ℝ),
      0 < c ∧ (∀ i, IsOpen (Q i)) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
      μ ((⋃ i, Q i))ᶜ < ENNReal.ofReal ε ∧
      (∀ i, Q i ⊆ (fun u : Work.EKLContract.SL3 => u • Work.EKLContract.mkX (g i)) ''
          (Work.EKLContract.V ρ)) ∧
      (∀ η : ℝ, 0 < η →
        μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ (frontier (Q i)))) ≤ ENNReal.ofReal (c * η)) := by
  classical
  obtain ⟨N, P, i₀, c, hc, hPmeas, hPdisj, hPcov, hPsub, hPi₀, hPthin⟩ :=
    thin_boundary_partition μ ε ρ hε hρ
  -- the union of the frontiers of the partition is `μ`-null
  have hUF : μ (⋃ i, frontier (P i)) = 0 :=
    measure_iUnion_frontier_eq_zero P hc fun η hη => by simpa [VThick_def] using hPthin η hη
  -- centres for the non-exceptional cells
  have hcenter : ∀ i : Fin N, i ≠ i₀ → ∃ g : SL3, P i ⊆ (fun u : SL3 => u • mkX g) '' (V ρ) := by
    intro i hi
    obtain ⟨x, hx⟩ := hPsub i hi
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, hx⟩
  let g : Fin N → SL3 := fun i => if h : i = i₀ then 1 else Classical.choose (hcenter i h)
  have hg : ∀ i, i ≠ i₀ → P i ⊆ (fun u : SL3 => u • mkX (g i)) '' (V ρ) := by
    intro i hi
    have := Classical.choose_spec (hcenter i hi)
    simpa only [g, dif_neg hi] using this
  -- the cells: the interiors of the non-exceptional pieces
  let Q : Fin N → Set X3 := fun i => if h : i = i₀ then ∅ else interior (P i)
  have hQeq : ∀ i, i ≠ i₀ → Q i = interior (P i) := by
    intro i hi; simp only [Q, dif_neg hi]
  have hQi₀ : Q i₀ = ∅ := by simp only [Q, dif_pos rfl]
  refine ⟨N, Q, g, c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · -- openness
    intro i
    by_cases hi : i = i₀
    · rw [hi, hQi₀]; exact isOpen_empty
    · rw [hQeq i hi]; exact isOpen_interior
  · -- pairwise disjointness
    intro i j hij
    have hPi : Q i ⊆ P i := by
      by_cases hi : i = i₀
      · rw [hi, hQi₀]; exact Set.empty_subset _
      · rw [hQeq i hi]; exact interior_subset
    have hPj : Q j ⊆ P j := by
      by_cases hj : j = i₀
      · rw [hj, hQi₀]; exact Set.empty_subset _
      · rw [hQeq j hj]; exact interior_subset
    exact (hPdisj i j hij).mono hPi hPj
  · -- the cells cover all but `ε` of the mass
    have hsub : (⋃ i, Q i)ᶜ ⊆ P i₀ ∪ ⋃ i, frontier (P i) := by
      intro x hx
      have hxall : x ∈ ⋃ i, P i := by rw [hPcov]; exact Set.mem_univ x
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxall
      by_cases hji : j = i₀
      · exact Or.inl (hji ▸ hj)
      · refine Or.inr (Set.mem_iUnion.mpr ⟨j, ?_⟩)
        have hxQ : x ∉ Q j := fun h => hx (Set.mem_iUnion.mpr ⟨j, h⟩)
        rw [hQeq j hji] at hxQ
        rw [frontier_eq_closure_inter_closure]
        refine ⟨subset_closure hj, ?_⟩
        rw [closure_compl]
        exact hxQ
    calc μ ((⋃ i, Q i))ᶜ
        ≤ μ (P i₀ ∪ ⋃ i, frontier (P i)) := measure_mono hsub
      _ ≤ μ (P i₀) + μ (⋃ i, frontier (P i)) := measure_union_le _ _
      _ = μ (P i₀) := by rw [hUF, add_zero]
      _ < ENNReal.ofReal ε := hPi₀
  · -- each cell sits in a `V ρ`-ball
    intro i
    by_cases hi : i = i₀
    · rw [hi, hQi₀]; exact Set.empty_subset _
    · rw [hQeq i hi]
      exact subset_trans interior_subset (hg i hi)
  · -- thin boundaries
    intro η hη
    have hsub : (⋃ i, VThick η (frontier (Q i))) ⊆ (⋃ i, VThick η (frontier (P i))) := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      by_cases hi₀ : i = i₀
      · rw [hi₀, hQi₀] at hi
        simp only [frontier_empty, VThick_def, Set.prod_empty, Set.image_empty] at hi
        exact absurd hi (by simp)
      · refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [hQeq i hi₀] at hi
        exact VThick_mono_right frontier_interior_subset η hi
    calc μ (⋃ i, VThick η (frontier (Q i)))
        ≤ μ (⋃ i, VThick η (frontier (P i))) := measure_mono hsub
      _ ≤ ENNReal.ofReal (c * η) := by simpa [VThick_def] using hPthin η hη

end Work.EKLC6Core
