import Mathlib
import Submission.Work.EKLC6Core.adapted_partition

/-!
# `Work.EKLC6Core.exists_covering_thin_inj_partition`

The partition of `X₃ = SL₃(ℝ)/SL₃(ℤ)` into finitely many disjoint measurable cells, one of which
is *exceptional* (of `μ`-measure `< ε`), the others lying in `V ρ`-balls around *Γ₃-injective*
centres, with a thin boundary in the quantitative sense of Pisa 7.26/7.27.

This is the form in which the "cut" construction consumes the covering: the exceptional cell
`Q i₀` carries the mass that is lost, the remaining cells are exactly the `V ρ`-balls of
`adapted_partition`, and since they are *open* the complement `(⋃ i ≠ i₀, Q i)ᶜ` has frontier
inside `⋃ ∂Q i`, so the thin-boundary estimate is inherited without change of constant.

The mathematical content (finding `ρ`, the cells, and the injective centres) is
`Work.EKLC6Core.adapted_partition`; here we only convert "covers all but `< ε`" into "partitions
all of `X₃` with one small cell".
-/

namespace Work.EKLC6Core

open MeasureTheory Set
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- The `V η`-thickening of a union is the union of the thickenings. -/
theorem VThick_iUnion {ι : Type*} (η : ℝ) (f : ι → Set X3) :
    VThick η (⋃ i, f i) = ⋃ i, VThick η (f i) := by
  ext z
  rw [VThick_def]
  simp only [Set.mem_image, Set.mem_prod, Set.mem_iUnion]
  constructor
  · rintro ⟨p, ⟨hp, i, hi⟩, rfl⟩
    exact ⟨i, p, ⟨hp, hi⟩, rfl⟩
  · rintro ⟨i, p, ⟨hp, hi⟩, rfl⟩
    exact ⟨p, ⟨hp, i, hi⟩, rfl⟩

theorem exists_covering_thin_inj_partition (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∃ (N : ℕ) (Q : Fin N → Set Work.EKLContract.X3) (i₀ : Fin N)
      (g : Fin N → Work.EKLContract.SL3) (c : ℝ),
      0 < c ∧
      (∀ i, MeasurableSet (Q i)) ∧
      (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
      (⋃ i, Q i) = Set.univ ∧
      (∀ i, i ≠ i₀ → Q i ⊆
        (fun v : Work.EKLContract.SL3 => v • Work.EKLContract.mkX (g i)) ''
          (Work.EKLContract.V ρ)) ∧
      (∀ i, i ≠ i₀ → ∀ γ : Work.EKLContract.SL3, γ ∈ Work.EKLContract.Γ3 →
        g i * γ * (g i)⁻¹ ∈ Work.EKLContract.V (60 * ρ) → γ = 1) ∧
      μ (Q i₀) < ENNReal.ofReal ε ∧
      (∀ η : ℝ, 0 < η →
        μ (⋃ i, Work.EKLC6Core.VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η)) := by
  classical
  -- The cells of `adapted_partition`: disjoint open sets of injective centres, covering all but
  -- `< ε` of `μ`.
  obtain ⟨N, Q, g, ρ, c, hρ, hc, hQopen, hQdisj, hQmem, hQsub, hQinj, hQcomp, hQthin⟩ :=
    adapted_partition μ ε hε
  -- Append the complement of the union as the exceptional cell, at the last index.
  let Q' : Fin (N + 1) → Set X3 := fun i => Fin.lastCases ((⋃ j, Q j)ᶜ) (fun j => Q j) i
  let g' : Fin (N + 1) → SL3 := fun i => Fin.lastCases (1 : SL3) (fun j => g j) i
  have hQ'cast : ∀ j : Fin N, Q' (Fin.castSucc j) = Q j := fun j => by
    simp only [Q', Fin.lastCases_castSucc]
  have hQ'last : Q' (Fin.last N) = (⋃ j, Q j)ᶜ := by simp only [Q', Fin.lastCases_last]
  have hg'cast : ∀ j : Fin N, g' (Fin.castSucc j) = g j := fun j => by
    simp only [g', Fin.lastCases_castSucc]
  refine ⟨ρ, hρ, N + 1, Q', Fin.last N, g', c, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- measurability
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hQ'cast j]; exact (hQopen j).measurableSet
    · rw [hQ'last]
      exact ((isOpen_iUnion fun j => hQopen j).isClosed_compl).measurableSet
  · -- pairwise disjointness
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
    · rw [hQ'cast a, hQ'cast b]
      exact hQdisj a b fun h => hij (by rw [h])
    · rw [hQ'cast a, hQ'last, Set.disjoint_left]
      intro x hx hx'
      exact hx' (mem_iUnion.mpr ⟨a, hx⟩)
    · rw [hQ'last, hQ'cast b, Set.disjoint_left]
      intro x hx hx'
      exact hx (mem_iUnion.mpr ⟨b, hx'⟩)
    · exact absurd rfl hij
  · -- the cells cover `X₃`
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ ⋃ j, Q j
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨Fin.castSucc j, by rw [hQ'cast j]; exact hj⟩
    · exact mem_iUnion.mpr ⟨Fin.last N, by rw [hQ'last]; exact hx⟩
  · -- the non-exceptional cells are `V ρ`-balls around their centres
    intro i hi
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hQ'cast j, hg'cast j]
      exact hQsub j
    · exact absurd rfl hi
  · -- the centres are `Γ₃`-injective at scale `60 ρ`
    intro i hi γ hγ hm
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hg'cast j] at hm
      exact hQinj j γ hγ hm
    · exact absurd rfl hi
  · -- the exceptional cell has measure `< ε`
    rw [hQ'last]; exact hQcomp
  · -- the boundary estimate is inherited
    intro η hη
    -- the frontier of the complement of a finite union of *open* sets lies in the union of the
    -- frontiers
    have hCfr : frontier ((⋃ j : Fin N, Q j)ᶜ) ⊆ ⋃ j : Fin N, frontier (Q j) := by
      rw [frontier_compl]
      exact Work.Misiurewicz.frontier_iUnion_subset (fun j : Fin N => Q j)
    have hsub : (⋃ i : Fin (N + 1), VThick η (frontier (Q' i)))
        ⊆ ⋃ j : Fin N, VThick η (frontier (Q j)) := by
      intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [hQ'cast j] at hi
        exact mem_iUnion.mpr ⟨j, hi⟩
      · rw [hQ'last] at hi
        have hz2 : z ∈ VThick η (⋃ j : Fin N, frontier (Q j)) :=
          VThick_mono_right hCfr η hi
        rw [VThick_iUnion] at hz2
        exact hz2
    exact le_trans (measure_mono hsub) (hQthin η hη)

end

end Work.EKLC6Core
