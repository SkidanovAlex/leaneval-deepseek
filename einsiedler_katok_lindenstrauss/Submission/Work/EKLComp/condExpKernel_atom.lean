import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.measure_iInter_eq_of_forall_eq_univ
import Submission.Work.EKLComp.measure_eq_one_of_measureReal_eq_one
import Submission.Work.EKLComp.condExpKernel_ae_mem_eq_one

/-!
# The conditional kernel is carried by the atoms of its σ-algebra

For a finite measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and a countably generated sub-σ-algebra
`𝔪.m ≤ borel X₃`, the conditional kernel `ProbabilityTheory.condExpKernel μ 𝔪.m` is carried by
the atoms of `𝔪.m`: for `μ`-almost every `x`,

`condExpKernel μ 𝔪.m x (atom 𝔪.m x) = 1`.

The proof has two halves.

* `condExpKernel_ae_mem_eq_one` : for a *fixed* `𝔪.m`-measurable set `B`, the value
  `condExpKernel μ 𝔪.m x B` is a version of the conditional probability `μ⟦B | 𝔪.m⟧`, which
  equals `1_B` almost everywhere because `B` is `𝔪.m`-measurable; hence almost every `x ∈ B`
  satisfies `condExpKernel μ 𝔪.m x B = 1`.
* `atom_eq_iInter_atomSlice` : if `A : ℕ → Set X₃` generates `𝔪.m`, then the atom of `x` is the
  intersection of the countably many *slices* `atomSlice A x n` (`= A n` if `x ∈ A n`, and
  `(A n)ᶜ` otherwise).  Each slice is one of `A n`, `(A n)ᶜ`, so the first half, applied to the
  countably many sets `A n` and their complements, shows that almost every `x` is such that every
  slice has full `condExpKernel μ 𝔪.m x`-measure; a countable intersection of measurable sets of
  full measure has full measure, which gives the statement.
-/

open MeasureTheory
open Work.EKLContract

namespace Work.EKLComp

/-! ## Atoms as intersections of slices -/

/-- The `n`-th slice of the atom of `x` determined by a generating sequence `A`: it is `A n`
if `x ∈ A n`, and its complement otherwise. -/
private noncomputable def atomSlice (A : ℕ → Set X3) (x : X3) (n : ℕ) : Set X3 := by
  classical
  exact if x ∈ A n then A n else (A n)ᶜ

/-- Membership in a slice is membership in `A n` for every point of the atom. -/
private theorem mem_atomSlice_iff {A : ℕ → Set X3} {x y : X3} {n : ℕ} :
    y ∈ atomSlice A x n ↔ (y ∈ A n ↔ x ∈ A n) := by
  unfold atomSlice
  by_cases h : x ∈ A n
  · rw [if_pos h]
    exact ⟨fun hy => ⟨fun _ => h, fun _ => hy⟩, fun h' => h'.mpr h⟩
  · rw [if_neg h]
    exact ⟨fun hy => ⟨fun hy' => absurd hy' hy, fun hx => absurd hx h⟩,
      fun h' hy => absurd (h'.mp hy) h⟩

private theorem measurableSet_atomSlice {m : MeasurableSpace X3} {A : ℕ → Set X3}
    (hA : ∀ n, MeasurableSet[m] (A n)) (x : X3) (n : ℕ) :
    MeasurableSet[m] (atomSlice A x n) := by
  unfold atomSlice
  by_cases h : x ∈ A n
  · rw [if_pos h]; exact hA n
  · rw [if_neg h]; exact (hA n).compl

/-- The atom of a σ-algebra is Mathlib's `measurableAtom`. -/
private theorem atom_eq_measurableAtom (m : MeasurableSpace X3) (x : X3) :
    Work.EKLContract.atom m x = @measurableAtom X3 m x := by
  have h1 : ∀ y ∈ Work.EKLContract.atom m x, y ∈ @measurableAtom X3 m x := by
    intro y hy
    simp only [measurableAtom, Set.mem_iInter]
    intro s hxs hms
    exact (Set.mem_sInter.mp hy) s ⟨hms, hxs⟩
  have h2 : ∀ y ∈ @measurableAtom X3 m x, y ∈ Work.EKLContract.atom m x := by
    intro y hy
    simp only [measurableAtom, Set.mem_iInter] at hy
    show y ∈ ⋂₀ {s : Set X3 | MeasurableSet[m] s ∧ x ∈ s}
    rw [Set.mem_sInter]
    rintro s ⟨hms, hxs⟩
    exact hy s hxs hms
  exact Set.Subset.antisymm h1 h2

/-- The coding of the atom of `x` by a countably generating sequence: `y` lies in the atom of
`x` exactly when `y` and `x` cannot be separated by the sets of the sequence. -/
private theorem mem_atom_iff (𝔪 : SigAlg)
    (hcg : @MeasurableSpace.CountablyGenerated X3 𝔪.m) (x y : X3) :
    y ∈ Work.EKLContract.atom 𝔪.m x ↔
      ∀ n, (y ∈ @MeasurableSpace.natGeneratingSequence X3 𝔪.m hcg n ↔
        x ∈ @MeasurableSpace.natGeneratingSequence X3 𝔪.m hcg n) := by
  rw [atom_eq_measurableAtom,
    @MeasurableSpace.measurableAtom_eq_countablyGeneratedAtom_natGeneratingSequence X3 𝔪.m hcg x]
  simp only [MeasurableSpace.countablyGeneratedAtom, Set.mem_iInter]
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · by_cases hx : x ∈ @MeasurableSpace.natGeneratingSequence X3 𝔪.m hcg n
    · have hn := h n
      rw [if_pos hx] at hn
      exact ⟨fun _ => hx, fun _ => hn⟩
    · have hn := h n
      rw [if_neg hx] at hn
      exact ⟨fun hy => absurd hy hn, fun hnx => absurd hnx hx⟩
  · by_cases hx : x ∈ @MeasurableSpace.natGeneratingSequence X3 𝔪.m hcg n
    · rw [if_pos hx]
      exact (h n).mpr hx
    · rw [if_neg hx]
      exact fun hy => hx ((h n).mp hy)

/-- The atom of `x` for a countably generated σ-algebra is the intersection of the slices of a
generating sequence. -/
private theorem atom_eq_iInter_atomSlice (𝔪 : SigAlg)
    (hcg : @MeasurableSpace.CountablyGenerated X3 𝔪.m) (x : X3) :
    Work.EKLContract.atom 𝔪.m x
      = ⋂ n, atomSlice (@MeasurableSpace.natGeneratingSequence X3 𝔪.m hcg) x n := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    rw [Set.mem_iInter]
    intro n
    rw [mem_atomSlice_iff]
    exact (mem_atom_iff 𝔪 hcg x y).mp hy n
  · intro y hy
    rw [mem_atom_iff 𝔪 hcg x y]
    intro n
    exact mem_atomSlice_iff.mp (Set.mem_iInter.mp hy n)

/-! ## The main statement -/

theorem condExpKernel_atom (𝔪 : Work.EKLComp.SigAlg)
    [StandardBorelSpace Work.EKLContract.X3] (hm : 𝔪.m ≤ Work.EKLComp.borelX3)
    (hgen : ∃ b : Set (Set Work.EKLContract.X3), b.Countable ∧
      𝔪.m = MeasurableSpace.generateFrom b)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ 𝔪.m x (Work.EKLContract.atom 𝔪.m x) = 1 := by
  classical
  have hcg : @MeasurableSpace.CountablyGenerated X3 𝔪.m :=
    MeasurableSpace.CountablyGenerated.mk (m := 𝔪.m) hgen
  set A : ℕ → Set X3 := @MeasurableSpace.natGeneratingSequence X3 𝔪.m hcg with hA
  have hAmeas : ∀ n, MeasurableSet[𝔪.m] (A n) := fun n =>
    @MeasurableSpace.measurableSet_natGeneratingSequence X3 𝔪.m hcg n
  -- Step 1: almost every `x` has all slices of full kernel measure, simultaneously in `n`.
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (ProbabilityTheory.condExpKernel μ 𝔪.m x) (atomSlice A x n) = 1 := by
    refine MeasureTheory.ae_all_iff.mpr fun n => ?_
    have h1 := condExpKernel_ae_mem_eq_one 𝔪 hm μ (hAmeas n)
    have h2 := condExpKernel_ae_mem_eq_one 𝔪 hm μ (hAmeas n).compl
    filter_upwards [h1, h2] with x hx1 hx2
    unfold atomSlice
    by_cases h : x ∈ A n
    · rw [if_pos h]; exact hx1 h
    · rw [if_neg h]; exact hx2 h
  -- Step 2: the atom is a countable intersection of slices, so it has full kernel measure.
  have hmarkov : ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.condExpKernel μ 𝔪.m) :=
    inferInstance
  filter_upwards [hall] with x hx
  have hatom : Work.EKLContract.atom 𝔪.m x = ⋂ n, atomSlice A x n := by
    rw [hA]
    exact atom_eq_iInter_atomSlice 𝔪 hcg x
  have huniv : (ProbabilityTheory.condExpKernel μ 𝔪.m x) Set.univ = 1 :=
    (hmarkov.isProbabilityMeasure x).measure_univ
  have hfin : (ProbabilityTheory.condExpKernel μ 𝔪.m x) Set.univ ≠ ⊤ := by
    rw [huniv]; exact ENNReal.one_ne_top
  have hmeas : ∀ n, MeasurableSet (atomSlice A x n) := fun n =>
    measurableSet_atomSlice (m := borelX3) (A := A) (fun k => hm (A k) (hAmeas k)) x n
  have hc : ∀ n, (ProbabilityTheory.condExpKernel μ 𝔪.m x) (atomSlice A x n)
      = (ProbabilityTheory.condExpKernel μ 𝔪.m x) Set.univ := fun n => by
    rw [huniv]; exact hx n
  rw [hatom]
  rw [measure_iInter_eq_of_forall_eq_univ hmeas hfin hc]
  exact huniv

end Work.EKLComp
