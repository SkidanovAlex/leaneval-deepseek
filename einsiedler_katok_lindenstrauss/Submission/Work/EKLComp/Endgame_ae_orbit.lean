import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Uij_range

/-!
# Endgame: an a.e. orbit of `⟨aDiag, u_ij⟩` meets a conull set

Component C10 of the frozen EKL contract ends by exhibiting a point `x : X₃` whose orbit under
the countable set

  `{aDiag t * u_ij(s) | t ∈ ℚ³, s ∈ ℚ}`

avoids a fixed null set.  The mathematics is purely measure-theoretic: the acting group is
*countable*, each of its elements acts by a measure-preserving map (by `A`-invariance and
`U_ij`-invariance of `μ`), and a countable intersection of conull sets in a probability space is
non-empty.

`exists_forall_mem_of_measurePreserving` below isolates the abstract statement; the requested
lemma `Endgame_ae_orbit` is the specialisation to the action of `SL₃(ℝ)` on `X₃`.
-/

open MeasureTheory

namespace Work.EKLComp

/-- **Countable family of measure-preserving self-maps meets a conull set.**  If `f i` is
measure preserving for every `i` in a countable index type and `μ Sᶜ = 0` with `μ` a probability
measure, then some point `x` has `f i x ∈ S` for all `i`.

The complement of `⋂ i, f i ⁻¹' S` is the countable union of the null sets `(f i ⁻¹' S)ᶜ`, so it
is null, and a null set cannot be all of `univ` in a probability space. -/
theorem exists_forall_mem_of_measurePreserving {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {ι : Type*} [Countable ι] {f : ι → α → α}
    (hf : ∀ i, MeasurePreserving (f i) μ μ) {S : Set α} (hS : μ Sᶜ = 0) :
    ∃ x, ∀ i, f i x ∈ S := by
  have hae : ∀ᵐ x ∂μ, ∀ i, f i x ∈ S := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have hset : {a : α | ¬ (f i a ∈ S)} = (f i ⁻¹' S)ᶜ := rfl
    rw [hset]
    have h := (hf i).preimage_null hS
    rwa [Set.preimage_compl] at h
  exact hae.exists

/-- **Endgame: a.e. orbit.**  For a probability measure `μ` on `X₃` invariant under the diagonal
group `A` and under the root group `U_ij`, and for any conull set `S`, there is a point `x` whose
`⟨aDiag, u_ij⟩`-orbit along *rational* parameters stays in `S`:
`(aDiag t * u_ij(s)) • x ∈ S` for all `t : Fin 3 → ℚ` and all `s : ℚ`. -/
theorem Endgame_ae_orbit (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hA : Work.EKLContract.IsAInvariant μ) (i j : Fin 3) (hij : i ≠ j)
    (hU : Work.EKLContract.IsUInvariant μ (Work.EKLContract.Uij hij))
    {S : Set Work.EKLContract.X3} (hS : μ Sᶜ = 0) :
    ∃ x : Work.EKLContract.X3, ∀ p : (Fin 3 → ℚ) × ℚ,
      (Work.EKLContract.aDiag (fun k => (p.1 k : ℝ)) * Work.EKLContract.uij hij (p.2 : ℝ)) • x ∈ S := by
  refine exists_forall_mem_of_measurePreserving (μ := μ)
    (f := fun p : (Fin 3 → ℚ) × ℚ => fun x : Work.EKLContract.X3 =>
      (Work.EKLContract.aDiag (fun k => (p.1 k : ℝ)) *
        Work.EKLContract.uij hij (p.2 : ℝ)) • x) ?_ hS
  intro p
  have hu : Work.EKLContract.uij hij ((p.2 : ℚ) : ℝ) ∈ Work.EKLContract.Uij hij :=
    Subgroup.subset_closure ⟨((p.2 : ℚ) : ℝ), rfl⟩
  have h1 : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag (fun k => (p.1 k : ℝ)) • x) μ μ :=
    hA (fun k => (p.1 k : ℝ))
  have h2 : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.uij hij ((p.2 : ℚ) : ℝ) • x) μ μ :=
    hU _ hu
  have h3 := h1.comp h2
  convert h3 using 1
  ext x
  simp only [Function.comp_apply, mul_smul]

end Work.EKLComp
