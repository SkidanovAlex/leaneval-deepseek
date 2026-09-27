import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.joinAtoms
import Submission.Work.EKLComp.condExpKernel_pos

/-!
# Measurability of `x ↦ κ x (atom 𝔫.m x)`

For a finite measure `ν` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a sub-σ-algebra `𝔪.m ≤ borel X₃` and a
countably generated sub-σ-algebra `𝔫.m ≤ borel X₃`, the map

`x ↦ condExpKernel ν 𝔪.m x (atom 𝔫.m x)`

is Borel measurable.

This is the "atom mass of the conditional kernel" that occurs when one decomposes the conditional
measure `condExpKernel ν 𝔪.m x` along the atoms of a finer σ-algebra `𝔫.m`.

The proof has two independent halves.

* The *assignment of atoms* `x ↦ atom 𝔫.m x` has Borel graph:
  `{p : X₃ × X₃ | p.2 ∈ atom 𝔫.m p.1}` is Borel.  Indeed, for a countable generating family `b`
  of `𝔫.m`, membership `y ∈ atom 𝔫.m x` means that `x` and `y` lie in exactly the same members of
  `b` (`atomG_generateFrom`), so the graph is the countable intersection, over `s ∈ b`, of the sets
  `(s ×ˢ s) ∪ (sᶜ ×ˢ sᶜ)`; these are Borel because `𝔫.m ≤ borel X₃` makes each generator Borel.
* For a *fixed* Borel set `A ⊆ X₃ × X₃` whose sections `A_x` are the sets of interest, the map
  `x ↦ condExpKernel ν 𝔪.m x (Prod.mk x ⁻¹' A)` is Borel.  This is
  `Work.EKLComp.measurable_condExpKernel_section'` (a consequence of `Kernel.measurable_kernel_prodMk_left`
  applied to the comap of `condExpKernel ν 𝔪.m` along `id`, which is measurable into `𝔪.m` because
  `𝔪.m ≤ borel X₃`).

Combining the two with `A` the graph of the atom assignment gives the statement.
-/

open MeasureTheory ProbabilityTheory

set_option linter.style.haveILetI false

namespace Work.EKLComp

open Work.EKLContract

/-- The graph of the atom assignment `x ↦ atom 𝔫.m x` is Borel, for a countably generated
σ-algebra `𝔫.m ≤ borel X₃`. -/
lemma measurableSet_atomGraph (𝔫 : SigAlg) (hn : 𝔫.m ≤ borel X3)
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ 𝔫.m = MeasurableSpace.generateFrom b) :
    MeasurableSet {p : X3 × X3 | p.2 ∈ Work.EKLContract.atom 𝔫.m p.1} := by
  obtain ⟨b, hbc, hbm⟩ := hgen
  haveI : Countable b := hbc
  -- membership in the atom of `x` is agreement with `x` on all generators
  have helem : ∀ x : X3,
      Work.EKLContract.atom 𝔫.m x
        = {y : X3 | ∀ s : b, y ∈ (s : Set X3) ↔ x ∈ (s : Set X3)} := by
    intro x
    rw [← atomG_eq_atom 𝔫.m x, hbm, atomG_generateFrom]
    ext y
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h s => h (s : Set X3) s.2, fun h s hs => h ⟨s, hs⟩⟩
  have hset : {p : X3 × X3 | p.2 ∈ Work.EKLContract.atom 𝔫.m p.1} =
      ⋂ (s : b), {p : X3 × X3 | p.2 ∈ (s : Set X3) ↔ p.1 ∈ (s : Set X3)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, helem p.1]
  rw [hset]
  refine MeasurableSet.iInter fun s => ?_
  have hsb : (s : Set X3) ∈ b := s.2
  have hs : MeasurableSet (s : Set X3) :=
    hn _ (by rw [hbm]; exact MeasurableSpace.measurableSet_generateFrom hsb)
  have hss : {p : X3 × X3 | p.2 ∈ (s : Set X3) ↔ p.1 ∈ (s : Set X3)}
      = ((s : Set X3) ×ˢ (s : Set X3)) ∪ ((s : Set X3)ᶜ ×ˢ (s : Set X3)ᶜ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_prod, Set.mem_compl_iff]
    tauto
  rw [hss]
  exact (hs.prod hs).union (hs.compl.prod hs.compl)

theorem measurable_kernel_atom (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] [StandardBorelSpace Work.EKLContract.X3]
    (𝔪 : Work.EKLComp.SigAlg) (hm : 𝔪.m ≤ borel Work.EKLContract.X3)
    (𝔫 : Work.EKLComp.SigAlg) (hn : 𝔫.m ≤ borel Work.EKLContract.X3)
    (hgen : ∃ b : Set (Set Work.EKLContract.X3), b.Countable ∧
      𝔫.m = MeasurableSpace.generateFrom b) :
    Measurable (fun x => ProbabilityTheory.condExpKernel ν 𝔪.m x (Work.EKLContract.atom 𝔫.m x)) := by
  have hG : MeasurableSet {p : X3 × X3 | p.2 ∈ Work.EKLContract.atom 𝔫.m p.1} :=
    measurableSet_atomGraph 𝔫 hn hgen
  have hmain : Measurable fun x : X3 =>
      ProbabilityTheory.condExpKernel ν 𝔪.m x
        (Prod.mk x ⁻¹' {p : X3 × X3 | p.2 ∈ Work.EKLContract.atom 𝔫.m p.1}) :=
    measurable_condExpKernel_section' 𝔪 hm ν hG
  have hfun : (fun x : X3 => ProbabilityTheory.condExpKernel ν 𝔪.m x
        (Prod.mk x ⁻¹' {p : X3 × X3 | p.2 ∈ Work.EKLContract.atom 𝔫.m p.1}))
      = fun x : X3 => ProbabilityTheory.condExpKernel ν 𝔪.m x (Work.EKLContract.atom 𝔫.m x) := by
    funext x
    congr 1
  rw [hfun] at hmain
  exact hmain

end Work.EKLComp
