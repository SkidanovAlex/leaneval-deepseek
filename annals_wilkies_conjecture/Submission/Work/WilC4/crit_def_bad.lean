import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.crit_def_bad_aux
import Submission.Work.WilC4.crit_def_bad_ru
import Submission.Work.WilC4.IntDomFam_definable
import Submission.Work.WilC4.RDpart_definable
import Submission.Work.WilC4.LUpart_definable
import Submission.Work.WilC4.LDpart_definable
import Submission.Work.WilC4g.definable_fibre_cons

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- The fibre of a `∅`-definable subset of `ℝ^{k+1}` along `x ↦ Fin.cons x c` is definable over
all of `ℝ` (in fact `LRc` names every real, so no parameters are needed at all; the parameter set
`Set.univ` of the statement is what makes this immediate). -/
private lemma fiber_univ {k : ℕ} {S : Set (Fin (k+1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc S) (c : Fin k → ℝ) :
    (Set.univ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc {x : ℝ | Fin.cons x c ∈ S} :=
  (WilC4g.definable_fibre_cons (A := (∅ : Set ℝ)) (B := S) hS c).mono (Set.subset_univ _)

theorem crit_def_bad {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadRU Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadRD Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadLU Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadLD Y) ∧
    (∀ c : Fin k → ℝ,
      (Set.univ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc {x : ℝ | Fin.cons x c ∈ BadRU Y} ∧
      (Set.univ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc {x : ℝ | Fin.cons x c ∈ BadRD Y} ∧
      (Set.univ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc {x : ℝ | Fin.cons x c ∈ BadLU Y} ∧
      (Set.univ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc {x : ℝ | Fin.cons x c ∈ BadLD Y}) := by
  have hI := IntDomFam_definable hY
  have hRU := badRU_part_definable hY
  have hRD := RDpart_definable hY
  have hLU := LUpart_definable hY
  have hLD := LDpart_definable hY
  have eRU : BadRU Y = IntDomFam Y ∩ RUpart Y := by
    ext v
    simp only [BadRU, IntDomFam, RUpart, Set.mem_setOf_eq, Set.mem_inter_iff]
  have eRD : BadRD Y = IntDomFam Y ∩ RDpart Y := by
    ext v
    simp only [BadRD, IntDomFam, RDpart, Set.mem_setOf_eq, Set.mem_inter_iff]
  have eLU : BadLU Y = IntDomFam Y ∩ LUpart Y := by
    ext v
    simp only [BadLU, IntDomFam, LUpart, Set.mem_setOf_eq, Set.mem_inter_iff]
  have eLD : BadLD Y = IntDomFam Y ∩ LDpart Y := by
    ext v
    simp only [BadLD, IntDomFam, LDpart, Set.mem_setOf_eq, Set.mem_inter_iff]
  have dRU : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadRU Y) := by
    rw [eRU]; exact hI.inter hRU
  have dRD : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadRD Y) := by
    rw [eRD]; exact hI.inter hRD
  have dLU : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadLU Y) := by
    rw [eLU]; exact hI.inter hLU
  have dLD : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BadLD Y) := by
    rw [eLD]; exact hI.inter hLD
  exact ⟨dRU, dRD, dLU, dLD,
    fun c => ⟨fiber_univ dRU c, fiber_univ dRD c, fiber_univ dLU c, fiber_univ dLD c⟩⟩

end Work.WilC4
