import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.shape_comap_conj
import Submission.Work.EKLC6Core.covariant_iterate
import Submission.Work.EKLC6Core.conjBox_mass_pos
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.box_facts
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLComp.measurableSet_smul_mem_atom
import Submission.Work.EKLContract.Interfaces

/-!
# `EKLC6Core.UBox` — the entrywise "`U`-ball" of radius `R`

`IsPlaqueAlgebra U Z A` bounds the matrix entries of the atom shapes `shape A U x` (`x ∈ Z`) by
some `C(x) < ∞`.  `UBox U R` is the corresponding closed entrywise box inside `U`; it is
compact, and the set of points whose atom shape is contained in `UBox U R` is the
positive-measure set of "comparable atoms" that Pisa 7.34/7.35 needs.  (Kept in its own module
below the C6 assembly so that both the assembly and its lemmas can import it.)
-/

namespace Work.EKLC6Core

open MeasureTheory
open Work.EKLContract

/-- The closed entrywise box of radius `R` inside a subgroup `U ≤ SL₃(ℝ)`: the "`U`-ball" of
Pisa 7.25/7.34.  `IsPlaqueAlgebra U Z A` bounds the entries of the atom shapes by some `C`, so
the atom shapes of a plaque algebra subordinate to `U` are contained in `UBox U R` for some
`R ≥ 1`; this is the source of the positive-measure set of "comparable" atoms in Pisa 7.34. -/
def UBox (U : Subgroup SL3) (R : ℝ) : Set SL3 := {g | g ∈ U ∧ ∀ i j, |g i j| ≤ R}

theorem continuous_entry (i j : Fin 3) :
    Continuous (fun g : SL3 => |g i j|) := by
  have h : Continuous fun g : SL3 => ((g : Matrix (Fin 3) (Fin 3) ℝ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact h.abs

theorem isClosed_UBox {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (R : ℝ) :
    IsClosed (UBox U R) := by
  have hbox : IsClosed {g : SL3 | ∀ i j, |g i j| ≤ R} := by
    rw [show {g : SL3 | ∀ i j, |g i j| ≤ R}
        = ⋂ i : Fin 3, ⋂ j : Fin 3, {g : SL3 | |g i j| ≤ R} by ext g; simp]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (continuous_entry i j) continuous_const
  rw [UBox]
  exact hU.inter hbox

theorem measurableSet_UBox {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (R : ℝ) :
    MeasurableSet (UBox U R) :=
  (isClosed_UBox hU R).measurableSet

theorem isCompact_UBox {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (UBox U R) := by
  refine (Work.EKLProd.sl3EntryBox_compact (fun _ _ => -R) (fun _ _ => R)).of_isClosed_subset
    (isClosed_UBox hU R) ?_
  intro g hg i j
  have h := abs_le.mp (hg.2 i j)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem one_mem_UBox {U : Subgroup SL3} {R : ℝ} (hR : 1 ≤ R) : (1 : SL3) ∈ UBox U R := by
  have h0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  refine ⟨U.one_mem, fun i j => ?_⟩
  show |((1 : Matrix (Fin 3) (Fin 3) ℝ)) i j| ≤ R
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, abs_one]; exact hR
  · rw [if_neg hij, abs_zero]; exact h0

end Work.EKLC6Core
