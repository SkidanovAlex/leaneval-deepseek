import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCxCert
import Submission.Work.MbarHomology.Qbar.QbarFacetListCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-!
# A kernel-cheap form of `bdOfEnum`

`bdEntryE` tests `x ∈ qFacet y` on the literal `Finset` table (twice: once directly and once
inside `qInc`).  `bdEntryF` tests membership in the literal facet list `qFacetL y` and reads
the incidence number from `qIncRow` directly; `bdOfEnum_eq_fast` shows the two boundary
operators coincide, so the `decide`s of `Qbar/CxData` can run on the fast form.
-/

namespace Work.MbarHomology

/-- `bdEntryE`, with the facet test on the literal facet lists. -/
def bdEntryF (E : ℕ → List (Fin 865)) (k : ℕ) (i : Fin (E k).length)
    (j : Fin (E (k+1)).length) : ℤ :=
  if (E k).get i ∈ BdFiber.qFacetL ((E (k+1)).get j) then
    qIncRow ((E (k+1)).get j) ((E k).get i) else 0

theorem bdEntryE_eq_fast (E : ℕ → List (Fin 865)) (k : ℕ) (i : Fin (E k).length)
    (j : Fin (E (k+1)).length) : bdEntryE E k i j = bdEntryF E k i j := by
  unfold bdEntryE bdEntryF qInc
  by_cases h : (E k).get i ∈ qFacet ((E (k+1)).get j)
  · rw [if_pos h, if_pos h, if_pos (BdFiber.mem_qFacetL_iff.mpr h)]
  · rw [if_neg h, if_neg (fun h2 => h (BdFiber.mem_qFacetL_iff.mp h2))]

/-- `bdOfEnum`, computed with `bdEntryF`. -/
def bdOfEnumF (E : ℕ → List (Fin 865)) (k : ℕ) :
    Work.Certificates.SOp (E k).length (E (k+1)).length :=
  ⟨fun j => (List.finRange (E k).length).filterMap fun i =>
      if bdEntryF E k i j = 0 then none else some (i, bdEntryF E k i j)⟩

theorem bdOfEnum_eq_fast (E : ℕ → List (Fin 865)) (k : ℕ) : bdOfEnum E k = bdOfEnumF E k := by
  unfold bdOfEnum bdOfEnumF
  simp only [bdEntryE_eq_fast]

end Work.MbarHomology
