import Mathlib
import Submission.Work.Resample.buQWSelDefs

namespace Work.Resample

/-- The list of records of the selection stage is the pointwise `ofFn` list: this is the
`List.zip`-vs-`ofFn` bookkeeping that every stage lemma about `buSelRecs` needs. -/
theorem buSelRecs_eq_ofFn (s t : ℕ) (u : List (ℤ × ℤ)) (hu : u.length = t) :
    buSelRecs s t u = buSelRecs' s t u := by
  apply List.ext_getElem
  · simp only [buSelRecs, buSelRecs', buSelKeys, List.length_map, List.length_zip,
      List.length_ofFn, hu, min_self]
  · intro n h1 _
    have hn : n < u.length := by
      simpa [buSelRecs, buSelKeys, List.length_map, List.length_zip, hu] using h1
    simp only [buSelRecs, buSelRecs', buSelKeys, List.getElem_map, List.getElem_zip,
      List.getElem_ofFn]
    rw [List.getD_eq_getElem u (0, 0) hn]

theorem buSelRecsSpec (s t : ℕ) (u : List (ℤ × ℤ)) (hu : u.length = t) :
    Work.Resample.buSelRecs s t u = Work.Resample.buSelRecs' s t u ∧
    (∀ i < t, (Work.Resample.buSelRecs s t u).getD i HvdH.Val.nil =
      HvdH.Val.cons (HvdH.Val.int ((Work.Resample.egLam s t i : ℕ) : ℤ)) (HvdH.cfxVal (u.getD i (0, 0)))) ∧
    (Work.Resample.buSelRecs s t u).map HvdH.pairKey = List.ofFn (fun i : Fin t => ((Work.Resample.egLam s t i : ℕ) : ℤ)) ∧
    (Work.Resample.buSelRecs s t u).length = t := by
  have hEq : buSelRecs s t u = buSelRecs' s t u := buSelRecs_eq_ofFn s t u hu
  refine ⟨hEq, ?_, ?_, ?_⟩
  · intro i hi
    rw [hEq, buSelRecs']
    rw [List.getD_eq_getElem _ HvdH.Val.nil (by simpa using hi)]
    simp [List.getElem_ofFn]
  · rw [hEq, buSelRecs', List.map_ofFn]
    rfl
  · rw [hEq, buSelRecs', List.length_ofFn]

end Work.Resample
