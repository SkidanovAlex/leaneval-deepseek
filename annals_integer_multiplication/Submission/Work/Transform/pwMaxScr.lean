import Mathlib
import Submission.Work.Transform.pwMaxDefs

namespace Work.Transform

open HvdH

/-- `HvdH.Stk = Fin 16` has 16 elements, so for any two distinct stacks there are seven stacks,
pairwise distinct and different from both.  (Concretely: exclude `src` and `mx`, which leaves 14,
and take any 7 of them.) -/
theorem pwMaxScr (src mx : HvdH.Stk) (h : src ≠ mx) :
    Nonempty (Work.Transform.Pw.Scr src mx) := by
  classical
  -- The 14 stacks different from `src` and from `mx`.
  set S : Finset HvdH.Stk := (Finset.univ.erase src).erase mx with hSdef
  have h1 : ((Finset.univ : Finset HvdH.Stk).erase src).card = 15 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ src), Finset.card_univ, Fintype.card_fin]
  have h2 : S.card = ((Finset.univ : Finset HvdH.Stk).erase src).card - 1 := by
    rw [hSdef]
    exact Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ mx⟩)
  have hScard : S.card = 14 := by omega
  have hlen : S.toList.length = 14 := by rw [Finset.length_toList, hScard]
  have h7 : 7 ≤ S.toList.length := by omega
  -- The first seven elements of that enumeration.
  let f : Fin 7 → HvdH.Stk := fun i => S.toList.get (Fin.castLE h7 i)
  have hmemS : ∀ i : Fin 7, f i ∈ S := by
    intro i
    simpa only [f] using Finset.mem_toList.mp (List.get_mem S.toList (Fin.castLE h7 i))
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hg : S.toList.get (Fin.castLE h7 i) = S.toList.get (Fin.castLE h7 j) := by
      simpa only [f] using hij
    exact Fin.castLE_injective h7 ((List.nodup_iff_injective_get.mp (Finset.nodup_toList S)) hg)
  have hnodup : [f 0, f 1, f 2, f 3, f 4, f 5, f 6].Nodup := by
    rw [show ([f 0, f 1, f 2, f 3, f 4, f 5, f 6] : List HvdH.Stk) = List.ofFn f from rfl]
    exact List.nodup_ofFn_ofInjective hf_inj
  have hmem_list : ∀ y ∈ ([f 0, f 1, f 2, f 3, f 4, f 5, f 6] : List HvdH.Stk), y ∈ S := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy | hy | hy | hy | hy | hy <;> subst hy <;> exact hmemS _
  have hne_src : ∀ x ∈ ([f 0, f 1, f 2, f 3, f 4, f 5, f 6] : List HvdH.Stk), x ≠ src := by
    intro x hx
    have hxS := hmem_list x hx
    rw [hSdef] at hxS
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hxS).2).1
  have hne_mx : ∀ x ∈ ([f 0, f 1, f 2, f 3, f 4, f 5, f 6] : List HvdH.Stk), x ≠ mx := by
    intro x hx
    have hxS := hmem_list x hx
    rw [hSdef] at hxS
    exact (Finset.mem_erase.mp hxS).1
  exact ⟨{ sp := f 0, spc := f 1, ds := f 2, tmp := f 3, sA := f 4, bA := f 5, bB := f 6,
           nodup := hnodup, ne_src := hne_src, ne_mx := hne_mx }⟩

end Work.Transform
