import Mathlib
import Submission.Work.CORE4.A7FGB.involution_support_injective

set_option linter.style.haveILetI false

namespace Work.CORE4.A7FGB

/-- At most three non-identity involutions of `A₇` have support exactly `T`, when `T` has four
elements.  Indeed, such an involution is determined by its value at a fixed point `a ∈ T`
(`involution_support_injective`), and that value lies in the three-element set `T \ {a}`. -/
theorem card_involutions_support_le_three (T : Finset (Fin 7)) (hT : T.card = 4) :
    (Finset.univ.filter (fun x : alternatingGroup (Fin 7) =>
      x * x = 1 ∧ x ≠ 1 ∧ (x : Equiv.Perm (Fin 7)).support = T)).card ≤ 3 := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hT]; norm_num)
  have hcard : (T.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, hT]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7)) a) ?_ ?_
  · -- the value at `a` of such an involution lies in `T \ {a}`
    intro x hx
    obtain ⟨-, _hx2, _hx1, hxs⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hmem : a ∈ (x : Equiv.Perm (Fin 7)).support := by rw [hxs]; exact ha
    have hne : (x : Equiv.Perm (Fin 7)) a ≠ a := Equiv.Perm.mem_support.mp hmem
    exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
      ⟨hne, by rw [← hxs]; exact Equiv.Perm.apply_mem_support.mpr hmem⟩)
  · -- two such involutions with the same value at `a` are equal
    intro x hx y hy hxy
    obtain ⟨-, hx2, _hx1, hxs⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨-, hy2, _hy1, hys⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    have hx2' : (x : Equiv.Perm (Fin 7)) * (x : Equiv.Perm (Fin 7)) = 1 := by
      simpa using congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) hx2
    have hy2' : (y : Equiv.Perm (Fin 7)) * (y : Equiv.Perm (Fin 7)) = 1 := by
      simpa using congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) hy2
    exact Subtype.ext (involution_support_injective T hT a ha _ _ hx2' hy2' hxs hys hxy)

/-- In `A₇`, if `V` is a group of order `4` whose non-identity elements are all involutions with
support exactly `T` (a four-element set), then `V` consists of *all* non-identity involutions
with support `T`.  Indeed there are exactly three of the latter, while `V` already has three
non-identity elements each of which is one of them. -/
theorem involution_support_mem (V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hT : T.card = 4) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (w : alternatingGroup (Fin 7)) (hw : w * w = 1) (hw1 : w ≠ 1)
    (hws : (w : Equiv.Perm (Fin 7)).support = T) : w ∈ V := by
  classical
  -- `S` : the set of all non-identity involutions of `A₇` with support `T`;
  -- `U` : the set of all elements of `V`.
  set S : Finset (alternatingGroup (Fin 7)) :=
    Finset.univ.filter (fun x : alternatingGroup (Fin 7) =>
      x * x = 1 ∧ x ≠ 1 ∧ (x : Equiv.Perm (Fin 7)).support = T) with hSdef
  set U : Finset (alternatingGroup (Fin 7)) :=
    Finset.univ.filter (fun x : alternatingGroup (Fin 7) => x ∈ V) with hUdef
  -- `U` is the underlying set of `V`, so it has four elements.
  have hUcard : U.card = 4 := by
    haveI : Fintype ↥V := Fintype.ofFinite V
    have h1 : U = Finset.univ.map
        (⟨Subtype.val, Subtype.val_injective⟩ : ↥V ↪ alternatingGroup (Fin 7)) := by
      ext x
      rw [hUdef]
      constructor
      · intro hx
        obtain ⟨-, hxV⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_map.mpr ⟨⟨x, hxV⟩, Finset.mem_univ _, rfl⟩
      · intro hx
        obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hv]
        exact v.2
    rw [h1, Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card, hVcard]
  -- Every non-identity element of `V` lies in `S`.
  have hsub : U.erase 1 ⊆ S := by
    intro x hx
    obtain ⟨hx1, hxU⟩ := Finset.mem_erase.mp hx
    rw [hUdef] at hxU
    have hxV : x ∈ V := (Finset.mem_filter.mp hxU).2
    rw [hSdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 x hxV, hx1, hsupp x hxV hx1⟩
  have h1U : (1 : alternatingGroup (Fin 7)) ∈ U := by
    rw [hUdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, V.one_mem⟩
  -- `S` has at most three elements while `U \ {1}` has exactly three, so they coincide.
  have hSeq : S = U.erase 1 := by
    have hScard : S.card ≤ 3 := by
      rw [hSdef]
      exact card_involutions_support_le_three T hT
    have herase : (U.erase 1).card = 3 := by
      rw [Finset.card_erase_of_mem h1U, hUcard]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  -- `w` lies in `S`, hence in `U \ {1}`, hence in `V`.
  have hwS : w ∈ S := by
    rw [hSdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hw1, hws⟩
  rw [hSeq] at hwS
  have hwU : w ∈ U := Finset.mem_of_mem_erase hwS
  rw [hUdef] at hwU
  exact (Finset.mem_filter.mp hwU).2

end Work.CORE4.A7FGB
