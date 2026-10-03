import Mathlib
import Submission.Work.Peluse.SwapC.cprocSubdivNodup
import Submission.Work.Peluse.SwapC.ofFn_equivFin_perm
import Submission.Work.Peluse.SwapC.pairSlots_perm_slotOfF

/-!
# The two ends of the iteration of `concatAll` (KKL Proposition 6.2)

`Work.Peluse.SwapC.genuineSlots Λ` is the list of slots of the concatenation state at the
subdivision `Λ`: the raw slots `CC.raw j l.str` of the leaves `l` of depth `≤ s - 1 - j`, followed by
the difference slots `CC.dff j a.str b.str` for the pairs of leaves whose strings first differ at
coordinate `s - 1 - j` (`a` carrying `true`).

* At `k = 0` the subdivision is the single leaf at the empty string, and the genuine slots are the
  `s` raw slots there (`genuineSlots_cproc_zero`).
* At `k = 2 ^ s - 1`, if all leaves have depth `s`, then no raw slot survives and the difference
  slots are exactly the `slotSet s` slots of the target (`genuineDiffs_perm_slotSet` below, whose
  hypotheses `Λ.Nodup` and "every string is a leaf" are supplied by `cprocSubdivNodup`).

The main theorem `cgenSlotsEndpoints` combines the two.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

open CC
open Classical
open scoped BigOperators

noncomputable section

/-- The condition `slotCond j a b` is exactly the membership of `(j, a, b)` in
`Work.Peluse.LadderP.Swap.slotSet s`. -/
lemma slotCond_iff_mem_slotSet {s : ℕ} (j : Fin s) (a b : Fin s → Bool) :
    slotCond j a b ↔ (j, a, b) ∈ LadderP.Swap.slotSet s := by
  rw [LadderP.Swap.slotSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun r hr => h1 r ?_, fun r hr => ?_⟩
    · omega
    · have hr' : r = ⟨s - 1 - j.val, by omega⟩ := by
        refine Fin.ext ?_
        simp only [Fin.val_mk]
        omega
      rw [hr']
      exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => h1 i ?_, ?_, ?_⟩
    · omega
    · have hr : (⟨s - 1 - j.val, by omega⟩ : Fin s).val + j.val + 1 = s := by
        simp only [Fin.val_mk]
        omega
      exact (h2 ⟨s - 1 - j.val, by omega⟩ hr).1
    · have hr : (⟨s - 1 - j.val, by omega⟩ : Fin s).val + j.val + 1 = s := by
        simp only [Fin.val_mk]
        omega
      exact (h2 ⟨s - 1 - j.val, by omega⟩ hr).2

/-! ## Part 1: the state at `k = 0` -/

/-- The single leaf of `cproc s 0`, the root of the process. -/
def croot (s : ℕ) : CLeaf s :=
  ⟨czero s, 0, by omega, fun _ _ => rfl⟩

@[simp] lemma croot_str (s : ℕ) : (croot s).str = czero s := rfl

@[simp] lemma croot_dep (s : ℕ) : (croot s).dep = 0 := rfl

lemma cproc_zero (s : ℕ) : cproc s 0 = [croot s] := rfl

/-- The slots of a single-leaf subdivision: there is no pair of *distinct* leaves, so there are no
difference slots. -/
lemma genuineDiffs_singleton {s : ℕ} (a : CLeaf s) : genuineDiffs [a] = [] := by
  have hprod : List.product [a] [a] = [(a, a)] := by simp [List.product]
  rw [genuineDiffs, hprod]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.filterMap_eq_nil_iff]
  intro j _
  rw [if_neg]
  rintro ⟨-, h1, h2⟩
  rw [h1] at h2
  exact Bool.noConfusion h2

lemma croot_raws (s : ℕ) :
    CLeaf.raws (croot s) = (List.finRange s).map (fun j : Fin s => CC.raw j (czero s)) := by
  rw [CLeaf.raws]
  congr 1
  rw [List.filter_eq_self]
  intro a _
  exact decide_eq_true_iff.mpr (Nat.zero_le _)

lemma genuineSlots_cproc_zero (s : ℕ) :
    (genuineSlots (cproc s 0)).Perm
      ((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))) := by
  rw [cproc_zero, genuineSlots]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
  rw [croot_raws, genuineDiffs_singleton]
  simp

/-! ## Part 2: the state at `k = 2 ^ s - 1` -/

/-- Membership in `List.product`, in the `List.product` spelling (the Mathlib lemma `List.mem_product`
is stated for the `×ˢ` notation, which is the same function only through the `SProd` instance). -/
lemma mem_List_product {α β : Type*} {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) ∈ List.product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp [List.product]

/-- `List.product` of a duplicate-free list with itself is duplicate-free. -/
lemma nodup_List_product {α : Type*} {l : List α} (h : l.Nodup) : (List.product l l).Nodup := by
  simpa only [List.product, SProd.sprod] using h.product h

/-- If every leaf of a subdivision has depth `s`, then every string of `{0,1}^s` occurs as a leaf:
the cell of a leaf of depth `s` is the single string `l.str`, and the cells partition `{0,1}^s`. -/
lemma mem_map_str_of_isSubdiv {s : ℕ} {Λ : List (CLeaf s)} (hsub : IsSubdiv Λ)
    (hd : ∀ l ∈ Λ, l.dep = s) : ∀ x : Fin s → Bool, x ∈ Λ.map CLeaf.str := by
  intro x
  obtain ⟨l, hl, -⟩ := hsub x
  have hstr : l.str = x := by
    funext i
    exact hl.2 i (by rw [hd l hl.1]; exact i.isLt)
  rw [← hstr]
  exact List.mem_map.mpr ⟨l, hl.1, rfl⟩

/-- A leaf of depth `s` has no raw slots. -/
lemma raws_eq_nil_of_dep_eq {s : ℕ} {l : CLeaf s} (h : l.dep = s) : CLeaf.raws l = [] := by
  rw [CLeaf.raws, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro j _
  rw [decide_eq_true_iff]
  intro hle
  rw [h] at hle
  omega

/-- A list of leaves of depth `s` has no raw slots at all. -/
lemma flatten_map_raws_eq_nil {s : ℕ} {Λ : List (CLeaf s)} (hd : ∀ l ∈ Λ, l.dep = s) :
    (Λ.map CLeaf.raws).flatten = [] := by
  rw [List.flatten_eq_nil_iff]
  intro l hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  exact raws_eq_nil_of_dep_eq (hd l' hl')

/-- The difference slots of `genuineDiffs`, written through `pairSlots` (the definition body
carries the plain conjunction, `pairSlots` the named condition `slotCond`). -/
lemma genuineDiffs_eq_flatMap {s : ℕ} (Λ : List (CLeaf s)) :
    genuineDiffs Λ = (Λ.product Λ).flatMap (fun p => pairSlots p.1.str p.2.str) := by
  rw [genuineDiffs]
  refine List.flatMap_congr ?_
  intro p _
  rw [pairSlots]
  refine List.filterMap_congr ?_
  intro j _
  exact ite_congr (propext Iff.rfl) (fun _ => rfl) (fun _ => rfl)

/-- The difference slots of `Λ`, rewritten as the slots of the string pairs of `Λ`. -/
lemma genuineDiffs_perm_filterMap {s : ℕ} (Λ : List (CLeaf s)) :
    (genuineDiffs Λ).Perm
      (((Λ.product Λ).map (fun p => (p.1.str, p.2.str))).filterMap
        (fun x => slotOfF x.1 x.2)) := by
  rw [genuineDiffs_eq_flatMap]
  rw [List.filterMap_eq_flatMap_toList]
  rw [List.flatMap_map]
  exact List.Perm.flatMap_left _ (fun p _ => pairSlots_perm_slotOfF p.1.str p.2.str)

/-- **The difference slots of a full subdivision.**  If `Λ` has no repeated leaf, every leaf has
depth `s` and every string of `{0,1}^s` occurs as a leaf, then the difference slots of `Λ` are
exactly the slots of `slotSet s`. -/
lemma genuineDiffs_perm_slotSet {s : ℕ} {Λ : List (CLeaf s)} (hnod : Λ.Nodup)
    (hd : ∀ l ∈ Λ, l.dep = s) (hcov : ∀ x : Fin s → Bool, x ∈ Λ.map CLeaf.str) :
    (genuineDiffs Λ).Perm
      ((LadderP.Swap.slotSet s).toList.map
        (fun t : Fin s × (Fin s → Bool) × (Fin s → Bool) => CC.dff t.1 t.2.1 t.2.2)) := by
  -- the list whose slots are counted, and the slot map
  have hnodC : (((Λ.product Λ).map (fun p => (p.1.str, p.2.str))).filterMap
      (fun x => slotOfF x.1 x.2)).Nodup := by
    refine List.Nodup.filterMap ?_ ?_
    · rintro x x' y hy hy'
      rw [Option.mem_def] at hy hy'
      rw [slotOfF_eq_some_iff x.1 x.2 y] at hy
      rw [slotOfF_eq_some_iff x'.1 x'.2 y] at hy'
      obtain ⟨j, -, hy⟩ := hy
      obtain ⟨j', -, hy'⟩ := hy'
      have hEq : CC.dff j x.1 x.2 = CC.dff j' x'.1 x'.2 := hy.symm.trans hy'
      obtain ⟨-, h1, h2⟩ := (CC.dff.injEq j x.1 x.2 j' x'.1 x'.2).mp hEq
      exact Prod.ext h1 h2
    · refine List.Nodup.map_on ?_ (nodup_List_product hnod)
      rintro p hp p' hp' heq
      have hs1 : p.1.str = p'.1.str := congrArg Prod.fst heq
      have hs2 : p.2.str = p'.2.str := congrArg Prod.snd heq
      have hdp : p.1.dep = s := hd p.1 (mem_List_product.mp hp).1
      have hdp' : p'.1.dep = s := hd p'.1 (mem_List_product.mp hp').1
      have hdq : p.2.dep = s := hd p.2 (mem_List_product.mp hp).2
      have hdq' : p'.2.dep = s := hd p'.2 (mem_List_product.mp hp').2
      have e1 : p.1 = p'.1 := by
        rw [CLeaf.mk.injEq]
        exact ⟨hs1, by rw [hdp, hdp']⟩
      have e2 : p.2 = p'.2 := by
        rw [CLeaf.mk.injEq]
        exact ⟨hs2, by rw [hdq, hdq']⟩
      exact Prod.ext e1 e2
  -- the elements of the two lists agree
  have hmemC : ∀ y : CC s,
      y ∈ (((Λ.product Λ).map (fun p => (p.1.str, p.2.str))).filterMap
            (fun x => slotOfF x.1 x.2))
        ↔ y ∈ ((LadderP.Swap.slotSet s).toList.map
            (fun t : Fin s × (Fin s → Bool) × (Fin s → Bool) => CC.dff t.1 t.2.1 t.2.2)) := by
    intro y
    simp only [List.mem_filterMap, List.mem_map, Finset.mem_toList]
    constructor
    · rintro ⟨x, ⟨p, hp, hpx⟩, hxy⟩
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpx
      rw [slotOfF_eq_some_iff x.1 x.2 y] at hxy
      obtain ⟨j, hj, hy⟩ := hxy
      exact ⟨(j, x.1, x.2), (slotCond_iff_mem_slotSet j x.1 x.2).mp hj, hy.symm⟩
    · rintro ⟨t, ht, hty⟩
      obtain ⟨j, a, b⟩ := t
      have hty' : CC.dff j a b = y := hty
      have hj : slotCond j a b := (slotCond_iff_mem_slotSet j a b).mpr ht
      obtain ⟨l₁, hl₁, e₁⟩ := List.mem_map.mp (hcov a)
      obtain ⟨l₂, hl₂, e₂⟩ := List.mem_map.mp (hcov b)
      refine ⟨(a, b), ⟨(l₁, l₂), mem_List_product.mpr ⟨hl₁, hl₂⟩, ?_⟩, ?_⟩
      · exact Prod.ext e₁ e₂
      · exact (slotOfF_eq_some_iff a b y).mpr ⟨j, hj, hty'.symm⟩
  -- the two lists are duplicate-free and have the same elements
  have hnodR : ((LadderP.Swap.slotSet s).toList.map
      (fun t : Fin s × (Fin s → Bool) × (Fin s → Bool) => CC.dff t.1 t.2.1 t.2.2)).Nodup := by
    refine List.Nodup.map ?_ (Finset.nodup_toList _)
    rintro ⟨j, a, b⟩ ⟨j', a', b'⟩ heq
    obtain ⟨h1, h2, h3⟩ := (CC.dff.injEq j a b j' a' b').mp heq
    rw [h1, h2, h3]
  refine (genuineDiffs_perm_filterMap Λ).trans ?_
  refine Multiset.coe_eq_coe.mp ((Multiset.Nodup.ext ?_ ?_).mpr ?_)
  · exact Multiset.coe_nodup.mpr hnodC
  · exact Multiset.coe_nodup.mpr hnodR
  · intro y
    rw [Multiset.mem_coe, Multiset.mem_coe]
    exact hmemC y

/-- **The two ends of the iteration of `Work.Peluse.SwapC.concatAll`** (KKL Proposition 6.2).
`Work.Peluse.SwapC.genuineSlots Λ` is the list of slots of the state at the subdivision `Λ`: the raw
slots `CC.raw j l.str` with `s - 1 - j ≥ l.dep`, followed by the differences `CC.dff j a.str b.str`
for pairs of distinct leaves whose strings first differ at coordinate `s - 1 - j` (`a` carrying
`true`).

At `k = 0` (the single leaf, the empty string) the genuine slots are the `s` raw slots at the empty
string.  At `k = 2^s - 1`, if every leaf of `cproc s (2^s - 1)` has depth `s` (proved separately as
`cprocBookkeeping`), the genuine slots are exactly the `slotSet s` slots of the target.

Route: for the first claim, `cproc s 0` is the single leaf `(czero s, 0)`, whose only raw slots are
the `s` raw slots (`genuineDiffs` is empty since there is only one leaf).  For the second, every
string of `{0,1}^s` is a leaf of depth `s`, so no raw slot remains (`s - 1 - j ≥ s` is false), and
the pairs of leaves are exactly the triples `(j,ε,ε')` with `ε, ε'` first differing at coordinate
`s - 1 - j` (`ε` carrying `true`, `ε'` carrying `false`), i.e. `slotSet s`. -/
theorem cgenSlotsEndpoints (s : ℕ) :
    ((Work.Peluse.SwapC.genuineSlots (Work.Peluse.SwapC.cproc s 0)).Perm
        ((List.finRange s).map (fun j : Fin s => Work.Peluse.SwapC.CC.raw j (Work.Peluse.SwapC.czero s))))
      ∧ (1 ≤ s → (∀ l ∈ Work.Peluse.SwapC.cproc s (2 ^ s - 1), l.dep = s) →
        (Work.Peluse.SwapC.genuineSlots (Work.Peluse.SwapC.cproc s (2 ^ s - 1))).Perm
          (List.ofFn (fun k : Fin (Work.Peluse.LadderP.Swap.slotCard s) =>
            Work.Peluse.SwapC.CC.dff (Work.Peluse.LadderP.Swap.slotAt s k).1
              (Work.Peluse.LadderP.Swap.slotAt s k).2.1
              (Work.Peluse.LadderP.Swap.slotAt s k).2.2))) := by
  constructor
  · exact genuineSlots_cproc_zero s
  · intro _ hdep
    have hsub : IsSubdiv (cproc s (2 ^ s - 1)) := (cprocSubdivNodup s (2 ^ s - 1)).1
    have hnod : (cproc s (2 ^ s - 1)).Nodup := (cprocSubdivNodup s (2 ^ s - 1)).2
    have hcov := mem_map_str_of_isSubdiv hsub hdep
    rw [genuineSlots, flatten_map_raws_eq_nil hdep, List.nil_append]
    refine (genuineDiffs_perm_slotSet hnod hdep hcov).trans ?_
    exact (ofFn_equivFin_perm (LadderP.Swap.slotSet s)
      (fun t : Fin s × (Fin s → Bool) × (Fin s → Bool) => CC.dff t.1 t.2.1 t.2.2)).symm

end

end Work.Peluse.SwapC
