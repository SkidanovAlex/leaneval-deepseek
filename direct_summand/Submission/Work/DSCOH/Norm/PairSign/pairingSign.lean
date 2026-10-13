import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.sign_sort_succAbove

namespace Work.DSCOH.Norm.PairSign

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-! ## Auxiliary order-embedding API for `Finset.orderEmbOfFin`

(Copied from `Submission.Work.DSCOH.Norm.ReadFib.readAFiber`, to keep this file self-contained.)
-/

section OrderEmbAux

variable {α : Type*} [LinearOrder α] [DecidableEq α]

/-- The index of `c` in the increasing enumeration `s.orderEmbOfFin h` is the number of elements
of `s` strictly below `c`, whenever `c` is in the range. -/
lemma card_filter_lt_of_orderEmbOfFin_eq {s : Finset α} {k : ℕ} (h : s.card = k) {i : Fin k}
    {c : α} (hc : s.orderEmbOfFin h i = c) :
    (s.filter (fun v => v < c)).card = (i : ℕ) := by
  have himg : s.filter (fun v => v < c)
      = (Finset.univ.filter (fun j : Fin k => j < i)).image (s.orderEmbOfFin h) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv, hvc⟩
      obtain ⟨j, hj⟩ := Set.mem_range.mp (show v ∈ Set.range (s.orderEmbOfFin h) from by
        rw [Finset.range_orderEmbOfFin]; exact hv)
      refine ⟨j, ?_, hj⟩
      rw [← hj, ← hc] at hvc
      exact (s.orderEmbOfFin h).lt_iff_lt.mp hvc
    · rintro ⟨j, hji, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s h j,
        by rw [← hc]; exact (s.orderEmbOfFin h).lt_iff_lt.mpr hji⟩
  rw [himg, Finset.card_image_of_injective _ (s.orderEmbOfFin h).injective]
  exact Work.DSCOH.Norm.filter_card_lt i

/-- Membership in the image of `s.orderEmbOfFin h` is described exactly by the count of the
elements of `s` below the value. -/
lemma orderEmbOfFin_apply_eq_iff {s : Finset α} {k : ℕ} (h : s.card = k) (i : Fin k) (c : α) :
    s.orderEmbOfFin h i = c ↔ c ∈ s ∧ (i : ℕ) = (s.filter (fun v => v < c)).card := by
  constructor
  · intro hc
    exact ⟨hc ▸ Finset.orderEmbOfFin_mem s h i, (card_filter_lt_of_orderEmbOfFin_eq h hc).symm⟩
  · rintro ⟨hcs, hcard⟩
    obtain ⟨j, hj⟩ := Set.mem_range.mp (show c ∈ Set.range (s.orderEmbOfFin h) from by
      rw [Finset.range_orderEmbOfFin]; exact hcs)
    have hji : j = i := Fin.ext (by
      have := card_filter_lt_of_orderEmbOfFin_eq h hj
      omega)
    rw [← hji]
    exact hj

/-- The increasing enumeration of a finset with one element removed, in terms of the enumeration
of the original: `Fin.succAbove` shifts the indices. -/
lemma orderEmbOfFin_erase_apply' {s : Finset α} {n : ℕ} (h : s.card = n + 1) (j : Fin (n + 1))
    (c : α) (hjc : s.orderEmbOfFin h j = c) (h' : (s.erase c).card = n) (m : Fin n) :
    (s.erase c).orderEmbOfFin h' m = s.orderEmbOfFin h (j.succAbove m) := by
  have key : (fun x : Fin n => s.orderEmbOfFin h (j.succAbove x))
      = ⇑((s.erase c).orderEmbOfFin h') := by
    refine Finset.orderEmbOfFin_unique h' (fun x => ?_) ?_
    · rw [Finset.mem_erase]
      refine ⟨?_, Finset.orderEmbOfFin_mem s h _⟩
      intro hcon
      have : j.succAbove x = j := (s.orderEmbOfFin h).injective (hcon.trans hjc.symm)
      exact Fin.succAbove_ne j x this
    · exact (s.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove j)
  exact congrFun key.symm m

/-- Membership in the image under an order embedding commutes with the increasing enumeration. -/
lemma orderEmbOfFin_image_apply {β : Type*} [LinearOrder β] [DecidableEq β]
    {s : Finset α} {k : ℕ} (e : α ↪o β) (h : s.card = k)
    (h' : (s.image e).card = k) (i : Fin k) :
    (s.image e).orderEmbOfFin h' i = e (s.orderEmbOfFin h i) := by
  have key : (fun x : Fin k => e (s.orderEmbOfFin h x)) = ⇑((s.image e).orderEmbOfFin h') := by
    refine Finset.orderEmbOfFin_unique h' (fun x => ?_) ?_
    · exact Finset.mem_image.mpr ⟨_, Finset.orderEmbOfFin_mem s h x, rfl⟩
    · exact e.strictMono.comp (s.orderEmbOfFin h).strictMono
  exact congrFun key.symm i

end OrderEmbAux

/-! ## `headVal` and the rank function -/

section TupleAux

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- `v` lies in the head of `x` at slot `a` iff its rank in the sorted order of `x` is `< a`. -/
lemma mem_headVal_iff_rank_lt {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) (v : Fin (k+1)) :
    v ∈ Work.DSCOH.Norm.headVal x a ↔ ((Tuple.sort x).symm v : ℕ) < (a : ℕ) := by
  rw [Work.DSCOH.Norm.headVal, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hje⟩
    rw [Finset.mem_filter] at hj
    have : (Tuple.sort x).symm v = j := by rw [← hje, Equiv.symm_apply_apply]
    rw [this]; exact hj.2
  · intro hv
    exact ⟨(Tuple.sort x).symm v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, Equiv.apply_symm_apply _ _⟩

/-- The values of the tail embedding, described by the order-embedding API. -/
lemma tailEmb_eq_iff {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1))
    (i : Fin ((k+1) - (a:ℕ))) (c : Fin (k+1)) :
    Work.DSCOH.Norm.tailEmb x a i = c ↔ c ∈ (Work.DSCOH.Norm.headVal x a)ᶜ ∧
      (i:ℕ) = ((Work.DSCOH.Norm.headVal x a)ᶜ.filter (fun v => v < c)).card := by
  rw [Work.DSCOH.Norm.tailEmb]
  exact orderEmbOfFin_apply_eq_iff (Work.DSCOH.Norm.compl_card x a) i c

/-- The rank of the `c`-deletion read: deleting the position `c` of `x` shifts the ranks by
`succAbove (Tuple.sort x).symm c`. -/
lemma sort_symm_succAbove {k : ℕ} (x : Fin (k+2) → ι) (c : Fin (k+2)) (u : Fin (k+1)) :
    (Tuple.sort x).symm (Fin.succAbove c u) =
      Fin.succAbove ((Tuple.sort x).symm c)
        ((Tuple.sort (Work.DSCOH.Norm.del x c)).symm u) := by
  show (Tuple.sort x).symm (Fin.succAbove c u) =
      Fin.succAbove ((Tuple.sort x).symm c)
        ((Tuple.sort (x ∘ Fin.succAbove c)).symm u)
  have h := congrFun (Work.DSCOH.Norm.sort_comp_succAbove x c)
    ((Tuple.sort (x ∘ Fin.succAbove c)).symm u)
  simp only [Function.comp_apply] at h
  have h2 : Fin.succAbove c u = (Tuple.sort x)
      (Fin.succAbove ((Tuple.sort x).symm c)
        ((Tuple.sort (x ∘ Fin.succAbove c)).symm u)) := by
    rw [h, Equiv.apply_symm_apply]
  rw [h2, Equiv.symm_apply_apply]

/-- The value of `Fin.succAbove`. -/
lemma succAbove_val {N : ℕ} (p : Fin (N+1)) (a : Fin N) :
    ((Fin.succAbove p a : Fin (N+1)) : ℕ) = if (a : ℕ) < (p : ℕ) then (a : ℕ) else (a : ℕ) + 1 := by
  by_cases h : (a : ℕ) < (p : ℕ)
  · have h' : a.castSucc < p := by simpa [Fin.lt_def] using h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', ite_eq_left h]
    simp
  · have h' : p ≤ a.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]; omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', ite_eq_right h]
    simp

/-- The value of `Fin.succAbove` when the slot is not below the notch. -/
lemma succAbove_val_le {N : ℕ} (p : Fin (N+1)) (a : Fin N) (h : (p : ℕ) ≤ (a : ℕ)) :
    ((Fin.succAbove p a : Fin (N+1)) : ℕ) = (a : ℕ) + 1 := by
  rw [succAbove_val]; exact ite_eq_right (not_lt.mpr h)

/-- The value of `Fin.succAbove` when the slot is below the notch. -/
lemma succAbove_val_lt {N : ℕ} (p : Fin (N+1)) (a : Fin N) (h : (a : ℕ) < (p : ℕ)) :
    ((Fin.succAbove p a : Fin (N+1)) : ℕ) = (a : ℕ) := by
  rw [succAbove_val]; exact ite_eq_left h

/-- `Finset.orderEmbOfFin` is insensitive to the (propositionally equal) cardinality proof and
index type. -/
lemma orderEmbOfFin_cast {α : Type*} [LinearOrder α] [DecidableEq α] {s : Finset α} {k l : ℕ}
    (h : s.card = k) (h' : s.card = l) (hl : k = l) (i : Fin k) :
    s.orderEmbOfFin h i = s.orderEmbOfFin h' (Fin.cast hl i) := rfl

end TupleAux

/-! ## The two tail correspondences -/

section Tails

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- **Tail correspondence, non-degenerate case.**  When `(Tuple.sort x).symm c ≤ a` (so that
`k' = succAbove ((Tuple.sort x).symm c) a = a+1` and the value `c` is not in the `x`-tail at
`k'`), the `c`-deletion tail of `del x c` at `a` maps under `succAbove c` onto the `x`-tail at
`k'`. -/
lemma tailEmb_del_succAbove_le {k : ℕ} (x : Fin (k+2) → ι) (c : Fin (k+2)) (a : Fin (k+1))
    (hpa : ((Tuple.sort x).symm c : ℕ) ≤ (a : ℕ)) (m : Fin ((k+1) - (a:ℕ))) :
    Fin.succAbove c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m)
      = Work.DSCOH.Norm.tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a)
          ⟨(m:ℕ), by rw [succAbove_val_le ((Tuple.sort x).symm c) a hpa]; omega⟩ := by
  set p : Fin (k+2) := (Tuple.sort x).symm c with hp
  set k' : Fin (k+2) := Fin.succAbove p a with hk'
  have hk'v : (k':ℕ) = (a:ℕ)+1 := by rw [hk']; exact succAbove_val_le p a hpa
  have hcl : (k+2) - (k':ℕ) = (k+1) - (a:ℕ) := by omega
  have hTxc : ((Work.DSCOH.Norm.headVal x k')ᶜ).card = (k+1) - (a:ℕ) := by
    rw [Work.DSCOH.Norm.compl_card x k', hcl]
  let g : Fin ((k+1)-(a:ℕ)) → Fin (k+2) :=
    fun m => Fin.succAbove c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m)
  have hgmem : ∀ m, g m ∈ (Work.DSCOH.Norm.headVal x k')ᶜ := by
    intro m
    rw [Finset.mem_compl, mem_headVal_iff_rank_lt]
    have hUm : Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m
        ∈ (Work.DSCOH.Norm.headVal (Work.DSCOH.Norm.del x c) a)ᶜ :=
      Finset.mem_compl.mpr (Work.DSCOH.Norm.tailEmb_mem _ a m)
    rw [Finset.mem_compl] at hUm
    have hrank : (a:ℕ) ≤ ((Tuple.sort (Work.DSCOH.Norm.del x c)).symm
        (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m) : Fin (k+1)) := by
      by_contra hcon
      exact hUm ((mem_headVal_iff_rank_lt (Work.DSCOH.Norm.del x c) a _).mpr (not_le.mp hcon))
    show ¬ (((Tuple.sort x).symm (Fin.succAbove c
      (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m)) : Fin (k+2)) : ℕ) < (k':ℕ)
    rw [sort_symm_succAbove x c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m),
      ← hp, hk']
    exact not_lt.mpr ((Fin.strictMono_succAbove p).le_iff_le.mpr hrank)
  have hgmono : StrictMono g :=
    ((Fin.strictMono_succAbove c).comp (Work.DSCOH.Norm.tailEmb _ a).strictMono)
  have key := Finset.orderEmbOfFin_unique hTxc hgmem hgmono
  have hstep : ∀ m : Fin ((k+1) - (a:ℕ)),
      (Work.DSCOH.Norm.headVal x k')ᶜ.orderEmbOfFin hTxc m
        = Work.DSCOH.Norm.tailEmb x k' ⟨(m:ℕ), by rw [hcl]; exact m.isLt⟩ := by
    intro m
    show (Work.DSCOH.Norm.headVal x k')ᶜ.orderEmbOfFin hTxc m
      = (Work.DSCOH.Norm.headVal x k')ᶜ.orderEmbOfFin (Work.DSCOH.Norm.compl_card x k')
          ⟨(m:ℕ), by rw [hcl]; exact m.isLt⟩
    rw [orderEmbOfFin_cast hTxc (Work.DSCOH.Norm.compl_card x k') hcl.symm m]
    exact congrArg _ (Fin.ext (by simp))
  rw [show Fin.succAbove c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m) = g m from rfl,
    congrFun key m, hstep m]

/-- **Tail correspondence, degenerate case.**  When `a < (Tuple.sort x).symm c` (so that
`k' = succAbove ((Tuple.sort x).symm c) a = a` and the value `c` is itself in the `x`-tail at
`k'`, at the index `j0` with `tailEmb x k' j0 = c`), the `c`-deletion tail of `del x c` at `a`
maps under `succAbove c` onto the `x`-tail at `k'` with `j0` deleted; the indices are shifted so
that `m` below `j0` corresponds to `m` and `m` at or above `j0` to `m+1`. -/
lemma tailEmb_del_succAbove_gt {k : ℕ} (x : Fin (k+2) → ι) (c : Fin (k+2)) (a : Fin (k+1))
    (hpa : (a : ℕ) < ((Tuple.sort x).symm c : ℕ))
    (j0 : Fin ((k+2) - ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ)))
    (hj0 : Work.DSCOH.Norm.tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a) j0 = c)
    (m : Fin ((k+1) - (a:ℕ))) :
    Fin.succAbove c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m)
      = Work.DSCOH.Norm.tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a)
          ⟨if (m:ℕ) < (j0:ℕ) then (m:ℕ) else (m:ℕ)+1, by
            have h1 : ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) = (a:ℕ) :=
              succAbove_val_lt ((Tuple.sort x).symm c) a hpa
            have h2 := j0.isLt
            have h3 := m.isLt
            split_ifs with hj
            · exact lt_trans hj h2
            · omega⟩ := by
  set Tx : Finset (Fin (k+2)) :=
    (Work.DSCOH.Norm.headVal x (Fin.succAbove ((Tuple.sort x).symm c) a))ᶜ with hTx
  have hkval : ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) = (a:ℕ) :=
    succAbove_val_lt ((Tuple.sort x).symm c) a hpa
  have hmem : c ∈ Tx := by
    rw [hTx, Finset.mem_compl, mem_headVal_iff_rank_lt, hkval]
    omega
  have hcard : (Tx.erase c).card = (k+1) - (a:ℕ) := by
    rw [Finset.card_erase_of_mem hmem, hTx, Work.DSCOH.Norm.compl_card]
    omega
  have hbnd : ∀ m : Fin ((k+1)-(a:ℕ)),
      (if (m:ℕ) < (j0:ℕ) then (m:ℕ) else (m:ℕ)+1) < (k+2) - ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) := by
    intro m
    have h2 := j0.isLt
    have h3 := m.isLt
    split_ifs with hj
    · exact lt_trans hj h2
    · omega
  let sh : Fin ((k+1)-(a:ℕ)) → Fin ((k+2) - ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ)) :=
    fun m => ⟨if (m:ℕ) < (j0:ℕ) then (m:ℕ) else (m:ℕ)+1, hbnd m⟩
  have hrank_aux : ∀ m : Fin ((k+1)-(a:ℕ)),
      ¬ (((Tuple.sort x).symm (Fin.succAbove c
        (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m)) : Fin (k+2)) : ℕ)
        < ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) := by
    intro m
    have hUm : Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m
        ∈ (Work.DSCOH.Norm.headVal (Work.DSCOH.Norm.del x c) a)ᶜ :=
      Finset.mem_compl.mpr (Work.DSCOH.Norm.tailEmb_mem _ a m)
    rw [Finset.mem_compl] at hUm
    have hrank : (a:ℕ) ≤ ((Tuple.sort (Work.DSCOH.Norm.del x c)).symm
        (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m) : Fin (k+1)) := by
      by_contra hcon
      exact hUm ((mem_headVal_iff_rank_lt (Work.DSCOH.Norm.del x c) a _).mpr (not_le.mp hcon))
    rw [sort_symm_succAbove x c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m)]
    exact not_lt.mpr ((Fin.strictMono_succAbove ((Tuple.sort x).symm c)).le_iff_le.mpr hrank)
  have key1 : (fun m : Fin ((k+1)-(a:ℕ)) =>
        Fin.succAbove c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m))
      = ⇑((Tx.erase c).orderEmbOfFin hcard) := by
    refine Finset.orderEmbOfFin_unique hcard (fun m => ?_) ?_
    · rw [Finset.mem_erase]
      refine ⟨Fin.succAbove_ne c _, ?_⟩
      rw [hTx, Finset.mem_compl, mem_headVal_iff_rank_lt]
      exact hrank_aux m
    · exact (Fin.strictMono_succAbove c).comp (Work.DSCOH.Norm.tailEmb _ a).strictMono
  have key2 : (fun m : Fin ((k+1)-(a:ℕ)) =>
        Work.DSCOH.Norm.tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a) (sh m))
      = ⇑((Tx.erase c).orderEmbOfFin hcard) := by
    refine Finset.orderEmbOfFin_unique hcard (fun m => ?_) ?_
    · rw [Finset.mem_erase]
      refine ⟨?_, Finset.orderEmbOfFin_mem _ _ _⟩
      intro hcon
      have h1 : (if (m:ℕ) < (j0:ℕ) then (m:ℕ) else (m:ℕ)+1) = (j0:ℕ) := by
        have h2 := congrArg Fin.val
          ((Work.DSCOH.Norm.tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a)).injective
            (hcon.trans hj0.symm))
        simpa only [sh, Fin.val_mk] using h2
      split_ifs at h1 <;> omega
    · exact (Work.DSCOH.Norm.tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a)).strictMono.comp
        (fun m1 m2 h12 => by
          have h12' : (m1:ℕ) < (m2:ℕ) := h12
          simp only [sh, Fin.lt_def]
          split_ifs <;> omega)
  have hk1 : Fin.succAbove c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a m)
      = (Tx.erase c).orderEmbOfFin hcard m := congrFun key1 m
  have hk2 : (Tx.erase c).orderEmbOfFin hcard m
      = Work.DSCOH.Norm.tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a)
          ⟨if (m:ℕ) < (j0:ℕ) then (m:ℕ) else (m:ℕ)+1, by
            have h1 : ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) = (a:ℕ) :=
              succAbove_val_lt ((Tuple.sort x).symm c) a hpa
            have h2 := j0.isLt
            have h3 := m.isLt
            split_ifs with hj
            · exact lt_trans hj h2
            · omega⟩ := (congrFun key2 m).symm
  rw [hk1, hk2]

end Tails

/-! ## The permutation relation -/

section Rel

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- **The permutational core of the pairing.**  With `k' := succAbove ((Tuple.sort x).symm c) a`,
`Sx := sigmaAPerm x k'`, `Sw := sigmaAPerm (del x c) a` and `pt := Sx.symm c` (the index at which
`Sx` takes the value `c`), the permutation `Sw` is obtained from `Sx` by transporting along the
deletion of `c`:  `Sx (succAbove pt j) = succAbove c (Sw j)` for all `j`. -/
lemma sigmaA_succAbove_del {k : ℕ} (x : Fin (k+2) → ι) (c : Fin (k+2)) (a : Fin (k+1)) :
    ∀ j : Fin (k+1),
      (Work.DSCOH.Norm.sigmaAPerm x (Fin.succAbove ((Tuple.sort x).symm c) a))
        (Fin.succAbove ((Work.DSCOH.Norm.sigmaAPerm x
          (Fin.succAbove ((Tuple.sort x).symm c) a)).symm c) j)
      = Fin.succAbove c ((Work.DSCOH.Norm.sigmaAPerm (Work.DSCOH.Norm.del x c) a) j) := by
  intro j
  set p : Fin (k+2) := (Tuple.sort x).symm c with hp
  set k' : Fin (k+2) := Fin.succAbove p a with hk'
  set Sx : Equiv.Perm (Fin (k+2)) := Work.DSCOH.Norm.sigmaAPerm x k' with hSx
  set Sw : Equiv.Perm (Fin (k+1)) := Work.DSCOH.Norm.sigmaAPerm (Work.DSCOH.Norm.del x c) a with hSw
  set pt : Fin (k+2) := Sx.symm c with hpt
  have hF1 : ∀ u : Fin (k+1), (Tuple.sort x) (Fin.succAbove p u)
      = Fin.succAbove c ((Tuple.sort (Work.DSCOH.Norm.del x c)) u) := by
    intro u
    exact congrFun (Work.DSCOH.Norm.sort_comp_succAbove x c) u
  have hSx_head : ∀ i : Fin (k+2), (i:ℕ) < (k':ℕ) → Sx i = (Tuple.sort x) i := by
    intro i hi
    rw [hSx, Work.DSCOH.Norm.sigmaAPerm_apply, Work.DSCOH.Norm.sigmaA_head x k' hi]
  have hSx_tail : ∀ i : Fin (k+2), ¬ (i:ℕ) < (k':ℕ) →
      Sx i = Work.DSCOH.Norm.tailEmb x k' ⟨(i:ℕ)-(k':ℕ), by
        have := i.isLt; have := k'.isLt; omega⟩ := by
    intro i hi
    rw [hSx, Work.DSCOH.Norm.sigmaAPerm_apply, Work.DSCOH.Norm.sigmaA_tail x k' hi]
  have hSw_head : ∀ i : Fin (k+1), (i:ℕ) < (a:ℕ) →
      Sw i = (Tuple.sort (Work.DSCOH.Norm.del x c)) i := by
    intro i hi
    rw [hSw, Work.DSCOH.Norm.sigmaAPerm_apply,
      Work.DSCOH.Norm.sigmaA_head (Work.DSCOH.Norm.del x c) a hi]
  have hSw_tail : ∀ i : Fin (k+1), ¬ (i:ℕ) < (a:ℕ) →
      Sw i = Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a
        ⟨(i:ℕ)-(a:ℕ), by have := i.isLt; have := a.isLt; omega⟩ := by
    intro i hi
    rw [hSw, Work.DSCOH.Norm.sigmaAPerm_apply,
      Work.DSCOH.Norm.sigmaA_tail (Work.DSCOH.Norm.del x c) a hi]
  rcases lt_or_ge ((a:ℕ)) ((p:ℕ)) with hab | hba
  · -- case A : a < p, so k' = a and c lies in the x-tail at k'
    have hk'v : (k':ℕ) = (a:ℕ) := by rw [hk']; exact succAbove_val_lt p a hab
    have hσp : (Tuple.sort x) p = c := by rw [hp]; exact Equiv.apply_symm_apply _ _
    have hmemT : c ∈ (Work.DSCOH.Norm.headVal x k')ᶜ := by
      rw [Finset.mem_compl, mem_headVal_iff_rank_lt, hk'v]
      omega
    obtain ⟨j0, hj0⟩ := Set.mem_range.mp (show c ∈ Set.range (Work.DSCOH.Norm.tailEmb x k') from by
      rw [Work.DSCOH.Norm.tailEmb, Finset.range_orderEmbOfFin]; exact hmemT)
    have hpt_eq : pt = ⟨(k':ℕ)+(j0:ℕ), by have := j0.isLt; omega⟩ := by
      rw [hpt, Equiv.symm_apply_eq]
      let e0 : Fin (k+2) := ⟨(k':ℕ)+(j0:ℕ), by have := j0.isLt; omega⟩
      have hge : ¬ (e0:ℕ) < (k':ℕ) := by simp only [e0, Fin.val_mk]; omega
      rw [hSx_tail e0 hge]
      have hidx : (⟨(e0:ℕ)-(k':ℕ), by simp only [e0, Fin.val_mk]; omega⟩ :
          Fin ((k+2)-(k':ℕ))) = j0 := Fin.ext (by simp only [e0, Fin.val_mk]; omega)
      rw [hidx, hj0]
    have hpt_val : (pt:ℕ) = (k':ℕ)+(j0:ℕ) := Fin.val_eq_of_eq hpt_eq
    rcases lt_or_ge ((j:ℕ)) ((a:ℕ)) with hja | hja
    · -- j < a
      have hlt : (j:ℕ) < (pt:ℕ) := by rw [hpt_val]; omega
      have hptj : ((Fin.succAbove pt j : Fin (k+2)) : ℕ) = (j:ℕ) := succAbove_val_lt pt j hlt
      have hpj : ((Fin.succAbove p j : Fin (k+2)) : ℕ) = (j:ℕ) :=
        succAbove_val_lt p j (by omega)
      rw [hSw_head j hja, hSx_head _ (by rw [hptj, hk'v]; omega : ((Fin.succAbove pt j : Fin (k+2)) : ℕ) < (k':ℕ))]
      rw [show Fin.succAbove pt j = Fin.succAbove p j from Fin.ext (by rw [hptj, hpj])]
      exact hF1 j
    · -- j ≥ a
      have hptj : ((Fin.succAbove pt j : Fin (k+2)) : ℕ)
          = (if (j:ℕ) < (k':ℕ)+(j0:ℕ) then (j:ℕ) else (j:ℕ)+1) := by
        rw [succAbove_val, hpt_val]
      rw [hSw_tail j (not_lt.mpr hja), hSx_tail _ (by rw [hptj]; split_ifs <;> omega :
          ¬ ((Fin.succAbove pt j : Fin (k+2)) : ℕ) < (k':ℕ))]
      rw [tailEmb_del_succAbove_gt x c a hab j0 hj0 ⟨(j:ℕ)-(a:ℕ), by omega⟩]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      rw [hptj]
      split_ifs <;> omega
  · -- case B : p ≤ a, so k' = a+1 and c lies in the x-head at k'
    have hk'v : (k':ℕ) = (a:ℕ)+1 := by rw [hk']; exact succAbove_val_le p a hba
    have hσp : (Tuple.sort x) p = c := by rw [hp]; exact Equiv.apply_symm_apply _ _
    have hSpc : Sx p = c := by
      rw [hSx_head p (by omega), hσp]
    have hpt_eq : pt = p := by
      rw [hpt, Equiv.symm_apply_eq]
      exact hSpc.symm
    rcases lt_or_ge ((j:ℕ)) ((a:ℕ)) with hja | hja
    · -- j < a
      rw [hSw_head j hja]
      have hlt : ((Fin.succAbove p j : Fin (k+2)) : ℕ) < (k':ℕ) := by
        rw [succAbove_val p j, hk'v]
        split_ifs <;> omega
      rw [show Sx (Fin.succAbove pt j) = Sx (Fin.succAbove p j) from by rw [hpt_eq],
        hSx_head _ hlt, hF1 j]
    · -- j ≥ a
      have hpj : ((Fin.succAbove p j : Fin (k+2)) : ℕ) = (j:ℕ)+1 :=
        succAbove_val_le p j (by omega)
      rw [hSw_tail j (by omega)]
      rw [show Sx (Fin.succAbove pt j) = Sx (Fin.succAbove p j) from by rw [hpt_eq],
        hSx_tail _ (by rw [hpj, hk'v]; omega :
          ¬ ((Fin.succAbove p j : Fin (k+2)) : ℕ) < (k':ℕ)),
        tailEmb_del_succAbove_le x c a hba ⟨(j:ℕ)-(a:ℕ), by omega⟩]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

end Rel

/-- **The sign identity for the "delete then read" versus "read then delete" pairing** of the
first (sorting) homotopy of Stacks 20.23.6.  With `x : Fin (k+2) → ι`, `c : Fin (k+2)`,
`a : Fin (k+1)`, `k' := Fin.succAbove ((Tuple.sort x).symm c) a` and `b : Fin (k+3)` the
position with `readA x k' b = c`, the `(c,a)`-coefficient of the "delete then read" term equals
the negative of the `(k',b)`-coefficient of the "read then delete" term.  Here `signA y e` is
the sign of the permutation `sigmaA y e` (agreeing with `Tuple.sort y` below `e` and increasing
on the tail `{e, …}`). -/
theorem pairingSign {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ} (x : Fin (k+2) → ι)
    (c : Fin (k+2)) (a : Fin (k+1)) (b : Fin (k+3))
    (hb : Work.DSCOH.Norm.readA x (Fin.succAbove ((Tuple.sort x).symm c) a) b = c) :
    (-1 : ℤ) ^ ((c : ℕ) + (a : ℕ)) * Work.DSCOH.Norm.signA (Work.DSCOH.Norm.del x c) a =
      - ((-1 : ℤ) ^ (((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) + (b : ℕ)) *
          Work.DSCOH.Norm.signA x (Fin.succAbove ((Tuple.sort x).symm c) a)) := by
  set p : Fin (k+2) := (Tuple.sort x).symm c with hp
  set k' : Fin (k+2) := Fin.succAbove p a with hk'
  set Sx : Equiv.Perm (Fin (k+2)) := Work.DSCOH.Norm.sigmaAPerm x k' with hSx
  set Sw : Equiv.Perm (Fin (k+1)) := Work.DSCOH.Norm.sigmaAPerm (Work.DSCOH.Norm.del x c) a with hSw
  set pt : Fin (k+2) := Sx.symm c with hpt
  have hrel : ∀ j : Fin (k+1), Sx (Fin.succAbove pt j) = Fin.succAbove c (Sw j) :=
    sigmaA_succAbove_del x c a
  have hsign : Equiv.Perm.sign Sw = Equiv.Perm.sign Sx * (-1 : ℤˣ) ^ ((c:ℕ) + (pt:ℕ)) := by
    have hcomp : Sx ∘ Fin.succAbove (Sx.symm c) = Fin.succAbove c ∘ Sw := by
      funext j
      simp only [Function.comp_apply]
      exact hrel j
    have h := sign_eq_of_comp_succAbove Sx c Sw hcomp
    rw [← hpt] at h
    exact h
  -- the parity of the exponents
  have hpar : (a:ℕ) + (pt:ℕ) + (k':ℕ) + (b:ℕ) = 2 * ((a:ℕ) + (pt:ℕ)) + 1 := by
    rcases lt_or_ge ((a:ℕ)) ((p:ℕ)) with hab | hba
    · -- degenerate case : a < p
      have hk'v : (k':ℕ) = (a:ℕ) := by rw [hk']; exact succAbove_val_lt p a hab
      have hσp : (Tuple.sort x) p = c := by rw [hp]; exact Equiv.apply_symm_apply _ _
      have hmemT : c ∈ (Work.DSCOH.Norm.headVal x k')ᶜ := by
        rw [Finset.mem_compl, mem_headVal_iff_rank_lt, hk'v]; omega
      obtain ⟨j0, hj0⟩ := Set.mem_range.mp (show c ∈ Set.range (Work.DSCOH.Norm.tailEmb x k') from by
        rw [Work.DSCOH.Norm.tailEmb, Finset.range_orderEmbOfFin]; exact hmemT)
      have hpt_eq : pt = ⟨(k':ℕ)+(j0:ℕ), by have := j0.isLt; omega⟩ := by
        rw [hpt, Equiv.symm_apply_eq]
        let e0 : Fin (k+2) := ⟨(k':ℕ)+(j0:ℕ), by have := j0.isLt; omega⟩
        have hge : ¬ (e0:ℕ) < (k':ℕ) := by simp only [e0, Fin.val_mk]; omega
        rw [hSx, Work.DSCOH.Norm.sigmaAPerm_apply, Work.DSCOH.Norm.sigmaA_tail x k' hge]
        have hidx : (⟨(e0:ℕ)-(k':ℕ), by simp only [e0, Fin.val_mk]; omega⟩ :
            Fin ((k+2)-(k':ℕ))) = j0 := Fin.ext (by simp only [e0, Fin.val_mk]; omega)
        rw [hidx, hj0]
      have hptv : (pt:ℕ) = (k':ℕ)+(j0:ℕ) := by rw [hpt_eq]
      have hbval : (b:ℕ) = (pt:ℕ)+1 := by
        by_cases hble : (b:ℕ) ≤ (k':ℕ)
        · rw [Work.DSCOH.Norm.readA_head x k' hble] at hb
          have hidx : (⟨(b:ℕ), by have := b.isLt; omega⟩ : Fin (k+2)) = p :=
            (Tuple.sort x).injective (hb.trans hσp.symm)
          have hbv : (b:ℕ) = (p:ℕ) := congrArg Fin.val hidx
          omega
        · rw [Work.DSCOH.Norm.readA_tail x k' hble] at hb
          have hidx : (⟨(b:ℕ)-1-(k':ℕ), by have := b.isLt; omega⟩ :
              Fin ((k+2)-(k':ℕ))) = j0 :=
            (Work.DSCOH.Norm.tailEmb x k').injective (hb.trans hj0.symm)
          have hbv : (b:ℕ)-1-(k':ℕ) = (j0:ℕ) := congrArg Fin.val hidx
          omega
      omega
    · -- non-degenerate case : p ≤ a
      have hk'v : (k':ℕ) = (a:ℕ)+1 := by rw [hk']; exact succAbove_val_le p a hba
      have hσp : (Tuple.sort x) p = c := by rw [hp]; exact Equiv.apply_symm_apply _ _
      have hSpc : Sx p = c := by
        rw [hSx, Work.DSCOH.Norm.sigmaAPerm_apply,
          Work.DSCOH.Norm.sigmaA_head x k' (by omega : (p:ℕ) < (k':ℕ))]
        exact hσp
      have hptv : (pt:ℕ) = (p:ℕ) := by
        have hpt_eq : pt = p := by rw [hpt, Equiv.symm_apply_eq]; exact hSpc.symm
        rw [hpt_eq]
      have hbval : (b:ℕ) = (p:ℕ) := by
        by_cases hble : (b:ℕ) ≤ (k':ℕ)
        · rw [Work.DSCOH.Norm.readA_head x k' hble] at hb
          have hidx : (⟨(b:ℕ), by have := b.isLt; omega⟩ : Fin (k+2)) = p :=
            (Tuple.sort x).injective (hb.trans hσp.symm)
          exact congrArg Fin.val hidx
        · rw [Work.DSCOH.Norm.readA_tail x k' hble] at hb
          have hmem : c ∈ Work.DSCOH.Norm.headVal x k' := by
            rw [mem_headVal_iff_rank_lt, ← hp, hk'v]; omega
          exact absurd (hb ▸ hmem) (Work.DSCOH.Norm.tailEmb_mem x k' _)
      omega
  -- the sign identity in `ℤˣ`
  have key : (-1 : ℤˣ) ^ ((c:ℕ) + (a:ℕ)) * Equiv.Perm.sign Sw =
      - ((-1 : ℤˣ) ^ ((k':ℕ) + (b:ℕ)) * Equiv.Perm.sign Sx) := by
    rw [hsign]
    have h1 : (-1 : ℤˣ) ^ ((c:ℕ) + (a:ℕ)) * (-1 : ℤˣ) ^ ((c:ℕ) + (pt:ℕ))
        = (-1 : ℤˣ) ^ ((a:ℕ) + (pt:ℕ)) := by
      rw [← pow_add]
      exact negOne_pow_eq_of_mod_two (by omega)
    have h2 : (-1 : ℤˣ) ^ ((a:ℕ) + (pt:ℕ))
        = - ((-1 : ℤˣ) ^ ((k':ℕ) + (b:ℕ))) := by
      have h3 : (-1 : ℤˣ) ^ ((a:ℕ) + (pt:ℕ))
          = (-1 : ℤˣ) ^ ((k':ℕ) + (b:ℕ) + 1) := negOne_pow_eq_of_mod_two (by omega)
      rw [h3, pow_succ, mul_neg, mul_one]
    calc (-1 : ℤˣ) ^ ((c:ℕ)+(a:ℕ)) * (Equiv.Perm.sign Sx * (-1 : ℤˣ) ^ ((c:ℕ)+(pt:ℕ)))
        = Equiv.Perm.sign Sx * ((-1 : ℤˣ) ^ ((c:ℕ)+(a:ℕ))
            * (-1 : ℤˣ) ^ ((c:ℕ)+(pt:ℕ))) :=
          mul_left_comm _ _ _
      _ = Equiv.Perm.sign Sx * (-1 : ℤˣ) ^ ((a:ℕ)+(pt:ℕ)) := by rw [h1]
      _ = Equiv.Perm.sign Sx * (- ((-1 : ℤˣ) ^ ((k':ℕ)+(b:ℕ)))) := by rw [h2]
      _ = - ((-1 : ℤˣ) ^ ((k':ℕ)+(b:ℕ)) * Equiv.Perm.sign Sx) := by
          rw [mul_neg, mul_comm (Equiv.Perm.sign Sx) ((-1 : ℤˣ) ^ ((k':ℕ)+(b:ℕ)))]
  have hSxA : Work.DSCOH.Norm.signA x k' = ((Equiv.Perm.sign Sx : ℤˣ) : ℤ) := by
    rw [Work.DSCOH.Norm.signA, ← hSx]
  have hSwA : Work.DSCOH.Norm.signA (Work.DSCOH.Norm.del x c) a
      = ((Equiv.Perm.sign Sw : ℤˣ) : ℤ) := by
    rw [Work.DSCOH.Norm.signA, ← hSw]
  rw [hSxA, hSwA]
  have hconv := congrArg (fun u : ℤˣ => (u : ℤ)) key
  simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_one] at hconv
  exact hconv

end Work.DSCOH.Norm.PairSign
