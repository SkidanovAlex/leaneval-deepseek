import Mathlib
import Submission.Work.Peluse.SwapC.concatState
import Submission.Work.Peluse.SwapC.pbox_perm

open scoped BigOperators

namespace Work.Peluse.SwapC

open Work.Peluse
open Work.Peluse.LadderP.Swap
open CC

/-! ## The permutation of the slot index induced by a list permutation

A list permutation `L ~ L'` of two lists of equal length induces a bijection of the index sets
`Fin L.length ≃ Fin L'.length` matching the entries.  This is the elementary combinatorial input of
`cStPerm`: the state `cSt` is a function of the slot *family* `k ↦ (cA q ι (L.get k), cB q ι (L.get k))`
of the slot index, and `pbox_perm` says that this function only sees the family up to a permutation
of the index. -/

/-- **A list permutation is realised by a bijection of the index sets matching the entries.**
For `h : L ~ L'` there is `σ : Fin L.length ≃ Fin L'.length` with `L'.get (σ k) = L.get k` for all
`k`. -/
lemma getEquivOfPerm {α : Type*} {L L' : List α} (h : L.Perm L') :
    ∃ σ : Fin L.length ≃ Fin L'.length, ∀ k : Fin L.length, L'.get (σ k) = L.get k := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun k => k.elim0⟩
  | cons x h ih =>
    rename_i l₁ l₂
    obtain ⟨σ, hσ⟩ := ih
    let f : Fin (l₁.length + 1) → Fin (l₂.length + 1) :=
      fun k => Fin.cases 0 (fun j => (σ j).succ) k
    let g : Fin (l₂.length + 1) → Fin (l₁.length + 1) :=
      fun k => Fin.cases 0 (fun j => (σ.symm j).succ) k
    have hgf : ∀ c, g (f c) = c := by
      intro c
      induction c using Fin.cases with
      | zero => simp [f, g, Fin.cases_zero]
      | succ j => simp [f, g, Fin.cases_succ]
    have hfg : ∀ c, f (g c) = c := by
      intro c
      induction c using Fin.cases with
      | zero => simp [f, g, Fin.cases_zero]
      | succ j => simp [f, g, Fin.cases_succ]
    have hf : Function.Bijective f :=
      ⟨fun a b hab => by
        calc a = g (f a) := (hgf a).symm
          _ = g (f b) := congrArg g hab
          _ = b := hgf b,
       fun b => ⟨g b, hfg b⟩⟩
    refine ⟨Equiv.ofBijective f hf, ?_⟩
    intro k
    show (x :: l₂).get (f k) = (x :: l₁).get k
    induction k using Fin.cases with
    | zero => simp [f, Fin.cases_zero]
    | succ j =>
      simp only [f, Fin.cases_succ, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
      simpa only [List.get_eq_getElem] using hσ j
  | swap x y l =>
    refine ⟨Equiv.swap (0 : Fin (l.length + 2)) 1, ?_⟩
    intro k
    induction k using Fin.cases with
    | zero => simp
    | succ j =>
      induction j using Fin.cases with
      | zero => simp
      | succ i => simp [Equiv.swap_apply_of_ne_of_ne, Fin.succ_ne_zero, Fin.succ_succ_ne_one]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨σ₁, hσ₁⟩ := ih₁
    obtain ⟨σ₂, hσ₂⟩ := ih₂
    exact ⟨σ₁.trans σ₂, fun k => by rw [Equiv.trans_apply, hσ₂ (σ₁ k), hσ₁ k]⟩

/-- **The box norm only sees the slot family up to a bijection of its index set.**  Reindexing the
slot index along `e : Fin d ≃ Fin d'` leaves `pbox` unchanged.  (Proof: `e` forces `d = d'`, after
which `e` is a permutation and `pbox_perm` applies.) -/
lemma pbox_compEquiv {d d' : ℕ} (e : Fin d ≃ Fin d') (q₁ q₂ : Fin d → ℤ) (M : ℕ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    pbox d q₁ q₂ M S f = pbox d' (fun k => q₁ (e.symm k)) (fun k => q₂ (e.symm k)) M S f := by
  have hd : d = d' := by
    have h := Fintype.card_congr e
    simpa using h
  subst hd
  exact (pbox_perm d e.symm q₁ q₂ M S f).symm

/-- **`pbox` of the slot family of a list only depends on the list up to permutation.**  For any
`g : α → ℤ × ℤ` and `h : L ~ L'`, the box norm of the family `k ↦ g (L.get k)` equals that of
`k ↦ g (L'.get k)`. -/
lemma pbox_perm_list {α : Type*} (g : α → ℤ × ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ)
    {L L' : List α} (h : L.Perm L') :
    pbox L.length (fun k => (g (L.get k)).1) (fun k => (g (L.get k)).2) M S f
      = pbox L'.length (fun k => (g (L'.get k)).1) (fun k => (g (L'.get k)).2) M S f := by
  obtain ⟨σ, hσ⟩ := getEquivOfPerm h
  rw [pbox_compEquiv σ (fun k => (g (L.get k)).1) (fun k => (g (L.get k)).2) M S f]
  have h₁ : (fun k : Fin L'.length => (g (L.get (σ.symm k))).1) = fun k => (g (L'.get k)).1 := by
    funext k
    rw [← hσ (σ.symm k), Equiv.apply_symm_apply]
  have h₂ : (fun k : Fin L'.length => (g (L.get (σ.symm k))).2) = fun k => (g (L'.get k)).2 := by
    funext k
    rw [← hσ (σ.symm k), Equiv.apply_symm_apply]
  rw [h₁, h₂]

/-- **The state of the iteration of `Work.Peluse.SwapC.concatAll` only depends on the multiset of
its slots.**  `cSt I q M N f L` is the average, over all index assignments
`ι : (Fin s → Bool) → I`, of the box norm of `f` with the slots `L`, the coefficients of a slot
`CC.raw j a` being `(q (ι a) j, 0)` and those of `CC.dff j a b` being `(q (ι a) j, q (ι b) j)`.

This is `pbox_perm` (`Submission/Work/Peluse/SwapC/pbox_perm.lean`) transported along the permutation
that the list permutation `L.Perm L'` induces on the slot indices `Fin L.length ≃ Fin L'.length`;
both coefficient families are functions of one slot, so a single permutation serves all `ι`. -/
theorem cStPerm (I : Type) [Fintype I] [Nonempty I] {s : ℕ} (q : I → Fin s → ℤ) (M N : ℕ)
    (f : ℤ → ℂ) {L L' : List (CC s)} (h : L.Perm L') : cSt I q M N f L = cSt I q M N f L' := by
  rw [cSt_def, cSt_def]
  congr 1
  funext ι
  exact pbox_perm_list (fun sl : CC s => (cA q ι sl, cB q ι sl)) M (symIcc N) f h

end Work.Peluse.SwapC
