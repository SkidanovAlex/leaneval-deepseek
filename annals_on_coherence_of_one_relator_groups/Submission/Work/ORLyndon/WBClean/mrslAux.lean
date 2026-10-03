import Mathlib
import Submission.Work.OROneRel.mrslDefs
import Submission.Work.OROneRel.rho_magRew
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.mrslExp
import Submission.Work.OROneRel.magRewRel_pow
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.weinbaumDefs


/-!
# Import-hygiene copy of `Submission.Work.OROneRel.mrslAux`

**This file is a verbatim copy** of `Submission/Work/OROneRel/mrslAux.lean`, moved into the *nested*
namespace `Work.OROneRel.WBClean` (so that inside it every unqualified name still resolves through
the parent namespace to the untouched `Work.OROneRel` development).  The reason is *import hygiene*:
the original reaches `Submission.Work.OROneRel.mrslAux`, which redeclares the public theorem
`Work.OROneRel.toWord_pow_of_isCyclicallyReduced` already declared by
`Submission.Work.OROneRel.magnus_step_root` — a dependency of
`Submission.Work.ORLyndon.epsNeZeroDescent` — so no module can import both cones.  Here the
duplicated theorem is renamed `Work.OROneRel.WBClean.toWord_pow_of_isCyclicallyReduced_wbc` and the
imports inside the copied chain are redirected; nothing else is changed.

Consumer: `Submission/Work/ORLyndon/occTerm_distinct_clean.lean`.  Everything in
`Submission/Work/ORLyndon/WBClean/` (and that file) can be deleted as soon as the duplicate
declaration is removed on the `OROneRel` side.
-/
/-!
# Auxiliary lemmas for the decorated transport

* `rewriteAux_add_const` — shifting the starting index of the Magnus rewriting shifts every
  decoration by a constant;
* the decoration shift `mmShiftList` on lists over `({x // x ≠ t} × ℤ)`, with its basic properties;
* `toWord_pow_of_isCyclicallyReduced_wbc` — the word of a power of a cyclically reduced relator is the
  concatenation of the powers of its word;
* `prod_expandLetter_eq_magnusMap` — the product of the words `expandLetter` of a decorated word is
  the Magnus map of that word;
* `magRewRel_conj_pow` — conjugating a relator by a power of `t` shifts the decorations of its
  Magnus rewriting.
-/

open Classical

namespace Work.OROneRel

namespace WBClean

universe u

variable {β : Type u}

/-! ### Shifting the starting index of the rewriting -/

/-- Shifting the starting index of the Magnus rewriting adds a constant to every decoration. -/
theorem rewriteAux_add_const (t : β) (c i : ℤ) (L : List (β × Bool)) :
    rewriteAux t (c + i) L =
      (rewriteAux t i L).map (fun p => ((p.1.1, p.1.2 + c), p.2)) := by
  classical
  induction L generalizing i with
  | nil => rw [rewriteAux.eq_1, rewriteAux.eq_1]; rfl
  | cons p L ih =>
    rw [rewriteAux.eq_def, rewriteAux.eq_def]
    by_cases h : p.1 = t
    · simp only [h, dif_pos]
      rw [Int.add_assoc]
      exact ih (i + (if p.2 then (1 : ℤ) else -1))
    · simp only [h, dif_neg, not_false_eq_true, List.map_cons]
      rw [ih i, Int.add_comm c i]

/-- Shifting the starting index by `c` and starting at `0`. -/
theorem rewriteAux_zero_add (t : β) (c : ℤ) (L : List (β × Bool)) :
    rewriteAux t c L = (rewrite t L).map (fun p => ((p.1.1, p.1.2 + c), p.2)) := by
  have := rewriteAux_add_const t c 0 L
  rw [add_zero] at this
  exact this

/-! ### The decoration shift on decorated words -/

/-- The shift of all decorations of a decorated letter. -/
def mmShift {t : β} (c : ℤ) : ({x : β // x ≠ t} × ℤ) × Bool → ({x : β // x ≠ t} × ℤ) × Bool :=
  fun p => ((p.1.1, p.1.2 + c), p.2)

theorem mmShift_apply {t : β} (c : ℤ) (p : ({x : β // x ≠ t} × ℤ) × Bool) :
    mmShift (t := t) c p = ((p.1.1, p.1.2 + c), p.2) := rfl

theorem mmShift_add {t : β} (c c' : ℤ) :
    mmShift (t := t) c ∘ mmShift (t := t) c' = mmShift (t := t) (c + c') := by
  funext p
  obtain ⟨⟨c₀, i⟩, b⟩ := p
  simp only [Function.comp_apply, mmShift_apply]
  congr 1
  ring

theorem mmShift_zero {t : β} : mmShift (t := t) 0 = id := by
  funext p
  obtain ⟨⟨c₀, i⟩, b⟩ := p
  simp [mmShift_apply]

/-- The shift of all decorations of a list of decorated letters. -/
def mmShiftList (t : β) (c : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    List (({x : β // x ≠ t} × ℤ) × Bool) :=
  D.map (mmShift c)

theorem mmShiftList_length (t : β) (c : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    (mmShiftList t c D).length = D.length := by
  rw [mmShiftList, List.length_map]

theorem mmShiftList_add (t : β) (c c' : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    mmShiftList t c (mmShiftList t c' D) = mmShiftList t (c + c') D := by
  rw [mmShiftList, mmShiftList, mmShiftList, List.map_map, mmShift_add]

theorem mmShiftList_zero (t : β) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    mmShiftList t 0 D = D := by
  rw [mmShiftList, mmShift_zero, List.map_id]

theorem mmShiftList_injective (t : β) (c : ℤ) : Function.Injective (mmShiftList t c) := by
  intro D₁ D₂ h
  have h' := congrArg (mmShiftList t (-c)) h
  rw [mmShiftList_add, mmShiftList_add, neg_add_cancel] at h'
  simpa only [mmShiftList_zero] using h'

theorem mem_mmShiftList {t : β} {c : ℤ} {D : List (({x : β // x ≠ t} × ℤ) × Bool)}
    {p : ({x : β // x ≠ t} × ℤ) × Bool} (h : p ∈ mmShiftList t c D) :
    ∃ q ∈ D, p = ((q.1.1, q.1.2 + c), q.2) := by
  rw [mmShiftList, List.mem_map] at h
  obtain ⟨q, hq, hq'⟩ := h
  exact ⟨q, hq, hq'.symm.trans (mmShift_apply c q)⟩

theorem mmShiftList_flatten_replicate (t : β) (c : ℤ)
    (D : List (({x : β // x ≠ t} × ℤ) × Bool)) (k : ℕ) :
    mmShiftList t c ((List.replicate k D).flatten) =
      (List.replicate k (mmShiftList t c D)).flatten := by
  rw [mmShiftList, mmShiftList, List.map_flatten, List.map_replicate]

/-- The Magnus rewriting of a shifted word is the shift of the Magnus rewriting. -/

theorem mmShiftList_comp (t : β) (c c' : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    (mmShiftList t c D).map (mmShift c') = mmShiftList t (c + c') D := by
  rw [mmShiftList, mmShiftList, List.map_map, mmShift_add, add_comm]

theorem mmShiftList_shift_neg (t : β) (j m : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    (mmShiftList t j D).map (mmShift (-m)) = mmShiftList t (j - m) D := by
  rw [mmShiftList, mmShiftList, List.map_map]
  congr 1
  funext p
  obtain ⟨⟨c₀, i⟩, b⟩ := p
  simp only [Function.comp_apply, mmShift]
  congr 1
  ring_nf

theorem mmShiftList_neg_self (t : β) (m : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    (mmShiftList t m D).map (mmShift (-m)) = D := by
  rw [mmShiftList_shift_neg, sub_self, mmShiftList_zero]

theorem rewriteAux_mmShiftList (t : β) (c : ℤ) (L : List (β × Bool)) :
    rewriteAux t c L = mmShiftList t c (rewrite t L) := by
  rw [rewriteAux_zero_add]
  rfl

theorem magShiftAut_apply_add (t : β) (j₁ j₂ : ℤ)
    (y : FreeGroup ({x : β // x ≠ t} × ℤ)) :
    magShiftAut t j₁ (magShiftAut t j₂ y) = magShiftAut t (j₁ + j₂) y := by
  rw [← MulAut.mul_apply, ← magShiftAut_add]

theorem rewrite_mmShiftList (t : β) (c : ℤ) (L : List (β × Bool)) :
    rewriteAux t c L = mmShiftList t c (rewrite t L) :=
  rewriteAux_zero_add t c L

theorem lift_flatten_replicate {t : β} {γ : Type u}
    (f : ({x : β // x ≠ t} × ℤ) × Bool → γ)
    (D : List (({x : β // x ≠ t} × ℤ) × Bool)) (k : ℕ) :
    ((List.replicate k D).flatten).map f = (List.replicate k (D.map f)).flatten := by
  rw [List.map_flatten, List.map_replicate]

/-! ### Powers of cyclically reduced relators -/

/-- The reduced word of the `k`-th power of a cyclically reduced word `L` is the `k`-fold
concatenation of `L`. -/
theorem toWord_pow_of_isCyclicallyReduced_wbc {γ : Type u} {L : List (γ × Bool)}
    (hL : FreeGroup.IsCyclicallyReduced L) (k : ℕ) :
    FreeGroup.toWord ((FreeGroup.mk L) ^ k) = (List.replicate k L).flatten := by
  rw [FreeGroup.toWord_pow, FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hL.isReduced]
  exact FreeGroup.IsReduced.reduce_eq (hL.flatten_replicate k).isReduced

/-! ### The length of the Magnus rewriting -/

theorem letterCountNot_eq_length_rewrite (t : β) (w : FreeGroup β) :
    letterCountNot t w = (rewrite t (FreeGroup.toWord w)).length := by
  rw [letterCountNot, rewrite, rewriteAux_length, List.countP_eq_length_filter]

/-! ### The expansion lifts the Magnus map -/

/-- The product of the words `expandLetter` of a decorated word is the Magnus map of that word. -/
theorem prod_expandLetter_eq_magnusMap (t : β)
    (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    (D.map (expandLetter t)).prod = magnusMap t (FreeGroup.mk D) := by
  classical
  have h : magnusMap t (FreeGroup.mk D) =
      (D.map (fun x => cond x.2 (magnusMap t (FreeGroup.of x.1))
        ((magnusMap t (FreeGroup.of x.1))⁻¹))).prod := by
    rw [show magnusMap t = FreeGroup.lift (fun p : ({x : β // x ≠ t} × ℤ) =>
      (FreeGroup.of t) ^ p.2 * FreeGroup.of (p.1 : β) * (FreeGroup.of t) ^ (-p.2)) from rfl]
    rw [FreeGroup.lift_mk]
    congr 1
    refine List.map_congr_left ?_
    intro p _
    obtain ⟨⟨c₀, i⟩, b⟩ := p
    cases b <;> simp [magnusMap_apply]
  rw [h]
  congr 1
  refine List.map_congr_left ?_
  intro p _
  obtain ⟨⟨c₀, i⟩, b⟩ := p
  rw [expandLetter]
  cases b
  · simp only [Bool.false_eq_true, reduceIte, cond_false]
    rw [magnusMap_apply]
    group
  · simp only [reduceIte, cond_true]
    rw [magnusMap_apply]
    group

/-! ### Powers of `t` -/

theorem mk_replicate_true (t : β) (k : ℕ) :
    FreeGroup.mk (List.replicate k ((t : β), true)) = (FreeGroup.of t) ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, ← FreeGroup.one_eq_mk, pow_zero]
  | succ k ih =>
    rw [List.replicate_succ, ← List.singleton_append, ← FreeGroup.mul_mk, ih, pow_succ']
    rfl

theorem mk_replicate_false (t : β) (k : ℕ) :
    FreeGroup.mk (List.replicate k ((t : β), false)) = (FreeGroup.of t) ^ (-(k : ℤ)) := by
  rw [show List.replicate k ((t : β), false) = FreeGroup.invRev (List.replicate k ((t : β), true))
      from by rw [FreeGroup.invRev, List.map_replicate, List.reverse_replicate]; rfl]
  rw [← FreeGroup.inv_mk, mk_replicate_true, zpow_neg, zpow_natCast]

theorem mk_runLetters (t : β) (n : ℤ) :
    FreeGroup.mk (runLetters t n) = (FreeGroup.of t) ^ n := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rw [runLetters, decide_eq_false (by omega), mk_replicate_false,
      show (FreeGroup.of t) ^ n = (FreeGroup.of t) ^ (-(n.natAbs : ℤ)) from by
        rw [Int.ofNat_natAbs_of_nonpos hn.le]; ring]
  · subst hn; simp [runLetters, FreeGroup.one_eq_mk]
  · rw [runLetters, decide_eq_true hn, mk_replicate_true, ← zpow_natCast,
      Int.natAbs_of_nonneg hn.le]

/-! ### The Magnus rewriting of a relator, as an element -/

/-- The Magnus rewriting of a word, as an element of the free group: the image of the word under
the Magnus map, with the frame correction `t ^ (-σ_t)`. -/
theorem magnusMap_rewrite (t : β) (X : List (β × Bool)) :
    magnusMap t (FreeGroup.mk (rewrite t X)) =
      FreeGroup.mk X * (FreeGroup.of t) ^ (-(sigmaList t X)) := by
  have h := rho_magRew t 0 X
  rw [rho_eq_magnusMap, magRew_zero_eq_rewrite] at h
  rw [h, ← sigmaList_eq_wordEps]; simp

/-- Two words representing the same element have Magnus rewritings representing the same element. -/
theorem mk_rewrite_eq_of_mk_eq {t : β} {X Y : List (β × Bool)}
    (h : FreeGroup.mk X = FreeGroup.mk Y) :
    FreeGroup.mk (rewrite t X) = FreeGroup.mk (rewrite t Y) := by
  refine (magMagnusMap_injective t) ?_
  rw [magnusMap_rewrite, magnusMap_rewrite]
  have hσ : sigmaList t X = sigmaList t Y := by
    have hx := sigma_mk t X
    have hy := sigma_mk t Y
    rw [h] at hx
    exact Multiplicative.ofAdd.injective (hx.symm.trans hy)
  rw [h, hσ]

/-- Conjugating a relator by a power of `t` shifts the Magnus rewriting. -/
theorem magRewRel_conj_zpow (t : β) (m : ℤ) (g : FreeGroup β) :
    magRewRel t ((FreeGroup.of t) ^ (-m) * g * (FreeGroup.of t) ^ m) =
      magShiftAut t (-m) (magRewRel t g) := by
  have hR : (magShiftAut t (-m)) (FreeGroup.mk (rewrite t (FreeGroup.toWord g))) =
      FreeGroup.mk ((rewrite t (FreeGroup.toWord g)).map
        (fun p : ({x : β // x ≠ t} × ℤ) × Bool => (magShiftBy t (-m) p.1, p.2))) := rfl
  have h1 : FreeGroup.mk (rewrite t (FreeGroup.toWord ((FreeGroup.of t) ^ (-m) * g * (FreeGroup.of t) ^ m)))
      = FreeGroup.mk (rewrite t (runLetters t (-m) ++ FreeGroup.toWord g ++ runLetters t m)) := by
    refine mk_rewrite_eq_of_mk_eq ?_
    rw [FreeGroup.mk_toWord, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, mk_runLetters, mk_runLetters]
    rw [FreeGroup.mk_toWord]
  have h2 : rewrite t (runLetters t (-m) ++ FreeGroup.toWord g ++ runLetters t m)
      = (rewrite t (FreeGroup.toWord g)).map (fun p => (magShiftBy t (-m) p.1, p.2)) := by
    rw [rewrite, List.append_assoc, rewriteAux_append, rewriteAux_runLetters, List.nil_append,
      sigmaList_runLetters, rewriteAux_append, rewriteAux_runLetters, List.append_nil,
      rewriteAux_zero_add]
    refine List.map_congr_left (fun p _ => ?_)
    rw [zero_add]
    rfl
  rw [magRewRel, magRewRel, hR, h1, h2]

end WBClean

end Work.OROneRel
