import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Params.defs
import Submission.Work.Params.sizearith
import Submission.Work.Params.basic
import Submission.Work.Params.qall
import Submission.Work.Params.uparfacts
import Submission.Work.Params.tsfacts
import Submission.Work.Params.rparbig

/-!
# Auxiliary lemmas for the `Params` program

* the lists `t`, `s` handed to `mapList` are determined by the pairwise relation `Forall₂`
  (`forall₂_ss`, `forall₂_ts`), which converts the existential post of `KernelLib.mapList` into an
  exact state;
* `intList` unfolds through a `map`/`bind` coercion, so `intList2` (whose `map` is syntactic) is
  introduced and related to it;
* the branches of the `ifZero` tests inside the two bodies, and the elementary arithmetic needed for
  the cost bounds.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- `ofList` of a list of integer values, in the "explicit `List.map`" form. -/
def intList2 (l : List ℕ) : Val := ofList (l.map (fun m : ℕ => Val.int (m : ℤ)))

theorem intList_eq_intList2 (l : List ℕ) : HvdH.intList l = intList2 l := by
  rw [intList2, HvdH.intList, bind_pure_comp]
  rw [show (Nat.cast <$> l) = List.map (fun m : ℕ => (m : ℤ)) l from rfl]
  rw [List.map_map]
  rfl

theorem intList2_map {l : List ℕ} (g : ℕ → ℕ) :
    intList2 (l.map g) = ofList (l.map (fun k => Val.int (g k : ℤ))) := by
  rw [intList2, List.map_map]
  rfl

theorem range_map_getD (l : List ℕ) (h : l.length = D) :
    (List.range D).map (fun k => l.getD k 0) = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, h]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem l 0 h2

/-! ## The two lists as `getD`s -/

theorem ssPar_getD (n k : ℕ) (hk : k < D) : (ssPar n).getD k 0 =
    (if k < dpar n then upar n + Ffac * (k+1)
     else 2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1)) := by
  rw [ssPar, List.getD_eq_getElem _ _ (by simpa [HvdH.D] using hk)]
  simp [List.getElem_map, List.getElem_range]

theorem tsPar_getD (n k : ℕ) (hk : k < D) : (tsPar n).getD k 0 =
    (if k < dpar n then rpar n / 2 else rpar n) := by
  rw [tsPar, List.getD_eq_getElem _ _ (by simpa [HvdH.D] using hk)]
  simp [List.getElem_map, List.getElem_range]

/-! ## `mapList`: the resulting list is determined -/

theorem forall₂_ss {n : ℕ} {ys : List Val}
    (h : List.Forall₂ (fun x y => ∃ k : ℕ, x = Val.int (k:ℤ) ∧ y = Val.int ((ssPar n).getD k 0 : ℤ))
      ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) ys) :
    ofList ys = HvdH.intList (ssPar n) := by
  have hlen : ys.length = D := by
    have h' := h.length_eq
    rw [List.length_map, List.length_range] at h'
    omega
  have hget : ∀ i (h1 : i < D) (h2 : i < ys.length),
      ys[i] = Val.int ((ssPar n).getD i 0 : ℤ) := by
    intro i h1 h2
    have h3 : i < ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))).length := by
      rw [List.length_map, List.length_range]; exact h1
    obtain ⟨k, hk, hy⟩ := h.get h3 h2
    have hx : ((List.range D).map (fun k : ℕ => Val.int (k:ℤ)))[i] = Val.int (i:ℤ) := by
      rw [List.getElem_map, List.getElem_range]
    have hki : k = i := by
      have hh : Val.int (i:ℤ) = Val.int (k:ℤ) := by rw [← hx]; exact hk
      have h2' : (i:ℤ) = (k:ℤ) := by cases hh; rfl
      have h3' : i = k := Int.ofNat_inj.mp h2'
      omega
    rw [hki] at hy
    exact hy
  have hys : ys = (List.range D).map (fun k : ℕ => Val.int ((ssPar n).getD k 0 : ℤ)) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range]; exact hlen
    · intro i h1 h2
      rw [List.getElem_map, List.getElem_range]
      rw [List.length_map, List.length_range] at h2
      exact hget i h2 h1
  rw [hys, ← intList2_map (g := fun k => (ssPar n).getD k 0),
    range_map_getD (ssPar n) (by simp only [ssPar, List.length_map, List.length_range]),
    ← intList_eq_intList2]

theorem forall₂_ts {n : ℕ} {ys : List Val}
    (h : List.Forall₂ (fun x y => ∃ k : ℕ, x = Val.int (k:ℤ) ∧ y = Val.int ((tsPar n).getD k 0 : ℤ))
      ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) ys) :
    ofList ys = HvdH.intList (tsPar n) := by
  have hlen : ys.length = D := by
    have h' := h.length_eq
    rw [List.length_map, List.length_range] at h'
    omega
  have hget : ∀ i (h1 : i < D) (h2 : i < ys.length),
      ys[i] = Val.int ((tsPar n).getD i 0 : ℤ) := by
    intro i h1 h2
    have h3 : i < ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))).length := by
      rw [List.length_map, List.length_range]; exact h1
    obtain ⟨k, hk, hy⟩ := h.get h3 h2
    have hx : ((List.range D).map (fun k : ℕ => Val.int (k:ℤ)))[i] = Val.int (i:ℤ) := by
      rw [List.getElem_map, List.getElem_range]
    have hki : k = i := by
      have hh : Val.int (i:ℤ) = Val.int (k:ℤ) := by rw [← hx]; exact hk
      have h2' : (i:ℤ) = (k:ℤ) := by cases hh; rfl
      have h3' : i = k := Int.ofNat_inj.mp h2'
      omega
    rw [hki] at hy
    exact hy
  have hys : ys = (List.range D).map (fun k : ℕ => Val.int ((tsPar n).getD k 0 : ℤ)) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range]; exact hlen
    · intro i h1 h2
      rw [List.getElem_map, List.getElem_range]
      rw [List.length_map, List.length_range] at h2
      exact hget i h2 h1
  rw [hys, ← intList2_map (g := fun k => (tsPar n).getD k 0),
    range_map_getD (tsPar n) (by simp only [tsPar, List.length_map, List.length_range]),
    ← intList_eq_intList2]

/-! ## Branches of the bodies -/

/-- The `0`/`1` produced by `lt` has a tiny encoding. -/
theorem isz_ite_le3 (c : Prop) [Decidable c] : isz (if c then (1:ℤ) else 0) ≤ 3 := by
  split_ifs <;> simp [HvdH.isz]

/-- `ifZero` on `lt`'s output, in terms of the natural comparison. -/
theorem ite_lt_swap {k dp : ℕ} (M₁ M₂ : List Val) :
    (if (if ((k:ℤ) < (dp:ℤ)) then (1:ℤ) else 0) = 0 then M₁ else M₂)
      = (if k < dp then M₂ else M₁) := by
  by_cases h : (k:ℤ) < (dp:ℤ)
  · have h' : k < dp := by exact_mod_cast h
    simp [if_pos h, if_pos h']
  · have h' : ¬ k < dp := by
      intro hlt
      exact h (by exact_mod_cast hlt)
    simp [if_neg h, if_neg h']

theorem cons_ite (c : Prop) [Decidable c] (a b : Val) (l : List Val) :
    (if c then a :: l else b :: l) = (if c then a else b) :: l := by
  split_ifs <;> rfl

/-! ## Elementary arithmetic of the parameters -/

theorem krpar_eq (n : ℕ) : (kTpar n + (D - 1)) / D = krpar n := by
  unfold krpar
  congr 1


theorem kT_le_Dkr (n : ℕ) : kTpar n ≤ D * krpar n := by
  have hD : 0 < D := by norm_num [HvdH.D]
  have hdiv := Nat.div_add_mod (kTpar n + D - 1) D
  have hmod := Nat.mod_lt (kTpar n + D - 1) hD
  unfold krpar
  omega

theorem bpar_pos {n : ℕ} (hn : 2 ≤ n) : 0 < bpar n := by
  rw [bpar]
  exact Nat.clog_pos (by norm_num) (by omega)

/-! ## The final cost -/

theorem vsz_ite_lt {a b V : ℕ} (hV : 6 ≤ V) :
    vsz (Val.int (if ((a : ℤ) < (b : ℤ)) then (1:ℤ) else 0)) ≤ V := by
  split_ifs <;> (rw [Work.Main.vsz_int, HvdH.isz]; norm_num; omega)

/-- The final cost: a chain whose cost is `S ≤ 77·W^40` is within `K·(n.size+1)^K`. -/
theorem final_cost {B W K0 S : ℕ} (hW : W = B ^ K0) (hB : 2 ≤ B) (hK0 : 1 ≤ K0)
    (hW100 : 77 ≤ W) (hS : S ≤ 77 * W ^ 40) :
    S ≤ (65536 * K0) * B ^ (65536 * K0) := by
  have h1 : 77 * W ^ 40 ≤ W ^ 41 := by
    calc 77 * W ^ 40 ≤ W * W ^ 40 := Nat.mul_le_mul_right _ hW100
      _ = W ^ 41 := by ring
  have h2 : W ^ 41 = B ^ (41 * K0) := by rw [hW]; ring
  have h3 : 41 * K0 ≤ 65536 * K0 := by nlinarith
  have h4 : B ^ (41 * K0) ≤ B ^ (65536 * K0) := Nat.pow_le_pow_right (by omega) h3
  have h5 : (1:ℕ) ≤ 65536 * K0 := by nlinarith
  calc S ≤ 77 * W ^ 40 := hS
    _ ≤ W ^ 41 := h1
    _ = B ^ (41 * K0) := h2
    _ ≤ B ^ (65536 * K0) := h4
    _ ≤ (65536 * K0) * B ^ (65536 * K0) := Nat.le_mul_of_pos_left _ h5

theorem vsz_intList2_le {l : List ℕ} {B : ℕ} (h : vsz (HvdH.intList l) ≤ B) :
    vsz (intList2 l) ≤ B := by
  rwa [← intList_eq_intList2 l]

theorem znonneg (m : ℕ) : (0:ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m

end Work.Params
