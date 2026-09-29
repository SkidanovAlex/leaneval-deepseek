import Mathlib
import Submission.Work.SynFFT.axisKit
import Submission.Work.SynFFT.zipCatWord
import Submission.Work.SynFFT.mergeLevelWord
import Submission.Work.SynFFT.lenTestWord
import Submission.Work.Kernel.kernelLib
import Submission.Work.Layout.Base

/-!
# `Work.SynFFT.axisMerge`

The merge phase of the synthetic FFT: starting from `stateVal Gs :: rest` (a list of groups encoded
as a value), run `mLevel` (merge adjacent groups row-wise, `zipCat`) repeatedly until a single group
is left, producing `stateVal (mAll Gs) :: rest`; cost `O(vsz (stateVal Gs) * (log (length Gs) + 1))`.

The level word (`Submission.Work.SynFFT.mergeLevelWord`, built on the pairwise row merge
`Submission.Work.SynFFT.zipCatWord`) and the length test (`Submission.Work.SynFFT.lenTestWord`) are
proved separately; this file contains the pure list/size facts and the outer `KernelLib.loop`
assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.SynFFT

open HvdH

/-! ## `ofList` and `vsz` -/

theorem am_ofList_cons_am (x : Val) (xs : List Val) : ofList (x :: xs) = Val.cons x (ofList xs) := rfl
theorem am_ofList_nil_am : ofList ([] : List Val) = Val.nil := rfl
theorem am_vsz_nil_am : vsz (Val.nil : Val) = 1 := rfl

theorem am_vsz_cons_am (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, List.length_cons, List.length_append]

theorem am_vsz_pos (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp [vsz, Val.enc]
  | nil => rw [am_vsz_nil_am]
  | cons a b => rw [am_vsz_cons_am]; omega

theorem am_vsz_ofList_sum (l : List Val) : vsz (ofList l) = (l.map vsz).sum + l.length + 1 := by
  induction l with
  | nil => rw [am_ofList_nil_am, am_vsz_nil_am]; simp
  | cons x xs ih =>
      rw [am_ofList_cons_am, am_vsz_cons_am, ih, List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem am_vsz_ofList_append_add_one (xs ys : List Val) :
    vsz (ofList (xs ++ ys)) + 1 = vsz (ofList xs) + vsz (ofList ys) := by
  induction xs with
  | nil => rw [List.nil_append, am_ofList_nil_am, am_vsz_nil_am]; ring
  | cons x xs ih =>
      rw [List.cons_append, am_ofList_cons_am, am_ofList_cons_am, am_vsz_cons_am, am_vsz_cons_am]
      omega

theorem am_vsz_ofList_append_le (xs ys : List Val) :
    vsz (ofList (xs ++ ys)) ≤ vsz (ofList xs) + vsz (ofList ys) := by
  have h := am_vsz_ofList_append_add_one xs ys
  omega

/-! ## The iteration `iter` of `mLevel` -/

theorem am_mLevel_of_length_le_one {Gs : List (List (List Val))} (h : Gs.length ≤ 1) :
    mLevel Gs = Gs := by
  match Gs with
  | [] => rfl
  | [G] => rfl
  | G₁ :: G₂ :: rest => simp at h

theorem am_iter_of_length_le_one {Gs : List (List (List Val))} (h : Gs.length ≤ 1) (j : ℕ) :
    iter j Gs = Gs := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iter_succ, am_mLevel_of_length_le_one h, ih]

theorem am_iter_succ_am (j : ℕ) (Gs : List (List (List Val))) :
    iter (j + 1) Gs = mLevel (iter j Gs) := by
  induction j generalizing Gs with
  | zero => rfl
  | succ j ih =>
      show iter (j + 1 + 1) Gs = mLevel (iter (j + 1) Gs)
      rw [iter_succ (j + 1) Gs, ih (mLevel Gs), ← iter_succ j Gs]

theorem am_iter_add_am (i : ℕ) : ∀ (j : ℕ) (Gs : List (List (List Val))),
    iter i (iter j Gs) = iter (i + j) Gs := by
  induction i with
  | zero => intro j Gs; simp
  | succ i ih =>
      intro j Gs
      show iter (i + 1) (iter j Gs) = iter (i + 1 + j) Gs
      rw [iter_succ, ← am_iter_succ_am j Gs, ih (j + 1) Gs]
      congr 1
      omega

theorem am_iter_len_le_one_of_len_le (k : ℕ) :
    ∀ (Gs : List (List (List Val))), Gs.length ≤ 2 ^ k → (iter k Gs).length ≤ 1 := by
  induction k with
  | zero => intro Gs h; simpa using h
  | succ k ih =>
      intro Gs h
      rw [iter_succ]
      refine ih (mLevel Gs) ?_
      rw [mLevel_length]
      omega

theorem am_iter_len_ge_two (k : ℕ) (Gs : List (List (List Val)))
    (h : 2 ≤ (iter k Gs).length) : 2 ^ k + 1 ≤ Gs.length := by
  by_contra hc
  have hc' : ¬ (2 ^ k + 1 ≤ Gs.length) := hc
  have hle : Gs.length ≤ 2 ^ k := by omega
  have := am_iter_len_le_one_of_len_le k Gs hle
  omega

theorem am_mAll_len_absorb : ∀ (n : ℕ) (Gs : List (List (List Val))), Gs.length = n →
    (mAll Gs).length ≤ 1 ∧ (2 ≤ Gs.length → mAll Gs = mAll (mLevel Gs)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Gs hn
    by_cases h1 : Gs.length ≤ 1
    · have hGs : mAll Gs = Gs := am_iter_of_length_le_one h1 Gs.length
      exact ⟨by rw [hGs]; omega, fun h2 => absurd h2 (by omega)⟩
    · have h2 : 2 ≤ Gs.length := by omega
      have hmL : (mLevel Gs).length < Gs.length := by rw [mLevel_length]; omega
      obtain ⟨ih1, -⟩ := ih (mLevel Gs).length (by omega) (mLevel Gs) rfl
      have hk'' : (mLevel Gs).length ≤ n - 1 := by
        have : (mLevel Gs).length < n := by rw [← hn]; exact hmL
        omega
      have hA : iter n Gs = iter (n - 1) (mLevel Gs) := by
        rw [show n = (n - 1) + 1 from by omega]
        exact iter_succ (n - 1) Gs
      have hB : iter (n - 1) (mLevel Gs) =
          iter (n - 1 - (mLevel Gs).length) (mAll (mLevel Gs)) := by
        have h3 : iter (n - 1 - (mLevel Gs).length) (iter (mLevel Gs).length (mLevel Gs))
            = iter (n - 1) (mLevel Gs) := by
          rw [am_iter_add_am (n - 1 - (mLevel Gs).length) (mLevel Gs).length (mLevel Gs)]
          rw [Nat.sub_add_cancel hk'']
        exact h3.symm
      have hC : iter (n - 1 - (mLevel Gs).length) (mAll (mLevel Gs)) = mAll (mLevel Gs) :=
        am_iter_of_length_le_one ih1 _
      have hmAll : mAll Gs = mAll (mLevel Gs) := by
        have h1' : mAll Gs = iter n Gs := by
          rw [show mAll Gs = iter Gs.length Gs from rfl, hn]
        rw [h1', hA, hB, hC]
      exact ⟨by rw [hmAll]; exact ih1, fun _ => hmAll⟩

theorem am_mAll_length_le_one (Gs : List (List (List Val))) : (mAll Gs).length ≤ 1 :=
  (am_mAll_len_absorb Gs.length Gs rfl).1

theorem am_mAll_mLevel_eq (Gs : List (List (List Val))) (h : 2 ≤ Gs.length) :
    mAll Gs = mAll (mLevel Gs) := (am_mAll_len_absorb Gs.length Gs rfl).2 h

theorem am_iter_length_eq_mAll {k : ℕ} {Gs : List (List (List Val))} (h : Gs.length ≤ k) :
    iter k Gs = mAll Gs := by
  have h1 : iter (k - Gs.length) (iter Gs.length Gs) = iter k Gs := by
    rw [am_iter_add_am]; congr 1; omega
  rw [← h1, show iter Gs.length Gs = mAll Gs from rfl]
  exact am_iter_of_length_le_one (am_mAll_length_le_one Gs) _

theorem am_mAll_of_length_le_one {Gs : List (List (List Val))} (h : Gs.length ≤ 1) :
    mAll Gs = Gs := am_iter_of_length_le_one h Gs.length

/-- If the merge iteration has already collapsed, it is `mAll`. -/
theorem am_iter_eq_mAll_of_len_le_one {Gs : List (List (List Val))} {k : ℕ}
    (h : (iter k Gs).length ≤ 1) : iter k Gs = mAll Gs := by
  by_cases hle : Gs.length ≤ k
  · exact am_iter_length_eq_mAll hle
  · have hk : k < Gs.length := Nat.not_le.mp hle
    have h1 : iter (Gs.length - k) (iter k Gs) = iter Gs.length Gs := by
      rw [am_iter_add_am (Gs.length - k) k Gs]
      rw [Nat.sub_add_cancel (by omega)]
    calc iter k Gs = iter (Gs.length - k) (iter k Gs) :=
          (am_iter_of_length_le_one h (Gs.length - k)).symm
      _ = iter Gs.length Gs := h1
      _ = mAll Gs := rfl

/-! ## Encoding sizes -/

/-- Weight of a group (list of rows). -/
def amGwt (G : List (List Val)) : ℕ := (G.map fun r => vsz (ofList r) + 1).sum

/-- Weight of a list of groups. -/
def amSwt (Gs : List (List (List Val))) : ℕ := (Gs.map fun G => vsz (grpVal G) + 1).sum

theorem am_sum_map_add_one {α : Type} (l : List α) (f : α → ℕ) :
    (l.map (fun x => f x + 1)).sum = (l.map f).sum + l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring_nf

theorem am_sum_map_vsz_ofList (G : List (List Val)) :
    ((G.map ofList).map vsz).sum = (G.map (fun r => vsz (ofList r))).sum := by
  induction G with
  | nil => simp
  | cons r rs ih => simp only [List.map_cons, List.sum_cons, ih]

theorem am_sum_map_vsz_grpVal (Gs : List (List (List Val))) :
    ((Gs.map grpVal).map vsz).sum = (Gs.map (fun G => vsz (grpVal G))).sum := by
  induction Gs with
  | nil => simp
  | cons r rs ih => simp only [List.map_cons, List.sum_cons, ih]

theorem am_vsz_grpVal (G : List (List Val)) : vsz (grpVal G) = amGwt G + 1 := by
  have h1 : vsz (grpVal G) = ((G.map ofList).map vsz).sum + (G.map ofList).length + 1 := by
    rw [grpVal, am_vsz_ofList_sum]
  have h2 : ((G.map ofList).map vsz).sum = (G.map (fun r => vsz (ofList r))).sum :=
    am_sum_map_vsz_ofList G
  have h2len : (G.map ofList).length = G.length := by simp
  have h3 : (G.map (fun r => vsz (ofList r) + 1)).sum
      = (G.map (fun r => vsz (ofList r))).sum + G.length :=
    am_sum_map_add_one G (fun r => vsz (ofList r))
  have hg : amGwt G = (G.map (fun r => vsz (ofList r) + 1)).sum := rfl
  rw [h1, h2, h2len, hg, h3]

theorem am_vsz_stateVal (Gs : List (List (List Val))) : vsz (stateVal Gs) = amSwt Gs + 1 := by
  have h1 : vsz (stateVal Gs) = ((Gs.map grpVal).map vsz).sum + (Gs.map grpVal).length + 1 := by
    rw [stateVal, am_vsz_ofList_sum]
  have h2 : ((Gs.map grpVal).map vsz).sum = (Gs.map (fun G => vsz (grpVal G))).sum :=
    am_sum_map_vsz_grpVal Gs
  have h2len : (Gs.map grpVal).length = Gs.length := by simp
  have h3 : (Gs.map (fun G => vsz (grpVal G) + 1)).sum
      = (Gs.map (fun G => vsz (grpVal G))).sum + Gs.length :=
    am_sum_map_add_one Gs (fun G => vsz (grpVal G))
  have hg : amSwt Gs = (Gs.map (fun G => vsz (grpVal G) + 1)).sum := rfl
  rw [h1, h2, h2len, hg, h3]

theorem am_gwt_cons (r : List Val) (G : List (List Val)) :
    amGwt (r :: G) = (vsz (ofList r) + 1) + amGwt G := by
  simp only [amGwt, List.map_cons, List.sum_cons]

theorem am_swt_cons (G : List (List Val)) (Gs : List (List (List Val))) :
    amSwt (G :: Gs) = (vsz (grpVal G) + 1) + amSwt Gs := by
  simp only [amSwt, List.map_cons, List.sum_cons]

theorem am_gwt_zipCat_le (G₁ G₂ : List (List Val)) :
    amGwt (zipCat G₁ G₂) ≤ amGwt G₁ + amGwt G₂ + 1 := by
  induction G₁ generalizing G₂ with
  | nil =>
      rw [zipCat_nil_left]
      have h0 : amGwt ([] : List (List Val)) = 0 := rfl
      omega
  | cons r₁ t₁ ih =>
      cases G₂ with
      | nil =>
          rw [zipCat_nil_right]
          have h0 : amGwt ([] : List (List Val)) = 0 := rfl
          omega
      | cons r₂ t₂ =>
          have hih := ih t₂
          have h2 := am_vsz_ofList_append_le r₁ r₂
          rw [show zipCat (r₁ :: t₁) (r₂ :: t₂) = (r₁ ++ r₂) :: zipCat t₁ t₂ from rfl]
          rw [am_gwt_cons, am_gwt_cons, am_gwt_cons]
          omega

theorem am_vsz_grpVal_zipCat_le (G₁ G₂ : List (List Val)) :
    vsz (grpVal (zipCat G₁ G₂)) ≤ vsz (grpVal G₁) + vsz (grpVal G₂) := by
  rw [am_vsz_grpVal, am_vsz_grpVal, am_vsz_grpVal]
  have := am_gwt_zipCat_le G₁ G₂
  omega

theorem am_swt_mLevel_le : ∀ (Gs : List (List (List Val))), amSwt (mLevel Gs) ≤ amSwt Gs
  | [] => le_rfl
  | [G] => le_rfl
  | G₁ :: G₂ :: rest => by
      have ih := am_swt_mLevel_le rest
      have h := am_vsz_grpVal_zipCat_le G₁ G₂
      rw [mLevel_cons_cons, am_swt_cons, am_swt_cons, am_swt_cons]
      omega

theorem am_vsz_stateVal_mLevel_le (Gs : List (List (List Val))) :
    vsz (stateVal (mLevel Gs)) ≤ vsz (stateVal Gs) := by
  rw [am_vsz_stateVal, am_vsz_stateVal]
  have := am_swt_mLevel_le Gs
  omega

theorem am_vsz_stateVal_iter_le : ∀ (k : ℕ) (Gs : List (List (List Val))),
    vsz (stateVal (iter k Gs)) ≤ vsz (stateVal Gs)
  | 0, Gs => le_rfl
  | k + 1, Gs => by
      rw [am_iter_succ_am]
      exact le_trans (am_vsz_stateVal_mLevel_le (iter k Gs)) (am_vsz_stateVal_iter_le k Gs)

/-- `2 ^ n` is at least one. -/
theorem am_one_le_two_pow (n : ℕ) : 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- Bit-size bound: `2 ^ j ≤ n` forces `j ≤ n.size`. -/
theorem am_le_size_of_two_pow_le {j n : ℕ} (hn : 1 ≤ n) (h : 2 ^ j ≤ n) : j ≤ n.size := by
  by_contra hc
  have hc' : ¬ (j ≤ n.size) := hc
  have hj : n.size + 1 ≤ j := by omega
  have hlt : n < 2 ^ n.size := Nat.size_le.mp le_rfl
  have h1 : 2 ^ (n.size + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have h2 : 2 ^ (n.size + 1) = 2 * 2 ^ n.size := by rw [pow_succ, Nat.mul_comm]
  omega

/-! ## Cost arithmetic for the level loop -/

/-- Cost of one loop round, given the two size bounds on the intermediate states. -/
theorem am_cost_body_le (K₁ K₂ KL V W₁ W₂ : ℕ) (h1 : W₁ ≤ V) (h2 : W₂ ≤ V) :
    K₁ * (W₁ + 1) + K₁ + (K₂ * (W₂ + 1) + K₂) ≤
      (2 * (K₁ + K₂ + 1) + KL) * (V + 1) := by
  have hV : 1 ≤ V + 1 := by omega
  have e1 : K₁ * (W₁ + 1) ≤ K₁ * (V + 1) := Nat.mul_le_mul le_rfl (by omega)
  have e2 : K₂ * (W₂ + 1) ≤ K₂ * (V + 1) := Nat.mul_le_mul le_rfl (by omega)
  have e3 : K₁ ≤ K₁ * (V + 1) := by
    calc K₁ = K₁ * 1 := (Nat.mul_one K₁).symm
      _ ≤ K₁ * (V + 1) := Nat.mul_le_mul le_rfl hV
  have e4 : K₂ ≤ K₂ * (V + 1) := by
    calc K₂ = K₂ * 1 := (Nat.mul_one K₂).symm
      _ ≤ K₂ * (V + 1) := Nat.mul_le_mul le_rfl hV
  calc K₁ * (W₁ + 1) + K₁ + (K₂ * (W₂ + 1) + K₂)
      ≤ K₁ * (V + 1) + K₁ * (V + 1) + (K₂ * (V + 1) + K₂ * (V + 1)) := by omega
    _ = 2 * (K₁ + K₂) * (V + 1) := by ring
    _ ≤ 2 * (K₁ + K₂ + 1) * (V + 1) := by
        have h : 2 * (K₁ + K₂) ≤ 2 * (K₁ + K₂ + 1) := by omega
        exact Nat.mul_le_mul h (le_rfl : V + 1 ≤ V + 1)
    _ ≤ (2 * (K₁ + K₂ + 1) + KL) * (V + 1) := by
        have h : 2 * (K₁ + K₂ + 1) ≤ 2 * (K₁ + K₂ + 1) + KL := by omega
        exact Nat.mul_le_mul h (le_rfl : V + 1 ≤ V + 1)

theorem am_mergeLoop_cost (K₁ K₂ KL V s : ℕ) :
    (s + 2) * ((2 * (K₁ + K₂ + 1) + KL) * (V + 1) + KL) + KL ≤
      20 * (K₁ + K₂ + 1 + KL) * (V + 1) * (s + 1) + 20 * (K₁ + K₂ + 1 + KL) := by
  set P : ℕ := K₁ + K₂ + 1 + KL with hP
  set E : ℕ := 2 * (K₁ + K₂ + 1) + KL with hE
  have hV : 1 ≤ V + 1 := by omega
  have hVs : 1 ≤ s + 1 := by omega
  have hEs : E ≤ 2 * P := by rw [hE, hP]; omega
  have hKL1 : KL ≤ E * (V + 1) := by
    have h1 : KL ≤ E := by rw [hE]; omega
    have h2 : E ≤ E * (V + 1) := by
      calc E = E * 1 := (Nat.mul_one E).symm
        _ ≤ E * (V + 1) := Nat.mul_le_mul le_rfl hV
    omega
  have hKL2 : KL ≤ P * (V + 1) * (s + 1) := by
    have h1 : KL ≤ P := by rw [hP]; omega
    have h2 : P ≤ P * (V + 1) * (s + 1) := by
      calc P = P * 1 * 1 := by ring
        _ ≤ P * (V + 1) * (s + 1) := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hV) hVs
    omega
  have step1 : (s + 2) * (E * (V + 1) + KL) + KL ≤ (s + 2) * (2 * (E * (V + 1))) + KL := by
    have h : E * (V + 1) + KL ≤ 2 * (E * (V + 1)) := by omega
    exact Nat.add_le_add_right (Nat.mul_le_mul (le_rfl : s + 2 ≤ s + 2) h) KL
  have step2 : (s + 2) * (2 * (E * (V + 1))) + KL
      ≤ (2 * (s + 1)) * (2 * (2 * P * (V + 1))) + KL := by
    have h1 : E * (V + 1) ≤ 2 * P * (V + 1) := Nat.mul_le_mul hEs le_rfl
    have h2 : 2 * (E * (V + 1)) ≤ 2 * (2 * P * (V + 1)) := by omega
    have h3 : s + 2 ≤ 2 * (s + 1) := by omega
    exact Nat.add_le_add_right (Nat.mul_le_mul h3 h2) KL
  have step3 : (2 * (s + 1)) * (2 * (2 * P * (V + 1))) + KL
      = 8 * P * (V + 1) * (s + 1) + KL := by ring
  have step4 : 8 * P * (V + 1) * (s + 1) + KL
      ≤ 8 * P * (V + 1) * (s + 1) + P * (V + 1) * (s + 1) := Nat.add_le_add_left hKL2 _
  have step5 : 8 * P * (V + 1) * (s + 1) + P * (V + 1) * (s + 1)
      = 9 * P * (V + 1) * (s + 1) := by ring
  have step6 : 9 * P * (V + 1) * (s + 1) ≤ 20 * P * (V + 1) * (s + 1) + 20 * P := by
    have h1 : 9 * P * (V + 1) * (s + 1) ≤ 20 * P * (V + 1) * (s + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega : 9 * P ≤ 20 * P) le_rfl) le_rfl
    omega
  calc (s + 2) * (E * (V + 1) + KL) + KL
      ≤ (s + 2) * (2 * (E * (V + 1))) + KL := step1
    _ ≤ (2 * (s + 1)) * (2 * (2 * P * (V + 1))) + KL := step2
    _ = 8 * P * (V + 1) * (s + 1) + KL := step3
    _ ≤ 8 * P * (V + 1) * (s + 1) + P * (V + 1) * (s + 1) := step4
    _ = 9 * P * (V + 1) * (s + 1) := step5
    _ ≤ 20 * P * (V + 1) * (s + 1) + 20 * P := step6

/-! ## The outer loop -/

/-- Assembly: the merge loop, given a level word and a length test. -/
theorem axisMerge_of
    (hlev : ∃ (prog : Cmd) (K : ℕ),
      ∀ (main : Cmd) (Gs : List (List (List Val))) (rest : List Val),
        WordR main prog (fun vs => vs = stateVal Gs :: rest)
          (fun _ out => out = stateVal (mLevel Gs) :: rest)
          (fun _ => K * (vsz (stateVal Gs) + 1) + K))
    (htest : ∃ (prog : Cmd) (K : ℕ),
      ∀ (main : Cmd) (Gs : List (List (List Val))) (rest : List Val),
        WordR main prog (fun vs => vs = stateVal Gs :: rest)
          (fun _ out => (Gs.length ≤ 1 → out = Val.int 0 :: stateVal Gs :: rest) ∧
            (2 ≤ Gs.length → out = Val.int 1 :: stateVal Gs :: rest))
          (fun _ => K * (vsz (stateVal Gs) + 1) + K)) :
    ∃ (prog : Cmd) (K : ℕ),
      ∀ (main : Cmd) (Gs : List (List (List Val))) (rest : List Val),
        WordR main prog (fun vs => vs = stateVal Gs :: rest)
          (fun _ out => out = stateVal (mAll Gs) :: rest)
          (fun _ => K * (vsz (stateVal Gs) + 1) * (Gs.length.size + 1) + K) := by
  obtain ⟨plev, K₁, hlev⟩ := hlev
  obtain ⟨ptest, K₂, htest⟩ := htest
  obtain ⟨comb, KL, hloop⟩ := Work.Kernel.kernelLib.loop
  refine ⟨comb (.seq plev ptest), 20 * (K₁ + K₂ + 1 + KL), ?_⟩
  intro main Gs rest
  have hbody : ∀ (i : ℕ) (vs : List Val),
      (∃ H : List (List (List Val)), vs = stateVal H :: rest ∧ H = iter i Gs) →
      WordR main (.seq plev ptest) (fun w => w = vs)
        (fun _ out => ∃ vs', (out = Val.int 0 :: vs' ∧ vs' = stateVal (mAll Gs) :: rest) ∨
          (out = Val.int 1 :: vs' ∧ (∃ H : List (List (List Val)),
            vs' = stateVal H :: rest ∧ H = iter (i + 1) Gs) ∧
            i + 1 < (Gs.length).size + 1))
        (fun _ => (2 * (K₁ + K₂ + 1) + KL) * (vsz (stateVal Gs) + 1)) := by
    intro i vs hI
    obtain ⟨H, rfl, hH⟩ := hI
    have hH' : mLevel H = iter (i + 1) Gs := by rw [hH, am_iter_succ_am]
    have hA : vsz (stateVal H) ≤ vsz (stateVal Gs) := by
      rw [hH]; exact am_vsz_stateVal_iter_le i Gs
    have hB : vsz (stateVal (mLevel H)) ≤ vsz (stateVal Gs) := by
      rw [hH']; exact am_vsz_stateVal_iter_le (i + 1) Gs
    have h1 : WordR main plev (fun w => w = stateVal H :: rest)
        (fun _ out => out = stateVal (mLevel H) :: rest)
        (fun _ => K₁ * (vsz (stateVal H) + 1) + K₁) := hlev main H rest
    have h2 : WordR main ptest (fun w => w = stateVal (mLevel H) :: rest)
        (fun _ out => ((mLevel H).length ≤ 1 → out = Val.int 0 :: stateVal (mLevel H) :: rest) ∧
          (2 ≤ (mLevel H).length → out = Val.int 1 :: stateVal (mLevel H) :: rest))
        (fun _ => K₂ * (vsz (stateVal (mLevel H)) + 1) + K₂) := htest main (mLevel H) rest
    have hseq := Work.Kernel.WordR_seq (main := main) (p := plev) (q := ptest)
      (P := fun w => w = stateVal H :: rest)
      (Q := fun _ out => out = stateVal (mLevel H) :: rest)
      (C := fun _ => K₁ * (vsz (stateVal H) + 1) + K₁)
      (P' := fun w => w = stateVal (mLevel H) :: rest)
      (Q' := fun _ out => ((mLevel H).length ≤ 1 → out = Val.int 0 :: stateVal (mLevel H) :: rest) ∧
        (2 ≤ (mLevel H).length → out = Val.int 1 :: stateVal (mLevel H) :: rest))
      (C' := fun _ => K₂ * (vsz (stateVal (mLevel H)) + 1) + K₂)
      (B := fun _ => K₂ * (vsz (stateVal (mLevel H)) + 1) + K₂)
      h1 h2 (fun vs0 mid hP hQ => ⟨hQ, le_rfl⟩)
    refine Work.Kernel.WordR_conseq (p := .seq plev ptest) hseq ?_ ?_ ?_
    · intro w hw; exact hw
    · intro w out hw hpost
      obtain ⟨-, hmid, hle1, hle2⟩ := hpost
      by_cases hlen : (mLevel H).length ≤ 1
      · have hmall : mLevel H = mAll Gs := by
          rw [hH']
          exact am_iter_eq_mAll_of_len_le_one (by rw [← hH']; exact hlen)
        exact ⟨stateVal (mLevel H) :: rest, Or.inl ⟨hle1 hlen, by rw [hmall]⟩⟩
      · have h2le : 2 ≤ (mLevel H).length := by omega
        have hge : 2 ^ (i + 1) + 1 ≤ Gs.length := by
          exact am_iter_len_ge_two (i + 1) Gs (by rw [← hH']; exact h2le)
        have hge' : 2 ^ (i + 1) ≤ Gs.length := by
          have h := hge
          generalize hQ : 2 ^ (i + 1) = P at h ⊢
          omega
        have hsz : i + 1 ≤ (Gs.length).size :=
          am_le_size_of_two_pow_le (j := i + 1) (n := Gs.length)
            (le_trans (am_one_le_two_pow (i + 1)) hge') hge'
        have hI' : ∃ H' : List (List (List Val)),
            stateVal (mLevel H) :: rest = stateVal H' :: rest ∧ H' = iter (i + 1) Gs :=
          ⟨mLevel H, rfl, hH'⟩
        exact ⟨stateVal (mLevel H) :: rest,
          Or.inr ⟨hle2 h2le, hI', by omega⟩⟩
    · intro w hw
      exact am_cost_body_le K₁ K₂ KL (vsz (stateVal Gs)) (vsz (stateVal H))
        (vsz (stateVal (mLevel H))) hA hB
  have hloop' := hloop main (.seq plev ptest)
    (fun i vs => ∃ H : List (List (List Val)), vs = stateVal H :: rest ∧ H = iter i Gs)
    (fun vs => vs = stateVal (mAll Gs) :: rest)
    ((2 * (K₁ + K₂ + 1) + KL) * (vsz (stateVal Gs) + 1))
    ((Gs.length).size + 1) hbody
  refine Work.Kernel.WordR_conseq (p := comb (.seq plev ptest)) hloop' ?_ ?_ ?_
  · intro vs hvs
    exact ⟨Gs, hvs, rfl⟩
  · intro vs out hvs hpost; exact hpost
  · intro vs hvs
    exact am_mergeLoop_cost K₁ K₂ KL (vsz (stateVal Gs)) (Gs.length).size

/-! ## The target -/

theorem axisMerge : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd)
    (Gs : List (List (List HvdH.Val))) (rest : List HvdH.Val),
  HvdH.WordR main prog
    (fun vs => vs = stateVal Gs :: rest)
    (fun _ out => out = stateVal (mAll Gs) :: rest)
    (fun _ => K * (HvdH.vsz (stateVal Gs) + 1) * (Gs.length.size + 1) + K) := by
  exact axisMerge_of (mergeLevelWord zipCatWord) lenTestWord

end Work.SynFFT
