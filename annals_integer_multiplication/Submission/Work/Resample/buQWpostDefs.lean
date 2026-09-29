import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWelemWord
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPreKit
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auMapListTail
import Submission.Work.Resample.buZipWithFun

/-!
# `Work.Resample.buQWpostDefs`: the list-level element maps of the post-round word

The word `Work.Resample.buQWpostWord` takes the window
`[cvecVal z, int σ, cvecVal v, cvecVal acc, int s, int p]`
to
`[cvecVal (buTdivV p z), cvecVal (buAddV acc (buSMulV σ (buTdivV p z)))]`.

It is built from two `KernelLib` combinators (`mapList` over `z` with the element map
`cfxVal a ↦ cfxVal (aᵢ /ᵗ 2^p)`, and `zipWith` of `acc` with the divided vector with the element
map `cfxVal a, cfxVal b ↦ cfxVal (a + σ b)`), glued by `roll`/`dup`/`drop` moves of the fixed
window.

This module fixes the two element maps as `Val`-level functions (`buShrF p`, `buLinF σ`) and proves
the pure list identities
* `(z.map cfxVal).map (buShrF p) = (buTdivV p z).map cfxVal`,
* `List.zipWith (buLinF σ) (acc.map cfxVal) (z.map cfxVal) = (buAddV acc (buSMulV σ z)).map cfxVal`
  (for `acc.length = z.length`),
which identify the outputs of the two combinators with the list-level functions `buTdivV`,
`buAddV`, `buSMulV` of `buQWdefs.lean`.  It also records the size arithmetic used by the cost
estimate of the assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## the two element maps -/

/-- The element map of `buTdivV p` on complex values: `cfxVal a ↦ cfxVal (aᵢ /ᵗ 2^p)`; on any
non-pair value it is the identity (it is only ever applied to `cfxVal`s). -/
def buShrF (p : ℕ) : Val → Val
  | Val.cons (Val.int x) (Val.int y) =>
      HvdH.cfxVal (Int.tdiv x ((2 : ℤ) ^ p), Int.tdiv y ((2 : ℤ) ^ p))
  | v => v

/-- The element map of the accumulation `acc + σ • z` on complex values. -/
def buLinF (σ : ℤ) : Val → Val → Val
  | Val.cons (Val.int x1) (Val.int x2), Val.cons (Val.int y1) (Val.int y2) =>
      HvdH.cfxVal (x1 + σ * y1, x2 + σ * y2)
  | _, _ => Val.nil

theorem buShrF_cfxVal (p : ℕ) (a : ℤ × ℤ) :
    buShrF p (HvdH.cfxVal a) = HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ p),
      Int.tdiv a.2 ((2 : ℤ) ^ p)) := rfl

theorem buLinF_cfxVal (σ : ℤ) (a b : ℤ × ℤ) :
    buLinF σ (HvdH.cfxVal a) (HvdH.cfxVal b) = HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2) := rfl

/-! ## the list identities -/

/-- `buShrF p` on `cfxVal`s is `buTdivV p`, as a list map. -/
theorem buShrF_map (p : ℕ) (z : List (ℤ × ℤ)) :
    (z.map HvdH.cfxVal).map (buShrF p) = (buTdivV p z).map HvdH.cfxVal := by
  induction z with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, buShrF_cfxVal, buTdivV, ih]

/-- `buAddV` of a mapped second argument is a `zipWith`. -/
theorem buAddV_map_eq (f : ℤ × ℤ → ℤ × ℤ) : ∀ (acc z : List (ℤ × ℤ)), acc.length = z.length →
    buAddV acc (z.map f) = List.zipWith (fun a b => (a.1 + (f b).1, a.2 + (f b).2)) acc z
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      have h' : as.length = bs.length := by simpa using h
      simp only [List.map_cons, buAddV, List.zipWith_cons_cons, buAddV_map_eq f as bs h']

/-- `buAddV` with `buSMulV σ` is a `zipWith`. -/
theorem buAddV_smul_eq (σ : ℤ) (acc z : List (ℤ × ℤ)) (h : acc.length = z.length) :
    buAddV acc (buSMulV σ z) = List.zipWith (fun a b => (a.1 + σ * b.1, a.2 + σ * b.2)) acc z :=
  buAddV_map_eq (fun b => (σ * b.1, σ * b.2)) acc z h

/-- `zipWith` of two `cfxVal`-mapped lists is the `cfxVal`-map of the pair-level `zipWith`. -/
theorem zipWith_cfxVal_map (σ : ℤ) (acc z : List (ℤ × ℤ)) :
    List.zipWith (buLinF σ) (acc.map HvdH.cfxVal) (z.map HvdH.cfxVal)
      = (List.zipWith (fun a b => (a.1 + σ * b.1, a.2 + σ * b.2)) acc z).map HvdH.cfxVal := by
  induction acc generalizing z with
  | nil => cases z <;> rfl
  | cons a as ih =>
      cases z with
      | nil => rfl
      | cons b bs =>
          simp only [List.map_cons, List.zipWith_cons_cons, buLinF_cfxVal, ih bs]

/-- The element map of the accumulation, at the level of lists. -/
theorem buZipAdd_eq (σ : ℤ) (acc z : List (ℤ × ℤ)) (h : acc.length = z.length) :
    List.zipWith (buLinF σ) (acc.map HvdH.cfxVal) (z.map HvdH.cfxVal)
      = (buAddV acc (buSMulV σ z)).map HvdH.cfxVal := by
  rw [buAddV_smul_eq σ acc z h, zipWith_cfxVal_map]

/-! ## size arithmetic -/

/-- The size of a `cfxVal` whose coordinates have `isz ≤ M`. -/
theorem vsz_cfxVal_le' {M : ℕ} {z : ℤ × ℤ} (h1 : isz z.1 ≤ M) (h2 : isz z.2 ≤ M) :
    vsz (HvdH.cfxVal z) ≤ 2 * M + 1 := by
  rw [Work.Fx.vsz_cfxVal]; omega

/-- The size of a vector of complex values whose coordinates have `isz ≤ M`. -/
theorem vsz_cvecVal_le' {M : ℕ} {u : List (ℤ × ℤ)}
    (h : ∀ z ∈ u, isz z.1 ≤ M ∧ isz z.2 ≤ M) :
    vsz (HvdH.cvecVal u) ≤ (u.length + 1) * (2 * M + 2) := by
  have h1 : ∀ v ∈ u.map HvdH.cfxVal, vsz v ≤ 2 * M + 1 := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    exact vsz_cfxVal_le' (h z hz).1 (h z hz).2
  have h2 := vsz_ofList_le (l := u.map HvdH.cfxVal) (B := 2 * M + 1) h1
  simpa [HvdH.cvecVal, List.length_map] using h2

/-- `2^22 · S · m` is absorbed by the final constant `2^(2^S+80)`. -/
theorem buPost_absorb {S m : ℕ} (hS : 40 ≤ S) :
    2 ^ 22 * S * m ≤ 2 ^ (2 ^ S + 80) * m := by
  have hS2 : S ≤ 2 ^ S := le_of_lt (Nat.lt_two_pow_self (n := S))
  have h1 : 2 ^ 22 * S ≤ 2 ^ 22 * 2 ^ S := Nat.mul_le_mul_left _ hS2
  have h2 : (2 : ℕ) ^ 22 * 2 ^ S = 2 ^ (S + 22) := by rw [← pow_add, Nat.add_comm]
  have h3 : S + 22 ≤ 2 ^ S + 80 := by omega
  have h4 : (2 : ℕ) ^ (S + 22) ≤ 2 ^ (2 ^ S + 80) := Nat.pow_le_pow_right (by norm_num) h3
  exact Nat.mul_le_mul_right m (le_trans h1 (le_trans (le_of_eq h2) h4))

/-- The window bound is absorbed by `(s+1)(p+1)`: `(s+2)(M+1) ≤ 300 (s+1)(p+1)` when
`M ≤ 89 (p+1)`. -/
theorem buPost_W_le {s p M : ℕ} (hM : M ≤ 89 * (p + 1)) :
    (s + 2) * (M + 1) ≤ 300 * (s + 1) * (p + 1) := by
  have h1 : M + 1 ≤ 89 * (p + 1) + 1 := by omega
  have h2 : 89 * (p + 1) + 1 ≤ 90 * (p + 1) := by
    have : 1 ≤ p + 1 := by omega
    nlinarith
  have h3 : s + 2 ≤ 3 * (s + 1) := by omega
  calc (s + 2) * (M + 1) ≤ (3 * (s + 1)) * (90 * (p + 1)) := Nat.mul_le_mul h3 (le_trans h1 h2)
    _ = 270 * ((s + 1) * (p + 1)) := by ring
    _ = 270 * (s + 1) * (p + 1) := by ring
    _ ≤ 300 * (s + 1) * (p + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))

/-- Every value of the fixed windows has `vsz ≤ (s+2)(M+1)`; hence any `roll`/`pick` on a window of
at most 7 values costs at most `64·KR·(s+2)(M+1)`. -/
theorem buPost_roll_le {KR k sz s M : ℕ} (hk : k + 1 ≤ 7) (hsz : sz ≤ 7 * ((s + 2) * (M + 1))) :
    KR * (k + 1) * (sz + 1) ≤ 64 * KR * ((s + 2) * (M + 1)) := by
  have hW : 1 ≤ (s + 2) * (M + 1) := by
    have h1 : 1 ≤ s + 2 := by omega
    have h2 : 1 ≤ M + 1 := by omega
    exact Nat.mul_pos (by omega) (by omega)
  have h1 : sz + 1 ≤ 7 * ((s + 2) * (M + 1)) + 1 := by omega
  have h2 : 7 * ((s + 2) * (M + 1)) + 1 ≤ 8 * ((s + 2) * (M + 1)) := by
    nlinarith [hW]
  calc KR * (k + 1) * (sz + 1) ≤ KR * 7 * (8 * ((s + 2) * (M + 1))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left KR hk) (le_trans h1 h2)
    _ = 56 * KR * ((s + 2) * (M + 1)) := by ring
    _ ≤ 64 * KR * ((s + 2) * (M + 1)) := by
        refine Nat.mul_le_mul_right _ ?_
        exact Nat.mul_le_mul_right KR (by norm_num)

/-! ## `Pipe` adapters for a fixed tail -/

theorem encs_append (A B : List Val) : encs (A ++ B) = encs A ++ encs B := by
  simp [HvdH.encs, List.map_append, List.flatten_append]

/-- A `WordR` whose pre/post fix a window `A` and a *fixed* tail `T` below it is a `Pipe` on
`A ++ T` (the arbitrary junk `rest` of the `Pipe` is handed to the `WordR` as part of its frame). -/
theorem Pipe.ofWordR2 {main prog : Cmd} {A B T : List Val} {c : ℕ}
    (h : WordR main prog (fun vs => vs = A ++ T) (fun _ out => out = B ++ T) (fun _ => c)) :
    Pipe main prog (A ++ T) (B ++ T) c := by
  intro rest vs hvs s R hR
  have hR' : s.stk 0 = encs (A ++ T) ++ (encs rest ++ R) := by
    rw [hR, hvs, encs_append, List.append_assoc]
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h (A ++ T) rfl s (encs rest ++ R) hR'
  refine ⟨out ++ rest, s', n, ?_, hev, hn, ?_, hoth⟩
  · rw [hout]
  · rw [hstk, encs_append, List.append_assoc]

end Work.Resample
