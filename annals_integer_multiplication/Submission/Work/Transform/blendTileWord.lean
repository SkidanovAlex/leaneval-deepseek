import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.Kernel.Raw
import Submission.Work.Transform.chirpAux

/-!
# `Work.Transform.blendTileWord` — tiling a fixed-point vector

`int t :: cvecVal u :: rest ↦ ofList Y :: rest` where `Y` is the vector `u` tiled `t` times,
i.e. `Y[a * P + b] = cfxVal (u[b])` for `a < t`, `b < P` (`P = u.length`).

Implementation: `LayoutLib.replicate` (build `ofList (replicate t (cvecVal u))`, the `t` copies as a
list of values) followed by `LayoutLib.flatten` (concatenate them).

Cost: `replicate` costs `O((t+1) * (vsz (cvecVal u) + 1) + isz t)`, `flatten` costs
`O(vsz (ofList (replicate t (cvecVal u))) + 1) = O(t * vsz (cvecVal u) + t)`, and
`vsz (cvecVal u) + 1 ≤ 16 * ((P+1)*(p+1) + 1)` because every coordinate of a point of the disc
`C̃◦` has `natAbs ≤ 2^p` (`chirpAux_vsz_cvecVal_le`); this gives the stated bound
`K * ((t+1) * ((P+1)*(p+1) + 1) + 1)`.

The index/length lemmas `length_flatten_replicate`, `getD_flatten_replicate` and the size estimates
`chirpAux_vsz_ofList`, `chirpAux_vsz_cvecVal_le` come from `Submission.Work.Transform.chirpAux`.
-/

namespace Work.Transform

open HvdH

-- `KernelLib` is part of the interface of the lemma (the caller supplies it) but the two LayoutLib
-- words used here are composed directly.
set_option linter.unusedVariables false

/-- Sum of the encoding sizes of the members of a `replicate`d list.  (Proved by hand rather than
from `List.sum_replicate`, whose `nsmul` produces a non-standard multiplication instance on `ℕ`.) -/
private theorem bt_sum_replicate (t : ℕ) (v : Val) :
    ((List.replicate t v).map vsz).sum = t * vsz v := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.map_cons, List.sum_cons, ih]
    ring

/-- Size estimate for a vector in the disc: `vsz (cvecVal u) + 1 ≤ 16 * ((P+1)*(p+1) + 1)`. -/
private theorem bt_sz {p P : ℕ} {u : List (ℤ × ℤ)} (hd : InDiscVec p P u) :
    vsz (cvecVal u) + 1 ≤ 16 * ((P + 1) * (p + 1) + 1) := by
  have h := chirpAux_vsz_cvecVal_le (n := P) hd
  nlinarith [Nat.zero_le P, Nat.zero_le p]

/-- Arithmetic of the two cost estimates: with `s + 1 ≤ 16 * M`, `1 ≤ M` and `iszt ≤ t + 2`,
the sum of the `replicate` and `flatten` costs is `≤ (19 * KR + 18 * KF) * ((t+1) * M + 1)`. -/
private theorem bt_cost {KR KF t s M iszt : ℕ} (hM : 1 ≤ M) (hs : s + 1 ≤ 16 * M)
    (hz : iszt ≤ t + 2) :
    KR * ((t + 1) * (s + 1) + iszt + 1) + KF * (t * s + t + 2)
      ≤ (KR * 19 + KF * 18) * ((t + 1) * M + 1) := by
  have ht : t + 1 ≤ (t + 1) * M + 1 := by
    have := Nat.le_mul_of_pos_right (m := M) (t + 1) hM
    omega
  have h1 : (t + 1) * (s + 1) ≤ 16 * ((t + 1) * M + 1) := by
    calc (t + 1) * (s + 1) ≤ (t + 1) * (16 * M) := Nat.mul_le_mul_left _ hs
      _ = 16 * ((t + 1) * M) := by ring
      _ ≤ 16 * ((t + 1) * M + 1) := by omega
  have h2 : iszt + 1 ≤ 3 * ((t + 1) * M + 1) := by omega
  have hA : (t + 1) * (s + 1) + iszt + 1 ≤ 19 * ((t + 1) * M + 1) := by omega
  have h3 : t * s + t ≤ 16 * ((t + 1) * M + 1) := by
    have hts : t * s + t = t * (s + 1) := by ring
    rw [hts]
    calc t * (s + 1) ≤ (t + 1) * (s + 1) := Nat.mul_le_mul_right _ (Nat.le_succ t)
      _ ≤ 16 * ((t + 1) * M + 1) := h1
  have hB : t * s + t + 2 ≤ 18 * ((t + 1) * M + 1) := by omega
  calc KR * ((t + 1) * (s + 1) + iszt + 1) + KF * (t * s + t + 2)
      ≤ KR * (19 * ((t + 1) * M + 1)) + KF * (18 * ((t + 1) * M + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hA) (Nat.mul_le_mul_left _ hB)
    _ = (KR * 19 + KF * 18) * ((t + 1) * M + 1) := by ring

theorem blendTileWord (hK : HvdH.KernelLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p t P : ℕ) (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
      u.length = P → HvdH.InDiscVec p P u →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int t :: HvdH.cvecVal u :: rest)
        (fun vs out => ∃ Y : List HvdH.Val,
          out = HvdH.ofList Y :: rest ∧ Y.length = t * P ∧
          ∀ a < t, ∀ b < P, Y.getD (a * P + b) HvdH.Val.nil = HvdH.cfxVal (u.getD b (0, 0)))
        (fun _ => K * ((t + 1) * ((P + 1) * (p + 1) + 1) + 1)) := by
  obtain ⟨progR, KR, hRep⟩ := hL.replicate
  obtain ⟨progF, KF, hFlat⟩ := hL.flatten
  refine ⟨.seq progR progF, KR * 19 + KF * 18, ?_⟩
  intro main p t P u rest hlen hdisc vs hvs s R hR
  -- step 1: `replicate` pushes the `t` copies of `cvecVal u` as a list of values
  obtain ⟨out1, s1, n1, hpost1, he1, hn1, hstk1, hoth1⟩ :=
    hRep main t (cvecVal u) vs ⟨rest, hvs⟩ s R hR
  obtain ⟨rest1, hvs1, hout1⟩ := hpost1
  have hrest1 : rest1 = rest := by
    rw [hvs] at hvs1
    exact ((List.cons.inj (List.cons.inj hvs1).2).2).symm
  rw [hrest1] at hout1
  have hmapL : (List.replicate t (u.map cfxVal)).map ofList = List.replicate t (cvecVal u) := by
    rw [List.map_replicate]; rfl
  -- step 2: `flatten` concatenates them
  obtain ⟨out2, s2, n2, hpost2, he2, hn2, hstk2, hoth2⟩ :=
    hFlat main (List.replicate t (u.map cfxVal))
      (ofList (List.replicate t (cvecVal u)) :: rest)
      ⟨rest, by rw [hmapL]⟩ s1 R (by rw [hstk1, hout1])
  obtain ⟨rest2, hmid2, hout2⟩ := hpost2
  have hrest2 : rest2 = rest := by
    rw [hmapL] at hmid2
    exact (List.cons.inj hmid2).2.symm
  rw [hrest2] at hout2
  refine ⟨out2, s2, n1 + n2,
    ⟨(List.replicate t (u.map cfxVal)).flatten, hout2, ?_, ?_⟩, Eval.seq he1 he2, ?_, ?_, ?_⟩
  · -- the length of the tiled vector
    rw [length_flatten_replicate, List.length_map, hlen]
  · -- the entries of the tiled vector
    intro a ha b hb
    have hbu : b < u.length := by rw [hlen]; exact hb
    have hg := getD_flatten_replicate (u.map cfxVal) Val.nil t a b
      (by rw [List.length_map]; exact hbu) ha
    rw [List.length_map, hlen] at hg
    rw [hg]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hbu), List.getElem_map,
      List.getD_eq_getElem _ _ hbu]
  · -- the cost
    have hcostF : n2 ≤ KF * (t * vsz (cvecVal u) + t + 2) := by
      refine le_trans hn2 (Nat.mul_le_mul_left KF ?_)
      rw [hmapL, chirpAux_vsz_ofList, bt_sum_replicate, List.length_replicate]
    have hz : isz t ≤ t + 2 := by
      have h : t.size ≤ t := Nat.size_le.mpr Nat.lt_two_pow_self
      show (t : ℤ).natAbs.size + 2 ≤ t + 2
      rw [Int.natAbs_natCast]
      omega
    calc n1 + n2 ≤ KR * ((t + 1) * (vsz (cvecVal u) + 1) + isz t + 1) +
          KF * (t * vsz (cvecVal u) + t + 2) := Nat.add_le_add hn1 hcostF
      _ ≤ (KR * 19 + KF * 18) * ((t + 1) * ((P + 1) * (p + 1) + 1) + 1) :=
          bt_cost (M := (P + 1) * (p + 1) + 1) (by omega) (bt_sz hdisc) hz
  · exact hstk2
  · intro k hk
    rw [hoth2 k hk, hoth1 k hk]

end Work.Transform
