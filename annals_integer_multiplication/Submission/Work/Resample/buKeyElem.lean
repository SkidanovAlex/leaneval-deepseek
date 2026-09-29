import Mathlib
import Submission.Work.Resample.buKit

/-!
# `Work.Resample.buKeyElem`

The destination key `(t·i) % s` of one source index, as a value-stack word.

This is the per-element word used by the selection stage of the one-dimensional `B̃` resampling
(paper §4, the keys `egKeyS s t i = (t i) mod s` of the `s`-point permutation `P̃_s`): given the
labelled window element `cons (int i) nil` on top of `int s` and `int t`, it produces
`int ((t·i) % s)` on top of the preserved `int s`, `int t`.

The word is the chain

`unconsV ; roll 1 ; drop ; pick 2 ; swap ; mulS ; pick 1 ; swap ; fmod`

— split the labelled element, discard the (here `nil`) payload, copy `t` on top and multiply to get
`t·i`, copy `s` and bring it back under the product, and take the truncated remainder.

Every step is one of the shared `KernelLib`/`IntLib` words, so its cost is a fixed multiple of a
polynomial in the sizes `isz i, isz s, isz t ≤ auSZ p ≤ 10 p + 400`; the linear factor
`(8 auSZ p + 8)²` per step is absorbed into a single `K * (p + 1) ^ K` by `buKeyPowBound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## Helper size and cost estimates -/

/-- `szl [int a, nil] = isz a + 1`. -/
theorem buKeySzl2 (a : ℤ) : Work.Fx.szl [Val.int a, Val.nil] = isz a + 1 := by
  simp [Work.Fx.szl, Work.Fx.vsz_int, Work.Fx.vsz_nil]

/-- `szl [int a, int b] = isz a + isz b`. -/
theorem buKeySzl2i (a b : ℤ) : Work.Fx.szl [Val.int a, Val.int b] = isz a + isz b := by
  simp [Work.Fx.szl, Work.Fx.vsz_int]

/-- `szl [int a, int b, int c] = isz a + isz b + isz c`. -/
theorem buKeySzl3 (a b c : ℤ) :
    Work.Fx.szl [Val.int a, Val.int b, Val.int c] = isz a + isz b + isz c := by
  simp [Work.Fx.szl, Work.Fx.vsz_int]; ring

/-- Absorbing a constant into the exponent: `M (p+1)^2 ≤ (8M+6) (p+1)^(8M+6)`. -/
theorem buKeyPowBound {M p : ℕ} (hM : 1 ≤ M) (hp : 2 ≤ p + 1) :
    M * (p + 1) ^ 2 ≤ (8 * M + 6) * (p + 1) ^ (8 * M + 6) := by
  have h1 : M < 2 ^ (4 * M + 3) :=
    lt_of_le_of_lt (show M ≤ 4 * M + 3 by omega) (Nat.lt_two_pow_self (n := 4 * M + 3))
  have h2 : (2 : ℕ) ^ (4 * M + 3) ≤ (p + 1) ^ (4 * M + 3) := Nat.pow_le_pow_left hp _
  have hMle : M ≤ (p + 1) ^ (4 * M + 3) := le_of_lt (lt_of_lt_of_le h1 h2)
  have hbase : 1 ≤ p + 1 := by omega
  have h3 : (p + 1) ^ 2 ≤ (p + 1) ^ (4 * M + 3) := Nat.pow_le_pow_right hbase (by omega)
  have h4 : M * (p + 1) ^ 2 ≤ (p + 1) ^ (4 * M + 3) * (p + 1) ^ (4 * M + 3) :=
    Nat.mul_le_mul hMle h3
  have h5 : (p + 1) ^ (4 * M + 3) * (p + 1) ^ (4 * M + 3) = (p + 1) ^ (8 * M + 6) := by
    rw [← pow_add]; congr 1; ring
  have h6 : (p + 1) ^ (8 * M + 6) ≤ (8 * M + 6) * (p + 1) ^ (8 * M + 6) :=
    le_mul_of_one_le_left (by positivity) (by omega)
  exact le_trans h4 (le_trans (le_of_eq h5) h6)

/-- For naturals, `Int.fmod` is the natural remainder. -/
theorem buKeyFmodNat (a b : ℕ) (hb : 0 < b) :
    Int.fmod ((a : ℕ) : ℤ) ((b : ℕ) : ℤ) = (((a % b : ℕ)) : ℤ) := by
  rw [Int.fmod_eq_emod_of_nonneg _ (by positivity)]
  exact (Int.natCast_emod a b).symm

/-- `isz (t·i) ≤ auSZ p` for `t, i < 2^p`: both factors fit in `2p` bits. -/
theorem buKeyIszMul (p s t i : ℕ) (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hi : i < s) :
    isz (((t * i : ℕ)) : ℤ) ≤ auSZ p := by
  have hti : t * i < 2 ^ p * 2 ^ p := by nlinarith
  have hpow : (2:ℕ) ^ p * 2 ^ p = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  rw [hpow] at hti
  have hsz : (t * i).size ≤ 2 * p := Nat.size_le.mpr hti
  rw [isz, Int.natAbs_natCast]
  simp only [auSZ]
  omega

/-- `KernelLib.unconsV` as a `Pipe` on a one-value window. -/
theorem buKeyUnconsV {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    (a b : Val) : Pipe main prog [.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv : vs = .cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv⟩ s R hR
  have hh : Val.cons a' b' = Val.cons a b := (List.cons.inj (hvs'.symm.trans hv)).1
  have ht : rest' = rest := (List.cons.inj (hvs'.symm.trans hv)).2
  have h1 : a' = a := (Val.cons.inj hh).1
  have h2 : b' = b := (Val.cons.inj hh).2
  exact ⟨out, s', n, by rw [hout, h1, h2, ht]; rfl, hev, hn, hstk, hoth⟩

/-! ## The word -/

theorem buKeyElem (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p s t : ℕ) (hp : 1 ≤ p) (hsp : s < 2 ^ p)
      (htp : t < 2 ^ p) (i : ℕ) (hi : i < s),
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil,
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil,
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest ∧
          out = [HvdH.Val.int (((t * i) % s : ℕ) : ℤ), HvdH.Val.int (s : ℤ),
            HvdH.Val.int (t : ℤ)] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨ucProg, Kuc, huc⟩ := KL.unconsV
  obtain ⟨rollProg, Kr, hroll⟩ := KL.roll
  obtain ⟨dropProg, Kd, hdrop⟩ := KL.drop
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  obtain ⟨swapProg, Ks, hswap⟩ := KL.swap
  obtain ⟨mulProg, Km, hmul⟩ := IL.mulS
  obtain ⟨fmProg, Kf, hfm⟩ := IL.fmod
  let Λ : ℕ := Kuc + Kr + Kd + Kpk + Ks + Km + Kf + 1
  let M : ℕ := 9 * Λ * 3208 ^ 2 + 1
  let K : ℕ := 8 * M + 6
  let prog : Cmd := Cmd.seq ucProg (Cmd.seq (rollProg 1) (Cmd.seq dropProg (Cmd.seq (pickProg 2)
    (Cmd.seq swapProg (Cmd.seq mulProg (Cmd.seq (pickProg 1) (Cmd.seq swapProg fmProg)))))))
  refine ⟨prog, K, ?_⟩
  intro main p s t hp hsp htp i hi rest
  have hS : 400 ≤ auSZ p := auSZ_ge p
  have hzi : isz ((i : ℤ)) ≤ auSZ p := isz_le_pow2 (le_of_lt (lt_trans hi hsp))
  have hzs : isz ((s : ℤ)) ≤ auSZ p := isz_le_pow2 (le_of_lt hsp)
  have hzt : isz ((t : ℤ)) ≤ auSZ p := isz_le_pow2 (le_of_lt htp)
  have hzit : isz ((i : ℤ) * (t : ℤ)) ≤ auSZ p := by
    rw [show (i : ℤ) * (t : ℤ) = ((t * i : ℕ) : ℤ) by push_cast; ring]
    exact buKeyIszMul p s t i hsp htp hi
  have hs0 : (0 : ℤ) < (s : ℤ) := by
    have : 0 < s := by omega
    exact_mod_cast this
  have huc_le : Kuc ≤ Λ := by simp only [Λ]; omega
  have hr_le : Kr ≤ Λ := by simp only [Λ]; omega
  have hd_le : Kd ≤ Λ := by simp only [Λ]; omega
  have hpk_le : Kpk ≤ Λ := by simp only [Λ]; omega
  have hs_le : Ks ≤ Λ := by simp only [Λ]; omega
  have hm_le : Km ≤ Λ := by simp only [Λ]; omega
  have hf_le : Kf ≤ Λ := by simp only [Λ]; omega
  let cb : ℕ := Λ * (8 * auSZ p + 8) ^ 2
  let V0 : List Val := [Val.cons (Val.int (i : ℤ)) Val.nil, Val.int (s : ℤ), Val.int (t : ℤ)]
  let V1 : List Val := [Val.int (i : ℤ), Val.nil, Val.int (s : ℤ), Val.int (t : ℤ)]
  let V2 : List Val := [Val.nil, Val.int (i : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
  let V3 : List Val := [Val.int (i : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
  let V4 : List Val := [Val.int (t : ℤ), Val.int (i : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
  let V5 : List Val := [Val.int (i : ℤ), Val.int (t : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
  let V6 : List Val := [Val.int ((i : ℤ) * (t : ℤ)), Val.int (s : ℤ), Val.int (t : ℤ)]
  let V7 : List Val := [Val.int (s : ℤ), Val.int ((i : ℤ) * (t : ℤ)), Val.int (s : ℤ),
    Val.int (t : ℤ)]
  let V8 : List Val := [Val.int ((i : ℤ) * (t : ℤ)), Val.int (s : ℤ), Val.int (s : ℤ),
    Val.int (t : ℤ)]
  let V9 : List Val := [Val.int (Int.fmod ((i : ℤ) * (t : ℤ)) (s : ℤ)), Val.int (s : ℤ),
    Val.int (t : ℤ)]
  let Vout : List Val := [Val.int (((t * i) % s : ℕ) : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
  have hfm' : Int.fmod ((i : ℤ) * (t : ℤ)) ((s : ℤ)) = (((t * i) % s : ℕ) : ℤ) := by
    rw [show (i : ℤ) * (t : ℤ) = ((t * i : ℕ) : ℤ) by push_cast; ring]
    exact buKeyFmodNat (t * i) s (by omega)
  -- step 1: split the labelled element `cons (int i) nil`
  have s1 : Pipe main ucProg V0 V1 cb := by
    have h := Pipe.appendTail (main := main) [Val.int (s : ℤ), Val.int (t : ℤ)]
      (buKeyUnconsV (main := main) huc (Val.int (i : ℤ)) Val.nil)
    have h' : Pipe main ucProg V0 V1 Kuc := by
      simpa only [V0, V1, List.singleton_append, List.cons_append, List.nil_append] using h
    refine Pipe.le h' ?_
    simp only [cb]
    calc Kuc ≤ Kuc * (8 * auSZ p + 8) ^ 2 := Nat.le_mul_of_pos_right Kuc (by positivity)
      _ ≤ Λ * (8 * auSZ p + 8) ^ 2 := Nat.mul_le_mul_right _ huc_le
  -- step 2: bring the `nil` payload to the top
  have s2 : Pipe main (rollProg 1) V1 V2 cb := by
    have h := Pipe.roll (prog := rollProg) (K := Kr) main hroll (A := V1) (k := 1)
      (by simp only [V1]; norm_num)
    refine Pipe.le (Pipe.rw h ?_) ?_
    · simp only [V1, V2]; simp
    · simp only [cb]
      have htake : V1.take 2 = [Val.int (i : ℤ), Val.nil] := by simp only [V1]; simp
      have hle' : (1 + 1) * (Work.Fx.szl (V1.take 2) + 1) ≤ (8 * auSZ p + 8) ^ 2 := by
        rw [htake, buKeySzl2]
        nlinarith [hS, hzi]
      calc Kr * (1 + 1) * (Work.Fx.szl (V1.take 2) + 1)
          = Kr * ((1 + 1) * (Work.Fx.szl (V1.take 2) + 1)) := by ring
        _ ≤ Λ * (8 * auSZ p + 8) ^ 2 := Nat.mul_le_mul hr_le hle'
  -- step 3: discard the payload
  have s3 : Pipe main dropProg V2 V3 cb := by
    have h := Pipe.appendTail (main := main) [Val.int (i : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
      (Pipe.drop (prog := dropProg) (K := Kd) main hdrop Val.nil)
    have h' : Pipe main dropProg V2 V3 (Kd * (vsz Val.nil + 1)) := by
      simpa only [V2, V3, List.singleton_append, List.nil_append] using h
    refine Pipe.le h' ?_
    simp only [cb, Work.Fx.vsz_nil]
    exact Nat.mul_le_mul hd_le (by nlinarith [hS])
  -- step 4: copy `t` on top
  have s4 : Pipe main (pickProg 2) V3 V4 cb := by
    have h := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick
      (A := V3) (k := 2) (by simp only [V3]; norm_num)
      (v := Val.int (t : ℤ)) (by simp only [V3]; simp)
    have h' : Pipe main (pickProg 2) V3 V4 (Kpk * (2 + 1) * (Work.Fx.szl (V3.take 3) + 1)) := by
      simpa only [V3, V4] using h
    refine Pipe.le h' ?_
    simp only [cb]
    have htake : V3.take 3 = [Val.int (i : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] := by
      simp only [V3]; simp
    have hle' : (2 + 1) * (Work.Fx.szl (V3.take 3) + 1) ≤ (8 * auSZ p + 8) ^ 2 := by
      rw [htake, buKeySzl3]
      nlinarith [hS, hzi, hzs, hzt]
    calc Kpk * (2 + 1) * (Work.Fx.szl (V3.take 3) + 1)
        = Kpk * ((2 + 1) * (Work.Fx.szl (V3.take 3) + 1)) := by ring
      _ ≤ Λ * (8 * auSZ p + 8) ^ 2 := Nat.mul_le_mul hpk_le hle'
  -- step 5: swap `t` under `i`
  have s5 : Pipe main swapProg V4 V5 cb := by
    have h := Pipe.appendTail (main := main) [Val.int (s : ℤ), Val.int (t : ℤ)]
      (Pipe.swap (prog := swapProg) (K := Ks) main hswap (Val.int (t : ℤ)) (Val.int (i : ℤ)))
    have h' : Pipe main swapProg V4 V5
        (Ks * (vsz (Val.int (t : ℤ)) + vsz (Val.int (i : ℤ)) + 1)) := by
      simpa only [V4, V5, List.cons_append, List.nil_append] using h
    refine Pipe.le h' ?_
    simp only [cb, Work.Fx.vsz_int]
    exact Nat.mul_le_mul hs_le (by nlinarith [hS, hzi, hzt])
  -- step 6: the product `i · t`
  have s6 : Pipe main mulProg V5 V6 cb := by
    have h := Pipe.appendTail (main := main) [Val.int (s : ℤ), Val.int (t : ℤ)]
      (Pipe.binOp (main := main) (hmul main) (a := (i : ℤ)) (b := (t : ℤ)) trivial)
    have h' : Pipe main mulProg V5 V6 (Km * isz ((i : ℤ)) * isz ((t : ℤ))) := by
      simpa only [V5, V6, List.cons_append, List.nil_append] using h
    refine Pipe.le h' ?_
    simp only [cb]
    have hle' : isz ((i : ℤ)) * isz ((t : ℤ)) ≤ (8 * auSZ p + 8) ^ 2 := by
      calc isz ((i : ℤ)) * isz ((t : ℤ)) ≤ auSZ p * auSZ p := Nat.mul_le_mul hzi hzt
        _ ≤ (8 * auSZ p + 8) ^ 2 := by nlinarith [hS]
    calc Km * isz ((i : ℤ)) * isz ((t : ℤ)) = Km * (isz ((i : ℤ)) * isz ((t : ℤ))) := by ring
      _ ≤ Λ * (8 * auSZ p + 8) ^ 2 := Nat.mul_le_mul hm_le hle'
  -- step 7: copy the divisor `s` on top
  have s7 : Pipe main (pickProg 1) V6 V7 cb := by
    have h := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick
      (A := V6) (k := 1) (by simp only [V6]; norm_num)
      (v := Val.int (s : ℤ)) (by simp only [V6]; simp)
    have h' : Pipe main (pickProg 1) V6 V7 (Kpk * (1 + 1) * (Work.Fx.szl (V6.take 2) + 1)) := by
      simpa only [V6, V7] using h
    refine Pipe.le h' ?_
    simp only [cb]
    have htake : V6.take 2 = [Val.int ((i : ℤ) * (t : ℤ)), Val.int (s : ℤ)] := by
      simp only [V6]; simp
    have hle' : (1 + 1) * (Work.Fx.szl (V6.take 2) + 1) ≤ (8 * auSZ p + 8) ^ 2 := by
      rw [htake, buKeySzl2i]
      nlinarith [hS, hzit, hzs]
    calc Kpk * (1 + 1) * (Work.Fx.szl (V6.take 2) + 1)
        = Kpk * ((1 + 1) * (Work.Fx.szl (V6.take 2) + 1)) := by ring
      _ ≤ Λ * (8 * auSZ p + 8) ^ 2 := Nat.mul_le_mul hpk_le hle'
  -- step 8: bring the divisor back under the product
  have s8 : Pipe main swapProg V7 V8 cb := by
    have h := Pipe.appendTail (main := main) [Val.int (s : ℤ), Val.int (t : ℤ)]
      (Pipe.swap (prog := swapProg) (K := Ks) main hswap (Val.int (s : ℤ))
        (Val.int ((i : ℤ) * (t : ℤ))))
    have h' : Pipe main swapProg V7 V8
        (Ks * (vsz (Val.int (s : ℤ)) + vsz (Val.int ((i : ℤ) * (t : ℤ))) + 1)) := by
      simpa only [V7, V8, List.cons_append, List.nil_append] using h
    refine Pipe.le h' ?_
    simp only [cb, Work.Fx.vsz_int]
    exact Nat.mul_le_mul hs_le (by nlinarith [hS, hzs, hzit])
  -- step 9: the truncated remainder
  have s9 : Pipe main fmProg V8 V9 cb := by
    have h := Pipe.appendTail (main := main) [Val.int (s : ℤ), Val.int (t : ℤ)]
      (Pipe.binOp (main := main) (hfm main) (a := (i : ℤ) * (t : ℤ)) (b := (s : ℤ)) hs0)
    have h' : Pipe main fmProg V8 V9 (Kf * isz ((i : ℤ) * (t : ℤ)) * isz ((s : ℤ))) := by
      simpa only [V8, V9, List.cons_append, List.nil_append] using h
    refine Pipe.le h' ?_
    simp only [cb]
    have hle' : isz ((i : ℤ) * (t : ℤ)) * isz ((s : ℤ)) ≤ (8 * auSZ p + 8) ^ 2 := by
      calc isz ((i : ℤ) * (t : ℤ)) * isz ((s : ℤ)) ≤ auSZ p * auSZ p := Nat.mul_le_mul hzit hzs
        _ ≤ (8 * auSZ p + 8) ^ 2 := by nlinarith [hS]
    calc Kf * isz ((i : ℤ) * (t : ℤ)) * isz ((s : ℤ))
        = Kf * (isz ((i : ℤ) * (t : ℤ)) * isz ((s : ℤ))) := by ring
      _ ≤ Λ * (8 * auSZ p + 8) ^ 2 := Nat.mul_le_mul hf_le hle'
  have hcomp : Pipe main prog V0 V9 (cb + (cb + (cb + (cb + (cb + (cb + (cb + (cb + cb)))))))) :=
    Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6
      (Pipe.comp s7 (Pipe.comp s8 s9)))))))
  have hM1 : 1 ≤ M := by simp only [M]; omega
  have hp2 : 2 ≤ p + 1 := by omega
  have hle : cb + (cb + (cb + (cb + (cb + (cb + (cb + (cb + cb))))))) ≤ K * (p + 1) ^ K := by
    have h1 : cb + (cb + (cb + (cb + (cb + (cb + (cb + (cb + cb))))))) ≤ 9 * cb := by omega
    have h2 : 9 * cb ≤ M * (p + 1) ^ 2 := by
      have hSB : 8 * auSZ p + 8 ≤ 3208 * (p + 1) := by simp only [auSZ]; omega
      have hsq : (8 * auSZ p + 8) ^ 2 ≤ (3208 * (p + 1)) ^ 2 := Nat.pow_le_pow_left hSB 2
      have hsq2 : (3208 * (p + 1)) ^ 2 = 3208 ^ 2 * (p + 1) ^ 2 := by ring
      have h9 : 9 * cb = 9 * Λ * (8 * auSZ p + 8) ^ 2 := by simp only [cb]; ring
      rw [h9]
      calc 9 * Λ * (8 * auSZ p + 8) ^ 2 ≤ 9 * Λ * (3208 * (p + 1)) ^ 2 :=
            Nat.mul_le_mul_left _ hsq
        _ = 9 * Λ * 3208 ^ 2 * (p + 1) ^ 2 := by rw [hsq2]; ring
        _ ≤ M * (p + 1) ^ 2 := by
            simp only [M]
            exact Nat.mul_le_mul_right _ (by omega)
    have h3 : M * (p + 1) ^ 2 ≤ K * (p + 1) ^ K := by
      simp only [K]
      exact buKeyPowBound hM1 hp2
    exact le_trans h1 (le_trans h2 h3)
  have hPipe : Pipe main prog V0 V9 (K * (p + 1) ^ K) := Pipe.le hcomp hle
  have hP := hPipe rest
  refine KL.conseq main prog (fun vs => vs = V0 ++ rest) (fun vs => vs = V0 ++ rest)
    (fun _ out => out = V9 ++ rest) (fun vs out => vs = V0 ++ rest ∧ out = Vout ++ rest)
    (fun _ => K * (p + 1) ^ K) (fun _ => K * (p + 1) ^ K) hP ?_ ?_ ?_
  · intro vs h; exact h
  · intro vs out h1 h2
    refine ⟨h1, ?_⟩
    rw [h2]
    have hV : V9 = Vout := by
      simp only [V9, Vout]
      rw [hfm']
    rw [hV]
  · intro vs h; exact le_refl _

end Work.Resample
