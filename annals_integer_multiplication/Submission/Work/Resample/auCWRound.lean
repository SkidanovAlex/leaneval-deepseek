import Mathlib
import Submission.Work.Resample.auCWDefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auRoundAux
import Submission.Work.Resample.pbWords
import Submission.Work.Resample.auCWIntMulSelf
import Submission.Work.Resample.auCWCarLow
import Submission.Work.Resample.auCWRecVal
import Submission.Work.Resample.auCWPark
import Submission.Work.Resample.auCWDisc

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.Resample

open HvdH
open Work.Fx

/-- Uniform bound for a single library call. -/
def auCWSC (p KS : ℕ) : ℕ := KS * (4096 * (p + 1))

theorem auCWSZ_le_4096 (p : ℕ) : SZ p ≤ 4096 * (p + 1) := by simp only [SZ]; omega

theorem auCWle_SZ {p k : ℕ} (h : k ≤ 8 * p + 8) : k ≤ SZ p := by simp only [SZ]; exact h

theorem auCWle_SC_const {K KS p : ℕ} (hK : K ≤ KS) : K ≤ auCWSC p KS := by
  refine le_trans hK ?_
  rw [auCWSC]
  exact Nat.le_mul_of_pos_right KS (by omega)

theorem auCWle_SC_one {K KS p : ℕ} (hK : K ≤ KS) {v : ℕ} (hv : v ≤ SZ p) : K * (v + 1) ≤ auCWSC p KS := by
  have hv' : v ≤ 8 * p + 8 := hv
  rw [auCWSC]
  exact Nat.mul_le_mul hK (by omega)

theorem auCWle_SC_two {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ SZ p) (hv : v ≤ SZ p) :
    K * (u + v) ≤ auCWSC p KS := by
  have hu' : u ≤ 8 * p + 8 := hu
  have hv' : v ≤ 8 * p + 8 := hv
  rw [auCWSC]
  exact Nat.mul_le_mul hK (by omega)

theorem auCWle_SC_two1 {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ SZ p) (hv : v ≤ SZ p) :
    K * (u + v + 1) ≤ auCWSC p KS := by
  have hu' : u ≤ 8 * p + 8 := hu
  have hv' : v ≤ 8 * p + 8 := hv
  rw [auCWSC]
  exact Nat.mul_le_mul hK (by omega)

theorem auCWle_SC_three1 {K KS p : ℕ} (hK : K ≤ KS) {u v w : ℕ} (hu : u ≤ SZ p) (hv : v ≤ SZ p)
    (hw : w ≤ SZ p) : K * (u + v + w + 1) ≤ auCWSC p KS := by
  have hu' : u ≤ 8 * p + 8 := hu
  have hv' : v ≤ 8 * p + 8 := hv
  have hw' : w ≤ 8 * p + 8 := hw
  rw [auCWSC]
  exact Nat.mul_le_mul hK (by omega)

theorem auCWle_SC_mul_small {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ 4) (hv : v ≤ p + 3) :
    K * u * v ≤ auCWSC p KS := by
  have h1 : u * v ≤ 4 * (p + 3) := Nat.mul_le_mul hu hv
  have h2 : 4 * (p + 3) ≤ 4096 * (p + 1) := by omega
  rw [auCWSC]
  calc K * u * v = K * (u * v) := by ring
    _ ≤ KS * (4096 * (p + 1)) := Nat.mul_le_mul hK (le_trans h1 h2)

theorem auCWle_SC_roll {K KS p : ℕ} (hK : K ≤ KS) {A : List Val} {k : ℕ} (hk : k ≤ 12)
    (hA : ∀ v ∈ A.take (k + 1), vsz v ≤ SZ p) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ auCWSC p KS := by
  have hlen : (A.take (k + 1)).length ≤ k + 1 := by rw [List.length_take]; omega
  have hsum : szl (A.take (k + 1)) ≤ (k + 1) * SZ p :=
    le_trans (szl_le_len_mul hA) (Nat.mul_le_mul_right _ hlen)
  have hk13 : k + 1 ≤ 13 := by omega
  have hsq : (k + 1) * (k + 1) ≤ 169 := by
    calc (k + 1) * (k + 1) ≤ 13 * 13 := Nat.mul_le_mul hk13 hk13
      _ = 169 := by norm_num
  have hSZp : SZ p = 8 * p + 8 := rfl
  have hD : (k + 1) * (szl (A.take (k + 1)) + 1) ≤ 4096 * (p + 1) := by
    calc (k + 1) * (szl (A.take (k + 1)) + 1)
        ≤ (k + 1) * ((k + 1) * SZ p + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (k + 1) * (k + 1) * SZ p + (k + 1) := by ring
      _ ≤ 169 * SZ p + 13 := Nat.add_le_add (Nat.mul_le_mul_right _ hsq) hk13
      _ = 169 * (8 * p + 8) + 13 := by rw [hSZp]
      _ ≤ 4096 * (p + 1) := by omega
  rw [auCWSC]
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1)
      = K * ((k + 1) * (szl (A.take (k + 1)) + 1)) := by ring
    _ ≤ KS * (4096 * (p + 1)) := Nat.mul_le_mul hK hD

theorem auCWnatAbs_lt_two_pow {a : ℤ} {k : ℕ} (h0 : 0 ≤ a) (h : a < ((2 ^ k : ℕ) : ℤ)) :
    a.natAbs < 2 ^ k := by
  have h2 : ((a.natAbs : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h0]; exact h
  exact_mod_cast h2

theorem auCWnatAbs_le_two_pow {a : ℤ} {k : ℕ} (h0 : 0 ≤ a) (h : a ≤ ((2 ^ k : ℕ) : ℤ)) :
    a.natAbs ≤ 2 ^ k := by
  have h2 : ((a.natAbs : ℕ) : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h0]; exact h
  exact_mod_cast h2

theorem auCWisz_le_of_natAbs_le {k : ℕ} {z : ℤ} (h : z.natAbs ≤ 2 ^ k) : isz z ≤ k + 3 := by
  have h1 : z.natAbs.size ≤ k + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right one_lt_two (by omega))
  simp only [isz]; omega

theorem auCWisz_le_of_natAbs_lt {k : ℕ} {z : ℤ} (h : z.natAbs < 2 ^ k) : isz z ≤ k + 2 := by
  have h1 : z.natAbs.size ≤ k := Nat.size_le.mpr h
  simp only [isz]; omega

theorem auCWvsz_awRec_le (zr zi : ℤ) : vsz (awRec zr zi) ≤ 10 := by
  unfold awRec
  split_ifs <;> decide +kernel

theorem auCWtoNat_two_mul (p : ℕ) : ((2 : ℤ) * (p : ℤ)).toNat = 2 * p := by
  have h : (0 : ℤ) ≤ 2 * (p : ℤ) := by positivity
  have h1 : (((2 : ℤ) * (p : ℤ)).toNat : ℤ) = 2 * (p : ℤ) := Int.toNat_of_nonneg h
  have h2 : (((2 : ℤ) * (p : ℤ)).toNat : ℤ) = ((2 * p : ℕ) : ℤ) := by push_cast; exact h1
  exact_mod_cast h2

theorem auCWtoNat_two_mul_add_one (p : ℕ) : ((1 + 2 * (p : ℤ)).toNat) = 2 * p + 1 := by
  have h : (0 : ℤ) ≤ 1 + 2 * (p : ℤ) := by positivity
  have h1 : ((1 + 2 * (p : ℤ)).toNat : ℤ) = 1 + 2 * (p : ℤ) := Int.toNat_of_nonneg h
  have h2 : ((1 + 2 * (p : ℤ)).toNat : ℤ) = ((2 * p + 1 : ℕ) : ℤ) := by
    push_cast
    linarith [h1]
  exact_mod_cast h2

theorem auCWpow_two_mul (p : ℕ) : (2 : ℤ) ^ ((2 * (p : ℤ)).toNat) = awSh p := by
  rw [auCWtoNat_two_mul]; rfl

theorem auCWpow_two_mul_add_one (p : ℕ) : (2 : ℤ) ^ ((1 + 2 * (p : ℤ)).toNat) = awMod p := by
  rw [auCWtoNat_two_mul_add_one]; simp only [awMod, awQ]

theorem auCWawCar_eq_zero_or_one_le {p : ℕ} {lo A : ℤ} (hl : 0 ≤ lo) (hA : 0 ≤ A)
    (hlo : lo < awMod p) (hA' : A ≤ awMod p) : awCar p lo A = 0 ∨ awCar p lo A = 1 := by
  rcases lt_or_eq_of_le hA' with hlt | heq
  · exact awCar_eq_zero_or_one hl hA hlo hlt
  · right
    subst heq
    have hM := awMod_pos p
    have h0 : 0 ≤ lo + awMod p := by linarith
    rw [awCar, Int.tdiv_eq_ediv_of_nonneg h0]
    have h2 : lo + awMod p = lo + awMod p * 1 := by ring
    rw [h2, Int.add_mul_ediv_left (a := lo) (b := awMod p) (c := 1) (by omega)]
    have h3 : lo / awMod p = 0 := Int.ediv_eq_zero_of_lt hl hlo
    rw [h3]; ring

theorem auCWawLow_natAbs_lt {p : ℕ} {lo A : ℤ} (hl : 0 ≤ lo) (hA : 0 ≤ A) :
    (awLow p lo A).natAbs < 2 ^ (2 * p + 1) := by
  have h := awLow_lt (p := p) hl hA
  have hmod : awMod p = (2 : ℤ) ^ (2 * p + 1) := by simp only [awMod, awQ]
  have hN : (((2 ^ (2 * p + 1) : ℕ)) : ℤ) = awMod p := by rw [hmod]; push_cast; ring
  refine auCWnatAbs_lt_two_pow (awLow_nonneg (p := p) hl hA) ?_
  rw [hN]
  exact h

/-- `unconsV` on a known `cons`-value. -/
theorem Pipe.auCWunconsVAt {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    {C0 a b : Val} (hC0 : C0 = .cons a b) : Pipe main prog [C0] [a, b] K := by
  intro rest vs hvs s R hR
  have hvs' : vs = .cons a b :: rest := by rw [hvs, hC0]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs2, hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hvs'⟩ s R hR
  obtain ⟨heq1, hrest⟩ := List.cons.inj (hvs2.symm.trans hvs')
  obtain ⟨ha, hb⟩ := Val.cons.inj heq1
  exact ⟨out, s', n, by rw [hout, ha, hb, hrest]; rfl, hev, hn, hstk, hoth⟩

/-- The round word, given its four library pieces. -/
theorem auCWRound_of
    (hMul : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm → ∀ (a b : ℤ), a.natAbs.size < N → b.natAbs.size < N →
      Pipe main prog [Val.int a, Val.int b] [Val.int (a * b)]
        (Cm (max a.natAbs.size b.natAbs.size) + K * (a.natAbs.size + b.natAbs.size + 1)))
    (hCar : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (M lo A : ℤ),
      0 ≤ lo → lo < M → 0 ≤ A → A ≤ M →
      Pipe main prog [Val.int M, Val.int lo, Val.int A]
        [Val.int ((lo + A) - Int.tdiv (lo + A) M * M), Val.int (Int.tdiv (lo + A) M)]
        (K * (isz M + isz lo + isz A + 1)))
    (hRec : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (zr zi : ℤ),
      Pipe main prog [Val.int zr, Val.int zi] [awRec zr zi] (K * (isz zr + isz zi + 1)))
    (hPark : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd)
      (rec li zi lr zr M sh k x y W Pv Lor Loi CHAIN : Val) (S : ℕ),
      (∀ v ∈ [rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv, Lor, Loi], vsz v ≤ S) →
      Pipe main prog [rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv, Lor, Loi, CHAIN]
        [Pv, lr, li, Val.cons rec CHAIN] (K * (S + 1)))
    (hDisc : ∀ (p : ℕ) (W x y : ℤ), 1 ≤ p → W.natAbs ≤ 2 ^ p → x ^ 2 + y ^ 2 ≤ 4 ^ p →
      x.natAbs ≤ 2 ^ p ∧ y.natAbs ≤ 2 ^ p ∧
      0 ≤ W * x + awSh p ∧ W * x + awSh p ≤ awMod p ∧
      0 ≤ W * y + awSh p ∧ W * y + awSh p ≤ awMod p)
    (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm →
      ∀ (p : ℕ) (W x y lo_r lo_i : ℤ) (CHAIN : HvdH.Val) (T : List HvdH.Val),
      1 ≤ p → K * p < N → W.natAbs ≤ 2 ^ p → x ^ 2 + y ^ 2 ≤ 4 ^ p →
      0 ≤ lo_r → lo_r < awMod p → 0 ≤ lo_i → lo_i < awMod p →
      HvdH.WordR main prog
        (fun vs => vs = AwPair W x y :: Val.int (p : ℤ) :: Val.int lo_r :: Val.int lo_i :: CHAIN :: T)
        (fun _ out => out = Val.int (p : ℤ)
          :: Val.int (awLow p lo_r (W * x + awSh p))
          :: Val.int (awLow p lo_i (W * y + awSh p))
          :: Val.cons (awRec (awCar p lo_r (W * x + awSh p)) (awCar p lo_i (W * y + awSh p))) CHAIN :: T)
        (fun _ => K * (Cm (K * p) + p + 1)) := by
  obtain ⟨mulP, Km, hmul⟩ := hMul
  obtain ⟨carP, Kc, hcar⟩ := hCar
  obtain ⟨recP, Kr, hrec⟩ := hRec
  obtain ⟨parkP, Kpw, hpark⟩ := hPark
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨dupP, Kdup, hdup⟩ := hk.dup
  obtain ⟨dropP, Kdrop, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨unconsP, Kunc, hunc⟩ := hk.unconsV
  obtain ⟨swapP, Kswap, hswap⟩ := hk.swap
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨mulSP, Kms, hmulS⟩ := hi.mulS
  obtain ⟨pow2P, Kpow2, hpow2⟩ := hi.pow2
  set KS : ℕ := Kpick + Kroll + Kdup + Kdrop + Kpush + Kunc + Kswap + Kadd + Kms + Kpow2
      + Km + Kc + Kr + Kpw + 1 with hKS
  have hKpick : Kpick ≤ KS := by omega
  have hKroll : Kroll ≤ KS := by omega
  have hKdup : Kdup ≤ KS := by omega
  have hKdrop : Kdrop ≤ KS := by omega
  have hKpush : Kpush ≤ KS := by omega
  have hKunc : Kunc ≤ KS := by omega
  have hKswap : Kswap ≤ KS := by omega
  have hKadd : Kadd ≤ KS := by omega
  have hKms : Kms ≤ KS := by omega
  have hKpow2 : Kpow2 ≤ KS := by omega
  have hKm : Km ≤ KS := by omega
  have hKc : Kc ≤ KS := by omega
  have hKr : Kr ≤ KS := by omega
  have hKpw : Kpw ≤ KS := by omega
  set KK : ℕ := 1048576 * KS + 64 with hKK
  let prog : HvdH.Cmd := Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (unconsP) swapP) unconsP) (pickP 3)) (pushP (Val.int 2))) mulSP) dupP) pow2P) (pickP 1)) (pushP (Val.int 1))) addP) pow2P) (pickP 3)) (pickP 6)) mulP) (pickP 2)) addP) (pickP 1)) (pickP 9)) swapP) carP) (pickP 6)) (pickP 8)) mulP) (pickP 4)) addP) (pickP 3)) (pickP 12)) swapP) carP) (pickP 3)) (pickP 2)) swapP) recP) parkP
  refine ⟨prog, KK, ?_⟩
  intro main N Cm hmon hMulB p W x y lo_r lo_i CHAIN T hp hKN hW hxy hlr0 hlrM hli0 hliM
  set CS : ℕ := Cm (KK * p) + auCWSC p KS with hCS
  have hSCCS : auCWSC p KS ≤ CS := by rw [hCS]; exact Nat.le_add_left _ _
  let Ap : Val := AwPair W x y
  let ZW : Val := Val.int W
  let Zx : Val := Val.int x
  let Zy : Val := Val.int y
  let Pv : Val := Val.int (p : ℤ)
  let Lor : Val := Val.int lo_r
  let Loi : Val := Val.int lo_i
  let K2 : Val := Val.int (2 * (p : ℤ))
  let K2b : Val := Val.int (1 + 2 * (p : ℤ))
  let Sv : Val := Val.int (awSh p)
  let Mv : Val := Val.int (awMod p)
  let Z1 : Val := Val.int 1
  let Z2 : Val := Val.int 2
  let Cxy : Val := Val.cons (Val.int x) (Val.int y)
  let Ar : ℤ := W * x + awSh p
  let Ai : ℤ := W * y + awSh p
  let lr : ℤ := awLow p lo_r Ar
  let zr : ℤ := awCar p lo_r Ar
  let li : ℤ := awLow p lo_i Ai
  let zi : ℤ := awCar p lo_i Ai
  let Lrv : Val := Val.int lr
  let Zrv : Val := Val.int zr
  let Liv : Val := Val.int li
  let Ziv : Val := Val.int zi
  let Wxv : Val := Val.int (W * x)
  let Wyv : Val := Val.int (W * y)
  let Arv : Val := Val.int Ar
  let Aiv : Val := Val.int Ai
  let Rc : Val := awRec zr zi

  -- arithmetic
  have hKK2 : 2 ≤ KK := by rw [hKK]; omega
  have hp1 : 1 ≤ p := hp
  have hKN2 : p + 1 < N := by
    have h2 : p + 1 ≤ KK * p := by
      calc p + 1 ≤ 2 * p := by omega
        _ ≤ KK * p := Nat.mul_le_mul_right p hKK2
    omega
  obtain ⟨hxb, hyb, hAr0, hArM, hAi0, hAiM⟩ := hDisc p W x y hp hW hxy
  have hmod2 : awMod p = (2 : ℤ) ^ (2 * p + 1) := by simp only [awMod, awQ]
  have hmodN : (((2 ^ (2 * p + 1) : ℕ)) : ℤ) = awMod p := by rw [hmod2]; push_cast; ring
  have hWxb : (W * x).natAbs ≤ 2 ^ (2 * p) := by
    rw [Int.natAbs_mul]
    calc W.natAbs * x.natAbs ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul hW hxb
      _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  have hWyb : (W * y).natAbs ≤ 2 ^ (2 * p) := by
    rw [Int.natAbs_mul]
    calc W.natAbs * y.natAbs ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul hW hyb
      _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  have hArnat : (W * x + awSh p).natAbs ≤ 2 ^ (2 * p + 1) :=
    auCWnatAbs_le_two_pow hAr0 (by rw [hmodN]; exact hArM)
  have hAinat : (W * y + awSh p).natAbs ≤ 2 ^ (2 * p + 1) :=
    auCWnatAbs_le_two_pow hAi0 (by rw [hmodN]; exact hAiM)
  -- sizes
  have hszW : isz W ≤ SZ p := by
    have h : isz W ≤ p + 3 := auCWisz_le_of_natAbs_le hW
    exact auCWle_SZ (by omega)
  have hszx : isz x ≤ SZ p := by
    have h : isz x ≤ p + 3 := auCWisz_le_of_natAbs_le hxb
    exact auCWle_SZ (by omega)
  have hszy : isz y ≤ SZ p := by
    have h : isz y ≤ p + 3 := auCWisz_le_of_natAbs_le hyb
    exact auCWle_SZ (by omega)
  have hszp : isz ((p : ℤ)) ≤ SZ p := by
    have h : isz ((p : ℤ)) ≤ p + 3 := auCWisz_le_of_natAbs_le (k := p) (z := (p : ℤ)) (by
      rw [Int.natAbs_natCast]
      exact le_of_lt (Nat.lt_two_pow_self (n := p)))
    exact auCWle_SZ (by omega)
  have hszlor : isz lo_r ≤ SZ p := by
    have h : isz lo_r ≤ 2 * p + 1 + 2 := auCWisz_le_of_natAbs_lt (k := 2 * p + 1) (z := lo_r) (by
      show lo_r.natAbs < 2 ^ (2 * p + 1)
      exact auCWnatAbs_lt_two_pow hlr0 (by rw [hmodN]; exact hlrM))
    exact auCWle_SZ (by omega)
  have hszloi : isz lo_i ≤ SZ p := by
    have h : isz lo_i ≤ 2 * p + 1 + 2 := auCWisz_le_of_natAbs_lt (k := 2 * p + 1) (z := lo_i) (by
      show lo_i.natAbs < 2 ^ (2 * p + 1)
      exact auCWnatAbs_lt_two_pow hli0 (by rw [hmodN]; exact hliM))
    exact auCWle_SZ (by omega)
  have hszK2 : isz (2 * (p : ℤ)) ≤ SZ p := by
    have h : isz (2 * (p : ℤ)) ≤ 2 * p + 3 := auCWisz_le_of_natAbs_le (k := 2 * p) (z := 2 * (p : ℤ)) (by
      rw [show (2 : ℤ) * (p : ℤ) = ((2 * p : ℕ) : ℤ) from by push_cast; ring, Int.natAbs_natCast]
      exact le_of_lt (Nat.lt_two_pow_self (n := 2 * p)))
    exact auCWle_SZ (by omega)
  have hszK2b : isz (1 + 2 * (p : ℤ)) ≤ SZ p := by
    have h : isz (1 + 2 * (p : ℤ)) ≤ 2 * p + 1 + 3 :=
      auCWisz_le_of_natAbs_le (k := 2 * p + 1) (z := 1 + 2 * (p : ℤ)) (by
        rw [show (1 : ℤ) + 2 * (p : ℤ) = ((2 * p + 1 : ℕ) : ℤ) from by push_cast; ring,
          Int.natAbs_natCast]
        exact le_of_lt (Nat.lt_two_pow_self (n := 2 * p + 1)))
    exact auCWle_SZ (by omega)
  have hszSv : isz (awSh p) ≤ SZ p := by
    have h : isz (awSh p) ≤ 2 * p + 3 := auCWisz_le_of_natAbs_le (k := 2 * p) (z := awSh p) (by
      have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
      simpa only [show awSh p = (2 : ℤ) ^ (2 * p) from rfl, Int.natAbs_pow, h2]
        using (le_refl (2 ^ (2 * p)) : 2 ^ (2 * p) ≤ 2 ^ (2 * p)))
    exact auCWle_SZ (by omega)
  have hszMv : isz (awMod p) ≤ SZ p := by
    have h : isz (awMod p) ≤ 2 * p + 1 + 3 := auCWisz_le_of_natAbs_le (k := 2 * p + 1) (z := awMod p) (by
      have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
      simpa only [show awMod p = (2 : ℤ) ^ (2 * p + 1) from by simp only [awMod, awQ],
        Int.natAbs_pow, h2]
        using (le_refl (2 ^ (2 * p + 1)) : 2 ^ (2 * p + 1) ≤ 2 ^ (2 * p + 1)))
    exact auCWle_SZ (by omega)
  have hsz0 : isz ((0 : ℤ)) ≤ SZ p := by
    have h : ((0 : ℤ)).natAbs.size ≤ 0 := Nat.size_le.mpr (by norm_num)
    have h2 : isz ((0 : ℤ)) ≤ 2 := by simp only [isz]; omega
    exact auCWle_SZ (by omega)
  have hsz1 : isz ((1 : ℤ)) ≤ SZ p := by
    have h : ((1 : ℤ)).natAbs.size ≤ 1 := Nat.size_le.mpr (by norm_num)
    have h2 : isz ((1 : ℤ)) ≤ 3 := by simp only [isz]; omega
    exact auCWle_SZ (by omega)
  have hsz2 : isz ((2 : ℤ)) ≤ SZ p := by
    have h : ((2 : ℤ)).natAbs.size ≤ 2 := Nat.size_le.mpr (by norm_num)
    have h2 : isz ((2 : ℤ)) ≤ 4 := by simp only [isz]; omega
    exact auCWle_SZ (by omega)
  have hsz2s : isz ((2 : ℤ)) ≤ 4 := by
    have h : ((2 : ℤ)).natAbs.size ≤ 2 := Nat.size_le.mpr (by norm_num)
    simp only [isz]; omega
  have hszps : isz ((p : ℤ)) ≤ p + 3 := auCWisz_le_of_natAbs_le (k := p) (z := (p : ℤ)) (by
    rw [Int.natAbs_natCast]
    exact le_of_lt (Nat.lt_two_pow_self (n := p)))
  have hszWx : isz (W * x) ≤ SZ p := by
    have h : isz (W * x) ≤ 2 * p + 3 := auCWisz_le_of_natAbs_le (k := 2 * p) (z := W * x) hWxb
    exact auCWle_SZ (by omega)
  have hszWy : isz (W * y) ≤ SZ p := by
    have h : isz (W * y) ≤ 2 * p + 3 := auCWisz_le_of_natAbs_le (k := 2 * p) (z := W * y) hWyb
    exact auCWle_SZ (by omega)
  have hszAr : isz Ar ≤ SZ p := by
    have h : isz Ar ≤ 2 * p + 1 + 3 := auCWisz_le_of_natAbs_le (k := 2 * p + 1) (z := Ar) (by
      show (W * x + awSh p).natAbs ≤ 2 ^ (2 * p + 1)
      exact hArnat)
    exact auCWle_SZ (by omega)
  have hszAi : isz Ai ≤ SZ p := by
    have h : isz Ai ≤ 2 * p + 1 + 3 := auCWisz_le_of_natAbs_le (k := 2 * p + 1) (z := Ai) (by
      show (W * y + awSh p).natAbs ≤ 2 ^ (2 * p + 1)
      exact hAinat)
    exact auCWle_SZ (by omega)
  have hszLr : isz lr ≤ SZ p := by
    have h : isz lr ≤ 2 * p + 1 + 2 := auCWisz_le_of_natAbs_lt (k := 2 * p + 1) (z := lr) (by
      show (awLow p lo_r Ar).natAbs < 2 ^ (2 * p + 1)
      exact auCWawLow_natAbs_lt hlr0 hAr0)
    exact auCWle_SZ (by omega)
  have hszLi : isz li ≤ SZ p := by
    have h : isz li ≤ 2 * p + 1 + 2 := auCWisz_le_of_natAbs_lt (k := 2 * p + 1) (z := li) (by
      show (awLow p lo_i Ai).natAbs < 2 ^ (2 * p + 1)
      exact auCWawLow_natAbs_lt hli0 hAi0)
    exact auCWle_SZ (by omega)
  have hzrcar : zr = 0 ∨ zr = 1 :=
    auCWawCar_eq_zero_or_one_le hlr0 hAr0 hlrM hArM
  have hzicar : zi = 0 ∨ zi = 1 :=
    auCWawCar_eq_zero_or_one_le hli0 hAi0 hliM hAiM
  have hszZr : isz zr ≤ SZ p := by
    rcases hzrcar with h | h
    · rw [h]; exact hsz0
    · rw [h]; exact hsz1
  have hszZi : isz zi ≤ SZ p := by
    rcases hzicar with h | h
    · rw [h]; exact hsz0
    · rw [h]; exact hsz1
  -- sizes (vsz form)
  have hsZW : vsz ZW ≤ SZ p := by show vsz (Val.int W) ≤ SZ p; rw [vsz_int]; exact hszW
  have hsZx : vsz Zx ≤ SZ p := by show vsz (Val.int x) ≤ SZ p; rw [vsz_int]; exact hszx
  have hsZy : vsz Zy ≤ SZ p := by show vsz (Val.int y) ≤ SZ p; rw [vsz_int]; exact hszy
  have hsPv : vsz Pv ≤ SZ p := by show vsz (Val.int (p : ℤ)) ≤ SZ p; rw [vsz_int]; exact hszp
  have hsLor : vsz Lor ≤ SZ p := by show vsz (Val.int lo_r) ≤ SZ p; rw [vsz_int]; exact hszlor
  have hsLoi : vsz Loi ≤ SZ p := by show vsz (Val.int lo_i) ≤ SZ p; rw [vsz_int]; exact hszloi
  have hsK2 : vsz K2 ≤ SZ p := by show vsz (Val.int (2 * (p : ℤ))) ≤ SZ p; rw [vsz_int]; exact hszK2
  have hsK2b : vsz K2b ≤ SZ p := by
    show vsz (Val.int (1 + 2 * (p : ℤ))) ≤ SZ p; rw [vsz_int]; exact hszK2b
  have hsSv : vsz Sv ≤ SZ p := by show vsz (Val.int (awSh p)) ≤ SZ p; rw [vsz_int]; exact hszSv
  have hsMv : vsz Mv ≤ SZ p := by show vsz (Val.int (awMod p)) ≤ SZ p; rw [vsz_int]; exact hszMv
  have hsZ1 : vsz Z1 ≤ SZ p := by show vsz (Val.int (1 : ℤ)) ≤ SZ p; rw [vsz_int]; exact hsz1
  have hsZ2 : vsz Z2 ≤ SZ p := by show vsz (Val.int (2 : ℤ)) ≤ SZ p; rw [vsz_int]; exact hsz2
  have hsWxv : vsz Wxv ≤ SZ p := by show vsz (Val.int (W * x)) ≤ SZ p; rw [vsz_int]; exact hszWx
  have hsWyv : vsz Wyv ≤ SZ p := by show vsz (Val.int (W * y)) ≤ SZ p; rw [vsz_int]; exact hszWy
  have hsArv : vsz Arv ≤ SZ p := by show vsz (Val.int Ar) ≤ SZ p; rw [vsz_int]; exact hszAr
  have hsAiv : vsz Aiv ≤ SZ p := by show vsz (Val.int Ai) ≤ SZ p; rw [vsz_int]; exact hszAi
  have hsLrv : vsz Lrv ≤ SZ p := by show vsz (Val.int lr) ≤ SZ p; rw [vsz_int]; exact hszLr
  have hsZrv : vsz Zrv ≤ SZ p := by show vsz (Val.int zr) ≤ SZ p; rw [vsz_int]; exact hszZr
  have hsLiv : vsz Liv ≤ SZ p := by show vsz (Val.int li) ≤ SZ p; rw [vsz_int]; exact hszLi
  have hsZiv : vsz Ziv ≤ SZ p := by show vsz (Val.int zi) ≤ SZ p; rw [vsz_int]; exact hszZi
  have hsRc : vsz Rc ≤ SZ p := by
    show vsz (awRec zr zi) ≤ SZ p
    have h := auCWvsz_awRec_le zr zi
    have hp8 : SZ p = 8 * p + 8 := rfl
    omega
  have hsCxy : vsz Cxy ≤ SZ p := by
    show vsz (Val.cons (Val.int x) (Val.int y)) ≤ SZ p
    have hx3 : isz x ≤ p + 3 := auCWisz_le_of_natAbs_le hxb
    have hy3 : isz y ≤ p + 3 := auCWisz_le_of_natAbs_le hyb
    have hszc : vsz (Val.cons (Val.int x) (Val.int y)) = vsz (Val.int x) + vsz (Val.int y) + 1 :=
      auRound_vsz_cons _ _
    rw [hszc, vsz_int, vsz_int]
    have hp8 : SZ p = 8 * p + 8 := rfl
    omega
  -- sizes of the operands of the outer products
  have hWsize2 : W.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt hW (Nat.pow_lt_pow_right one_lt_two (by omega))
  have hxsize2 : x.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt hxb (Nat.pow_lt_pow_right one_lt_two (by omega))
  have hysize2 : y.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt hyb (Nat.pow_lt_pow_right one_lt_two (by omega))
  have hWsize : W.natAbs.size < N := by omega
  have hxsize : x.natAbs.size < N := by omega
  have hysize : y.natAbs.size < N := by omega
  have htoNatK2 : (2 * (p : ℤ)).toNat ≤ SZ p := by
    have h : (2 * (p : ℤ)).toNat = 2 * p := auCWtoNat_two_mul p
    rw [h]
    have hp8 : SZ p = 8 * p + 8 := rfl
    omega
  have htoNatK2b : (1 + 2 * (p : ℤ)).toNat ≤ SZ p := by
    have h : (1 + 2 * (p : ℤ)).toNat = 2 * p + 1 := auCWtoNat_two_mul_add_one p
    rw [h]
    have hp8 : SZ p = 8 * p + 8 := rfl
    omega
  have hmaxWx : max W.natAbs.size x.natAbs.size ≤ KK * p := by
    have h1 : max W.natAbs.size x.natAbs.size ≤ p + 1 := max_le hWsize2 hxsize2
    have h2 : p + 1 ≤ KK * p := by
      calc p + 1 ≤ 2 * p := by omega
        _ ≤ KK * p := Nat.mul_le_mul_right p hKK2
    omega
  have hmaxWy : max W.natAbs.size y.natAbs.size ≤ KK * p := by
    have h1 : max W.natAbs.size y.natAbs.size ≤ p + 1 := max_le hWsize2 hysize2
    have h2 : p + 1 ≤ KK * p := by
      calc p + 1 ≤ 2 * p := by omega
        _ ≤ KK * p := Nat.mul_le_mul_right p hKK2
    omega

  have s1 : Pipe main unconsP [Ap, Pv, Lor, Loi, CHAIN] [ZW, Cxy, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Pv, Lor, Loi, CHAIN]
      (Pipe.auCWunconsVAt hunc (C0 := AwPair W x y) (a := Val.int W) (b := Cxy) rfl)) (auCWle_SC_const hKunc)
  have s2 : Pipe main swapP [ZW, Cxy, Pv, Lor, Loi, CHAIN] [Cxy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Pv, Lor, Loi, CHAIN]
      (Pipe.swap main hswap ZW Cxy)) (auCWle_SC_two1 hKswap hsZW hsCxy)
  have s3 : Pipe main unconsP [Cxy, ZW, Pv, Lor, Loi, CHAIN] [Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.auCWunconsVAt hunc (C0 := Cxy) (a := Val.int x) (b := Val.int y) rfl)) (auCWle_SC_const hKunc)
  have s4 : Pipe main (pickP 3) [Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Pv, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4 = [Zx, Zy, ZW, Pv] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hsZx
      · exact hsZy
      · exact hsZW
      · exact hsPv
    refine Pipe.le (Pipe.pickAt main hpick (A := [Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 3) (by simp)
      (v := Pv) (by simp)) (auCWle_SC_roll hKpick (k := 3) (by omega) hm)
  have s5 : Pipe main (pushP (Val.int 2)) [Pv, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Z2, Pv, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.pushOnAny (T := [Pv, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (hpush main (Val.int 2)))
      (auCWle_SC_one hKpush hsZ2)
  have s6 : Pipe main mulSP [Z2, Pv, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.binOp (hmulS main) (a := (2:ℤ)) (b := (p:ℤ)) trivial)) (auCWle_SC_mul_small hKms hsz2s hszps)
  have s7 : Pipe main dupP [K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [K2, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (Pipe.dup main hdup K2))
      (auCWle_SC_one hKdup hsK2)
  have s8 : Pipe main pow2P [K2, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.rw (Pipe.le (Pipe.appendTail [K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.unOp (hpow2 main) (a := 2 * (p:ℤ)) (by positivity))) (auCWle_SC_two hKpow2 htoNatK2 hszK2))
      (by rw [auCWpow_two_mul p]; rfl)
  have s9 : Pipe main (pickP 1) [Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [K2, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 2, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 2 = [Sv, K2] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hsSv
      · exact hsK2
    refine Pipe.le (Pipe.pickAt main hpick (A := [Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 1) (by simp)
      (v := K2) (by simp)) (auCWle_SC_roll hKpick (k := 1) (by omega) hm)
  have s10 : Pipe main (pushP (Val.int 1)) [K2, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Z1, K2, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.pushOnAny (T := [K2, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (hpush main (Val.int 1)))
      (auCWle_SC_one hKpush hsZ1)
  have s11 : Pipe main addP [Z1, K2, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [K2b, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.binOp (hadd main) (a := (1:ℤ)) (b := 2 * (p:ℤ)) trivial)) (auCWle_SC_two hKadd hsz1 hszK2)
  have s12 : Pipe main pow2P [K2b, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.rw (Pipe.le (Pipe.appendTail [Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.unOp (hpow2 main) (a := 1 + 2 * (p:ℤ)) (by positivity))) (auCWle_SC_two hKpow2 htoNatK2b hszK2b))
      (by rw [auCWpow_two_mul_add_one p]; rfl)
  have s13 : Pipe main (pickP 3) [Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Zx, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4 = [Mv, Sv, K2, Zx] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hsMv
      · exact hsSv
      · exact hsK2
      · exact hsZx
    refine Pipe.le (Pipe.pickAt main hpick (A := [Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 3) (by simp)
      (v := Zx) (by simp)) (auCWle_SC_roll hKpick (k := 3) (by omega) hm)
  have s14 : Pipe main (pickP 6) [Zx, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [ZW, Zx, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Zx, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 7, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Zx, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 7 = [Zx, Mv, Sv, K2, Zx, Zy, ZW] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsZx
      · exact hsMv
      · exact hsSv
      · exact hsK2
      · exact hsZx
      · exact hsZy
      · exact hsZW
    refine Pipe.le (Pipe.pickAt main hpick (A := [Zx, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 6) (by simp)
      (v := ZW) (by simp)) (auCWle_SC_roll hKpick (k := 6) (by omega) hm)
  have s15 : Pipe main mulP [ZW, Zx, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Wxv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] CS := by
    refine Pipe.le (Pipe.appendTail [Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (hmul main N Cm hmon hMulB W x hWsize hxsize)) ?_
    refine Nat.add_le_add (hmon hmaxWx)
      (auCWle_SC_two1 hKm ?_ ?_)
    · exact auCWle_SZ (by omega)
    · exact auCWle_SZ (by omega)
  have s16 : Pipe main (pickP 2) [Wxv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Sv, Wxv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Wxv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 3, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Wxv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 3 = [Wxv, Mv, Sv] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hsWxv
      · exact hsMv
      · exact hsSv
    refine Pipe.le (Pipe.pickAt main hpick (A := [Wxv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 2) (by simp)
      (v := Sv) (by simp)) (auCWle_SC_roll hKpick (k := 2) (by omega) hm)
  have s17 : Pipe main addP [Sv, Wxv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.rw (Pipe.le (Pipe.appendTail [Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.binOp (hadd main) (a := awSh p) (b := W * x) trivial)) (auCWle_SC_two hKadd hszSv hszWx))
      (by rw [add_comm]; rfl)
  have s18 : Pipe main (pickP 1) [Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 2, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 2 = [Arv, Mv] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hsArv
      · exact hsMv
    refine Pipe.le (Pipe.pickAt main hpick (A := [Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 1) (by simp)
      (v := Mv) (by simp)) (auCWle_SC_roll hKpick (k := 1) (by omega) hm)
  have s19 : Pipe main (pickP 9) [Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Lor, Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 10, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 10 = [Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsMv
      · exact hsArv
      · exact hsMv
      · exact hsSv
      · exact hsK2
      · exact hsZx
      · exact hsZy
      · exact hsZW
      · exact hsPv
      · exact hsLor
    refine Pipe.le (Pipe.pickAt main hpick (A := [Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 9) (by simp)
      (v := Lor) (by simp)) (auCWle_SC_roll hKpick (k := 9) (by omega) hm)
  have s20 : Pipe main swapP [Lor, Mv, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Mv, Lor, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.swap main hswap Lor Mv)) (auCWle_SC_two1 hKswap hsLor hsMv)
  have s21 : Pipe main carP [Mv, Lor, Arv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (hcar main (awMod p) lo_r Ar hlr0 hlrM hAr0 hArM))
      (auCWle_SC_three1 hKc hszMv hszlor hszAr)
  have s22 : Pipe main (pickP 6) [Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 7, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 7 = [Lrv, Zrv, Mv, Sv, K2, Zx, Zy] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsLrv
      · exact hsZrv
      · exact hsMv
      · exact hsSv
      · exact hsK2
      · exact hsZx
      · exact hsZy
    refine Pipe.le (Pipe.pickAt main hpick (A := [Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 6) (by simp)
      (v := Zy) (by simp)) (auCWle_SC_roll hKpick (k := 6) (by omega) hm)
  have s23 : Pipe main (pickP 8) [Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [ZW, Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 9, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 9 = [Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsZy
      · exact hsLrv
      · exact hsZrv
      · exact hsMv
      · exact hsSv
      · exact hsK2
      · exact hsZx
      · exact hsZy
      · exact hsZW
    refine Pipe.le (Pipe.pickAt main hpick (A := [Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 8) (by simp)
      (v := ZW) (by simp)) (auCWle_SC_roll hKpick (k := 8) (by omega) hm)
  have s24 : Pipe main mulP [ZW, Zy, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Wyv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] CS := by
    refine Pipe.le (Pipe.appendTail [Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (hmul main N Cm hmon hMulB W y hWsize hysize)) ?_
    refine Nat.add_le_add (hmon hmaxWy)
      (auCWle_SC_two1 hKm ?_ ?_)
    · exact auCWle_SZ (by omega)
    · exact auCWle_SZ (by omega)
  have s25 : Pipe main (pickP 4) [Wyv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Sv, Wyv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Wyv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 5, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Wyv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 5 = [Wyv, Lrv, Zrv, Mv, Sv] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hsWyv
      · exact hsLrv
      · exact hsZrv
      · exact hsMv
      · exact hsSv
    refine Pipe.le (Pipe.pickAt main hpick (A := [Wyv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 4) (by simp)
      (v := Sv) (by simp)) (auCWle_SC_roll hKpick (k := 4) (by omega) hm)
  have s26 : Pipe main addP [Sv, Wyv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.rw (Pipe.le (Pipe.appendTail [Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.binOp (hadd main) (a := awSh p) (b := W * y) trivial)) (auCWle_SC_two hKadd hszSv hszWy))
      (by rw [add_comm]; rfl)
  have s27 : Pipe main (pickP 3) [Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4 = [Aiv, Lrv, Zrv, Mv] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hsAiv
      · exact hsLrv
      · exact hsZrv
      · exact hsMv
    refine Pipe.le (Pipe.pickAt main hpick (A := [Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 3) (by simp)
      (v := Mv) (by simp)) (auCWle_SC_roll hKpick (k := 3) (by omega) hm)
  have s28 : Pipe main (pickP 12) [Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Loi, Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 13, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 13 = [Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsMv
      · exact hsAiv
      · exact hsLrv
      · exact hsZrv
      · exact hsMv
      · exact hsSv
      · exact hsK2
      · exact hsZx
      · exact hsZy
      · exact hsZW
      · exact hsPv
      · exact hsLor
      · exact hsLoi
    refine Pipe.le (Pipe.pickAt main hpick (A := [Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 12) (by simp)
      (v := Loi) (by simp)) (auCWle_SC_roll hKpick (k := 12) (by omega) hm)
  have s29 : Pipe main swapP [Loi, Mv, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Mv, Loi, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.swap main hswap Loi Mv)) (auCWle_SC_two1 hKswap hsLoi hsMv)
  have s30 : Pipe main carP [Mv, Loi, Aiv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (hcar main (awMod p) lo_i Ai hli0 hliM hAi0 hAiM))
      (auCWle_SC_three1 hKc hszMv hszloi hszAi)
  have s31 : Pipe main (pickP 3) [Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Zrv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 4 = [Liv, Ziv, Lrv, Zrv] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hsLiv
      · exact hsZiv
      · exact hsLrv
      · exact hsZrv
    refine Pipe.le (Pipe.pickAt main hpick (A := [Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 3) (by simp)
      (v := Zrv) (by simp)) (auCWle_SC_roll hKpick (k := 3) (by omega) hm)
  have s32 : Pipe main (pickP 2) [Zrv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Ziv, Zrv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Zrv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 3, vsz v ≤ SZ p := by
      intro v hv
      rw [show ([Zrv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] : List Val).take 3 = [Zrv, Liv, Ziv] from rfl] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hsZrv
      · exact hsLiv
      · exact hsZiv
    refine Pipe.le (Pipe.pickAt main hpick (A := [Zrv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]) (k := 2) (by simp)
      (v := Ziv) (by simp)) (auCWle_SC_roll hKpick (k := 2) (by omega) hm)
  have s33 : Pipe main swapP [Ziv, Zrv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Zrv, Ziv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN]
      (Pipe.swap main hswap Ziv Zrv)) (auCWle_SC_two1 hKswap hsZiv hsZrv)
  have s34 : Pipe main recP [Zrv, Ziv, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Rc, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (auCWSC p KS) := by
    refine Pipe.le (Pipe.appendTail [Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] (hrec main zr zi))
      (auCWle_SC_two1 hKr hszZr hszZi)
  have s35 : Pipe main parkP [Rc, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi, CHAIN] [Pv, Lrv, Liv, Val.cons Rc CHAIN] (auCWSC p KS) := by
    have hm : ∀ v ∈ ([Rc, Liv, Ziv, Lrv, Zrv, Mv, Sv, K2, Zx, Zy, ZW, Pv, Lor, Loi] : List Val), vsz v ≤ SZ p := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsRc
      · exact hsLiv
      · exact hsZiv
      · exact hsLrv
      · exact hsZrv
      · exact hsMv
      · exact hsSv
      · exact hsK2
      · exact hsZx
      · exact hsZy
      · exact hsZW
      · exact hsPv
      · exact hsLor
      · exact hsLoi
    refine Pipe.le (hpark main Rc Liv Ziv Lrv Zrv Mv Sv K2 Zx Zy ZW Pv Lor Loi CHAIN (SZ p) hm)
      (auCWle_SC_one hKpw (le_refl (SZ p)))

  have g1 := s1
  have g2 := Pipe.comp g1 s2
  have g3 := Pipe.comp g2 s3
  have g4 := Pipe.comp g3 s4
  have g5 := Pipe.comp g4 s5
  have g6 := Pipe.comp g5 s6
  have g7 := Pipe.comp g6 s7
  have g8 := Pipe.comp g7 s8
  have g9 := Pipe.comp g8 s9
  have g10 := Pipe.comp g9 s10
  have g11 := Pipe.comp g10 s11
  have g12 := Pipe.comp g11 s12
  have g13 := Pipe.comp g12 s13
  have g14 := Pipe.comp g13 s14
  have g15 := Pipe.comp g14 s15
  have g16 := Pipe.comp g15 s16
  have g17 := Pipe.comp g16 s17
  have g18 := Pipe.comp g17 s18
  have g19 := Pipe.comp g18 s19
  have g20 := Pipe.comp g19 s20
  have g21 := Pipe.comp g20 s21
  have g22 := Pipe.comp g21 s22
  have g23 := Pipe.comp g22 s23
  have g24 := Pipe.comp g23 s24
  have g25 := Pipe.comp g24 s25
  have g26 := Pipe.comp g25 s26
  have g27 := Pipe.comp g26 s27
  have g28 := Pipe.comp g27 s28
  have g29 := Pipe.comp g28 s29
  have g30 := Pipe.comp g29 s30
  have g31 := Pipe.comp g30 s31
  have g32 := Pipe.comp g31 s32
  have g33 := Pipe.comp g32 s33
  have g34 := Pipe.comp g33 s34
  have g35 := Pipe.comp g34 s35
  have hfin : Pipe main prog [Ap, Pv, Lor, Loi, CHAIN] [Pv, Lrv, Liv, Val.cons Rc CHAIN] (35 * CS) := by
    refine Pipe.le g35 ?_
    omega

  have hcw : 35 * CS ≤ KK * (Cm (KK * p) + p + 1) := by
    rw [hCS]
    calc 35 * (Cm (KK * p) + auCWSC p KS) = 35 * Cm (KK * p) + 35 * auCWSC p KS := by ring
      _ ≤ KK * Cm (KK * p) + KK * (p + 1) := Nat.add_le_add
          (Nat.mul_le_mul_right _ (by omega)) (by
            rw [auCWSC]
            have h1 : 35 * (KS * (4096 * (p + 1))) = (35 * 4096 * KS) * (p + 1) := by ring
            rw [h1]
            exact Nat.mul_le_mul_right _ (by omega))
      _ = KK * (Cm (KK * p) + p + 1) := by ring
  exact (Pipe.le hfin hcw) T

theorem auCWRound (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm →
      ∀ (p : ℕ) (W x y lo_r lo_i : ℤ) (CHAIN : HvdH.Val) (T : List HvdH.Val),
      1 ≤ p → K * p < N → W.natAbs ≤ 2 ^ p → x ^ 2 + y ^ 2 ≤ 4 ^ p →
      0 ≤ lo_r → lo_r < Work.Resample.awMod p → 0 ≤ lo_i → lo_i < Work.Resample.awMod p →
      HvdH.WordR main prog
        (fun vs => vs = Work.Resample.AwPair W x y :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int lo_r
          :: HvdH.Val.int lo_i :: CHAIN :: T)
        (fun _ out => out = HvdH.Val.int (p : ℤ)
          :: HvdH.Val.int (Work.Resample.awLow p lo_r (W * x + Work.Resample.awSh p))
          :: HvdH.Val.int (Work.Resample.awLow p lo_i (W * y + Work.Resample.awSh p))
          :: HvdH.Val.cons (Work.Resample.awRec (Work.Resample.awCar p lo_r (W * x + Work.Resample.awSh p))
              (Work.Resample.awCar p lo_i (W * y + Work.Resample.awSh p))) CHAIN :: T)
        (fun _ => K * (Cm (K * p) + p + 1)) :=
  auCWRound_of (auCWIntMulSelf hk hi) (auCWCarLow hk hi) (auCWRecVal hk hi) (auCWPark hk)
    auCWDisc hk hi

end Work.Resample
