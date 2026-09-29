import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.auMapListTail
import Submission.Work.Resample.buWdKit
import Submission.Work.IntLib.encodeNatBridge

set_option maxHeartbeats 8000000

namespace Work.Resample

open HvdH

/-! ## Elementary value-size facts -/

/-- `vsz` of an integer value is `isz`. -/
theorem buVsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  show (Val.int z).enc.length = isz z
  exact Work.IntLib.vsz_int z

/-- `vsz` of a `cons` value. -/
theorem buVsz_cons (a b : Val) : vsz (Val.cons a b) = 1 + vsz a + vsz b := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]
  omega

/-- `vsz` of a list value. -/
theorem buVsz_ofList (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v vs ih =>
    have h : ofList (v :: vs) = Val.cons v (ofList vs) := rfl
    rw [h, buVsz_cons, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- `vsz` of a replicated list of `int 0`. -/
theorem buVsz_ofList_replicate_zero (k : ℕ) :
    vsz (ofList (List.replicate k (Val.int 0))) = 3 * k + 1 := by
  induction k with
  | zero => simp [ofList, vsz, Val.enc]
  | succ k ih =>
    rw [List.replicate_succ]
    have h : ofList (Val.int 0 :: List.replicate k (Val.int 0))
        = Val.cons (Val.int 0) (ofList (List.replicate k (Val.int 0))) := rfl
    rw [h, buVsz_cons, ih, buVsz_int]
    have h0 : isz (0 : ℤ) = 2 := by simp [isz]
    rw [h0]
    ring

/-! ## The list of indices `0, …, s-1` and the diagonal-weight element map -/

/-- The list of indices `0, …, s-1` as integer values. -/
def buIdxList (s : ℕ) : List Val := (List.range s).map (fun i : ℕ => Val.int (i : ℤ))

theorem buIdxList_length (s : ℕ) : (buIdxList s).length = s := by simp [buIdxList]

/-- The element function of the diagonal-weight list: `int ℓ` becomes `int (buWd p α s t ℓ)`. -/
noncomputable def buWdOf (p α s t : ℕ) : Val → Val
  | .int z => .int (buWd p α s t z)
  | _ => .nil

theorem buWdOf_int (p α s t : ℕ) (z : ℤ) :
    buWdOf p α s t (.int z) = .int (buWd p α s t z) := rfl

/-- Mapping the index list with `buWdOf` gives the `range`-list of the diagonal weights. -/
theorem buIdxList_map (p α s t : ℕ) :
    (buIdxList s).map (buWdOf p α s t)
      = (List.range s).map (fun i : ℕ => Val.int (buWd p α s t (i : ℤ))) := by
  rw [buIdxList, List.map_map]
  apply List.map_congr_left
  intro i _
  exact buWdOf_int p α s t (i : ℤ)

/-- `(ofFn f).map g`, with `f` integer-valued, is the `range`-map of `g ∘ f`. -/
theorem map_ofFn_map_range {s : ℕ} (f : Fin s → ℤ) (g : ℤ → Val) (h : ℕ → ℤ)
    (hf : ∀ i (hi : i < s), f ⟨i, hi⟩ = h i) :
    (List.ofFn f).map g = (List.range s).map (fun i : ℕ => g (h i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < s := by simpa using h2
    rw [List.getElem_map, List.getElem_map, List.getElem_ofFn, List.getElem_range]
    exact congrArg g (hf i hi)

/-- `buL9` is `ofList` of the index list mapped with `buWdOf`. -/
theorem buL9_eq_ofList (p α s t : ℕ) :
    buL9 p α s t
      = ofList ((List.range s).map (fun i : ℕ => Val.int (buWd p α s t (i : ℤ)))) := by
  simp only [buL9, zl]
  rw [map_ofFn_map_range (fun i : Fin s => buWd p α s t (i : ℤ)) Val.int
      (fun i => buWd p α s t (i : ℤ)) (fun i hi => rfl)]

/-! ## Cost absorbers -/

/-- `C ≤ (p+1)^C`. -/
theorem buPow_le_self (p C : ℕ) (hp : 1 ≤ p) : C ≤ (p + 1) ^ C := by
  have h1 : C < 2 ^ C := Nat.lt_two_pow_self (n := C)
  have h2 : 2 ^ C ≤ (p + 1) ^ C := Nat.pow_le_pow_left (by omega) C
  omega

/-- `C·(p+1)^n ≤ (p+1)^(C+n)`. -/
theorem buCoeff_pow_le (p C n : ℕ) (hp : 1 ≤ p) : C * (p + 1) ^ n ≤ (p + 1) ^ (C + n) := by
  calc C * (p + 1) ^ n ≤ (p + 1) ^ C * (p + 1) ^ n := Nat.mul_le_mul_right _ (buPow_le_self p C hp)
    _ = (p + 1) ^ (C + n) := by rw [← pow_add]

/-- Sum of four terms, each at most `(s+1)(p+1)^M`. -/
theorem buFour_le {s p M a b c d : ℕ} (hp : 2 ≤ p + 1)
    (h1 : a ≤ (s + 1) * (p + 1) ^ M) (h2 : b ≤ (s + 1) * (p + 1) ^ M)
    (h3 : c ≤ (s + 1) * (p + 1) ^ M) (h4 : d ≤ (s + 1) * (p + 1) ^ M) :
    a + (b + (c + d)) ≤ (s + 1) * (p + 1) ^ (M + 2) := by
  have hX : a + (b + (c + d)) ≤ 4 * ((s + 1) * (p + 1) ^ M) := by linarith
  have hY : 4 * ((s + 1) * (p + 1) ^ M) ≤ (s + 1) * (p + 1) ^ (M + 2) := by
    calc 4 * ((s + 1) * (p + 1) ^ M) = ((s + 1) * (p + 1) ^ M) * 4 := by ring
      _ ≤ ((s + 1) * (p + 1) ^ M) * (p + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith [hp])
      _ = (s + 1) * ((p + 1) ^ M * (p + 1) ^ 2) := by ring
      _ = (s + 1) * (p + 1) ^ (M + 2) := by rw [← pow_add]
  linarith

/-- Cost of a `mapList` over `s` elements: `s·(c + Kml·(L+1)) + Kml`. -/
theorem buMapCost_le {s c Kml L p M : ℕ} (hp : 2 ≤ p + 1)
    (hc : c ≤ (p + 1) ^ M) (hL : Kml * (L + 1) ≤ (p + 1) ^ M) (hK : Kml ≤ M) :
    s * (c + Kml * (L + 1)) + Kml ≤ (s + 1) * (p + 1) ^ (M + 1) := by
  have h1 : c + Kml * (L + 1) ≤ 2 * (p + 1) ^ M := by linarith
  have h2 : c + Kml * (L + 1) ≤ (p + 1) ^ (M + 1) := by
    refine le_trans h1 ?_
    calc 2 * (p + 1) ^ M ≤ (p + 1) * (p + 1) ^ M := Nat.mul_le_mul_right _ hp
      _ = (p + 1) ^ (M + 1) := by rw [pow_succ]; ring
  have h3 : Kml ≤ (p + 1) ^ (M + 1) := by
    refine le_trans hK ?_
    refine le_trans (buPow_le_self p M (by omega)) ?_
    exact Nat.pow_le_pow_right (by omega) (by omega)
  calc s * (c + Kml * (L + 1)) + Kml ≤ s * (p + 1) ^ (M + 1) + (p + 1) ^ (M + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h2) h3
    _ = (s + 1) * (p + 1) ^ (M + 1) := by ring

/-! ## The word -/

/-! ## Cost helpers for the index-range word -/

/-- Three terms, each at most `(p+1)^m`, sum to at most `(p+1)^(m+2)`. -/
theorem buAdd3_le {p m a b c : ℕ} (hp : 2 ≤ p + 1)
    (h1 : a ≤ (p + 1) ^ m) (h2 : b ≤ (p + 1) ^ m) (h3 : c ≤ (p + 1) ^ m) :
    a + (b + c) ≤ (p + 1) ^ (m + 2) := by
  have hX : a + (b + c) ≤ 3 * (p + 1) ^ m := by linarith
  have hq : (3 : ℕ) ≤ (p + 1) ^ 2 := by nlinarith [hp]
  have hY : 3 * (p + 1) ^ m ≤ (p + 1) ^ (m + 2) := by
    calc 3 * (p + 1) ^ m = (p + 1) ^ m * 3 := by ring
      _ ≤ (p + 1) ^ m * (p + 1) ^ 2 := Nat.mul_le_mul_left _ hq
      _ = (p + 1) ^ (m + 2) := by rw [← pow_add]
  linarith

/-- `x^a + x^b ≤ x^c` when `a ≤ b`, `b + 1 ≤ c` and `x ≥ 2`. -/
theorem buPow_add_pow_le {x a b c : ℕ} (hx : 2 ≤ x) (hab : a ≤ b) (hbc : b + 1 ≤ c) :
    x ^ a + x ^ b ≤ x ^ c := by
  have h1 : x ^ a ≤ x ^ b := Nat.pow_le_pow_right (by omega) hab
  have h2 : x ^ b + x ^ b ≤ x ^ (b + 1) := by
    calc x ^ b + x ^ b = 2 * x ^ b := by ring
      _ ≤ x * x ^ b := Nat.mul_le_mul_right _ hx
      _ = x ^ b * x := by ring
      _ = x ^ (b + 1) := by rw [pow_succ]
  have h3 : x ^ (b + 1) ≤ x ^ c := Nat.pow_le_pow_right (by omega) hbc
  calc x ^ a + x ^ b ≤ x ^ b + x ^ b := Nat.add_le_add_right h1 _
    _ ≤ x ^ c := le_trans h2 h3

/-- Five terms, each at most `(s+1)(p+1)^M`, sum to at most `(s+1)(p+1)^(M+3)`. -/
theorem buFive_le {s p M a b c d e : ℕ} (hp : 2 ≤ p + 1)
    (h1 : a ≤ (s + 1) * (p + 1) ^ M) (h2 : b ≤ (s + 1) * (p + 1) ^ M)
    (h3 : c ≤ (s + 1) * (p + 1) ^ M) (h4 : d ≤ (s + 1) * (p + 1) ^ M)
    (h5 : e ≤ (s + 1) * (p + 1) ^ M) :
    a + (b + (c + (d + e))) ≤ (s + 1) * (p + 1) ^ (M + 3) := by
  have hX : a + (b + (c + (d + e))) ≤ 5 * ((s + 1) * (p + 1) ^ M) := by
    have h5X : (5 : ℕ) * ((s + 1) * (p + 1) ^ M)
        = ((s + 1) * (p + 1) ^ M) + (((s + 1) * (p + 1) ^ M)
          + (((s + 1) * (p + 1) ^ M) + (((s + 1) * (p + 1) ^ M)
            + ((s + 1) * (p + 1) ^ M)))) := by ring
    rw [h5X]
    exact Nat.add_le_add h1 (Nat.add_le_add h2 (Nat.add_le_add h3 (Nat.add_le_add h4 h5)))
  have hq : (5 : ℕ) ≤ (p + 1) ^ 3 := by
    have h23 : (2 : ℕ) ^ 3 ≤ (p + 1) ^ 3 := Nat.pow_le_pow_left hp 3
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  have hY : 5 * ((s + 1) * (p + 1) ^ M) ≤ (s + 1) * (p + 1) ^ (M + 3) := by
    calc 5 * ((s + 1) * (p + 1) ^ M) = ((s + 1) * (p + 1) ^ M) * 5 := by ring
      _ ≤ ((s + 1) * (p + 1) ^ M) * (p + 1) ^ 3 := Nat.mul_le_mul_left _ hq
      _ = (s + 1) * ((p + 1) ^ M * (p + 1) ^ 3) := by ring
      _ = (s + 1) * (p + 1) ^ (M + 3) := by rw [← pow_add]
  linarith

/-- A phase cost `K · A` with `A ≤ (s+1)(p+1)^10` is at most `(s+1)(p+1)^M` when `K+10 ≤ M`. -/
theorem buPhase_le {s p K M A : ℕ} (hp : 1 ≤ p) (hA : A ≤ (s + 1) * (p + 1) ^ 10)
    (hKM : K + 10 ≤ M) : K * A ≤ (s + 1) * (p + 1) ^ M := by
  calc K * A ≤ (p + 1) ^ K * A := Nat.mul_le_mul_right A (buPow_le_self p K hp)
    _ ≤ (p + 1) ^ K * ((s + 1) * (p + 1) ^ 10) := Nat.mul_le_mul_left _ hA
    _ = (s + 1) * ((p + 1) ^ K * (p + 1) ^ 10) := by ring
    _ = (s + 1) * (p + 1) ^ (K + 10) := by rw [← pow_add]
    _ ≤ (s + 1) * (p + 1) ^ M := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKM)

/-- Read the index out of a label `cons (int i) _`. -/
def buIdxOf : Val → Val
  | .cons (.int z) _ => .int z
  | _ => .nil

theorem buIdxOf_cons (i : ℤ) (b : Val) : buIdxOf (Val.cons (Val.int i) b) = Val.int i := rfl

/-- `unconsV` as a `Pipe`. -/
theorem Pipe.unconsVOne {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    (a b : Val) : Pipe main prog [.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv2 : vs = .cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv2⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.val_cons_inj3 (hvs'.symm.trans hv2)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

/-- The index-range word: from `int s` produce `ofList [int 0, …, int (s-1)]`. -/
theorem buRangeWord_self (KL : HvdH.KernelLib) (LL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p s : ℕ) (hs : 1 ≤ s) (hsp : s < 2 ^ p)
      (hp : 100 ≤ p),
      Work.Resample.Pipe main prog [HvdH.Val.int (s : ℤ)]
        [HvdH.ofList ((List.range s).map (fun i : ℕ => HvdH.Val.int (i : ℤ)))]
        (K * (s + 1) * (p + 1) ^ K) := by
  obtain ⟨pushProg, Kpu, hpush⟩ := KL.pushVal
  obtain ⟨swapProg, Ksw, hswap⟩ := KL.swap
  obtain ⟨replProg, Krepl, hrepl⟩ := LL.replicate
  obtain ⟨enumProg, Kenum, henum⟩ := LL.enumerate
  obtain ⟨ucProg, Kuc, huc⟩ := KL.unconsV
  obtain ⟨dropProg, Kdr, hdrop⟩ := KL.drop
  obtain ⟨comb, Kml, hML⟩ := MapListField.of_kernel KL
  set Nc : ℕ := Kuc + Ksw + Kdr + Kml + 10 with hNc
  set M : ℕ := Kpu + Krepl + Kenum + Nc + 10 with hM
  refine ⟨Cmd.seq (pushProg (Val.int 0))
    (Cmd.seq swapProg (Cmd.seq replProg (Cmd.seq enumProg
      (comb (Cmd.seq ucProg (Cmd.seq swapProg dropProg)))))), M + 3, ?_⟩
  intro main p s hs hsp hp
  have hbase : 2 ≤ p + 1 := by omega
  have hp1 : 1 ≤ p := by omega
  have hS3 : buSZ p + 3 ≤ (p + 1) ^ 8 := by have := buSZ_add8_le p hp; omega
  have hS4 : (buSZ p + 3) + 1 ≤ (p + 1) ^ 8 := by have := buSZ_add8_le p hp; omega
  have hisz_s : isz ((s : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hsp
  have hvsz0 : vsz (Val.int 0) = 2 := by rw [buVsz_int]; simp [isz]
  have h0 : isz (0 : ℤ) = 2 := by simp [isz]
  have hsize_s : s.size ≤ p := Nat.size_le.mpr hsp
  -- the element word of the `mapList` combinator
  have helem : ∀ x ∈ (List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int 0)),
      Pipe main (Cmd.seq ucProg (Cmd.seq swapProg dropProg)) [x] [buIdxOf x]
        (Kuc + (Ksw * (buSZ p + 3) + Kdr * 3)) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < s := List.mem_range.mp hi
    have hisz_i : isz ((i : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt (by omega)
    have h1 : Pipe main ucProg [Val.cons (Val.int (i : ℤ)) (Val.int 0)]
        [Val.int (i : ℤ), Val.int 0] Kuc :=
      Pipe.unconsVOne main huc (Val.int (i : ℤ)) (Val.int 0)
    have h2 : Pipe main swapProg [Val.int (i : ℤ), Val.int 0]
        [Val.int 0, Val.int (i : ℤ)]
        (Ksw * (vsz (Val.int (i : ℤ)) + vsz (Val.int 0) + 1)) :=
      Pipe.swap main hswap (Val.int (i : ℤ)) (Val.int 0)
    have h3 : Pipe main dropProg [Val.int 0, Val.int (i : ℤ)] [Val.int (i : ℤ)]
        (Kdr * (vsz (Val.int 0) + 1)) :=
      Pipe.appendTail [Val.int (i : ℤ)] (Pipe.drop main hdrop (Val.int 0))
    have hAll := Pipe.comp h1 (Pipe.comp h2 h3)
    have key : Kuc + (Ksw * (vsz (Val.int (i : ℤ)) + vsz (Val.int 0) + 1)
        + Kdr * (vsz (Val.int 0) + 1)) ≤ Kuc + (Ksw * (buSZ p + 3) + Kdr * 3) := by
      have e1 : vsz (Val.int (i : ℤ)) = isz ((i : ℤ)) := buVsz_int _
      rw [e1, hvsz0]
      have hA : isz ((i : ℤ)) + 2 + 1 ≤ buSZ p + 3 := by omega
      have hB : Kdr * (2 + 1) ≤ Kdr * 3 := le_of_eq rfl
      exact Nat.add_le_add_left (Nat.add_le_add (Nat.mul_le_mul_left _ hA) hB) _
    refine Pipe.le (Pipe.rw hAll ?_) key
    rw [buIdxOf_cons]
  have hxsz : ∀ x ∈ (List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int 0)),
      vsz x ≤ buSZ p + 3 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < s := List.mem_range.mp hi
    have hisz_i : isz ((i : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt (by omega)
    have hvs : vsz (Val.cons (Val.int (i : ℤ)) (Val.int 0))
        = 1 + isz ((i : ℤ)) + isz (0 : ℤ) := by
      simp only [buVsz_cons, buVsz_int]
    rw [hvs, h0]
    omega
  have hysz : ∀ x ∈ (List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int 0)),
      vsz (buIdxOf x) ≤ buSZ p + 3 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < s := List.mem_range.mp hi
    have hisz_i : isz ((i : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt (by omega)
    have hvs : vsz (buIdxOf (Val.cons (Val.int (i : ℤ)) (Val.int 0))) = isz ((i : ℤ)) := by
      simp only [buIdxOf_cons, buVsz_int]
    rw [hvs]
    omega
  -- the five phases
  have P1 : Pipe main (pushProg (Val.int 0)) [Val.int (s : ℤ)] [Val.int 0, Val.int (s : ℤ)]
      (Kpu * (vsz (Val.int 0) + 1)) :=
    Pipe.appendTail [Val.int (s : ℤ)] (Pipe.pushVal hpush (Val.int 0))
  have P2 : Pipe main swapProg [Val.int 0, Val.int (s : ℤ)] [Val.int (s : ℤ), Val.int 0]
      (Ksw * (vsz (Val.int 0) + vsz (Val.int (s : ℤ)) + 1)) :=
    Pipe.swap main hswap (Val.int 0) (Val.int (s : ℤ))
  have P3 : Pipe main replProg [Val.int (s : ℤ), Val.int 0]
      [ofList (List.replicate s (Val.int 0))]
      (Krepl * ((s + 1) * (vsz (Val.int 0) + 1) + isz ((s : ℤ)) + 1)) :=
    Pipe.replicate main hrepl
  have P4 : Pipe main enumProg [ofList (List.replicate s (Val.int 0))]
      [ofList ((List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int 0)))]
      (Kenum * (vsz (ofList (List.replicate s (Val.int 0))) + s * (s.size + 1) + 1)) := by
    refine Pipe.rw (Pipe.le (Pipe.enumerate (main := main) (prog := enumProg) (K := Kenum) henum
      (xs := List.replicate s (Val.int 0))) ?_) ?_
    · rw [List.length_replicate]
    · exact congrArg (fun l : List Val => [ofList l])
        (enumerate_replicate s (Val.int 0))
  have P5 := Pipe.mapListFun (comb := comb) (Kml := Kml) hML
    (main := main) (q := Cmd.seq ucProg (Cmd.seq swapProg dropProg))
    (rest := ([] : List Val))
    (xs := (List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int 0)))
    (F := buIdxOf)
    (c := Kuc + (Ksw * (buSZ p + 3) + Kdr * 3)) (L := buSZ p + 3) helem hxsz hysz
  have hmap : List.map buIdxOf
        (List.map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int 0)) (List.range s))
      = List.map (fun i : ℕ => Val.int (i : ℤ)) (List.range s) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact buIdxOf_cons (i : ℤ) (Val.int 0)
  have h45 := Pipe.comp P4 P5
  have h45' := Pipe.rw h45 (congrArg (fun l : List Val => [ofList l]) hmap)
  have hall := Pipe.comp P1 (Pipe.comp P2 (Pipe.comp P3 h45'))
  refine Pipe.le hall ?_
  -- cost bookkeeping
  have h3p : (3 : ℕ) ≤ (p + 1) ^ 2 := by nlinarith [hp]
  have h3p8 : (3 : ℕ) ≤ (p + 1) ^ 8 := le_trans h3p (Nat.pow_le_pow_right (by omega) (by omega))
  have h3p10 : (3 : ℕ) ≤ (p + 1) ^ 10 := le_trans h3p (Nat.pow_le_pow_right (by omega) (by omega))
  have h8 : (p + 1) ^ 8 ≤ (p + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h210 : (p + 1) ^ 2 + (p + 1) ^ 8 ≤ (p + 1) ^ 10 :=
    buPow_add_pow_le (by omega) (by omega) (by omega)
  have hA1 : vsz (Val.int 0) + 1 ≤ (s + 1) * (p + 1) ^ 10 := by
    rw [hvsz0]
    calc 2 + 1 = 3 := rfl
      _ ≤ (p + 1) ^ 10 := h3p10
      _ = 1 * (p + 1) ^ 10 := (one_mul _).symm
      _ ≤ (s + 1) * (p + 1) ^ 10 := Nat.mul_le_mul_right _ (by omega)
  have hA2 : vsz (Val.int 0) + vsz (Val.int (s : ℤ)) + 1 ≤ (s + 1) * (p + 1) ^ 10 := by
    have hvs : vsz (Val.int (s : ℤ)) = isz ((s : ℤ)) := buVsz_int _
    rw [hvsz0, hvs]
    calc 2 + isz ((s : ℤ)) + 1 ≤ buSZ p + 3 := by omega
      _ ≤ (p + 1) ^ 8 := hS3
      _ ≤ (p + 1) ^ 10 := h8
      _ = 1 * (p + 1) ^ 10 := (one_mul _).symm
      _ ≤ (s + 1) * (p + 1) ^ 10 := Nat.mul_le_mul_right _ (by omega)
  have hA3 : (s + 1) * (vsz (Val.int 0) + 1) + isz ((s : ℤ)) + 1
      ≤ (s + 1) * (p + 1) ^ 10 := by
    rw [hvsz0]
    have h3' : (s + 1) * (2 + 1) = (s + 1) * 3 := by ring
    rw [h3']
    have h1 : (s + 1) * 3 ≤ (s + 1) * (p + 1) ^ 2 := Nat.mul_le_mul_left _ h3p
    have h2 : isz ((s : ℤ)) + 1 ≤ (s + 1) * (p + 1) ^ 8 := by
      calc isz ((s : ℤ)) + 1 ≤ (p + 1) ^ 8 := by omega
        _ = 1 * (p + 1) ^ 8 := (one_mul _).symm
        _ ≤ (s + 1) * (p + 1) ^ 8 := Nat.mul_le_mul_right _ (by omega)
    have hsum : (s + 1) * 3 + (isz ((s : ℤ)) + 1)
        ≤ (s + 1) * (p + 1) ^ 2 + (s + 1) * (p + 1) ^ 8 := Nat.add_le_add h1 h2
    have hcomb : (s + 1) * (p + 1) ^ 2 + (s + 1) * (p + 1) ^ 8 ≤ (s + 1) * (p + 1) ^ 10 := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ h210
    have hg : (s + 1) * 3 + isz ((s : ℤ)) + 1 = (s + 1) * 3 + (isz ((s : ℤ)) + 1) := by ring
    rw [hg]
    exact le_trans hsum hcomb
  have hA4 : vsz (ofList (List.replicate s (Val.int 0))) + s * (s.size + 1) + 1
      ≤ (s + 1) * (p + 1) ^ 10 := by
    rw [buVsz_ofList_replicate_zero]
    have h1 : 3 * s + 1 ≤ (s + 1) * (p + 1) ^ 2 := by
      have h4 : (3 * s + 1) ≤ (s + 1) * 4 := by nlinarith [hs]
      have h5 : (s + 1) * 4 ≤ (s + 1) * (p + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith [hp])
      linarith
    have h2 : s * (s.size + 1) ≤ (s + 1) * (p + 1) ^ 2 := by
      have h5 : s * (s.size + 1) ≤ s * (p + 1) := Nat.mul_le_mul_left _ (by omega)
      have h6 : s * (p + 1) ≤ (s + 1) * (p + 1) := Nat.mul_le_mul_right _ (by omega)
      have h7 : (s + 1) * (p + 1) ≤ (s + 1) * (p + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith [hp])
      linarith
    have h3 : 1 ≤ (s + 1) * (p + 1) ^ 2 := by
      have h8 : 1 ≤ (s + 1) := by omega
      have h9 : (1 : ℕ) ≤ (p + 1) ^ 2 := by nlinarith [hp]
      calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
        _ ≤ (s + 1) * (p + 1) ^ 2 := Nat.mul_le_mul h8 h9
    have hsum : (3 * s + 1) + (s * (s.size + 1) + 1) ≤ 3 * ((s + 1) * (p + 1) ^ 2) := by
      have h10 : 3 * ((s + 1) * (p + 1) ^ 2)
          = (s + 1) * (p + 1) ^ 2 + ((s + 1) * (p + 1) ^ 2 + (s + 1) * (p + 1) ^ 2) := by ring
      rw [h10]
      exact Nat.add_le_add h1 (Nat.add_le_add h2 h3)
    have hfin : 3 * ((s + 1) * (p + 1) ^ 2) ≤ (s + 1) * (p + 1) ^ 10 := by
      calc 3 * ((s + 1) * (p + 1) ^ 2) = (s + 1) * (3 * (p + 1) ^ 2) := by ring
        _ ≤ (s + 1) * ((p + 1) ^ 8 * (p + 1) ^ 2) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3p8)
        _ = (s + 1) * (p + 1) ^ 10 := by rw [← pow_add]
    have hg : 3 * s + 1 + s * (s.size + 1) + 1 = (3 * s + 1) + (s * (s.size + 1) + 1) := by ring
    rw [hg]
    exact le_trans hsum hfin
  -- the `mapList` phase
  have hcin : Kuc + (Ksw * (buSZ p + 3) + Kdr * 3) ≤ (p + 1) ^ Nc := by
    have h1 : Kuc ≤ (p + 1) ^ (Nc - 2) :=
      le_trans (buPow_le_self p Kuc hp1) (Nat.pow_le_pow_right (by omega) (by rw [hNc]; omega))
    have h2 : Ksw * (buSZ p + 3) ≤ (p + 1) ^ (Nc - 2) := by
      calc Ksw * (buSZ p + 3) ≤ (p + 1) ^ Ksw * (buSZ p + 3) :=
            Nat.mul_le_mul_right _ (buPow_le_self p Ksw hp1)
        _ ≤ (p + 1) ^ Ksw * (p + 1) ^ 8 := Nat.mul_le_mul_left _ hS3
        _ = (p + 1) ^ (Ksw + 8) := by rw [← pow_add]
        _ ≤ (p + 1) ^ (Nc - 2) := Nat.pow_le_pow_right (by omega) (by rw [hNc]; omega)
    have h3 : Kdr * 3 ≤ (p + 1) ^ (Nc - 2) := by
      calc Kdr * 3 ≤ (p + 1) ^ Kdr * 3 := Nat.mul_le_mul_right _ (buPow_le_self p Kdr hp1)
        _ ≤ (p + 1) ^ Kdr * (p + 1) ^ 2 := Nat.mul_le_mul_left _ h3p
        _ = (p + 1) ^ (Kdr + 2) := by rw [← pow_add]
        _ ≤ (p + 1) ^ (Nc - 2) := Nat.pow_le_pow_right (by omega) (by rw [hNc]; omega)
    have h := buAdd3_le (p := p) (m := Nc - 2) hbase h1 h2 h3
    refine le_trans h ?_
    rw [Nat.sub_add_cancel (by rw [hNc]; omega)]
  have hLcin : Kml * ((buSZ p + 3) + 1) ≤ (p + 1) ^ Nc := by
    calc Kml * ((buSZ p + 3) + 1) ≤ (p + 1) ^ Kml * ((buSZ p + 3) + 1) :=
          Nat.mul_le_mul_right _ (buPow_le_self p Kml hp1)
      _ ≤ (p + 1) ^ Kml * (p + 1) ^ 8 := Nat.mul_le_mul_left _ hS4
      _ = (p + 1) ^ (Kml + 8) := by rw [← pow_add]
      _ ≤ (p + 1) ^ Nc := Nat.pow_le_pow_right (by omega) (by rw [hNc]; omega)
  have hKcin : Kml ≤ Nc := by rw [hNc]; omega
  have hc1 : Kpu * (vsz (Val.int 0) + 1) ≤ (s + 1) * (p + 1) ^ M :=
    buPhase_le (s := s) (p := p) (K := Kpu) (M := M) (A := vsz (Val.int 0) + 1) hp1 hA1
      (by rw [hM, hNc]; omega)
  have hc2 : Ksw * (vsz (Val.int 0) + vsz (Val.int (s : ℤ)) + 1) ≤ (s + 1) * (p + 1) ^ M :=
    buPhase_le (s := s) (p := p) (K := Ksw) (M := M)
      (A := vsz (Val.int 0) + vsz (Val.int (s : ℤ)) + 1) hp1 hA2 (by rw [hM, hNc]; omega)
  have hc3 : Krepl * ((s + 1) * (vsz (Val.int 0) + 1) + isz ((s : ℤ)) + 1)
      ≤ (s + 1) * (p + 1) ^ M :=
    buPhase_le (s := s) (p := p) (K := Krepl) (M := M)
      (A := (s + 1) * (vsz (Val.int 0) + 1) + isz ((s : ℤ)) + 1) hp1 hA3
      (by rw [hM, hNc]; omega)
  have hc4 : Kenum * (vsz (ofList (List.replicate s (Val.int 0))) + s * (s.size + 1) + 1)
      ≤ (s + 1) * (p + 1) ^ M :=
    buPhase_le (s := s) (p := p) (K := Kenum) (M := M)
      (A := vsz (ofList (List.replicate s (Val.int 0))) + s * (s.size + 1) + 1) hp1 hA4
      (by rw [hM, hNc]; omega)
  have hc5 := buMapCost_le (s := s) (c := Kuc + (Ksw * (buSZ p + 3) + Kdr * 3))
    (Kml := Kml) (L := buSZ p + 3) (p := p) (M := Nc) hbase hcin hLcin hKcin
  have hc5' : ((List.range s).map
        (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int 0))).length
        * (Kuc + (Ksw * (buSZ p + 3) + Kdr * 3) + Kml * ((buSZ p + 3) + 1)) + Kml
      ≤ (s + 1) * (p + 1) ^ M := by
    rw [List.length_map, List.length_range]
    exact le_trans hc5 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by rw [hM]; omega)))
  have hfin := buFive_le (s := s) (p := p) (M := M) hbase hc1 hc2 hc3 hc4 hc5'
  have hlast : (s + 1) * (p + 1) ^ (M + 3) ≤ (M + 3) * (s + 1) * (p + 1) ^ (M + 3) := by
    have h1 : (s + 1) * (p + 1) ^ (M + 3) = 1 * ((s + 1) * (p + 1) ^ (M + 3)) :=
      (one_mul _).symm
    rw [h1, show (M + 3) * (s + 1) * (p + 1) ^ (M + 3)
        = (M + 3) * ((s + 1) * (p + 1) ^ (M + 3)) by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  exact le_trans hfin hlast

theorem buDwWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (dwProg : HvdH.Cmd) (Kd : ℕ)
    (dwSpec : ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)),
      ∀ rest : List HvdH.Val, HvdH.WordR main dwProg
        (fun vs => vs = [HvdH.Val.int ℓ] ++ Work.Resample.buCB p α s t ++ rest)
        (fun vs out => vs = [HvdH.Val.int ℓ] ++ Work.Resample.buCB p α s t ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.buWd p α s t ℓ)] ++ Work.Resample.buCB p α s t ++ rest)
        (fun _ => Kd * (p + 1) ^ Kd)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      (∀ ℓ : ℤ, HvdH.isz (Work.Resample.buWd p α s t ℓ) ≤ Work.Resample.buSZ p) →
      Work.Resample.Pipe main prog (Work.Resample.buCB p α s t)
        (Work.Resample.buL9 p α s t :: Work.Resample.buCB p α s t)
        (K * (s + 1) * (p + 1) ^ K) := by
  obtain ⟨comb, Kml, hML⟩ := MapListField.of_kernel KL
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  obtain ⟨rangeProg, Kr, hRange⟩ := buRangeWord_self KL LL
  set N : ℕ := 3 * Kpk + 2 * Kr + 2 * Kd + Kml + 33 with hN
  refine ⟨Cmd.seq (pickProg 2) (Cmd.seq rangeProg (comb dwProg)), N + 4, ?_⟩
  intro main p α s t hs hst hα hp htp hαp hsz
  have hsp : s < 2 ^ p := by omega
  have hbase : 2 ≤ p + 1 := by omega
  have hp1 : 1 ≤ p := by omega
  have hs1 : 1 ≤ s := by omega
  -- size bounds for the entries of the canonical block
  have hpt : isz ((p : ℤ)) ≤ buSZ p := isz_p_le_buSZ p
  have hαlt : α < 2 ^ p := by
    have h1 : α ≤ α ^ 2 := by
      calc α = α * 1 := (Nat.mul_one α).symm
        _ ≤ α * α := Nat.mul_le_mul_left α (by omega)
        _ = α ^ 2 := by ring
    have h2 : p < 2 ^ p := Nat.lt_two_pow_self (n := p)
    omega
  have ha : isz ((α : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hαlt
  have hss : isz ((s : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hsp
  have htake3 : (buCB p α s t).take 3 = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ)] := rfl
  have htake : Work.Fx.szl ((buCB p α s t).take 3) + 1 ≤ 3 * buSZ p + 1 := by
    rw [htake3]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, buVsz_int]
    omega
  -- phase 1: copy the `s` entry of the block to the top of the stack
  have P1 : Pipe main (pickProg 2) (buCB p α s t) ([Val.int (s : ℤ)] ++ buCB p α s t)
      (Kpk * 3 * (Work.Fx.szl ((buCB p α s t).take 3) + 1)) :=
    Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick (A := buCB p α s t) (k := 2)
      (v := Val.int (s : ℤ)) (by simp [buCB]) (by simp [buCB])
  -- phase 2: the list of indices `0, …, s-1`
  have P2 : Pipe main rangeProg ([Val.int (s : ℤ)] ++ buCB p α s t)
      ([ofList (buIdxList s)] ++ buCB p α s t)
      (Kr * (s + 1) * (p + 1) ^ Kr) :=
    Pipe.appendTail (buCB p α s t) (hRange main p s hs1 hsp hp)
  -- phase 3: map the given element word over the index list
  have helem : ∀ x ∈ buIdxList s,
      Pipe main dwProg (x :: buCB p α s t) (buWdOf p α s t x :: buCB p α s t)
        (Kd * (p + 1) ^ Kd) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < s := List.mem_range.mp hi
    have hℓ0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
    have hℓs : (i : ℤ) < (s : ℤ) := by exact_mod_cast hi'
    intro rest
    refine Work.Kernel.WordR_conseq
      (dwSpec main p α s t hs hst hα hp htp hαp (i : ℤ) hℓ0 hℓs rest)
      (fun vs hv => hv) ?_ (fun vs _ => le_rfl)
    intro vs out hv hout
    exact hout.2
  have hxsz : ∀ x ∈ buIdxList s, vsz x ≤ 1 + 2 * buSZ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < s := List.mem_range.mp hi
    rw [buVsz_int]
    have h : isz ((i : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt (by omega)
    omega
  have hysz : ∀ x ∈ buIdxList s, vsz (buWdOf p α s t x) ≤ 1 + 2 * buSZ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [buWdOf_int, buVsz_int]
    have h : isz (buWd p α s t (i : ℤ)) ≤ buSZ p := hsz (i : ℤ)
    omega
  have P3 := auMapListTail (comb := comb) (Kml := Kml) hML (main := main) (q := dwProg)
    (T := buCB p α s t) (xs := buIdxList s) (F := buWdOf p α s t)
    (c := Kd * (p + 1) ^ Kd) (L := 1 + 2 * buSZ p) helem hxsz hysz
  have P3' : Pipe main (comb dwProg) ([ofList (buIdxList s)] ++ buCB p α s t)
      ([buL9 p α s t] ++ buCB p α s t)
      ((buIdxList s).length * (Kd * (p + 1) ^ Kd + Kml * ((1 + 2 * buSZ p) + 1)) + Kml) := by
    have hB : ofList ((buIdxList s).map (buWdOf p α s t)) :: buCB p α s t
        = [buL9 p α s t] ++ buCB p α s t := by
      have h1 : ofList ((buIdxList s).map (buWdOf p α s t)) = buL9 p α s t :=
        (congrArg ofList (buIdxList_map p α s t)).trans (buL9_eq_ofList p α s t).symm
      have h2 : buL9 p α s t :: buCB p α s t = [buL9 p α s t] ++ buCB p α s t := rfl
      exact (congrArg (fun l : Val => l :: buCB p α s t) h1).trans h2
    exact Pipe.rw P3 hB
  have hall : Pipe main (Cmd.seq (pickProg 2) (Cmd.seq rangeProg (comb dwProg)))
      (buCB p α s t) ([buL9 p α s t] ++ buCB p α s t)
      (Kpk * 3 * (Work.Fx.szl ((buCB p α s t).take 3) + 1)
        + (Kr * (s + 1) * (p + 1) ^ Kr
          + ((buIdxList s).length * (Kd * (p + 1) ^ Kd
              + Kml * ((1 + 2 * buSZ p) + 1)) + Kml))) :=
    Pipe.comp P1 (Pipe.comp P2 P3')
  rw [buIdxList_length] at hall
  refine Pipe.le hall ?_
  -- cost bookkeeping
  have hN1 : 3 * Kpk + 16 ≤ N := by rw [hN]; omega
  have hN2 : Kr + Kr ≤ N := by rw [hN]; omega
  have hN3 : 2 * Kd + Kml + 17 ≤ N := by rw [hN]; omega
  have hN4 : Kml ≤ N := by rw [hN]; omega
  have h16 : 3 * buSZ p + 1 ≤ (p + 1) ^ 16 := by
    have h1 : 3 * buSZ p + 1 ≤ (buSZ p + 8) ^ 2 := by nlinarith [Nat.zero_le (buSZ p)]
    calc 3 * buSZ p + 1 ≤ (buSZ p + 8) ^ 2 := h1
      _ ≤ ((p + 1) ^ 8) ^ 2 := Nat.pow_le_pow_left (buSZ_add8_le p hp) 2
      _ = (p + 1) ^ 16 := by rw [← pow_mul]
  have hb1 : Kpk * 3 * (Work.Fx.szl ((buCB p α s t).take 3) + 1) ≤ (s + 1) * (p + 1) ^ N := by
    calc Kpk * 3 * (Work.Fx.szl ((buCB p α s t).take 3) + 1)
        ≤ Kpk * 3 * (3 * buSZ p + 1) := Nat.mul_le_mul_left _ htake
      _ = 3 * Kpk * (3 * buSZ p + 1) := by ring
      _ ≤ (p + 1) ^ (3 * Kpk) * (p + 1) ^ 16 :=
            Nat.mul_le_mul (by simpa using buCoeff_pow_le p (3 * Kpk) 0 hp1) h16
      _ = (p + 1) ^ (3 * Kpk + 16) := by rw [← pow_add]
      _ ≤ (p + 1) ^ N := Nat.pow_le_pow_right (by omega) hN1
      _ = 1 * (p + 1) ^ N := (one_mul _).symm
      _ ≤ (s + 1) * (p + 1) ^ N := Nat.mul_le_mul_right _ (by omega)
  have hb2 : Kr * (s + 1) * (p + 1) ^ Kr ≤ (s + 1) * (p + 1) ^ N := by
    calc Kr * (s + 1) * (p + 1) ^ Kr ≤ (p + 1) ^ Kr * (s + 1) * (p + 1) ^ Kr :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (s + 1) (buPow_le_self p Kr hp1))
      _ = (s + 1) * ((p + 1) ^ Kr * (p + 1) ^ Kr) := by ring
      _ = (s + 1) * (p + 1) ^ (Kr + Kr) := by rw [← pow_add]
      _ ≤ (s + 1) * (p + 1) ^ N := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hN2)
  have hKd : Kd * (p + 1) ^ Kd ≤ (p + 1) ^ (Kd + Kd) := by
    calc Kd * (p + 1) ^ Kd ≤ (p + 1) ^ Kd * (p + 1) ^ Kd :=
          Nat.mul_le_mul_right _ (buPow_le_self p Kd hp1)
      _ = (p + 1) ^ (Kd + Kd) := by rw [← pow_add]
  have hL16 : (1 + 2 * buSZ p) + 1 ≤ (p + 1) ^ 16 := by
    have h1 : (1 + 2 * buSZ p) + 1 ≤ (buSZ p + 8) ^ 2 := by nlinarith [Nat.zero_le (buSZ p)]
    calc (1 + 2 * buSZ p) + 1 ≤ (buSZ p + 8) ^ 2 := h1
      _ ≤ ((p + 1) ^ 8) ^ 2 := Nat.pow_le_pow_left (buSZ_add8_le p hp) 2
      _ = (p + 1) ^ 16 := by rw [← pow_mul]
  have hKmlL : Kml * ((1 + 2 * buSZ p) + 1) ≤ (p + 1) ^ (Kml + 16) := by
    calc Kml * ((1 + 2 * buSZ p) + 1) ≤ Kml * (p + 1) ^ 16 := Nat.mul_le_mul_left _ hL16
      _ ≤ (p + 1) ^ Kml * (p + 1) ^ 16 := Nat.mul_le_mul_right _ (buPow_le_self p Kml hp1)
      _ = (p + 1) ^ (Kml + 16) := by rw [← pow_add]
  have hb3 : s * (Kd * (p + 1) ^ Kd + Kml * ((1 + 2 * buSZ p) + 1)) ≤ (s + 1) * (p + 1) ^ N := by
    have hc : Kd * (p + 1) ^ Kd ≤ (p + 1) ^ (2 * Kd + Kml + 16) :=
      le_trans hKd (Nat.pow_le_pow_right (by omega) (by omega))
    have hL : Kml * ((1 + 2 * buSZ p) + 1) ≤ (p + 1) ^ (2 * Kd + Kml + 16) :=
      le_trans hKmlL (Nat.pow_le_pow_right (by omega) (by omega))
    have hK : Kml ≤ 2 * Kd + Kml + 16 := by omega
    have h := buMapCost_le (s := s) (c := Kd * (p + 1) ^ Kd) (Kml := Kml)
      (L := 1 + 2 * buSZ p) (p := p) (M := 2 * Kd + Kml + 16) hbase hc hL hK
    refine le_trans (Nat.le_add_right _ _) (le_trans h ?_)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hb4 : Kml ≤ (s + 1) * (p + 1) ^ N := by
    refine le_trans hN4 ?_
    calc N ≤ (p + 1) ^ N := buPow_le_self p N hp1
      _ = 1 * (p + 1) ^ N := (one_mul _).symm
      _ ≤ (s + 1) * (p + 1) ^ N := Nat.mul_le_mul_right _ (by omega)
  have hfin := buFour_le (s := s) (p := p) (M := N) hbase hb1 hb2 hb3 hb4
  calc Kpk * 3 * (Work.Fx.szl ((buCB p α s t).take 3) + 1)
        + (Kr * (s + 1) * (p + 1) ^ Kr
          + (s * (Kd * (p + 1) ^ Kd + Kml * ((1 + 2 * buSZ p) + 1)) + Kml))
      ≤ (s + 1) * (p + 1) ^ (N + 2) := hfin
    _ ≤ (s + 1) * (p + 1) ^ (N + 4) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ = 1 * ((s + 1) * (p + 1) ^ (N + 4)) := (one_mul _).symm
    _ ≤ (N + 4) * ((s + 1) * (p + 1) ^ (N + 4)) := Nat.mul_le_mul_right _ (by omega)
    _ = (N + 4) * (s + 1) * (p + 1) ^ (N + 4) := by ring

end Work.Resample
