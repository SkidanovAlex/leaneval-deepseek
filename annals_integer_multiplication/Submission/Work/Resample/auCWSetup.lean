import Mathlib
import Submission.Work.Resample.auCWDefs
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auOffCop
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auInnerElem
import Submission.Work.ConvR.basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.auCWSetup`: the setup word of the chunk word `q` (paper Lemma 4.9)

Given one chunk `cons (ofList WTS) (ofList WIN)` on top of the parameter block
`auPvals p α s t = [off, cop, p, table]`, this word

1. splits the chunk into its two lists (`KernelLib.unconsV`),
2. zips them pointwise into the list of pairs `AwPair (W i) (z i).1 (z i).2`
   (`KernelLib.zipWith` with the one-element body `KernelLib.consV`),
3. pushes the three accumulator values `int 0`, `int 0`, `nil` under the list,
   copies the precision `int p` out of the parameter block (`KernelLib.pick 6`) and
   moves the list back on top (`KernelLib.roll 4`).

The cost is `K*(L+1)*(p+1)`, i.e. linear in the chunk length `L` and in `p`; the uniform
bounds on the sizes of the parameter values (`auOff`, `auCop`, `p`) and of the chunk entries
are what makes the `pick`/`roll` costs fit.
-/

/-! ## Elementary helpers -/

/-- `a ≤ a * b` for `1 ≤ b`. -/
private theorem cw_le_mul {a b : ℕ} (hb : 1 ≤ b) : a ≤ a * b := by
  calc a = a * 1 := by ring
    _ ≤ a * b := Nat.mul_le_mul_left a hb

/-- Sum of the sizes of a list of values, bounded by the length times a uniform bound. -/
private theorem cw_list_sum_le {zs : List Val} {Lz : ℕ} (h : ∀ z ∈ zs, vsz z ≤ Lz) :
    (zs.map vsz).sum ≤ zs.length * Lz := by
  induction zs with
  | nil => simp
  | cons a t ih =>
    have ha : vsz a ≤ Lz := h a (by simp)
    have ht : ∀ z ∈ t, vsz z ≤ Lz := fun z hz => h z (by simp [hz])
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have := ih ht
    nlinarith [Nat.zero_le (vsz a), Nat.zero_le ((t.map vsz).sum)]

/-- The encoding size of a `cons`-chain of length `L` whose entries are all bounded by `Lz`. -/
private theorem cw_vsz_ofList {zs : List Val} {L Lz : ℕ} (hlen : zs.length = L)
    (h : ∀ i < L, vsz (zs.getD i .nil) ≤ Lz) : vsz (ofList zs) ≤ L * (Lz + 1) + 1 := by
  have hmem : ∀ z ∈ zs, vsz z ≤ Lz := by
    intro z hz
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hz
    have hiL : i < L := by rw [← hlen]; exact hi
    rw [← hix, ← List.getD_eq_getElem zs .nil hi]
    exact h i hiL
  have hsum : (zs.map vsz).sum ≤ zs.length * Lz := cw_list_sum_le hmem
  rw [hlen] at hsum
  rw [Work.ConvR.vsz_ofList, hlen, Nat.mul_succ]
  omega

/-- A list of length `n` is determined by its `getD` values. -/
private theorem cw_eq_range_map_getD {α : Type*} (l : List α) (d : α) (f : ℕ → α) {n : ℕ}
    (hlen : l.length = n) (h : ∀ i < n, l.getD i d = f i) : l = (List.range n).map f := by
  induction l generalizing n f with
  | nil =>
    have hn : n = 0 := by simpa using hlen.symm
    subst hn
    simp
  | cons a t ih =>
    cases n with
    | zero => simp at hlen
    | succ m =>
      have hlen' : t.length = m := by simpa using hlen
      have ha : a = f 0 := by have := h 0 (by simp); simpa using this
      have ht : t = (List.range m).map (fun i => f (i + 1)) := by
        refine ih (n := m) (f := fun i => f (i + 1)) hlen' ?_
        intro i hi
        have := h (i + 1) (by simp; omega)
        simpa using this
      rw [ha, ht, List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl

/-- Sizes of the parameter values of `auPvals p α s t`. -/
private theorem cw_param_sz (p α s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) (hαp : α ^ 2 < p) :
    isz ((auOff p α s : ℕ) : ℤ) ≤ p + 2 ∧
    isz ((auCop p α s : ℕ) : ℤ) ≤ 4 * p + 5 ∧
    isz ((p : ℤ)) ≤ p + 2 := by
  have hOfflt : auOff p α s < 2 ^ p := by
    have := auOffCop_aux_off_le p α s
    omega
  have hM : auM p α ≤ 2 * p := auOffCop_aux_auM_le p α hαp
  have hCople : auCop p α s ≤ 4 * p + 3 := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; simp [auCop]
    · rw [auCop]
      apply Nat.div_le_of_le_mul
      have h1 : auOff p α s + 2 * s + 2 * auM p α ≤ 3 * s + 4 * p := by
        have := auOffCop_aux_off_le p α s; omega
      have h2 : 3 * s + 4 * p ≤ s * (4 * p + 3) := by
        have h3 : 4 * p ≤ 4 * p * s := cw_le_mul (by omega)
        nlinarith [h3]
      omega
  have hone : ∀ n : ℕ, n.size ≤ n := fun n => Nat.size_le.mpr Nat.lt_two_pow_self
  refine ⟨?_, ?_, ?_⟩
  · rw [isz_natCast]
    have := Nat.size_le.mpr hOfflt
    omega
  · rw [isz_natCast]; have := hone (auCop p α s); omega
  · rw [isz_natCast]; have := hone p; omega

/-- The cost arithmetic of the setup word. -/
private theorem cw_cost_le (L p Kp Ku Kv Kz Kr Kc : ℕ) :
    Ku + (L * (Kc + Kz * (3 * p + 12)) + Kz) + (Kv * 2 + Kv * 3 + Kv * 3)
      + Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1)
      + Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1)
    ≤ 10000 * (Kp + Ku + Kv + Kz + Kr + Kc + 1) * ((L + 1) * (p + 1)) := by
  set A : ℕ := (L + 1) * (p + 1) with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [Nat.zero_le L, Nat.zero_le p]
  have hAp : p + 1 ≤ A := by rw [hA]; nlinarith [Nat.zero_le L, Nat.zero_le p]
  have hApos : 0 < A := by omega
  have hBs : (L + 1) * (3 * p + 12) ≤ 15 * A := by
    calc (L + 1) * (3 * p + 12) ≤ (L + 1) * (15 * (p + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 15 * A := by rw [hA]; ring
  have hp45 : 4 * p + 5 ≤ 5 * A := by
    have h1 : 5 * (p + 1) ≤ 5 * A := Nat.mul_le_mul_left 5 hAp
    omega
  have e1 : L * (Kc + Kz * (3 * p + 12)) ≤ (Kc + 15 * Kz) * A := by
    have hf : Kc + Kz * (3 * p + 12) ≤ (Kc + 15 * Kz) * (p + 1) := by
      have h1 : Kc ≤ Kc * (p + 1) := cw_le_mul (by omega)
      have h2 : Kz * (3 * p + 12) ≤ Kz * (15 * (p + 1)) :=
        Nat.mul_le_mul_left Kz (by omega)
      nlinarith [h1, h2]
    calc L * (Kc + Kz * (3 * p + 12)) ≤ L * ((Kc + 15 * Kz) * (p + 1)) :=
          Nat.mul_le_mul_left L hf
      _ = (Kc + 15 * Kz) * (L * (p + 1)) := by ring
      _ ≤ (Kc + 15 * Kz) * A :=
          Nat.mul_le_mul_left _ (by rw [hA]; exact Nat.mul_le_mul_right (p + 1) (by omega))
  have e2 : Kz ≤ Kz * A := cw_le_mul hA1
  have e3 : Kv * 2 + Kv * 3 + Kv * 3 ≤ 8 * Kv * A := by
    have h1 : Kv * 2 + Kv * 3 + Kv * 3 = 8 * Kv := by ring
    rw [h1]; exact cw_le_mul hA1
  have e4 : Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1) ≤ 987 * Kp * A := by
    have hb : 7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1 ≤ 141 * A := by omega
    calc Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1) ≤ Kp * 7 * (141 * A) :=
          Nat.mul_le_mul_left _ hb
      _ = 987 * Kp * A := by ring
  have e5 : Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1) ≤ 380 * Kr * A := by
    have hb : 5 * ((L + 1) * (3 * p + 12)) + 1 ≤ 76 * A := by omega
    calc Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1) ≤ Kr * 5 * (76 * A) :=
          Nat.mul_le_mul_left _ hb
      _ = 380 * Kr * A := by ring
  have e6 : Ku ≤ Ku * A := cw_le_mul hA1
  have hcx : (Kc + 15 * Kz + Kz + 8 * Kv + 987 * Kp + 380 * Kr + Ku) * A
      = (Kc + 15 * Kz) * A + Kz * A + 8 * Kv * A + 987 * Kp * A + 380 * Kr * A
        + Ku * A := by ring
  have h1 : Ku + (L * (Kc + Kz * (3 * p + 12)) + Kz) + (Kv * 2 + Kv * 3 + Kv * 3)
      + Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1)
      + Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1)
      ≤ (Kc + 15 * Kz + Kz + 8 * Kv + 987 * Kp + 380 * Kr + Ku) * A := by
    rw [hcx]
    nlinarith [e1, e2, e3, e4, e5, e6]
  have h2 : Kc + 15 * Kz + Kz + 8 * Kv + 987 * Kp + 380 * Kr + Ku
      ≤ 10000 * (Kp + Ku + Kv + Kz + Kr + Kc + 1) := by omega
  exact le_trans h1 (Nat.mul_le_mul_right A h2)

/-! ## The pointwise predicates of the zip -/

/-- Element precondition of the zip body: an integer weight and a fixed-point pair. -/
private def CwP (p : ℕ) (x y : Val) : Prop :=
  ∃ W a b : ℤ, x = Val.int W ∧ y = Val.cons (Val.int a) (Val.int b) ∧
    W.natAbs ≤ 2 ^ p ∧ a ^ 2 + b ^ 2 ≤ 4 ^ p

/-- Element postcondition of the zip body. -/
private def CwQ (x y zz : Val) : Prop :=
  ∃ W a b : ℤ, x = Val.int W ∧ y = Val.cons (Val.int a) (Val.int b) ∧ zz = AwPair W a b

private theorem cwQ_int {W a b : ℤ} {zz : Val}
    (h : CwQ (Val.int W) (Val.cons (Val.int a) (Val.int b)) zz) : zz = AwPair W a b := by
  obtain ⟨W', a', b', hx, hy, hz⟩ := h
  have h1 : W' = W := (Val.int.inj hx).symm
  have h2 : a' = a := (Val.int.inj (Val.cons.inj hy).1).symm
  have h3 : b' = b := (Val.int.inj (Val.cons.inj hy).2).symm
  rw [hz, h1, h2, h3]

/-- The facts about the value produced by the body of the zip. -/
private theorem cwQ_facts {W a b : ℤ} {zz : Val}
    (h : CwQ (Val.int W) (Val.cons (Val.int a) (Val.int b)) zz) :
    zz = AwPair W a b ∧ vsz zz = isz W + isz a + isz b + 2 := by
  refine ⟨cwQ_int h, ?_⟩
  rw [cwQ_int h]
  change vsz (Val.cons (Val.int W) (Val.cons (Val.int a) (Val.int b)))
    = isz W + isz a + isz b + 2
  rw [Work.ConvR.vsz_cons, Work.ConvR.vsz_cons, Work.ConvR.vsz_int,
    Work.ConvR.vsz_int, Work.ConvR.vsz_int]
  ring

/-- `KernelLib.consV` as a `Pipe` on a two-value window. -/
private theorem cwPipe_consV {consP : Cmd} {Kc : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b r, vs = a :: b :: r ∧ out = .cons a b :: r) (fun _ => Kc))
    (a b : Val) : Pipe main consP [a, b] [.cons a b] Kc := by
  intro r vs hvs s R hR
  have hv2 : vs = a :: b :: r := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have h2 := List.cons.inj h1.2
  exact ⟨out, s', n, by rw [hout, h1.1, h2.1, h2.2]; rfl, hev, hn, hstk, hoth⟩

/-- Consequence rule for `WordR`. -/
private theorem cw_conseq {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ} (h : WordR main p P Q C)
    (hP : ∀ vs, P' vs → P vs) (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out)
    (hC : ∀ vs, P' vs → C vs ≤ C' vs) : WordR main p P' Q' C' := by
  intro vs hP' s R hR
  obtain ⟨out, s', n, hQh, hev, hn, hstk, hoth⟩ := h vs (hP vs hP') s R hR
  exact ⟨out, s', n, hQ vs out hP' hQh, hev, le_trans hn (hC vs hP'), hstk, hoth⟩

theorem auCWSetup (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t L : ℕ) (W : ℕ → ℤ) (z : ℕ → ℤ × ℤ)
      (WTS WIN : List HvdH.Val) (rest : List HvdH.Val),
      1 ≤ p → s < t → t < 2 ^ p → α ^ 2 < p →
      WTS.length = L → WIN.length = L →
      (∀ i < L, WTS.getD i .nil = HvdH.Val.int (W i)) →
      (∀ i < L, WIN.getD i .nil = HvdH.cfxVal (z i)) →
      (∀ i < L, (W i).natAbs ≤ 2 ^ p) → (∀ i < L, HvdH.inDisc p (z i)) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN) :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ out => out = HvdH.ofList ((List.range L).map fun i => Work.Resample.AwPair (W i) (z i).1 (z i).2)
            :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int 0 :: HvdH.Val.int 0 :: HvdH.Val.nil
            :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ => K * (L + 1) * (p + 1)) := by
  obtain ⟨consP, Kc, hcons⟩ := hk.consV
  obtain ⟨zipP, Kz, hzip⟩ := hk.zipWith
  obtain ⟨pushP, Kv, hpush⟩ := hk.pushVal
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨unconsP, Ku, huncons⟩ := hk.unconsV
  refine ⟨Cmd.seq unconsP (Cmd.seq (zipP consP)
      (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pushP Val.nil) (pushP (Val.int 0)))
        (pushP (Val.int 0))) (pickP 6)) (rollP 4))),
    10000 * (Kp + Ku + Kv + Kz + Kr + Kc + 1), ?_⟩
  intro main p α s t L W z WTS WIN rest hp hst htp hαp hWTS hWIN hWg hZg hWb hZd
  -- size facts
  obtain ⟨hOffsz, hCopsz, hPsz⟩ := cw_param_sz p α s t hst htp hαp
  have hiz0 : isz (0 : ℤ) = 2 := by decide
  have hvnil : vsz (Val.nil) = 1 := rfl
  have hszZ0 : vsz (Val.int (0 : ℤ)) = 2 := by rw [Work.ConvR.vsz_int]; exact hiz0
  -- the per-element word of the zip
  have hbody : ∀ x y, CwP p x y → WordR main consP
      (fun vs => vs = x :: y :: (auPvals p α s t ++ rest))
      (fun _ out => ∃ zz, out = zz :: (auPvals p α s t ++ rest) ∧ CwQ x y zz ∧
        vsz zz ≤ 3 * p + 11)
      (fun _ => Kc) := by
    intro x y hxy
    obtain ⟨W', a, b, rfl, rfl, hWb', hab⟩ := hxy
    refine cw_conseq (cwPipe_consV main hcons (Val.int W') (Val.cons (Val.int a) (Val.int b))
      (auPvals p α s t ++ rest)) (fun vs hvs => hvs) ?_ (fun vs hvs => le_refl Kc)
    intro vs out hvs hout
    have hdisc : inDisc p (a, b) := hab
    have h1 : isz W' ≤ p + 3 := Work.ConvR.isz_le_of_natAbs_le hWb'
    have h2 : isz a ≤ p + 3 :=
      Work.ConvR.isz_le_of_natAbs_le (Work.ConvR.natAbs_fst_le_of_inDisc hdisc)
    have h3 : isz b ≤ p + 3 :=
      Work.ConvR.isz_le_of_natAbs_le (Work.ConvR.natAbs_snd_le_of_inDisc hdisc)
    refine ⟨Val.cons (Val.int W') (Val.cons (Val.int a) (Val.int b)), ?_,
      ⟨W', a, b, rfl, rfl, rfl⟩, ?_⟩
    · rw [hout]; rfl
    · rw [Work.ConvR.vsz_cons, Work.ConvR.vsz_cons, Work.ConvR.vsz_int, Work.ConvR.vsz_int,
        Work.ConvR.vsz_int]
      omega
  -- the zip
  have hlen : WTS.length = WIN.length := by rw [hWTS, hWIN]
  have hPmem : ∀ i < WTS.length, CwP p (WTS.getD i .nil) (WIN.getD i .nil) := by
    intro i hi
    have hiL : i < L := by rwa [hWTS] at hi
    exact ⟨W i, (z i).1, (z i).2, hWg i hiL, hZg i hiL, hWb i hiL,
      show inDisc p (z i) from hZd i hiL⟩
  have hLmem : ∀ x ∈ WTS ++ WIN, vsz x ≤ 3 * p + 11 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
      have hiL : i < L := by rw [← hWTS]; exact hi
      rw [← hix, ← List.getD_eq_getElem WTS .nil hi, hWg i hiL, Work.ConvR.vsz_int]
      have := Work.ConvR.isz_le_of_natAbs_le (hWb i hiL)
      omega
    · obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
      have hiL : i < L := by rw [← hWIN]; exact hi
      rw [← hix, ← List.getD_eq_getElem WIN .nil hi, hZg i hiL]
      have := Work.ConvR.vsz_cfxVal_le (p := p) (hZd i hiL)
      rw [Work.ConvR.cfxSz] at this
      omega
  have hzipInst := hzip main consP (auPvals p α s t ++ rest) (CwP p) CwQ Kc (3 * p + 11)
    hbody WTS WIN hlen hPmem hLmem
  -- the first word: split the chunk
  have hunc : Pipe main unconsP [Val.cons (ofList WTS) (ofList WIN)] [ofList WTS, ofList WIN] Ku :=
    Pipe.unconsV huncons (ofList WTS) (ofList WIN)
  -- the tail word: three constants and a copy of `int p` under the list
  have htail : ∀ Z : Val, vsz Z ≤ (L + 1) * (3 * p + 12) →
      Pipe main (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pushP Val.nil) (pushP (Val.int 0)))
        (pushP (Val.int 0))) (pickP 6)) (rollP 4))
        [Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ),
          auTable p α s t]
        [Z, Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Val.int ((auOff p α s : ℕ) : ℤ),
          Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t]
        (Kv * 2 + Kv * 3 + Kv * 3
          + Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1)
          + Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1)) := by
    intro Z hZ
    -- step 1: push `nil`
    have P1 : Pipe main (pushP Val.nil)
        [Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ),
          auTable p α s t]
        [Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ),
          Val.int (p : ℤ), auTable p α s t] (Kv * 2) := by
      refine Pipe.le (Pipe.pushOnAny (T := [Z, Val.int ((auOff p α s : ℕ) : ℤ),
        Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t])
        (hpush main Val.nil)) ?_
      rw [hvnil]
    -- steps 2, 3: push `int 0` twice
    have P2 : Pipe main (pushP (Val.int 0))
        [Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ),
          Val.int (p : ℤ), auTable p α s t]
        [Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ),
          Val.int (p : ℤ), auTable p α s t] (Kv * 3) := by
      refine Pipe.le (Pipe.pushOnAny (T := [Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ),
        Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t])
        (hpush main (Val.int 0))) ?_
      rw [hszZ0]
    have P3 : Pipe main (pushP (Val.int 0))
        [Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ),
          Val.int (p : ℤ), auTable p α s t]
        [Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ),
          Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t] (Kv * 3) := by
      refine Pipe.le (Pipe.pushOnAny (T := [Val.int 0, Val.nil, Z,
        Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ),
        auTable p α s t]) (hpush main (Val.int 0))) ?_
      rw [hszZ0]
    -- step 4: copy `int p` (index 6 of the window) to the top
    have P4 : Pipe main (pickP 6)
        [Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t]
        (Val.int (p : ℤ) :: [Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t])
        (Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1)) := by
      have hj : 3 * p + 12 ≤ (L + 1) * (3 * p + 12) := by
        calc 3 * p + 12 = 1 * (3 * p + 12) := by ring
          _ ≤ (L + 1) * (3 * p + 12) := Nat.mul_le_mul_right _ (by omega)
      have hmem : ∀ v ∈ ([Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ)] : List Val),
          vsz v ≤ (L + 1) * (3 * p + 12) + 4 * p + 5 := by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hszZ0]; omega
        · rw [hszZ0]; omega
        · rw [hvnil]; omega
        · omega
        · rw [Work.ConvR.vsz_int]; omega
        · rw [Work.ConvR.vsz_int]; omega
        · rw [Work.ConvR.vsz_int]; omega
      refine Pipe.le (Pipe.pick main hpick (A := [Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t]) (k := 6) (by simp)) ?_
      show Kp * 7 * (Work.Fx.szl (([Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t] : List Val).take 7) + 1)
        ≤ Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1)
      have hszl : Work.Fx.szl (([Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t] : List Val).take 7)
          ≤ 7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) := by
        have htake : ([Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t] : List Val).take 7 = [Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ)] := rfl
        rw [htake]
        simpa using szl_le_len_mul (A := ([Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ)] : List Val))
          (n := (L + 1) * (3 * p + 12) + 4 * p + 5) hmem
      exact Nat.mul_le_mul_left (Kp * 7) (by omega)
    -- step 5: bring the list back on top (index 4 of the window)
    have P5 : Pipe main (rollP 4)
        [Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t]
        [Z, Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t]
        (Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1)) := by
      have hj : 3 * p + 12 ≤ (L + 1) * (3 * p + 12) := by
        calc 3 * p + 12 = 1 * (3 * p + 12) := by ring
          _ ≤ (L + 1) * (3 * p + 12) := Nat.mul_le_mul_right _ (by omega)
      have hmem : ∀ v ∈ ([Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z] : List Val),
          vsz v ≤ (L + 1) * (3 * p + 12) := by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · rw [Work.ConvR.vsz_int]; omega
        · rw [hszZ0]; omega
        · rw [hszZ0]; omega
        · rw [hvnil]; omega
        · omega
      refine Pipe.le (Pipe.roll main hroll (A := [Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t]) (k := 4) (by simp)) ?_
      show Kr * 5 * (Work.Fx.szl (([Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t] : List Val).take 5) + 1)
        ≤ Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1)
      have hszl : Work.Fx.szl (([Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t] : List Val).take 5)
          ≤ 5 * ((L + 1) * (3 * p + 12)) := by
        have htake : ([Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z, Val.int ((auOff p α s : ℕ) : ℤ), Val.int ((auCop p α s : ℕ) : ℤ), Val.int (p : ℤ), auTable p α s t] : List Val).take 5 = [Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z] := rfl
        rw [htake]
        simpa using szl_le_len_mul (A := ([Val.int (p : ℤ), Val.int 0, Val.int 0, Val.nil, Z] : List Val))
          (n := (L + 1) * (3 * p + 12)) hmem
      exact Nat.mul_le_mul_left (Kr * 5) (by omega)
    -- compose the five steps
    have hcomp := Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp P1 P2) P3) P4) P5
    exact Pipe.le hcomp (by omega)
  -- assembly
  have hZs : ∀ {zs : List Val}, zs.length = L → (∀ i < L, vsz (zs.getD i .nil) ≤ 3 * p + 11) →
      vsz (ofList zs) ≤ (L + 1) * (3 * p + 12) := by
    intro zs hlen' hsz
    have h1 := cw_vsz_ofList (zs := zs) (L := L) (Lz := 3 * p + 11) hlen' hsz
    have h2 : L * (3 * p + 11 + 1) + 1 ≤ (L + 1) * (3 * p + 12) := by
      have he : (3 * p + 11 + 1 : ℕ) = 3 * p + 12 := by ring
      rw [he, Nat.add_mul, one_mul]
      omega
    omega
  intro vs hvs st0 Rg hRg
  -- step 1: split the chunk
  obtain ⟨mid₁, st₁, n₁, hmid₁, hev₁, hn₁, hstk₁, hoth₁⟩ :=
    hunc (auPvals p α s t ++ rest) vs hvs st0 Rg hRg
  -- step 2: zip the two lists
  obtain ⟨mid₂, st₂, n₂, hQ₂, hev₂, hn₂, hstk₂, hoth₂⟩ :=
    hzipInst mid₁ (by rw [hmid₁]; rfl) st₁ Rg hstk₁
  obtain ⟨zs, hmid₂, hlen₂, hQz⟩ := hQ₂
  -- step 3: rearrange
  have hlenL : zs.length = L := by rw [hlen₂, hWTS]
  have hQzi : ∀ i < L, CwQ (Val.int (W i)) (Val.cons (Val.int (z i).1) (Val.int (z i).2))
      (zs.getD i .nil) := by
    intro i hi
    have h := hQz i (by rwa [hWTS])
    rwa [hWg i hi, hZg i hi] at h
  have hszzs : ∀ i < L, vsz (zs.getD i .nil) ≤ 3 * p + 11 := by
    intro i hi
    have h := (cwQ_facts (hQzi i hi)).2
    rw [h]
    have h1 : isz (W i) ≤ p + 3 := Work.ConvR.isz_le_of_natAbs_le (hWb i hi)
    have h2 : isz (z i).1 ≤ p + 3 := Work.ConvR.isz_le_of_natAbs_le
      (Work.ConvR.natAbs_fst_le_of_inDisc (show inDisc p (z i) from hZd i hi))
    have h3 : isz (z i).2 ≤ p + 3 := Work.ConvR.isz_le_of_natAbs_le
      (Work.ConvR.natAbs_snd_le_of_inDisc (show inDisc p (z i) from hZd i hi))
    omega
  obtain ⟨out, st₃, n₃, hout, hev₃, hn₃, hstk₃, hoth₃⟩ :=
    htail (ofList zs) (hZs hlenL hszzs) rest mid₂ (by rw [hmid₂]; rfl) st₂ Rg hstk₂
  -- the resulting list is the pointwise pair list
  have hzget : ∀ i < L, zs.getD i .nil = AwPair (W i) (z i).1 (z i).2 := by
    intro i hi
    exact (cwQ_facts (hQzi i hi)).1
  have hzs : zs = (List.range L).map (fun i => AwPair (W i) (z i).1 (z i).2) :=
    cw_eq_range_map_getD zs Val.nil (fun i => AwPair (W i) (z i).1 (z i).2) hlenL hzget
  refine ⟨out, st₃, n₁ + (n₂ + n₃), ?_, Eval.seq hev₁ (Eval.seq hev₂ hev₃), ?_, hstk₃, ?_⟩
  · -- the final value list
    rw [hout, hzs]
    rfl
  · -- the cost
    have hc1 : n₁ ≤ Ku := hn₁
    have hc2 : n₂ ≤ L * (Kc + Kz * (3 * p + 12)) + Kz := by
      refine le_trans hn₂ ?_
      have h : (3 * p + 11 + 1 : ℕ) = 3 * p + 12 := by ring
      rw [hWTS, h]
    have hc3 : n₃ ≤ Kv * 2 + Kv * 3 + Kv * 3
        + Kp * 7 * (7 * ((L + 1) * (3 * p + 12) + 4 * p + 5) + 1)
        + Kr * 5 * (5 * ((L + 1) * (3 * p + 12)) + 1) := hn₃
    have hmain : n₁ + (n₂ + n₃)
        ≤ 10000 * (Kp + Ku + Kv + Kz + Kr + Kc + 1) * ((L + 1) * (p + 1)) := by
      have h := cw_cost_le L p Kp Ku Kv Kz Kr Kc
      omega
    calc n₁ + (n₂ + n₃)
        ≤ 10000 * (Kp + Ku + Kv + Kz + Kr + Kc + 1) * ((L + 1) * (p + 1)) := hmain
      _ = 10000 * (Kp + Ku + Kv + Kz + Kr + Kc + 1) * (L + 1) * (p + 1) := by ring
  · -- the other stacks are restored
    intro k hk
    rw [hoth₃ k hk, hoth₂ k hk, hoth₁ k hk]

end Work.Resample
