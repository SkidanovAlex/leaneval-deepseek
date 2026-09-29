import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.chirpTabKit
import Submission.Work.ConvR.basic
import Submission.Work.Fx.FxCommon
import Submission.Work.Transform.extractCvec
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPrepDefs

/-!
# `Work.Transform.ztabCis`: the length-`r` table `c ↦ ζ^c` for `ζ = e^{πi/r}` (paper Prop 3.5)

This file proves `Work.Transform.ztabCis`, assembling the library `Prop`s `KernelLib`,
`IntLib`, `LayoutLib`, `FxLib` into a straight-line program:

* `Work.Transform.ztabIdx` — the index list `(List.range r).map Val.int`
  (`LayoutLib.replicate`, `LayoutLib.enumerate` and a `mapList` peel of the labels);
* `Work.Transform.ztabElem` — the per-element word
  `int c :: int p :: int r :: rest ↦ cfxVal w :: int p :: int r :: rest` by one `FxLib.cis`
  call with denominator `2r` (the identity `e^{2πi c/(2r)} = ζ_r^c`);
* the main `Work.Transform.ztabCis` — `KernelLib.mapList` of the element word over the index
  list, and `Work.Transform.extractCvec` to read the result back as a list of pairs.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH
open Work.Resample

/-! ## Sizes -/

theorem isz_zero : isz (0 : ℤ) = 2 := by simp [isz]

theorem isz_one : isz (1 : ℤ) = 3 := by simp [isz, Nat.size]

/-! ## Budget arithmetic -/

theorem const_le_pow {C q : ℕ} (hq : 2 ≤ q) : C ≤ q ^ (2 * C) := by
  have h1 : C < 2 ^ C := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ C ≤ 2 ^ (2 * C) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ (2 * C) ≤ q ^ (2 * C) := Nat.pow_le_pow_left hq _
  exact le_of_lt (lt_of_lt_of_le h1 (le_trans h2 h3))

theorem const_mul_le_pow {C q K : ℕ} (hq : 3 ≤ q) (hK : 2 * C + 4 ≤ K) : C * (q + 4) ≤ q ^ K := by
  have h1 : C ≤ q ^ (2 * C) := const_le_pow (by omega)
  have h2 : q + 4 ≤ q ^ 4 := by
    have hq2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : q + 4 ≤ q ^ 2 := by rw [show q ^ 2 = q * q by ring]; nlinarith only [hq]
    exact le_trans h3 hq2
  calc C * (q + 4) ≤ q ^ (2 * C) * q ^ 4 := Nat.mul_le_mul h1 h2
    _ = q ^ (2 * C + 4) := by rw [← pow_add]
    _ ≤ q ^ K := Nat.pow_le_pow_right (by omega) hK

theorem pow_budget {p K C : ℕ} (h1 : K * 4 ^ K ≤ C) (h2 : K ≤ C) :
    K * (4 * (p + 1)) ^ K ≤ C * (p + 1) ^ C := by
  have h3 : (4 * (p + 1)) ^ K = 4 ^ K * (p + 1) ^ K := by rw [mul_pow]
  calc K * (4 * (p + 1)) ^ K = (K * 4 ^ K) * (p + 1) ^ K := by rw [h3]; ring
    _ ≤ C * (p + 1) ^ K := Nat.mul_le_mul_right _ h1
    _ ≤ C * (p + 1) ^ C := Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) h2)

/-- `KernelLib.unconsV` as a `Pipe`. -/
theorem pipe_unconsV {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    (a b : Val) : Pipe main prog [.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv : vs = .cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, b, rest, hv⟩ s R hR
  obtain ⟨hvab, hr⟩ := List.cons.inj (hvs'.symm.trans hv)
  obtain ⟨ha, hb⟩ := Val.cons.inj hvab
  exact ⟨out, s', n, by rw [hout, ha, hb, hr]; rfl, hev, hn, hstk, hoth⟩

/-- `KernelLib.pick` as a `Pipe`, with the cost evaluated on the window. -/
theorem pipe_pick {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : A.length = k + 1) :
    Pipe main (prog k) A (A.getD k .nil :: A) (K * (k + 1) * (Work.Fx.szl A + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append, hk]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have htake : vs.take (k + 1) = A := by rw [hvs, ← hk, List.take_left]
  have hn' : n ≤ K * (k + 1) * (Work.Fx.szl A + 1) := by
    simpa only [htake, Work.Fx.szl] using hn
  have hpost : out = (A.getD k .nil :: A) ++ rest := by
    rw [hout, hvs, Work.Fx.getD_append_of_lt (by omega : k < A.length), List.cons_append]
  exact ⟨out, s', n, hpost, hev, hn', hstk, hoth⟩

/-- `KernelLib.roll` as a `Pipe`, with the cost evaluated on the window. -/
theorem pipe_roll {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : A.length = k + 1) :
    Pipe main (prog k) A (A.getD k .nil :: A.eraseIdx k) (K * (k + 1) * (Work.Fx.szl A + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append, hk]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have htake : vs.take (k + 1) = A := by rw [hvs, ← hk, List.take_left]
  have hn' : n ≤ K * (k + 1) * (Work.Fx.szl A + 1) := by
    simpa only [htake, Work.Fx.szl] using hn
  have hpost : out = (A.getD k .nil :: A.eraseIdx k) ++ rest := by
    rw [hout, hvs, Work.Fx.getD_append_of_lt (by omega : k < A.length),
      Work.Fx.eraseIdx_append_of_lt (by omega : k < A.length), List.cons_append]
  exact ⟨out, s', n, hpost, hev, hn', hstk, hoth⟩

/-- The peel word: `cons (int i) _ ↦ int i`. -/
def peelF : Val → Val
  | .cons (.int i) _ => .int i
  | _ => .nil

/-! ## Small list lemmas -/

/-- Injectivity of a three-element `cons` prefix. -/
theorem cons₃_eq {a b c : Val} {l l' : List Val} (h : a :: b :: c :: l = a :: b :: c :: l') :
    l = l' := by
  have h1 := (List.cons.inj h).2
  have h2 := (List.cons.inj h1).2
  exact (List.cons.inj h2).2

/-- `List.Forall₂` read at an index, in `getD` form. -/
theorem forall₂_getD {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (d₁ : α) (d₂ : β) {i : ℕ}
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : R (l₁.getD i d₁) (l₂.getD i d₂) := by
  rw [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂]
  simpa only [List.get_eq_getElem] using List.Forall₂.get h h₁ h₂

/-- The `cis` phase identity: `e^{2πi c/(2r)} = ζ_r^c`. -/
theorem exp_cis_two_r (r c : ℕ) (hr : 0 < r) :
    Complex.exp (2 * Real.pi * Complex.I * ((c : ℤ) : ℂ) / ((2 * r : ℕ) : ℂ)) = zeta r c := by
  rw [zeta]
  congr 1
  have hr' : ((r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp

/-! ## The index list `(List.range r).map Val.int` -/

theorem ztabIdx (hK : KernelLib) (hL : LayoutLib) :
    ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p r : ℕ) (rest : List Val),
      100 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) →
      WordR main prog
        (fun vs => vs = Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest)
        (fun _ out => out = ofList ((List.range r).map (fun i : ℕ => Val.int (i : ℤ))) ::
          Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest)
        (fun _ => K * (r * (p + 1) ^ K + 1)) := by
  obtain ⟨pushProg, Kpush, hpush⟩ := hK.pushVal
  obtain ⟨pickProg, Kpick, hpick⟩ := hK.pick
  obtain ⟨repProg, Krep, hrep⟩ := hL.replicate
  obtain ⟨enumProg, Ken, hen⟩ := hL.enumerate
  obtain ⟨mapP, Kml, hmapML⟩ := hK.mapList
  obtain ⟨unconsProg, Ku, huncons⟩ := hK.unconsV
  obtain ⟨swapProg, Ks, hswap⟩ := hK.swap
  obtain ⟨dropProg, Kd, hdrop⟩ := hK.drop
  set peelProg : Cmd := .seq (.seq unconsProg swapProg) dropProg with hpeelProg
  set CI : ℕ := 3 * (Kpush + Kpick + Krep + Ken + Kml + Ku + Ks + Kd + 1) with hCIdef
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pushProg (.int 0)) (pickProg 2)) repProg) enumProg)
      (mapP peelProg), 4000 * CI + 1000, ?_⟩
  intro main p r rest hp hr hlt
  have hrsz : r.size ≤ p - 1 := Nat.size_le.mpr hlt
  have hszr : isz ((r : ℤ)) ≤ p + 1 := by
    have h := Work.Transform.isz_natCast_le (n := r) (p := p - 1) hlt
    omega
  have hszp : isz ((p : ℤ)) ≤ p + 2 := isz_natCast_le (Nat.lt_two_pow_self (n := p))
  -- the peel word on one element
  have hpeel : ∀ i, i < r → Pipe main peelProg [Val.cons (Val.int (i : ℤ)) (Val.int 0)]
      [Val.int (i : ℤ)] (Ku + Ks * (p + 4) + 3 * Kd) := by
    intro i hi
    have hir : i < 2 ^ (p - 1) := lt_of_lt_of_le hi (le_of_lt hlt)
    have hsz : isz ((i : ℤ)) ≤ p + 1 := by
      have h := Work.Transform.isz_natCast_le (n := i) (p := p - 1) hir
      omega
    have h1 : Pipe main unconsProg [Val.cons (Val.int (i : ℤ)) (Val.int 0)]
        [Val.int (i : ℤ), Val.int 0] Ku :=
      pipe_unconsV (main := main) (huncons main) (Val.int (i : ℤ)) (Val.int 0)
    have h2 : Pipe main swapProg [Val.int (i : ℤ), Val.int 0] [Val.int 0, Val.int (i : ℤ)]
        (Ks * (vsz (Val.int (i : ℤ)) + vsz (Val.int 0) + 1)) :=
      Pipe.swap main hswap (Val.int (i : ℤ)) (Val.int 0)
    have h3 : Pipe main dropProg [Val.int 0, Val.int (i : ℤ)] [Val.int (i : ℤ)]
        (Kd * (vsz (Val.int 0) + 1)) :=
      Pipe.appendTail (main := main) (prog := dropProg) [Val.int (i : ℤ)]
        (Pipe.drop main hdrop (Val.int 0))
    have h123 : Pipe main peelProg [Val.cons (Val.int (i : ℤ)) (Val.int 0)] [Val.int (i : ℤ)]
        (Ku + Ks * (vsz (Val.int (i : ℤ)) + vsz (Val.int 0) + 1) + Kd * (vsz (Val.int 0) + 1)) :=
      Pipe.comp (Pipe.comp h1 h2) h3
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int, isz_zero] at h123
    refine Pipe.le h123 ?_
    have h1' : isz ((i : ℤ)) + 2 + 1 ≤ p + 4 := by omega
    have h2' : Ks * (isz ((i : ℤ)) + 2 + 1) ≤ Ks * (p + 4) := Nat.mul_le_mul_left _ h1'
    have h3' : Kd * (2 + 1) = 3 * Kd := by ring
    rw [h3']
    omega
  -- the list of labels
  set xs : List Val := (List.range r).map (fun i : ℕ => Val.cons (.int (i : ℤ)) (.int 0)) with hxs
  have hxslen : xs.length = r := by rw [hxs]; simp
  have hxmem : ∀ x ∈ xs, ∃ i, i < r ∧ x = Val.cons (.int (i : ℤ)) (.int 0) := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i, by simpa using hi, ?_⟩
    rw [← hix, List.getElem_map, List.getElem_range]
  have hinner : ∀ x ∈ xs, Pipe main peelProg [x] [peelF x] (Ku + Ks * (p + 4) + 3 * Kd) := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := hxmem x hx
    have h1 : peelF (Val.cons (.int (i : ℤ)) (.int 0)) = Val.int (i : ℤ) := rfl
    rw [hix]
    exact Pipe.rw (hpeel i hi) (by rw [h1])
  have hxs2 : ∀ x ∈ xs, vsz x ≤ p + 4 := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := hxmem x hx
    rw [hix, Work.Fx.vsz_cons, Work.Fx.vsz_int, Work.Fx.vsz_int, isz_zero]
    have hsz : isz ((i : ℤ)) ≤ p + 1 := by
      have hir : i < 2 ^ (p - 1) := lt_of_lt_of_le hi (le_of_lt hlt)
      have h := Work.Transform.isz_natCast_le (n := i) (p := p - 1) hir
      omega
    omega
  have hy2 : ∀ x ∈ xs, vsz (peelF x) ≤ p + 4 := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := hxmem x hx
    have h1 : peelF (Val.cons (Val.int (i : ℤ)) (Val.int 0)) = Val.int (i : ℤ) := rfl
    rw [hix, h1, Work.Fx.vsz_int]
    have hsz : isz ((i : ℤ)) ≤ p + 1 := by
      have hir : i < 2 ^ (p - 1) := lt_of_lt_of_le hi (le_of_lt hlt)
      have h := Work.Transform.isz_natCast_le (n := i) (p := p - 1) hir
      omega
    omega
  -- the `mapList` step
  have hmapW : WordR main (mapP peelProg)
      (fun vs => vs = ofList xs :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
      (fun _ out => out = ofList (xs.map peelF) :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
      (fun _ => r * (Ku + Ks * (p + 4) + 3 * Kd + Kml * (p + 5)) + Kml) := by
    have hML : MapListField mapP Kml := hmapML
    have h := mapListFun (hML := hML) (main := main) (q := peelProg)
      (rest := Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest) (xs := xs) (F := peelF)
      (c := Ku + Ks * (p + 4) + 3 * Kd) (L := p + 4) hinner hxs2 hy2
    rw [hxslen] at h
    simpa [Nat.add_assoc] using h
  -- the four deterministic steps
  have hpipe1 : Pipe main (pushProg (.int 0)) [Val.int (p : ℤ), Val.int (r : ℤ)]
      [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)] (Kpush * 3) := by
    have h := Pipe.pushOnAny (main := main) (v := Val.int 0)
      (T := [Val.int (p : ℤ), Val.int (r : ℤ)]) (hpush main (Val.int 0))
    rw [Work.Fx.vsz_int, isz_zero] at h
    exact h
  have hpipe2 : Pipe main (pickProg 2) [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)]
      [Val.int (r : ℤ), Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)]
      (Kpick * 3 * (Work.Fx.szl [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)] + 1)) := by
    have h := pipe_pick (main := main) (prog := pickProg) hpick
      (A := [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)]) (k := 2) (by simp)
    have hwin : [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)].getD 2 Val.nil
        :: [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)]
        = [Val.int (r : ℤ), Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)] := by simp
    rw [hwin] at h
    exact h
  have hpipe3 : Pipe main repProg [Val.int (r : ℤ), Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)]
      [ofList (List.replicate r (Val.int 0)), Val.int (p : ℤ), Val.int (r : ℤ)]
      (Krep * ((r + 1) * 3 + isz ((r : ℤ)) + 1)) := by
    have h := Pipe.appendTail (main := main) (prog := repProg)
      ([Val.int (p : ℤ), Val.int (r : ℤ)]) (Pipe.replicate main hrep (k := r) (v := Val.int 0))
    rw [Work.Fx.vsz_int, isz_zero] at h
    exact h
  have hpipe4 : Pipe main enumProg
      [ofList (List.replicate r (Val.int 0)), Val.int (p : ℤ), Val.int (r : ℤ)]
      [ofList ((List.range (List.replicate r (Val.int 0)).length).map
        (fun i : ℕ => Val.cons (.int (i : ℤ)) ((List.replicate r (Val.int 0)).getD i .nil))),
        Val.int (p : ℤ), Val.int (r : ℤ)]
      (Ken * (vsz (ofList (List.replicate r (Val.int 0)))
        + (List.replicate r (Val.int 0)).length
          * ((List.replicate r (Val.int 0)).length.size + 1) + 1)) := by
    have h := Pipe.appendTail (main := main) (prog := enumProg)
      ([Val.int (p : ℤ), Val.int (r : ℤ)])
      (Pipe.enumerate main hen (xs := List.replicate r (Val.int 0)))
    simpa using h
  have h1234 : Pipe main (Cmd.seq (Cmd.seq (Cmd.seq (pushProg (.int 0)) (pickProg 2)) repProg) enumProg)
      [Val.int (p : ℤ), Val.int (r : ℤ)]
      [ofList xs, Val.int (p : ℤ), Val.int (r : ℤ)]
      (((Kpush * 3 + Kpick * 3 * (Work.Fx.szl [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)] + 1))
        + Krep * ((r + 1) * 3 + isz ((r : ℤ)) + 1))
        + Ken * (vsz (ofList (List.replicate r (Val.int 0)))
            + (List.replicate r (Val.int 0)).length
              * ((List.replicate r (Val.int 0)).length.size + 1) + 1)) := by
    have h := Pipe.comp (Pipe.comp (Pipe.comp hpipe1 hpipe2) hpipe3) hpipe4
    have hlabel : (List.range (List.replicate r (Val.int 0)).length).map
        (fun i : ℕ => Val.cons (.int (i : ℤ)) ((List.replicate r (Val.int 0)).getD i .nil)) = xs := by
      rw [hxs]
      exact enumerate_replicate r (Val.int 0)
    rw [hlabel] at h
    exact h
  -- compose and convert
  have hseq := Work.Kernel.WordR_seq (main := main)
    (P := fun vs => vs = [Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest)
    (Q := fun _ mid => mid = [ofList xs, Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest)
    (C := fun _ => ((Kpush * 3 + Kpick * 3 * (Work.Fx.szl [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)] + 1))
        + Krep * ((r + 1) * 3 + isz ((r : ℤ)) + 1))
        + Ken * (vsz (ofList (List.replicate r (Val.int 0)))
            + (List.replicate r (Val.int 0)).length
              * ((List.replicate r (Val.int 0)).length.size + 1) + 1))
    (P' := fun mid => mid = ofList xs :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
    (Q' := fun _ out => out = ofList (xs.map peelF) :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
    (C' := fun _ => r * (Ku + Ks * (p + 4) + 3 * Kd + Kml * (p + 5)) + Kml)
    (B := fun _ => r * (Ku + Ks * (p + 4) + 3 * Kd + Kml * (p + 5)) + Kml)
    (h1234 rest) hmapW (fun _ _ _ h => ⟨h, le_rfl⟩)
  have hindex : ofList (xs.map peelF)
      = ofList ((List.range r).map (fun i : ℕ => Val.int (i : ℤ))) := by
    congr 1
    rw [hxs, List.map_map]
    apply List.map_congr_left
    intro i _
    simp [peelF, Function.comp]
  refine Work.Kernel.WordR_conseq hseq ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    rfl
  · intro vs out _ hout
    obtain ⟨_mid, _hmid, hout'⟩ := hout
    rw [hout', hindex]
  · intro vs _
    -- the numerical bound (small terms first, so that the arithmetic stays cheap)
    set K : ℕ := 4000 * CI + 1000 with hKdef
    set s1 : ℕ := Kpush * 3 with hs1
    set s2 : ℕ := Kpick * 3 * (Work.Fx.szl [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)] + 1) with hs2
    set s3 : ℕ := Krep * ((r + 1) * 3 + isz ((r : ℤ)) + 1) with hs3
    set s4 : ℕ := Ken * (vsz (ofList (List.replicate r (Val.int 0)))
        + (List.replicate r (Val.int 0)).length
          * ((List.replicate r (Val.int 0)).length.size + 1) + 1) with hs4
    set s5 : ℕ := r * (Ku + Ks * (p + 4) + 3 * Kd + Kml * (p + 5)) + Kml with hs5
    set T : ℕ := r * (p + 1) ^ K with hTdef
    have hpow2 : (p + 1) ^ 2 ≤ (p + 1) ^ K := Nat.pow_le_pow_right (by omega) (by omega)
    have hvsz : vsz (ofList (List.replicate r (Val.int 0))) = 3 * r + 1 := by
      simp only [Work.ConvR.vsz_ofList, List.length_replicate, List.map_replicate,
        Work.Fx.vsz_int, isz_zero, List.sum_replicate]
      ring
    have b1 : s1 ≤ CI * 3 := by
      rw [hs1]
      have h1 : Kpush ≤ CI := by simp only [hCIdef]; omega
      exact Nat.mul_le_mul_right 3 h1
    have hszl0 : Work.Fx.szl [Val.int 0, Val.int (p : ℤ), Val.int (r : ℤ)]
        = 2 + isz ((p : ℤ)) + isz ((r : ℤ)) := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Work.Fx.vsz_int, isz_zero, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have b2 : s2 ≤ CI * (3 * (2 * p + 7)) := by
      rw [hs2, hszl0]
      have h1 : Kpick * 3 ≤ CI := by simp only [hCIdef]; omega
      have h5 : 2 + isz ((p : ℤ)) + isz ((r : ℤ)) + 1 ≤ 3 * (2 * p + 7) := by omega
      exact Nat.mul_le_mul h1 h5
    have b3 : s3 ≤ CI * (3 * r + p + 5) := by
      rw [hs3]
      have h1 : Krep ≤ CI := by simp only [hCIdef]; omega
      have h5 : (r + 1) * 3 + isz ((r : ℤ)) + 1 ≤ 3 * r + p + 5 := by omega
      exact Nat.mul_le_mul h1 h5
    have b4 : s4 ≤ CI * (r * (p + 1) + 3 * r + 2) := by
      rw [hs4]
      have h1 : Ken ≤ CI := by simp only [hCIdef]; omega
      have h5 : vsz (ofList (List.replicate r (Val.int 0)))
            + (List.replicate r (Val.int 0)).length
              * ((List.replicate r (Val.int 0)).length.size + 1) + 1
          ≤ r * (p + 1) + 3 * r + 2 := by
        have h6 : (List.replicate r (Val.int 0)).length
            * ((List.replicate r (Val.int 0)).length.size + 1) ≤ r * (p + 1) := by
          rw [List.length_replicate]
          calc r * (r.size + 1) ≤ r * (p - 1 + 1) :=
                Nat.mul_le_mul_left r (by have := hrsz; omega)
            _ = r * p := by rw [Nat.sub_add_cancel (by omega)]
            _ ≤ r * (p + 1) := Nat.mul_le_mul_left r (by omega)
        rw [hvsz]
        omega
      exact Nat.mul_le_mul h1 h5
    have b5 : s5 ≤ CI * (2 * (r * (2 * p + 13))) := by
      rw [hs5]
      have h1 : Ku ≤ CI := by simp only [hCIdef]; omega
      have h2 : Ks ≤ CI := by simp only [hCIdef]; omega
      have h3 : Kd ≤ CI := by simp only [hCIdef]; omega
      have h4 : Kml ≤ CI := by simp only [hCIdef]; omega
      have hA : Ku + Ks * (p + 4) + 3 * Kd + Kml * (p + 5) ≤ CI * (2 * p + 13) := by
        have e1 : Ks * (p + 4) ≤ CI * (p + 4) := Nat.mul_le_mul_right _ h2
        have e2 : Kml * (p + 5) ≤ CI * (p + 5) := Nat.mul_le_mul_right _ h4
        have e3 : Ku ≤ CI * 1 := by simpa using h1
        have e4 : 3 * Kd ≤ CI * 3 := by
          calc 3 * Kd = Kd * 3 := by ring
            _ ≤ CI * 3 := Nat.mul_le_mul_right 3 h3
        nlinarith only [e1, e2, e3, e4]
      have hB : r * (CI * (2 * p + 13)) + CI ≤ CI * (2 * (r * (2 * p + 13))) := by
        have h6 : r * (CI * (2 * p + 13)) = CI * (r * (2 * p + 13)) := by ring
        have h7 : CI * 1 ≤ CI * (r * (2 * p + 13)) :=
          Nat.mul_le_mul_left CI (by nlinarith only [hr, hp])
        rw [h6]
        have h8 := h7
        simp only [Nat.mul_one] at h8
        linarith only [h8]
      exact le_trans (Nat.add_le_add (Nat.mul_le_mul_left r hA) h4) hB
    have hsum : (((s1 + s2) + s3) + s4) + s5 ≤ CI * (7 * p + 31 + 33 * r + 5 * (r * p)) := by
      have h1 : CI * 3 + CI * (3 * (2 * p + 7)) + CI * (3 * r + p + 5)
          + CI * (r * (p + 1) + 3 * r + 2) + CI * (2 * (r * (2 * p + 13)))
          ≤ CI * (7 * p + 31 + 33 * r + 5 * (r * p)) := by
        have hb : 3 + 3 * (2 * p + 7) + (3 * r + p + 5) + (r * (p + 1) + 3 * r + 2)
            + 2 * (r * (2 * p + 13)) ≤ 7 * p + 31 + 33 * r + 5 * (r * p) := by linarith
        calc CI * 3 + CI * (3 * (2 * p + 7)) + CI * (3 * r + p + 5)
            + CI * (r * (p + 1) + 3 * r + 2) + CI * (2 * (r * (2 * p + 13)))
            = CI * (3 + 3 * (2 * p + 7) + (3 * r + p + 5) + (r * (p + 1) + 3 * r + 2)
                + 2 * (r * (2 * p + 13))) := by ring
          _ ≤ CI * (7 * p + 31 + 33 * r + 5 * (r * p)) := Nat.mul_le_mul_left CI hb
      have h2 : (((s1 + s2) + s3) + s4) + s5
          ≤ CI * 3 + CI * (3 * (2 * p + 7)) + CI * (3 * r + p + 5)
            + CI * (r * (p + 1) + 3 * r + 2) + CI * (2 * (r * (2 * p + 13))) := by
        linarith only [b1, b2, b3, b4, b5]
      linarith only [h1, h2]
    have hT1 : 7 * p + 31 ≤ T := by
      rw [hTdef]
      have h2 : 7 * p + 31 ≤ 2 * (p + 1) ^ 2 := by nlinarith only [hp]
      calc 7 * p + 31 ≤ 2 * (p + 1) ^ 2 := h2
        _ ≤ r * (p + 1) ^ 2 := by nlinarith only [hr]
        _ ≤ r * (p + 1) ^ K := Nat.mul_le_mul_left r hpow2
    have hT2 : 33 * r ≤ T := by
      rw [hTdef]
      have h2 : 33 ≤ (p + 1) ^ 2 := by nlinarith only [hp]
      calc 33 * r ≤ (p + 1) ^ 2 * r := Nat.mul_le_mul_right r h2
        _ = r * (p + 1) ^ 2 := by ring
        _ ≤ r * (p + 1) ^ K := Nat.mul_le_mul_left r hpow2
    have hT3 : 5 * (r * p) ≤ T := by
      rw [hTdef]
      have h2 : 5 * p ≤ (p + 1) ^ 2 := by nlinarith only [hp]
      calc 5 * (r * p) = r * (5 * p) := by ring
        _ ≤ r * (p + 1) ^ 2 := Nat.mul_le_mul_left r h2
        _ ≤ r * (p + 1) ^ K := Nat.mul_le_mul_left r hpow2
    have hB : 7 * p + 31 + 33 * r + 5 * (r * p) ≤ 3 * T := by linarith only [hT1, hT2, hT3]
    calc (((s1 + s2) + s3) + s4) + s5 ≤ CI * (7 * p + 31 + 33 * r + 5 * (r * p)) := hsum
      _ ≤ CI * (3 * T) := Nat.mul_le_mul_left CI hB
      _ = (3 * CI) * T := by rw [← Nat.mul_assoc, Nat.mul_comm CI 3]
      _ ≤ K * T := Nat.mul_le_mul_right T (by simp only [hKdef]; omega)
      _ ≤ K * (T + 1) := Nat.mul_le_mul_left K (Nat.le_succ T)

/-! ## The per-element word: `c ↦ ζ^c` by one `cis` call -/

theorem ztabElem (hK : KernelLib) (hI : IntLib) (hF : FxLib) :
    ∃ (prog : Cmd) (C : ℕ),
    ∀ (main : Cmd) (p r : ℕ), 100 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) →
    ∀ (c : ℕ), c < r → ∀ (rest : List Val),
      WordR main prog
        (fun vs => vs = Val.int (c : ℤ) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest)
        (fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest ∧
          inDisc p w ∧ vsz (cfxVal w) ≤ ConvR.cfxSz p ∧
          (2 : ℝ) ^ p * ‖fxC p w - zeta r c‖ < 2)
        (fun _ => C * (p + 1) ^ C) := by
  obtain ⟨pushProg, Kpush, hpush⟩ := hK.pushVal
  obtain ⟨pickProg, Kpick, hpick⟩ := hK.pick
  obtain ⟨rollProg, Kroll, hroll⟩ := hK.roll
  obtain ⟨swapProg, Kswap, hswap⟩ := hK.swap
  obtain ⟨shlProg, Kshl, hshl⟩ := hI.shl
  obtain ⟨cisProg, Kcis, hcis⟩ := hF.cis
  set CI : ℕ := 4 * (Kpush + Kpick + Kroll + Kswap + Kshl + Kcis * 4 ^ Kcis + 1) with hCIdef
  set Cst : ℕ := CI * CI + CI + 1 with hCdef
  refine ⟨(Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pushProg (.int 1)) (pickProg 3)) shlProg)
      (pickProg 2)) (rollProg 2)) swapProg).seq cisProg, Cst, ?_⟩
  intro main p r hp hr hlt c hc rest
  have hszc : isz ((c : ℤ)) ≤ p + 1 := by
    have hcr : c < 2 ^ (p - 1) := lt_of_lt_of_le hc (le_of_lt hlt)
    have h := Work.Transform.isz_natCast_le (n := c) (p := p - 1) hcr
    omega
  have hszp : isz ((p : ℤ)) ≤ p + 2 := isz_natCast_le (Nat.lt_two_pow_self (n := p))
  have hszr : isz ((r : ℤ)) ≤ p + 1 := by
    have h := Work.Transform.isz_natCast_le (n := r) (p := p - 1) hlt
    omega
  have hsz2r : isz (((2 * r : ℕ) : ℤ)) ≤ p + 2 := by
    have h2 : 2 * r < 2 ^ p := by
      have h3 : 2 ^ p = 2 * 2 ^ (p - 1) := by
        conv_lhs => rw [show p = (p - 1) + 1 by omega]
        rw [pow_succ]
        ring
      rw [h3]
      omega
    have h := Work.Transform.isz_natCast_le (n := 2 * r) (p := p) h2
    omega
  set s1 : ℕ := Kpush * 4 with hs1
  set s2 : ℕ := Kpick * 4 * (Work.Fx.szl [Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ),
    Val.int (r : ℤ)] + 1) with hs2
  set s3 : ℕ := Kshl * (isz ((r : ℤ)) + 4) with hs3
  set s4 : ℕ := Kpick * 3 * (Work.Fx.szl [Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ),
    Val.int (p : ℤ)] + 1) with hs4
  set s5 : ℕ := Kroll * 3 * (Work.Fx.szl [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)),
    Val.int (c : ℤ)] + 1) with hs5
  set s6 : ℕ := Kswap * (isz ((c : ℤ)) + isz ((p : ℤ)) + 1) with hs6
  set s7 : ℕ := Kcis * (p + isz ((c : ℤ)) + isz (((2 * r : ℕ) : ℤ))) ^ Kcis with hs7
  -- step 1: push `int 1`
  have hstep1 : Pipe main (pushProg (.int 1)) [Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]
      [Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)] s1 := by
    rw [hs1]
    have h := Pipe.pushOnAny (main := main) (v := Val.int 1)
      (T := [Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]) (hpush main (Val.int 1))
    rw [Work.Fx.vsz_int, isz_one] at h
    exact h
  -- step 2: copy `int r`
  have hstep2 : Pipe main (pickProg 3)
      [Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]
      [Val.int (r : ℤ), Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)] s2 := by
    rw [hs2]
    have h := pipe_pick (main := main) (prog := pickProg) hpick
      (A := [Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]) (k := 3) (by simp)
    have hwin : [Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)].getD 3 Val.nil
        :: [Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]
        = [Val.int (r : ℤ), Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)] := by simp
    rw [hwin] at h
    exact h
  -- step 3: `int r ↦ int (2r)`
  have hstep3 : Pipe main shlProg
      [Val.int (r : ℤ), Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]
      [Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)] s3 := by
    rw [hs3]
    have h := Pipe.binOp (main := main) (prog := shlProg) (hshl main)
      (a := (r : ℤ)) (b := (1 : ℤ)) (by norm_num : (0 : ℤ) ≤ 1)
    have h24 := Pipe.appendTail (main := main) (prog := shlProg)
      ([Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]) h
    have htn : ((1 : ℤ).toNat) = 1 := by decide
    have hcost : Kshl * (isz ((r : ℤ)) + ((1 : ℤ).toNat) + isz (1 : ℤ)) ≤ Kshl * (isz ((r : ℤ)) + 4) := by
      rw [htn, isz_one]
    have heq : Val.int ((r : ℤ) * 2 ^ ((1 : ℤ).toNat)) = Val.int (((2 * r : ℕ) : ℤ)) := by
      rw [htn]
      congr 1
      push_cast
      ring
    exact Pipe.rw (Pipe.le h24 hcost) (by rw [heq]; rfl)
  -- step 4: copy `int p`
  have hstep4 : Pipe main (pickProg 2)
      [Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]
      [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ), Val.int (p : ℤ),
        Val.int (r : ℤ)] s4 := by
    rw [hs4]
    have h := pipe_pick (main := main) (prog := pickProg) hpick
      (A := [Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ), Val.int (p : ℤ)]) (k := 2) (by simp)
    have hget : [Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ), Val.int (p : ℤ)].getD 2 Val.nil
        = Val.int (p : ℤ) := by simp
    rw [hget] at h
    exact Pipe.appendTail (main := main) [Val.int (r : ℤ)] h
  -- step 5: roll `int c` to the top
  have hstep5 : Pipe main (rollProg 2)
      [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ), Val.int (p : ℤ),
        Val.int (r : ℤ)]
      [Val.int (c : ℤ), Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (p : ℤ),
        Val.int (r : ℤ)] s5 := by
    rw [hs5]
    have h := pipe_roll (main := main) (prog := rollProg) hroll
      (A := [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ)]) (k := 2) (by simp)
    have hget : [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ)].getD 2 Val.nil
        = Val.int (c : ℤ) := by simp
    have herase : [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ)].eraseIdx 2
        = [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ))] := by simp
    rw [hget, herase] at h
    exact Pipe.appendTail (main := main) [Val.int (p : ℤ), Val.int (r : ℤ)] h
  -- step 6: swap `int p` in front of `int c`
  have hstep6 : Pipe main swapProg
      [Val.int (c : ℤ), Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (p : ℤ),
        Val.int (r : ℤ)]
      [Val.int (p : ℤ), Val.int (c : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (p : ℤ),
        Val.int (r : ℤ)] s6 := by
    rw [hs6]
    have h := Pipe.swap main hswap (Val.int (c : ℤ)) (Val.int (p : ℤ))
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int] at h
    exact Pipe.appendTail (main := main) (prog := swapProg)
      [Val.int (((2 * r : ℕ) : ℤ)), Val.int (p : ℤ), Val.int (r : ℤ)] h
  -- step 7: the `cis` call
  have hcis' : WordR main cisProg
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: Val.int (((2 * r : ℕ) : ℤ)) ::
        ([Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest))
      (fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: ([Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest) ∧
        inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - zeta r c‖ < 2)
      (fun _ => s7) := by
    rw [hs7]
    have hk : 1 ≤ 2 * r := by omega
    refine Work.Kernel.WordR_conseq (hcis main p (c : ℤ) (2 * r) hp hk) ?_ ?_ (fun _ _ => le_rfl)
    · intro vs hv
      exact ⟨[Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest, hv⟩
    · intro vs out hv hout
      obtain ⟨r', w, hvs', hout', hdisc, herr⟩ := hout
      have hr' : r' = [Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest := by
        have h2 : Val.int (p : ℤ) :: Val.int (c : ℤ) :: Val.int (((2 * r : ℕ) : ℤ)) :: r'
            = Val.int (p : ℤ) :: Val.int (c : ℤ) :: Val.int (((2 * r : ℕ) : ℤ))
              :: ([Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest) := by
          rw [← hvs']
          exact hv
        exact cons₃_eq h2
      refine ⟨w, ?_, hdisc, ?_⟩
      · have hpost : out = cfxVal w :: ([Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest) := by
          rw [hout', hr']
        exact hpost
      · rw [exp_cis_two_r r c (by omega)] at herr
        exact herr
  -- compose
  have hpipe := Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp hstep1 hstep2) hstep3)
    hstep4) hstep5) hstep6
  have hseq := Work.Kernel.WordR_seq (main := main)
    (P := fun vs => vs = [Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest)
    (Q := fun _ mid => mid = [Val.int (p : ℤ), Val.int (c : ℤ), Val.int (((2 * r : ℕ) : ℤ)),
      Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest)
    (C := fun _ => (((((s1 + s2) + s3) + s4) + s5) + s6))
    (P' := fun mid => mid = Val.int (p : ℤ) :: Val.int (c : ℤ) :: Val.int (((2 * r : ℕ) : ℤ)) ::
      ([Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest))
    (Q' := fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: ([Val.int (p : ℤ), Val.int (r : ℤ)] ++ rest) ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - zeta r c‖ < 2)
    (C' := fun _ => s7) (B := fun _ => s7)
    (hpipe rest) hcis' (fun _ _ _ h => ⟨h, le_rfl⟩)
  refine Work.Kernel.WordR_conseq hseq ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    rfl
  · intro vs out _ hout
    obtain ⟨_mid, _hmid, w, hout', hdisc, herr⟩ := hout
    have hpost : out = cfxVal w :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest := by
      rw [hout']
      rfl
    exact ⟨w, hpost, hdisc, ConvR.vsz_cfxVal_le hdisc, herr⟩
  · intro vs _
    -- the cost bound
    have hszl1 : Work.Fx.szl [Val.int 1, Val.int (c : ℤ), Val.int (p : ℤ), Val.int (r : ℤ)]
        = 3 + isz ((c : ℤ)) + isz ((p : ℤ)) + isz ((r : ℤ)) := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Work.Fx.vsz_int, isz_zero, isz_one, Nat.add_zero, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    have hszl2 : Work.Fx.szl [Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ), Val.int (p : ℤ)]
        = isz (((2 * r : ℕ) : ℤ)) + isz ((c : ℤ)) + isz ((p : ℤ)) := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Work.Fx.vsz_int, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hszl3 : Work.Fx.szl [Val.int (p : ℤ), Val.int (((2 * r : ℕ) : ℤ)), Val.int (c : ℤ)]
        = isz ((p : ℤ)) + isz (((2 * r : ℕ) : ℤ)) + isz ((c : ℤ)) := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Work.Fx.vsz_int, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have b1 : s1 ≤ CI * 4 := by
      rw [hs1]
      have h1 : Kpush ≤ CI := by simp only [hCIdef]; omega
      exact Nat.mul_le_mul_right 4 h1
    have b2 : s2 ≤ CI * (12 * p + 32) := by
      rw [hs2, hszl1]
      have h1 : Kpick * 4 ≤ CI := by simp only [hCIdef]; omega
      have h5 : 3 + isz ((c : ℤ)) + isz ((p : ℤ)) + isz ((r : ℤ)) + 1 ≤ 12 * p + 32 := by omega
      exact Nat.mul_le_mul h1 h5
    have b3 : s3 ≤ CI * (p + 5) := by
      rw [hs3]
      have h1 : Kshl ≤ CI := by simp only [hCIdef]; omega
      have h5 : isz ((r : ℤ)) + 4 ≤ p + 5 := by omega
      exact Nat.mul_le_mul h1 h5
    have b4 : s4 ≤ CI * (9 * p + 18) := by
      rw [hs4, hszl2]
      have h1 : Kpick * 3 ≤ CI := by simp only [hCIdef]; omega
      have h5 : isz (((2 * r : ℕ) : ℤ)) + isz ((c : ℤ)) + isz ((p : ℤ)) + 1
          ≤ 9 * p + 18 := by omega
      exact Nat.mul_le_mul h1 h5
    have b5 : s5 ≤ CI * (9 * p + 18) := by
      rw [hs5, hszl3]
      have h1 : Kroll * 3 ≤ CI := by simp only [hCIdef]; omega
      have h5 : isz ((p : ℤ)) + isz (((2 * r : ℕ) : ℤ)) + isz ((c : ℤ)) + 1
          ≤ 9 * p + 18 := by omega
      exact Nat.mul_le_mul h1 h5
    have b6 : s6 ≤ CI * (2 * p + 4) := by
      rw [hs6]
      have h1 : Kswap ≤ CI := by simp only [hCIdef]; omega
      have h5 : isz ((c : ℤ)) + isz ((p : ℤ)) + 1 ≤ 2 * p + 4 := by omega
      exact Nat.mul_le_mul h1 h5
    have b7 : s7 ≤ CI * (p + 1) ^ CI := by
      rw [hs7]
      have h1 : Kcis ≤ CI := by
        have h2 : 1 ≤ 4 ^ Kcis := pow_pos (by norm_num : (0 : ℕ) < 4) Kcis
        have h3 : Kcis ≤ Kcis * 4 ^ Kcis := by
          calc Kcis = Kcis * 1 := (Nat.mul_one Kcis).symm
            _ ≤ Kcis * 4 ^ Kcis := Nat.mul_le_mul_left Kcis h2
        simp only [hCIdef]
        omega
      have h2 : Kcis * 4 ^ Kcis ≤ CI := by simp only [hCIdef]; omega
      have h3 : p + isz ((c : ℤ)) + isz (((2 * r : ℕ) : ℤ)) ≤ 4 * (p + 1) := by omega
      have h4 : Kcis * (p + isz ((c : ℤ)) + isz (((2 * r : ℕ) : ℤ))) ^ Kcis
          ≤ Kcis * (4 * (p + 1)) ^ Kcis :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 Kcis)
      exact le_trans h4 (pow_budget h2 h1)
    have hsum6 : (((((s1 + s2) + s3) + s4) + s5) + s6) ≤ CI * (33 * p + 81) := by
      have hb : 4 + (12 * p + 32) + (p + 5) + (9 * p + 18) + (9 * p + 18) + (2 * p + 4)
          ≤ 33 * p + 81 := by linarith
      calc (((((s1 + s2) + s3) + s4) + s5) + s6)
          ≤ CI * 4 + CI * (12 * p + 32) + CI * (p + 5) + CI * (9 * p + 18)
            + CI * (9 * p + 18) + CI * (2 * p + 4) := by
            linarith only [b1, b2, b3, b4, b5, b6]
        _ = CI * (4 + (12 * p + 32) + (p + 5) + (9 * p + 18) + (9 * p + 18) + (2 * p + 4)) := by
            ring
        _ ≤ CI * (33 * p + 81) := Nat.mul_le_mul_left CI hb
    have hCst : (p + 1) ^ 2 ≤ (p + 1) ^ Cst := Nat.pow_le_pow_right (by omega) (by omega)
    have hCI3 : 3 ≤ CI := by simp only [hCIdef]; omega
    have hA6 : CI * (33 * p + 81) ≤ CI * CI * (p + 1) ^ Cst := by
      have h1 : 33 * p + 81 ≤ CI * (p + 1) ^ 2 := by nlinarith only [hCI3, hp]
      calc CI * (33 * p + 81) ≤ CI * (CI * (p + 1) ^ 2) := Nat.mul_le_mul_left CI h1
        _ = CI * CI * (p + 1) ^ 2 := by rw [← Nat.mul_assoc]
        _ ≤ CI * CI * (p + 1) ^ Cst := Nat.mul_le_mul_left _ hCst
    have hA7 : CI * (p + 1) ^ CI ≤ CI * (p + 1) ^ Cst :=
      Nat.mul_le_mul_left CI (Nat.pow_le_pow_right (by omega) (by simp only [hCdef]; omega))
    calc (((((s1 + s2) + s3) + s4) + s5) + s6) + s7
        ≤ CI * (33 * p + 81) + CI * (p + 1) ^ CI := by linarith only [hsum6, b7]
      _ ≤ CI * CI * (p + 1) ^ Cst + CI * (p + 1) ^ Cst := by linarith only [hA6, hA7]
      _ = (CI * CI + CI) * (p + 1) ^ Cst := by rw [Nat.add_mul]
      _ ≤ Cst * (p + 1) ^ Cst := Nat.mul_le_mul_right _ (by simp only [hCdef]; omega)


/-- **The length-`r` table `c ↦ ζ^c` for `ζ = e^{πi/r}` (paper Prop 3.5), via `r` calls of
`FxLib.cis`.**

From `int p :: int r` (with `rest` untouched below), produce the length-`r` vector `bs` with
`bs[c] ≈ ζ^c` (error `< 2` after scaling by `2^p`, each entry in the disc) at cost
`K*(r*(p+1)^K + 1)`.

Intended implementation (all from the library Props, no new programs beyond straight-line glue):
* build the index list `(List.range r).map Val.int` cheaply: `LayoutLib.replicate r (.int 0)`
  (`r` copies of `int 0`), then `LayoutLib.enumerate` (label entry `i` with `int i`, as
  `cons (.int i) (.int 0)`), then `KernelLib.mapList` with the word "`unconsV`, `swap`, `drop`"
  (keep the index, drop the payload);
* then `KernelLib.mapList` with the word that turns `int c :: .int p :: .int r :: rest'` into
  `cfxVal w :: .int p :: .int r :: rest'`: `pick 2`, `pick 2`, `roll 2`, `swap`, then
  `FxLib.cis p (c : ℤ) (2 * r)` (the `pick`s copy the `.int r` and `.int p` that sit in `rest'`,
  and the arrangement `int p :: int c :: int (2*r) :: ...` is what `cis` expects);
  the phase identity is `Complex.exp (2*π*i*c/(2*r)) = zeta r c` (`zeta_double`-style arithmetic;
  `Submission/Work/Transform/chirpTabKit.lean` has the `m*m` variant `exp_cis_eq_zeta`).

Cost: `r ≥ 2`, `r < 2^(p-1)` give `isz c ≤ p+1` (`c < r`) and `isz (2*r) ≤ p+2`, so each `cis`
costs `K_cis*(p + isz c + isz (2*r))^K_cis ≤ K_cis*(4*(p+1))^K_cis`; `mapList`'s uniform bound is
`L = cfxSz p = 2*p+8` (`vsz (cfxVal w) ≤ cfxSz p` for `inDisc p w`, see
`Work.ConvR.vsz_cfxVal_le`); `replicate` is `O(r)`, `enumerate` is `O(r*(r.size+1)) = O(r*p)`,
the peel map is `O(r*p)`, and `2*K_cis + r.size` are absorbed into `K`. -/
theorem ztabCis : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r : ℕ) (rest : List HvdH.Val),
      100 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.Val.int r :: rest)
        (fun _ out => ∃ (bs : List (ℤ × ℤ)),
          out = HvdH.cvecVal bs :: HvdH.Val.int p :: HvdH.Val.int r :: rest ∧
          bs.length = r ∧ HvdH.InDiscVec p r bs ∧
          (∀ c < r, (2 : ℝ) ^ p * ‖HvdH.fxC p (bs.getD c (0, 0)) -
            Work.Transform.zeta r c‖ < 2))
        (fun _ => K * (r * (p + 1) ^ K + 1)) := by
  intro hK hI hL hF
  obtain ⟨idxProg, K1, hidx⟩ := ztabIdx hK hL
  obtain ⟨elemProg, Ce, helem⟩ := ztabElem hK hI hF
  obtain ⟨mapP, Kml, hmapML⟩ := hK.mapList
  set Cmap : ℕ := 2 * Kml + 3 * Ce + 8 with hCmap
  refine ⟨Cmd.seq idxProg (mapP elemProg), K1 + Cmap, ?_⟩
  intro main p r rest hp hr hlt
  set xs : List Val := (List.range r).map (fun i : ℕ => Val.int (i : ℤ)) with hxs
  set Qbig : Val → Val → Prop := (fun x y => ∃ i, i < r ∧ x = Val.int (i : ℤ) ∧
      ∃ w : ℤ × ℤ, y = cfxVal w ∧ inDisc p w ∧ vsz (cfxVal w) ≤ ConvR.cfxSz p ∧
        (2 : ℝ) ^ p * ‖fxC p w - zeta r i‖ < 2) with hQdef
  have hxslen : xs.length = r := by rw [hxs]; simp
  -- the inner (per-element) word
  have hinner : ∀ x, (∃ i, i < r ∧ x = Val.int (i : ℤ)) → WordR main elemProg
      (fun vs => vs = x :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
      (fun _ out => ∃ y, out = y :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest) ∧
        Qbig x y ∧ vsz y ≤ ConvR.cfxSz p)
      (fun _ => Ce * (p + 1) ^ Ce) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine Work.Kernel.WordR_conseq (helem main p r hp hr hlt i hi rest) ?_ ?_ (fun _ _ => le_rfl)
    · intro vs hv; exact hv
    · intro vs out _ hout
      obtain ⟨w, hout', hdisc, hvsz, herr⟩ := hout
      exact ⟨cfxVal w, hout', ⟨i, hi, rfl, w, rfl, hdisc, hvsz, herr⟩, hvsz⟩
  -- the list condition for `mapList`
  have hxscond : ∀ x ∈ xs, (∃ i, i < r ∧ x = Val.int (i : ℤ)) ∧ vsz x ≤ ConvR.cfxSz p := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < r := by simpa using hi
    have hxi : x = Val.int (i : ℤ) := by rw [← hix, List.getElem_map, List.getElem_range]
    refine ⟨⟨i, hi', hxi⟩, ?_⟩
    rw [hxi, Work.Fx.vsz_int]
    have hsz : isz ((i : ℤ)) ≤ p + 1 := by
      have hir : i < 2 ^ (p - 1) := lt_of_lt_of_le hi' (le_of_lt hlt)
      have h := Work.Transform.isz_natCast_le (n := i) (p := p - 1) hir
      omega
    simp only [Work.ConvR.cfxSz]
    omega
  have hmap := hmapML main elemProg (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest)
      (fun x => ∃ i, i < r ∧ x = Val.int (i : ℤ)) Qbig (Ce * (p + 1) ^ Ce) (ConvR.cfxSz p)
      hinner xs hxscond
  have hmap' : WordR main (mapP elemProg)
      (fun vs => vs = ofList xs :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
      (fun _ out => ∃ ys, out = ofList ys :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest) ∧
        List.Forall₂ Qbig xs ys)
      (fun _ => r * (Ce * (p + 1) ^ Ce + Kml * (ConvR.cfxSz p + 1)) + Kml) := by
    rw [hxslen] at hmap
    exact hmap
  -- compose with the index-list word
  have hseq := Work.Kernel.WordR_seq (main := main)
    (P := fun vs => vs = Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest)
    (Q := fun _ mid => mid = ofList xs :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
    (C := fun _ => K1 * (r * (p + 1) ^ K1 + 1))
    (P' := fun mid => mid = ofList xs :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest))
    (Q' := fun _ out => ∃ ys, out = ofList ys :: (Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest) ∧
      List.Forall₂ Qbig xs ys)
    (C' := fun _ => r * (Ce * (p + 1) ^ Ce + Kml * (ConvR.cfxSz p + 1)) + Kml)
    (B := fun _ => r * (Ce * (p + 1) ^ Ce + Kml * (ConvR.cfxSz p + 1)) + Kml)
    (hidx main p r rest hp hr hlt) hmap' (fun _ _ _ h => ⟨h, le_rfl⟩)
  refine Work.Kernel.WordR_conseq hseq ?_ ?_ ?_
  · intro vs hv; exact hv
  · intro vs out _ hout
    obtain ⟨mid, hmid, ys, hys, hfor⟩ := hout
    have hylen : ys.length = r := by
      have h1 := hfor.length_eq
      rw [hxslen] at h1
      exact h1.symm
    have hget : ∀ i < r, ∃ w : ℤ × ℤ, ys.getD i .nil = cfxVal w ∧ inDisc p w ∧
        (2 : ℝ) ^ p * ‖fxC p w - zeta r i‖ < 2 := by
      intro i hi
      have hi1 : i < xs.length := by rw [hxslen]; exact hi
      have hi2 : i < ys.length := by rw [hylen]; exact hi
      have hQ := forall₂_getD hfor .nil .nil hi1 hi2
      simp only [hQdef] at hQ
      obtain ⟨j, _hj, hxj, w, hw, hdisc, _hvsz, herr⟩ := hQ
      have hxsget : xs.getD i .nil = Val.int (i : ℤ) := by
        rw [hxs]
        exact getD_map_range (fun i : ℕ => Val.int (i : ℤ)) .nil hi
      have hij : i = j := by
        have h1 : (i : ℤ) = (j : ℤ) := by
          rw [hxsget] at hxj
          exact Val.int.inj hxj
        exact_mod_cast h1
      rw [← hij] at herr
      exact ⟨w, hw, hdisc, herr⟩
    obtain ⟨bs, hbs, hblen, hbdisc⟩ :=
      extractCvec (N := r) (Q := fun i w => inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - zeta r i‖ < 2)
        hylen hget
    refine ⟨bs, ?_, hblen, ?_, ?_⟩
    · rw [hys, hbs]
    · refine ⟨hblen, ?_⟩
      intro z hz
      obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
      have hi' : i < r := by rw [← hblen]; exact hi
      have h1 := (hbdisc i hi').1
      rw [List.getD_eq_getElem _ _ hi] at h1
      rwa [hzi] at h1
    · intro cc hcc
      exact (hbdisc cc hcc).2
  · intro vs _
    have hcf : ConvR.cfxSz p + 1 = 2 * p + 9 := by simp only [Work.ConvR.cfxSz]
    rw [hcf]
    set T : ℕ := r * (p + 1) ^ (K1 + Cmap) with hTdef
    have hpow : (p + 1) ^ K1 ≤ (p + 1) ^ (K1 + Cmap) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hA : K1 * (r * (p + 1) ^ K1 + 1) ≤ K1 * (T + 1) := by
      rw [hTdef]
      exact Nat.mul_le_mul_left K1 (Nat.add_le_add_right (Nat.mul_le_mul_left r hpow) 1)
    have hCe : Ce * (p + 1) ^ Ce ≤ (p + 1) ^ (K1 + Cmap) := by
      have h1 : Ce ≤ (p + 1) ^ (2 * Ce) := const_le_pow (by omega)
      have h2 : 2 * Ce ≤ (K1 + Cmap) - Ce := by simp only [hCmap]; omega
      calc Ce * (p + 1) ^ Ce ≤ (p + 1) ^ (2 * Ce) * (p + 1) ^ Ce := Nat.mul_le_mul_right _ h1
        _ = (p + 1) ^ (2 * Ce + Ce) := by rw [← pow_add]
        _ ≤ (p + 1) ^ ((K1 + Cmap) - Ce + Ce) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = (p + 1) ^ (K1 + Cmap) := by rw [Nat.sub_add_cancel (by simp only [hCmap]; omega)]
    have hKml : Kml * (2 * p + 9) ≤ (p + 1) ^ (K1 + Cmap) := by
      have h1 : Kml ≤ (p + 1) ^ (2 * Kml) := const_le_pow (by omega)
      have h2 : 2 * p + 9 ≤ (p + 1) ^ 4 := by
        have h3 : (p + 1) ^ 2 ≤ (p + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
        have h4 : 2 * p + 9 ≤ (p + 1) ^ 2 := by
          rw [show (p + 1) ^ 2 = (p + 1) * (p + 1) by ring]
          nlinarith only [hp]
        exact le_trans h4 h3
      have h5 : 2 * Kml + 4 ≤ K1 + Cmap := by simp only [hCmap]; omega
      calc Kml * (2 * p + 9) ≤ (p + 1) ^ (2 * Kml) * (p + 1) ^ 4 := Nat.mul_le_mul h1 h2
        _ = (p + 1) ^ (2 * Kml + 4) := by rw [← pow_add]
        _ ≤ (p + 1) ^ (K1 + Cmap) := Nat.pow_le_pow_right (by omega) h5
    have hB : r * (Ce * (p + 1) ^ Ce + Kml * (2 * p + 9)) + Kml ≤ Cmap * (T + 1) := by
      have h1 : Ce * (p + 1) ^ Ce + Kml * (2 * p + 9) ≤ 2 * (p + 1) ^ (K1 + Cmap) := by
        linarith only [hCe, hKml]
      have h2 : r * (Ce * (p + 1) ^ Ce + Kml * (2 * p + 9))
          ≤ r * (2 * (p + 1) ^ (K1 + Cmap)) := Nat.mul_le_mul_left r h1
      have h3 : r * (2 * (p + 1) ^ (K1 + Cmap)) = 2 * T := by rw [hTdef, Nat.mul_left_comm]
      have h4 : Kml ≤ Cmap := by simp only [hCmap]; omega
      have h5 : 2 * T + Kml ≤ Cmap * (T + 1) := by
        have h6 : 2 * T ≤ Cmap * T := Nat.mul_le_mul_right T (by simp only [hCmap]; omega)
        have h7 : Kml ≤ Cmap * 1 := by simpa only [Nat.mul_one] using h4
        nlinarith only [h6, h7]
      linarith only [h2, h3, h5]
    calc K1 * (r * (p + 1) ^ K1 + 1)
          + (r * (Ce * (p + 1) ^ Ce + Kml * (2 * p + 9)) + Kml)
        ≤ K1 * (T + 1) + Cmap * (T + 1) := by linarith only [hA, hB]
      _ = (K1 + Cmap) * (T + 1) := (Nat.add_mul K1 Cmap (T + 1)).symm

end Work.Transform
