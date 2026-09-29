import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.auPreKit

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## Elementary helpers -/

theorem mulK_le_mulK {a b K : ℕ} (h : a ≤ b) : K * a ≤ K * b := Nat.mul_le_mul (le_refl K) h

theorem mul_le_mulK {a b K : ℕ} (h : a ≤ b) : a * K ≤ b * K := Nat.mul_le_mul h (le_refl K)

theorem pow_mono_base {a b n : ℕ} (h : a ≤ b) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ]; exact Nat.mul_le_mul ih h

theorem isz_natCast_le_auSZ {p n : ℕ} (h : n < 2 ^ p) : isz ((n : ℤ)) ≤ auSZ p := by
  rw [isz, Int.natAbs_natCast]
  simp only [auSZ]
  have h1 : n.size ≤ p := Nat.size_le.mpr h
  omega

theorem isz_self_le_auSZ (p : ℕ) : isz ((p : ℤ)) ≤ auSZ p := by
  rw [isz, Int.natAbs_natCast]
  simp only [auSZ]
  have h1 : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  omega

theorem hundred_auSZ_le_pow (p : ℕ) (hp : 100 ≤ p) : 100 * auSZ p + 100 ≤ (p + 1) ^ 4 := by
  have h1 : (100 : ℕ) ^ 3 ≤ p ^ 3 := pow_mono_base (by omega : (100 : ℕ) ≤ p)
  norm_num at h1
  have h2 : (1000000 : ℕ) * p ≤ p ^ 4 := by
    calc (1000000 : ℕ) * p ≤ p ^ 3 * p := Nat.mul_le_mul h1 (le_refl p)
      _ = p ^ 4 := by ring
  have h3 : (1000 : ℕ) * p + 40100 ≤ 1000000 * p := by omega
  have h4 : p ^ 4 ≤ (p + 1) ^ 4 := pow_mono_base (by omega : p ≤ p + 1)
  simp only [auSZ]
  omega

/-! ## The index and answer lists -/

/-- `s` copies of `nil`. -/
def buNilL (s : ℕ) : List Val := List.replicate s Val.nil

/-- The list of index labels `cons (int i) nil`, `i < s`. -/
def buIdxL (s : ℕ) : List Val := (List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) Val.nil)

/-- The list of destination keys `(t i) % s`, `i < s`. -/
def buAnsL (s t : ℕ) : List Val := List.ofFn (fun i : Fin s => Val.int ((egKeyS s t (i : ℕ) : ℤ)))

theorem buL8_eq_ofList (p s t : ℕ) : buL8 p 2 s t = ofList (buAnsL s t) := by
  simp only [buL8, zl, buAnsL, List.map_ofFn, Function.comp_def]

theorem length_buIdxL (s : ℕ) : (buIdxL s).length = s := by simp [buIdxL]

theorem buNilL_getD (s i : ℕ) : (buNilL s).getD i Val.nil = Val.nil := by
  rw [buNilL]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]

theorem enumerate_buNilL (s : ℕ) :
    (List.range (buNilL s).length).map
        (fun i : ℕ => Val.cons (Val.int (i : ℤ)) ((buNilL s).getD i Val.nil)) = buIdxL s := by
  have hlen : (buNilL s).length = s := by simp [buNilL]
  rw [hlen, buIdxL]
  congr 1
  funext i
  simp only [buNilL_getD]

theorem vsz_ofList_buNilL (s : ℕ) : vsz (ofList (buNilL s)) ≤ (s + 1) * 2 := by
  have hmem : ∀ x ∈ buNilL s, vsz x ≤ 1 := by
    intro x hx
    rw [buNilL] at hx
    rw [List.eq_of_mem_replicate hx]
    simp [vsz, Val.enc]
  have h := vsz_ofList_le (l := buNilL s) (B := 1) hmem
  rw [buNilL, List.length_replicate] at h
  exact h

theorem vsz_ofList_buAnsL {s t p : ℕ} (hsp : s < 2 ^ p) :
    vsz (ofList (buAnsL s t)) ≤ (s + 1) * (auSZ p + 1) := by
  have hmem : ∀ x ∈ buAnsL s t, vsz x ≤ auSZ p := by
    rw [buAnsL, List.forall_mem_ofFn_iff]
    intro j
    rw [vsz_int_eq]
    have hj : (j : ℕ) < s := j.isLt
    have hmod : egKeyS s t (j : ℕ) < s := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)
    exact isz_natCast_le_auSZ (p := p) (lt_trans hmod hsp)
  have h := vsz_ofList_le (l := buAnsL s t) (B := auSZ p) hmem
  rw [buAnsL, List.length_ofFn] at h
  exact h

/-! ## The cost arithmetic -/

theorem buKeysArith (Kkn Ksw Kr Kpk Kp Kml Krep Kenu p s : ℕ) (hp : 100 ≤ p) :
    Ksw * (2 * auSZ p + 1) + Kr * 3 * (3 * auSZ p + 1) + Ksw * (2 * auSZ p + 1)
      + Kpk * (auSZ p + 1) + Kp * 2 + Ksw * (auSZ p + 2)
      + Krep * (2 * (s + 1) + auSZ p + 1) + Kenu * (2 * (s + 1) + s * (p + 1) + 1)
      + (s * (Kkn * (p + 1) ^ Kkn + Kml * (auSZ p + 3)) + Kml)
      + Kr * 4 * ((s + 1) * (auSZ p + 1) + 3 * auSZ p + 1)
      + Ksw * (auSZ p + (s + 1) * (auSZ p + 1) + 1)
    ≤ (16 * (Ksw + Kr + Kpk + Kp + Kml + Krep + Kenu + Kkn + 10) + 2 * Kkn + 10) * (s + 1)
      * (p + 1) ^ (16 * (Ksw + Kr + Kpk + Kp + Kml + Krep + Kenu + Kkn + 10) + 2 * Kkn + 10) := by
  set S := auSZ p with hS
  set W := (p + 1) ^ 4 with hW
  set V := (s + 1) * (100 * S + 100) with hV
  set KB := Ksw + Kr + Kpk + Kp + Kml + Krep + Kenu + Kkn + 10 with hKB
  set Kf := 16 * KB + 2 * Kkn + 10 with hKf
  have hSW : 100 * S + 100 ≤ W := by rw [hS, hW]; exact hundred_auSZ_le_pow p hp
  have hSge : p ≤ S := by rw [hS]; simp only [auSZ]; omega
  have hs1 : 1 ≤ s + 1 := by omega
  have hone : ∀ n : ℕ, n ≤ (s + 1) * n := by
    intro n
    calc n = 1 * n := (Nat.one_mul n).symm
      _ ≤ (s + 1) * n := mul_le_mulK hs1
  have hP1 : 2 * S + 1 ≤ V := by
    rw [hV]
    calc 2 * S + 1 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP2 : 3 * (3 * S + 1) ≤ V := by
    rw [hV]
    calc 3 * (3 * S + 1) ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP4 : S + 1 ≤ V := by
    rw [hV]
    calc S + 1 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP5 : 2 ≤ V := by
    rw [hV]
    calc 2 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP6 : S + 2 ≤ V := by
    rw [hV]
    calc S + 2 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP7 : 2 * (s + 1) + S + 1 ≤ V := by
    rw [hV]
    calc 2 * (s + 1) + (S + 1) ≤ 2 * (s + 1) + (s + 1) * (S + 1) :=
          Nat.add_le_add_left (hone (S + 1)) _
      _ = (s + 1) * (2 + (S + 1)) := by ring
      _ ≤ (s + 1) * (100 * S + 100) := mulK_le_mulK (by omega)
  have hP8 : 2 * (s + 1) + s * (p + 1) + 1 ≤ V := by
    rw [hV]
    calc 2 * (s + 1) + s * (p + 1) + 1
        ≤ (s + 1) * 2 + (s + 1) * (p + 1) + (s + 1) * 1 := by
          refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
          · exact le_of_eq (Nat.mul_comm 2 (s + 1))
          · exact mul_le_mulK (by omega : s ≤ s + 1)
          · exact hone 1
      _ = (s + 1) * (2 + (p + 1) + 1) := by ring
      _ ≤ (s + 1) * (100 * S + 100) := mulK_le_mulK (by omega)
  have hP9 : (s + 1) * (S + 3) ≤ V := by
    rw [hV]
    exact mulK_le_mulK (by omega)
  have hP10 : 4 * ((s + 1) * (S + 1) + 3 * S + 1) ≤ V := by
    rw [hV]
    calc 4 * ((s + 1) * (S + 1) + 3 * S + 1)
        ≤ 4 * ((s + 1) * (S + 1) + (s + 1) * (3 * S + 1)) :=
          Nat.mul_le_mul (le_refl 4) (Nat.add_le_add_left (hone (3 * S + 1)) _)
      _ = 4 * ((s + 1) * ((S + 1) + (3 * S + 1))) := by ring
      _ = (s + 1) * (16 * S + 8) := by ring
      _ ≤ (s + 1) * (100 * S + 100) := mulK_le_mulK (by omega)
  have hP11 : S + (s + 1) * (S + 1) + 1 ≤ V := by
    rw [hV]
    calc S + (s + 1) * (S + 1) + 1
        ≤ (s + 1) * S + (s + 1) * (S + 1) + (s + 1) * 1 :=
          Nat.add_le_add (Nat.add_le_add (hone S) (le_refl _)) (hone 1)
      _ = (s + 1) * (2 * S + 2) := by ring
      _ ≤ (s + 1) * (100 * S + 100) := mulK_le_mulK (by omega)
  have hKB1 : Ksw ≤ KB := by rw [hKB]; omega
  have hKB2 : Kr ≤ KB := by rw [hKB]; omega
  have hKB3 : Kpk ≤ KB := by rw [hKB]; omega
  have hKB4 : Kp ≤ KB := by rw [hKB]; omega
  have hKB5 : Kml ≤ KB := by rw [hKB]; omega
  have hKB6 : Krep ≤ KB := by rw [hKB]; omega
  have hKB7 : Kenu ≤ KB := by rw [hKB]; omega
  have t1 : Ksw * (2 * S + 1) ≤ KB * V := Nat.mul_le_mul hKB1 hP1
  have t2 : Kr * 3 * (3 * S + 1) ≤ KB * V := by
    rw [show Kr * 3 * (3 * S + 1) = Kr * (3 * (3 * S + 1)) by ring]
    exact Nat.mul_le_mul hKB2 hP2
  have t3 : Ksw * (2 * S + 1) ≤ KB * V := t1
  have t4 : Kpk * (S + 1) ≤ KB * V := Nat.mul_le_mul hKB3 hP4
  have t5 : Kp * 2 ≤ KB * V := Nat.mul_le_mul hKB4 hP5
  have t6 : Ksw * (S + 2) ≤ KB * V := Nat.mul_le_mul hKB1 hP6
  have t7 : Krep * (2 * (s + 1) + S + 1) ≤ KB * V := Nat.mul_le_mul hKB6 hP7
  have t8 : Kenu * (2 * (s + 1) + s * (p + 1) + 1) ≤ KB * V := Nat.mul_le_mul hKB7 hP8
  have t9 : s * (Kkn * (p + 1) ^ Kkn + Kml * (S + 3)) + Kml
      ≤ (s + 1) * Kkn * (p + 1) ^ Kkn + KB * V := by
    have hsplit : s * (Kkn * (p + 1) ^ Kkn + Kml * (S + 3)) + Kml
        = s * Kkn * (p + 1) ^ Kkn + (s * Kml * (S + 3) + Kml) := by ring
    rw [hsplit]
    refine Nat.add_le_add ?_ ?_
    · rw [show s * Kkn * (p + 1) ^ Kkn = s * (Kkn * (p + 1) ^ Kkn) by ring]
      rw [show (s + 1) * Kkn * (p + 1) ^ Kkn = (s + 1) * (Kkn * (p + 1) ^ Kkn) by ring]
      exact mul_le_mulK (by omega)
    · calc s * Kml * (S + 3) + Kml = Kml * (s * (S + 3) + 1) := by ring
        _ ≤ Kml * ((s + 1) * (S + 3)) := mulK_le_mulK (by
              rw [show (s + 1) * (S + 3) = s * (S + 3) + (S + 3) by ring]; omega)
        _ ≤ KB * ((s + 1) * (S + 3)) := mul_le_mulK hKB5
        _ ≤ KB * V := mulK_le_mulK hP9
  have t10 : Kr * 4 * ((s + 1) * (S + 1) + 3 * S + 1) ≤ KB * V := by
    rw [show Kr * 4 * ((s + 1) * (S + 1) + 3 * S + 1)
        = Kr * (4 * ((s + 1) * (S + 1) + 3 * S + 1)) by ring]
    exact Nat.mul_le_mul hKB2 hP10
  have t11 : Ksw * (S + (s + 1) * (S + 1) + 1) ≤ KB * V := Nat.mul_le_mul hKB1 hP11
  have hsum : Ksw * (2 * S + 1) + Kr * 3 * (3 * S + 1) + Ksw * (2 * S + 1)
      + Kpk * (S + 1) + Kp * 2 + Ksw * (S + 2)
      + Krep * (2 * (s + 1) + S + 1) + Kenu * (2 * (s + 1) + s * (p + 1) + 1)
      + (s * (Kkn * (p + 1) ^ Kkn + Kml * (S + 3)) + Kml)
      + Kr * 4 * ((s + 1) * (S + 1) + 3 * S + 1)
      + Ksw * (S + (s + 1) * (S + 1) + 1)
      ≤ 11 * (KB * V) + (s + 1) * Kkn * (p + 1) ^ Kkn := by
    first
      | omega
      | linarith [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]
  have hVW : V ≤ (s + 1) * W := by
    rw [hV]
    exact mulK_le_mulK hSW
  have hKf_ge1 : 11 * KB + 4 ≤ Kf := by rw [hKf, hKB]; omega
  have hKf_ge2 : Kkn + Kkn ≤ Kf := by rw [hKf, hKB]; omega
  have hKf2 : 2 ≤ Kf := by rw [hKf, hKB]; omega
  have hpow1 : 11 * KB * W ≤ (p + 1) ^ Kf := by
    have h1 : 11 * KB ≤ (p + 1) ^ (11 * KB) := by
      have h2 : 11 * KB ≤ 2 ^ (11 * KB) := le_of_lt (Nat.lt_two_pow_self (n := 11 * KB))
      calc 11 * KB ≤ 2 ^ (11 * KB) := h2
        _ ≤ (p + 1) ^ (11 * KB) := pow_mono_base (by omega : 2 ≤ p + 1)
    calc 11 * KB * W = 11 * KB * (p + 1) ^ 4 := by rw [hW]
      _ ≤ (p + 1) ^ (11 * KB) * (p + 1) ^ 4 := Nat.mul_le_mul h1 (le_refl _)
      _ = (p + 1) ^ (11 * KB + 4) := by rw [pow_add]
      _ ≤ (p + 1) ^ Kf := Nat.pow_le_pow_right (by omega : 0 < p + 1) hKf_ge1
  have hpow2 : Kkn * (p + 1) ^ Kkn ≤ (p + 1) ^ Kf := by
    have h1 : Kkn ≤ (p + 1) ^ Kkn := by
      calc Kkn ≤ 2 ^ Kkn := le_of_lt (Nat.lt_two_pow_self (n := Kkn))
        _ ≤ (p + 1) ^ Kkn := pow_mono_base (by omega : 2 ≤ p + 1)
    calc Kkn * (p + 1) ^ Kkn ≤ (p + 1) ^ Kkn * (p + 1) ^ Kkn := Nat.mul_le_mul h1 (le_refl _)
      _ = (p + 1) ^ (Kkn + Kkn) := by rw [pow_add]
      _ ≤ (p + 1) ^ Kf := Nat.pow_le_pow_right (by omega : 0 < p + 1) hKf_ge2
  calc Ksw * (2 * S + 1) + Kr * 3 * (3 * S + 1) + Ksw * (2 * S + 1)
      + Kpk * (S + 1) + Kp * 2 + Ksw * (S + 2)
      + Krep * (2 * (s + 1) + S + 1) + Kenu * (2 * (s + 1) + s * (p + 1) + 1)
      + (s * (Kkn * (p + 1) ^ Kkn + Kml * (S + 3)) + Kml)
      + Kr * 4 * ((s + 1) * (S + 1) + 3 * S + 1)
      + Ksw * (S + (s + 1) * (S + 1) + 1)
      ≤ 11 * (KB * V) + (s + 1) * Kkn * (p + 1) ^ Kkn := hsum
    _ ≤ 11 * (KB * ((s + 1) * W)) + (s + 1) * (Kkn * (p + 1) ^ Kkn) :=
        Nat.add_le_add (mulK_le_mulK (mulK_le_mulK hVW)) (le_of_eq (by ring))
    _ = (s + 1) * (11 * KB * W) + (s + 1) * (Kkn * (p + 1) ^ Kkn) := by ring
    _ ≤ (s + 1) * (p + 1) ^ Kf + (s + 1) * (p + 1) ^ Kf :=
        Nat.add_le_add (mulK_le_mulK hpow1) (mulK_le_mulK hpow2)
    _ = 2 * ((s + 1) * (p + 1) ^ Kf) := by ring
    _ ≤ Kf * ((s + 1) * (p + 1) ^ Kf) := mul_le_mulK hKf2
    _ = Kf * (s + 1) * (p + 1) ^ Kf := by ring

/-! ## The list-level extraction -/

theorem buKeysYs (s t : ℕ) {ys : List Val}
    (h : List.Forall₂ (fun x y => ∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil ∧
        y = Val.int (((t * i) % s : ℕ) : ℤ))
      ((List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) Val.nil)) ys) :
    ys = buAnsL s t := by
  have hba : buAnsL s t = List.ofFn (fun i : Fin s => Val.int ((egKeyS s t (i : ℕ) : ℤ))) := rfl
  rw [hba]
  have hlen : ys.length = s := by
    have h1 := List.Forall₂.length_eq h
    simp only [List.length_map, List.length_range] at h1
    omega
  refine List.ext_get ?_ ?_
  · rw [hlen, List.length_ofFn]
  · intro n h1 h2
    show ys[n]'h1 = (List.ofFn (fun i : Fin s => Val.int ((egKeyS s t (i : ℕ) : ℤ))))[n]'h2
    rw [List.getElem_ofFn]
    have hx : n < ((List.range s).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) Val.nil)).length := by
      simp only [List.length_map, List.length_range]
      omega
    have hR := (List.forall₂_iff_get.mp h).2 n hx h1
    obtain ⟨i, hi, hxe, hye⟩ := hR
    rw [List.get_eq_getElem] at hxe hye
    rw [List.getElem_map, List.getElem_range] at hxe
    have hn : n = i := by
      have h1' : Val.int ((n : ℤ)) = Val.int ((i : ℤ)) := (Val.cons.inj hxe).1
      have h2' : ((n : ℤ)) = ((i : ℤ)) := Val.int.inj h1'
      exact_mod_cast h2'
    subst hn
    rw [hye]
    simp only [egKeyS]

/-! ## The word -/

theorem buKeysWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (keyProg : HvdH.Cmd) (Kk : ℕ)
    (keySpec : ∀ (main : HvdH.Cmd) (p s t : ℕ) (hp : 1 ≤ p) (hsp : s < 2 ^ p)
      (htp : t < 2 ^ p) (i : ℕ) (hi : i < s),
      ∀ rest : List HvdH.Val, HvdH.WordR main keyProg
        (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil,
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil,
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest ∧
          out = [HvdH.Val.int (((t * i) % s : ℕ) : ℤ), HvdH.Val.int (s : ℤ),
            HvdH.Val.int (t : ℤ)] ++ rest)
        (fun _ => Kk * (p + 1) ^ Kk)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (s t : ℕ) (hsp : s < 2 ^ p)
      (htp : t < 2 ^ p) (hp : 100 ≤ p),
      Work.Resample.Pipe main prog
        ([HvdH.Val.int (p : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++
          [HvdH.Val.int (Work.Resample.auPi p)])
        (Work.Resample.buL8 p 2 s t ::
          [HvdH.Val.int (p : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++
          [HvdH.Val.int (Work.Resample.auPi p)])
        (K * (s + 1) * (p + 1) ^ K) := by
  obtain ⟨swP, Ksw, hSw⟩ := KL.swap
  obtain ⟨rlP, Kr, hRl⟩ := KL.roll
  obtain ⟨pkP, Kpk, hPk⟩ := KL.pick
  obtain ⟨psP, Kp, hPs⟩ := KL.pushVal
  obtain ⟨mlP, Kml, hMl⟩ := KL.mapList
  obtain ⟨repP, Krep, hRep⟩ := LL.replicate
  obtain ⟨enuP, Kenu, hEnu⟩ := LL.enumerate
  refine ⟨Cmd.seq swP (Cmd.seq (rlP 2) (Cmd.seq swP (Cmd.seq (pkP 0) (Cmd.seq (psP Val.nil)
      (Cmd.seq swP (Cmd.seq repP (Cmd.seq enuP (Cmd.seq (mlP keyProg) (Cmd.seq (rlP 3) swP))))))))),
    (16 * (Ksw + Kr + Kpk + Kp + Kml + Krep + Kenu + Kk + 10) + 2 * Kk + 10), ?_⟩
  intro main p s t hsp htp hp
  have hPsz : isz ((p : ℤ)) ≤ auSZ p := isz_self_le_auSZ p
  have hSsz : isz ((s : ℤ)) ≤ auSZ p := isz_natCast_le_auSZ hsp
  have hTsz : isz ((t : ℤ)) ≤ auSZ p := isz_natCast_le_auSZ htp
  have hBn : vsz (ofList (buAnsL s t)) ≤ (s + 1) * (auSZ p + 1) := vsz_ofList_buAnsL hsp
  have hcost2 : Work.Fx.szl
      (List.take (2 + 1) [Val.int (s : ℤ), Val.int (p : ℤ), Val.int (t : ℤ), Val.int (auPi p)])
      ≤ 3 * auSZ p := by
    have htake : List.take (2 + 1)
        [Val.int (s : ℤ), Val.int (p : ℤ), Val.int (t : ℤ), Val.int (auPi p)]
        = [Val.int (s : ℤ), Val.int (p : ℤ), Val.int (t : ℤ)] := rfl
    rw [htake]
    have hs : Work.Fx.szl ([Val.int (s : ℤ), Val.int (p : ℤ), Val.int (t : ℤ)] : List Val)
        = isz ((s : ℤ)) + isz ((p : ℤ)) + isz ((t : ℤ)) := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        vsz_int_eq]
      ring
    rw [hs]; omega
  have hcost4 : Work.Fx.szl
      (List.take 1 [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      ≤ auSZ p := by
    have htake : List.take 1
        [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)]
        = [Val.int (s : ℤ)] := rfl
    rw [htake]
    have hs : Work.Fx.szl ([Val.int (s : ℤ)] : List Val) = isz ((s : ℤ)) := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        vsz_int_eq]
      ring
    rw [hs]; exact hSsz
  have hcost10 : Work.Fx.szl
      (List.take (3 + 1) [ofList (buAnsL s t), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
        Val.int (auPi p)]) ≤ (s + 1) * (auSZ p + 1) + 3 * auSZ p := by
    have htake : List.take (3 + 1)
        [ofList (buAnsL s t), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
          Val.int (auPi p)]
        = [ofList (buAnsL s t), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ)] := rfl
    rw [htake]
    have hs : Work.Fx.szl
        ([ofList (buAnsL s t), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ)] : List Val)
        = vsz (ofList (buAnsL s t)) + isz ((s : ℤ)) + isz ((t : ℤ)) + isz ((p : ℤ)) := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        vsz_int_eq]
      ring
    rw [hs]; omega
  have st1 : Pipe main swP
      [Val.int (p : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)]
      [Val.int (s : ℤ), Val.int (p : ℤ), Val.int (t : ℤ), Val.int (auPi p)]
      (Ksw * (2 * auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail [Val.int (t : ℤ), Val.int (auPi p)]
      (Pipe.swap main hSw (Val.int (p : ℤ)) (Val.int (s : ℤ)))) ?_
    exact mulK_le_mulK (by rw [vsz_int_eq, vsz_int_eq]; omega)
  have st2 : Pipe main (rlP 2)
      [Val.int (s : ℤ), Val.int (p : ℤ), Val.int (t : ℤ), Val.int (auPi p)]
      [Val.int (t : ℤ), Val.int (s : ℤ), Val.int (p : ℤ), Val.int (auPi p)]
      (Kr * 3 * (3 * auSZ p + 1)) := by
    refine Pipe.le (Pipe.roll main hRl
      (A := [Val.int (s : ℤ), Val.int (p : ℤ), Val.int (t : ℤ), Val.int (auPi p)]) (k := 2) (by simp)) ?_
    exact mulK_le_mulK (by omega)
  have st3 : Pipe main swP
      [Val.int (t : ℤ), Val.int (s : ℤ), Val.int (p : ℤ), Val.int (auPi p)]
      [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)]
      (Ksw * (2 * auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail [Val.int (p : ℤ), Val.int (auPi p)]
      (Pipe.swap main hSw (Val.int (t : ℤ)) (Val.int (s : ℤ)))) ?_
    exact mulK_le_mulK (by rw [vsz_int_eq, vsz_int_eq]; omega)
  have st4 : Pipe main (pkP 0)
      [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)]
      (Val.int (s : ℤ) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (Kpk * (auSZ p + 1)) := by
    refine Pipe.le (Pipe.pick main hPk
      (A := [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)]) (k := 0)
      (by simp)) ?_
    show Kpk * (0 + 1) * (Work.Fx.szl (List.take (0 + 1)
      [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)]) + 1)
      ≤ Kpk * (auSZ p + 1)
    rw [show (0 : ℕ) + 1 = 1 by omega, Nat.mul_one]
    exact mulK_le_mulK (by omega)
  have st5 : Pipe main (psP Val.nil)
      (Val.int (s : ℤ) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (Val.nil :: Val.int (s : ℤ) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
        Val.int (auPi p)])
      (Kp * 2) := by
    refine Pipe.le (Pipe.pushOnAny (T := Val.int (s : ℤ) ::
        [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (hPs main Val.nil)) ?_
    exact mulK_le_mulK (by simp [vsz, Val.enc])
  have st6 : Pipe main swP
      (Val.nil :: Val.int (s : ℤ) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
        Val.int (auPi p)])
      (Val.int (s : ℤ) :: Val.nil :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
        Val.int (auPi p)])
      (Ksw * (auSZ p + 2)) := by
    refine Pipe.le (Pipe.appendTail [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
      Val.int (auPi p)] (Pipe.swap main hSw Val.nil (Val.int (s : ℤ)))) ?_
    exact mulK_le_mulK (by rw [vsz_int_eq, show vsz Val.nil = 1 from rfl]; omega)
  have st7 : Pipe main repP
      (Val.int (s : ℤ) :: Val.nil :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
        Val.int (auPi p)])
      (ofList (buNilL s) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (Krep * (2 * (s + 1) + auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
      Val.int (auPi p)]
      (@Pipe.ofWordR main repP [Val.int (s : ℤ), Val.nil] [ofList (buNilL s)]
        (Krep * ((s + 1) * (vsz Val.nil + 1) + isz ((s : ℤ)) + 1)) (hRep main s Val.nil))) ?_
    exact mulK_le_mulK (by simp only [vsz, Val.enc, List.length_cons, List.length_nil]; omega)
  have st8 : Pipe main enuP
      (ofList (buNilL s) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (ofList (buIdxL s) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (Kenu * (2 * (s + 1) + s * (p + 1) + 1)) := by
    have hpipe : Pipe main enuP [ofList (buNilL s)]
        [ofList ((List.range (buNilL s).length).map
          (fun i : ℕ => Val.cons (Val.int (i : ℤ)) ((buNilL s).getD i Val.nil)))]
        (Kenu * (vsz (ofList (buNilL s)) + (buNilL s).length * ((buNilL s).length.size + 1) + 1)) :=
      @Pipe.ofWordR main enuP [ofList (buNilL s)]
        [ofList ((List.range (buNilL s).length).map
          (fun i : ℕ => Val.cons (Val.int (i : ℤ)) ((buNilL s).getD i Val.nil)))]
        (Kenu * (vsz (ofList (buNilL s)) + (buNilL s).length * ((buNilL s).length.size + 1) + 1))
        (hEnu main (buNilL s))
    have hpipe2 : Pipe main enuP [ofList (buNilL s)] [ofList (buIdxL s)]
        (Kenu * (vsz (ofList (buNilL s)) + (buNilL s).length * ((buNilL s).length.size + 1) + 1)) :=
      Pipe.rw hpipe (by rw [enumerate_buNilL])
    refine Pipe.le (Pipe.appendTail [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
      Val.int (auPi p)] hpipe2) ?_
    have h1 : vsz (ofList (List.replicate s Val.nil)) ≤ (s + 1) * 2 := vsz_ofList_buNilL s
    have h3 : s * (s.size + 1) ≤ s * (p + 1) :=
      Nat.mul_le_mul (le_refl s) (by have := Nat.size_le.mpr hsp; omega)
    refine mulK_le_mulK ?_
    rw [buNilL, List.length_replicate]
    omega
  have st9 : Pipe main (mlP keyProg)
      (ofList (buIdxL s) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (ofList (buAnsL s t) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (s * (Kk * (p + 1) ^ Kk + Kml * (auSZ p + 3)) + Kml) := by
    intro rest'
    have hq : ∀ x, (∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil) →
        WordR main keyProg
          (fun vs => vs = x :: ([Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
            Val.int (auPi p)] ++ rest'))
          (fun _ out => ∃ y, out = y :: ([Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
            Val.int (auPi p)] ++ rest') ∧
            (∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil ∧
              y = Val.int (((t * i) % s : ℕ) : ℤ)) ∧ vsz y ≤ auSZ p + 2)
          (fun _ => Kk * (p + 1) ^ Kk) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hkey := keySpec main p s t (by omega) hsp htp i hi
        ([Val.int (p : ℤ), Val.int (auPi p)] ++ rest')
      refine Work.Kernel.WordR_conseq hkey ?_ ?_ ?_
      · intro vs hv
        simpa only [List.cons_append, List.nil_append] using hv
      · intro vs out hv hpost
        obtain ⟨-, hout⟩ := hpost
        refine ⟨Val.int (((t * i) % s : ℕ) : ℤ), ?_, ⟨i, hi, rfl, rfl⟩, ?_⟩
        · simpa only [List.cons_append, List.nil_append] using hout
        · rw [vsz_int_eq]
          have hs0 : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
          have hm := Nat.mod_lt (t * i) hs0
          exact le_trans (isz_natCast_le_auSZ (p := p) (lt_trans hm hsp)) (by omega)
      · intro vs _
        exact le_refl _
    have hxs : ∀ x ∈ buIdxL s,
        (∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil) ∧ vsz x ≤ auSZ p + 2 := by
      intro x hx
      rw [buIdxL] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hi
      refine ⟨⟨i, hi, rfl⟩, ?_⟩
      rw [vsz_cons_eq, vsz_int_eq, show vsz Val.nil = 1 from rfl]
      have hi' := isz_natCast_le_auSZ (p := p) (lt_trans hi hsp)
      omega
    have hres := hMl main keyProg
      ([Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)] ++ rest')
      (fun x => ∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil)
      (fun x y => ∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil ∧
        y = Val.int (((t * i) % s : ℕ) : ℤ))
      (Kk * (p + 1) ^ Kk) (auSZ p + 2) hq (buIdxL s) hxs
    refine Work.Kernel.WordR_conseq hres ?_ ?_ ?_
    · intro vs hv; exact hv
    · intro vs out hv hpost
      obtain ⟨ys, hout, hfor⟩ := hpost
      have hys : ys = buAnsL s t := buKeysYs s t hfor
      rw [hout, hys]
      rfl
    · intro vs _
      refine le_of_eq ?_
      rw [length_buIdxL, show (auSZ p + 2) + 1 = auSZ p + 3 by omega]
  have st10 : Pipe main (rlP 3)
      (ofList (buAnsL s t) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ), Val.int (auPi p)])
      (Val.int (p : ℤ) :: ofList (buAnsL s t) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)])
      (Kr * 4 * ((s + 1) * (auSZ p + 1) + 3 * auSZ p + 1)) := by
    refine Pipe.le (Pipe.roll main hRl
      (A := [ofList (buAnsL s t), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (p : ℤ),
        Val.int (auPi p)]) (k := 3) (by simp)) ?_
    exact mulK_le_mulK (by omega)
  have st11 : Pipe main swP
      (Val.int (p : ℤ) :: ofList (buAnsL s t) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)])
      (ofList (buAnsL s t) :: Val.int (p : ℤ) :: [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)])
      (Ksw * (auSZ p + (s + 1) * (auSZ p + 1) + 1)) := by
    refine Pipe.le (Pipe.appendTail [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)]
      (Pipe.swap main hSw (Val.int (p : ℤ)) (ofList (buAnsL s t)))) ?_
    exact mulK_le_mulK (by rw [vsz_int_eq]; omega)
  have hchain : Pipe main
      (Cmd.seq swP (Cmd.seq (rlP 2) (Cmd.seq swP (Cmd.seq (pkP 0) (Cmd.seq (psP Val.nil)
        (Cmd.seq swP (Cmd.seq repP (Cmd.seq enuP (Cmd.seq (mlP keyProg)
          (Cmd.seq (rlP 3) swP))))))))))
      [Val.int (p : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)]
      (ofList (buAnsL s t) :: [Val.int (p : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] ++
        [Val.int (auPi p)])
      (Ksw * (2 * auSZ p + 1)
        + (Kr * 3 * (3 * auSZ p + 1)
          + (Ksw * (2 * auSZ p + 1)
            + (Kpk * (auSZ p + 1)
              + (Kp * 2
                + (Ksw * (auSZ p + 2)
                  + (Krep * (2 * (s + 1) + auSZ p + 1)
                    + (Kenu * (2 * (s + 1) + s * (p + 1) + 1)
                      + ((s * (Kk * (p + 1) ^ Kk + Kml * (auSZ p + 3)) + Kml)
                        + (Kr * 4 * ((s + 1) * (auSZ p + 1) + 3 * auSZ p + 1)
                          + Ksw * (auSZ p + (s + 1) * (auSZ p + 1) + 1))))))))))) := by
    refine Pipe.comp st1 ?_
    refine Pipe.comp st2 ?_
    refine Pipe.comp st3 ?_
    refine Pipe.comp st4 ?_
    refine Pipe.comp st5 ?_
    refine Pipe.comp st6 ?_
    refine Pipe.comp st7 ?_
    refine Pipe.comp st8 ?_
    refine Pipe.comp st9 ?_
    refine Pipe.comp st10 ?_
    exact st11
  refine Pipe.le (Pipe.rw hchain ?_) ?_
  · show ofList (buAnsL s t) :: [Val.int (p : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] ++
        [Val.int (auPi p)]
      = buL8 p 2 s t :: [Val.int (p : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] ++
        [Val.int (auPi p)]
    rw [buL8_eq_ofList]
  · have harith := buKeysArith Kk Ksw Kr Kpk Kp Kml Krep Kenu p s hp
    first
      | linarith [harith]
      | omega

end Work.Resample
