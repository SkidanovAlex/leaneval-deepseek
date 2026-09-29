import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buKeyTools
import Submission.Work.Resample.buKeysWord

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## The cost arithmetic

The word built below is a chain of twelve library calls.  With `S = auSZ p` its cost is at most
the sum

`Kpk*(16S+4) + (Kpk*(16S+4) + (Kpk*(25S+5) + (Kp*2 + (Ksw*(S+2) + (Krep*(2(s+1)+S+1)
 + (Kenu*(2(s+1)+s(p+1)+1) + (s*(Kk*(p+1)^Kk + Kml*(S+3)) + Kml + (Ksw*((s+1)*(S+1)+S+1)
 + (Kdr*(S+1) + (Ksw*((s+1)*(S+1)+S+1) + Kdr*(S+1)))))))))))`,

which this lemma bounds by `Kf*(s+1)*(p+1)^Kf` with
`Kf = 16*KB + 2*Kk + 10`, `KB = Kpk+Kp+Ksw+Krep+Kenu+Kml+Kdr+Kk+10`. -/

theorem buKeysBArith (Kpk Kp Ksw Krep Kenu Kml Kdr Kk p s : ℕ) (hp : 100 ≤ p) :
    Kpk * (16 * auSZ p + 4) + (Kpk * (16 * auSZ p + 4) + (Kpk * (25 * auSZ p + 5) + (Kp * 2 + (Ksw * (auSZ p + 2) + (Krep * (2 * (s + 1) + auSZ p + 1) + (Kenu * (2 * (s + 1) + s * (p + 1) + 1) + (s * (Kk * (p + 1) ^ Kk + Kml * (auSZ p + 3)) + Kml + (Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1) + (Kdr * (auSZ p + 1) + (Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1) + (Kdr * (auSZ p + 1))))))))))))
    ≤ (16 * (Kpk + Kp + Ksw + Krep + Kenu + Kml + Kdr + Kk + 10) + 2 * Kk + 10) * (s + 1)
      * (p + 1) ^ (16 * (Kpk + Kp + Ksw + Krep + Kenu + Kml + Kdr + Kk + 10) + 2 * Kk + 10) := by
  set S := auSZ p with hS
  set W := (p + 1) ^ 4 with hW
  set V := (s + 1) * (100 * S + 100) with hV
  set KB := Kpk + Kp + Ksw + Krep + Kenu + Kml + Kdr + Kk + 10 with hKB
  set Kf := 16 * KB + 2 * Kk + 10 with hKf
  have hSW : 100 * S + 100 ≤ W := by rw [hS, hW]; exact hundred_auSZ_le_pow p hp
  have hSge : p ≤ S := by rw [hS]; simp only [auSZ]; omega
  have hone : ∀ n : ℕ, n ≤ (s + 1) * n := by
    intro n
    calc n = 1 * n := (Nat.one_mul n).symm
      _ ≤ (s + 1) * n := mul_le_mulK (by omega : 1 ≤ s + 1)
  have hP1 : 16 * S + 4 ≤ V := by
    rw [hV]
    calc 16 * S + 4 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP3 : 25 * S + 5 ≤ V := by
    rw [hV]
    calc 25 * S + 5 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP4 : 2 ≤ V := by
    rw [hV]
    calc 2 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP5 : S + 2 ≤ V := by
    rw [hV]
    calc S + 2 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP6 : 2 * (s + 1) + S + 1 ≤ V := by
    rw [hV]
    calc 2 * (s + 1) + (S + 1) ≤ 2 * (s + 1) + (s + 1) * (S + 1) :=
          Nat.add_le_add_left (hone (S + 1)) _
      _ = (s + 1) * (2 + (S + 1)) := by ring
      _ ≤ (s + 1) * (100 * S + 100) := mulK_le_mulK (by omega)
  have hP7 : 2 * (s + 1) + s * (p + 1) + 1 ≤ V := by
    rw [hV]
    calc 2 * (s + 1) + s * (p + 1) + 1
        ≤ (s + 1) * 2 + (s + 1) * (p + 1) + (s + 1) * 1 := by
          refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
          · exact le_of_eq (Nat.mul_comm 2 (s + 1))
          · exact mul_le_mulK (by omega : s ≤ s + 1)
          · exact hone 1
      _ = (s + 1) * (2 + (p + 1) + 1) := by ring
      _ ≤ (s + 1) * (100 * S + 100) := mulK_le_mulK (by omega)
  have hP9 : (s + 1) * (S + 1) + S + 1 ≤ V := by
    rw [hV]
    calc (s + 1) * (S + 1) + (S + 1) ≤ (s + 1) * (S + 1) + (s + 1) * (S + 1) :=
          Nat.add_le_add_left (hone (S + 1)) _
      _ = (s + 1) * (2 * S + 2) := by ring
      _ ≤ (s + 1) * (100 * S + 100) := mulK_le_mulK (by omega)
  have hP10 : S + 1 ≤ V := by
    rw [hV]
    calc S + 1 ≤ 100 * S + 100 := by omega
      _ ≤ (s + 1) * (100 * S + 100) := hone _
  have hP11 : (s + 1) * (S + 3) ≤ V := by
    rw [hV]
    exact mulK_le_mulK (by omega)
  have hKB1 : Kpk ≤ KB := by rw [hKB]; omega
  have hKB2 : Kp ≤ KB := by rw [hKB]; omega
  have hKB3 : Ksw ≤ KB := by rw [hKB]; omega
  have hKB4 : Krep ≤ KB := by rw [hKB]; omega
  have hKB5 : Kenu ≤ KB := by rw [hKB]; omega
  have hKB6 : Kml ≤ KB := by rw [hKB]; omega
  have hKB7 : Kdr ≤ KB := by rw [hKB]; omega
  have t1 : Kpk * (16 * S + 4) ≤ KB * V := Nat.mul_le_mul hKB1 hP1
  have t2 : Kpk * (16 * S + 4) ≤ KB * V := Nat.mul_le_mul hKB1 hP1
  have t3 : Kpk * (25 * S + 5) ≤ KB * V := Nat.mul_le_mul hKB1 hP3
  have t4 : Kp * 2 ≤ KB * V := Nat.mul_le_mul hKB2 hP4
  have t5 : Ksw * (S + 2) ≤ KB * V := Nat.mul_le_mul hKB3 hP5
  have t6 : Krep * (2 * (s + 1) + S + 1) ≤ KB * V := Nat.mul_le_mul hKB4 hP6
  have t7 : Kenu * (2 * (s + 1) + s * (p + 1) + 1) ≤ KB * V := Nat.mul_le_mul hKB5 hP7
  have t8 : s * (Kk * (p + 1) ^ Kk + Kml * (S + 3)) + Kml
      ≤ (s + 1) * Kk * (p + 1) ^ Kk + KB * V := by
    have hsplit : s * (Kk * (p + 1) ^ Kk + Kml * (S + 3)) + Kml
        = s * Kk * (p + 1) ^ Kk + (s * Kml * (S + 3) + Kml) := by ring
    rw [hsplit]
    refine Nat.add_le_add ?_ ?_
    · rw [show s * Kk * (p + 1) ^ Kk = s * (Kk * (p + 1) ^ Kk) by ring]
      rw [show (s + 1) * Kk * (p + 1) ^ Kk = (s + 1) * (Kk * (p + 1) ^ Kk) by ring]
      exact mul_le_mulK (by omega)
    · calc s * Kml * (S + 3) + Kml = Kml * (s * (S + 3) + 1) := by ring
        _ ≤ Kml * ((s + 1) * (S + 3)) := mulK_le_mulK (by
              rw [show (s + 1) * (S + 3) = s * (S + 3) + (S + 3) by ring]; omega)
        _ ≤ KB * ((s + 1) * (S + 3)) := mul_le_mulK hKB6
        _ ≤ KB * V := mulK_le_mulK hP11
  have t9 : Ksw * ((s + 1) * (S + 1) + S + 1) ≤ KB * V := Nat.mul_le_mul hKB3 hP9
  have t10 : Kdr * (S + 1) ≤ KB * V := Nat.mul_le_mul hKB7 hP10
  have t11 : Ksw * ((s + 1) * (S + 1) + S + 1) ≤ KB * V := Nat.mul_le_mul hKB3 hP9
  have t12 : Kdr * (S + 1) ≤ KB * V := Nat.mul_le_mul hKB7 hP10
  have hsum : Kpk * (16 * S + 4) + (Kpk * (16 * S + 4) + (Kpk * (25 * S + 5) + (Kp * 2 + (Ksw * (S + 2) + (Krep * (2 * (s + 1) + S + 1) + (Kenu * (2 * (s + 1) + s * (p + 1) + 1) + (s * (Kk * (p + 1) ^ Kk + Kml * (S + 3)) + Kml + (Ksw * ((s + 1) * (S + 1) + S + 1) + (Kdr * (S + 1) + (Ksw * ((s + 1) * (S + 1) + S + 1) + (Kdr * (S + 1))))))))))))
      ≤ 12 * (KB * V) + (s + 1) * Kk * (p + 1) ^ Kk := by
    first
      | omega
      | linarith [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12]
  have hVW : V ≤ (s + 1) * W := by
    rw [hV]
    exact mulK_le_mulK hSW
  have hKf_ge1 : 12 * KB + 4 ≤ Kf := by rw [hKf, hKB]; omega
  have hKf_ge2 : Kk + Kk ≤ Kf := by rw [hKf, hKB]; omega
  have hKf2 : 2 ≤ Kf := by rw [hKf, hKB]; omega
  have hpow1 : 12 * KB * W ≤ (p + 1) ^ Kf := by
    have h1 : 12 * KB ≤ (p + 1) ^ (12 * KB) := by
      have h2 : 12 * KB ≤ 2 ^ (12 * KB) := le_of_lt (Nat.lt_two_pow_self (n := 12 * KB))
      calc 12 * KB ≤ 2 ^ (12 * KB) := h2
        _ ≤ (p + 1) ^ (12 * KB) := pow_mono_base (by omega : 2 ≤ p + 1)
    calc 12 * KB * W = 12 * KB * (p + 1) ^ 4 := by rw [hW]
      _ ≤ (p + 1) ^ (12 * KB) * (p + 1) ^ 4 := Nat.mul_le_mul h1 (le_refl _)
      _ = (p + 1) ^ (12 * KB + 4) := by rw [pow_add]
      _ ≤ (p + 1) ^ Kf := Nat.pow_le_pow_right (by omega : 0 < p + 1) hKf_ge1
  have hpow2 : Kk * (p + 1) ^ Kk ≤ (p + 1) ^ Kf := by
    have h1 : Kk ≤ (p + 1) ^ Kk := by
      calc Kk ≤ 2 ^ Kk := le_of_lt (Nat.lt_two_pow_self (n := Kk))
        _ ≤ (p + 1) ^ Kk := pow_mono_base (by omega : 2 ≤ p + 1)
    calc Kk * (p + 1) ^ Kk ≤ (p + 1) ^ Kk * (p + 1) ^ Kk := Nat.mul_le_mul h1 (le_refl _)
      _ = (p + 1) ^ (Kk + Kk) := by rw [pow_add]
      _ ≤ (p + 1) ^ Kf := Nat.pow_le_pow_right (by omega : 0 < p + 1) hKf_ge2
  calc Kpk * (16 * S + 4) + (Kpk * (16 * S + 4) + (Kpk * (25 * S + 5) + (Kp * 2 + (Ksw * (S + 2) + (Krep * (2 * (s + 1) + S + 1) + (Kenu * (2 * (s + 1) + s * (p + 1) + 1) + (s * (Kk * (p + 1) ^ Kk + Kml * (S + 3)) + Kml + (Ksw * ((s + 1) * (S + 1) + S + 1) + (Kdr * (S + 1) + (Ksw * ((s + 1) * (S + 1) + S + 1) + (Kdr * (S + 1))))))))))))
      ≤ 12 * (KB * V) + (s + 1) * Kk * (p + 1) ^ Kk := hsum
    _ ≤ 12 * (KB * ((s + 1) * W)) + (s + 1) * (Kk * (p + 1) ^ Kk) :=
        Nat.add_le_add (mulK_le_mulK (mulK_le_mulK hVW)) (le_of_eq (by ring))
    _ = (s + 1) * (12 * KB * W) + (s + 1) * (Kk * (p + 1) ^ Kk) := by ring
    _ ≤ (s + 1) * (p + 1) ^ Kf + (s + 1) * (p + 1) ^ Kf :=
        Nat.add_le_add (mulK_le_mulK hpow1) (mulK_le_mulK hpow2)
    _ = 2 * ((s + 1) * (p + 1) ^ Kf) := by ring
    _ ≤ Kf * ((s + 1) * (p + 1) ^ Kf) := mul_le_mulK hKf2
    _ = Kf * (s + 1) * (p + 1) ^ Kf := by ring
    _ = (16 * (Kpk + Kp + Ksw + Krep + Kenu + Kml + Kdr + Kk + 10) + 2 * Kk + 10) * (s + 1)
        * (p + 1) ^ (16 * (Kpk + Kp + Ksw + Krep + Kenu + Kml + Kdr + Kk + 10) + 2 * Kk + 10) := by
        rw [hKf, hKB]

/-! ## `isz` bounds for the block entries -/

theorem buKeysB_vsz_block {p α s t : ℕ} (hs : 2 ≤ s) (hst : s < t) (hαp : α ^ 2 < p)
    (hp : 100 ≤ p) (htp : t < 2 ^ p) (hα : 2 ≤ α) :
    ∀ v ∈ buCB p α s t, vsz v ≤ auSZ p := by
  have hsp : s < 2 ^ p := by omega
  have hs0 : 0 < s := by omega
  have hα2p : α < 2 ^ p := by
    have h1 : α ≤ α * α := by
      rcases Nat.eq_zero_or_pos α with h | h
      · omega
      · calc α = α * 1 := (Nat.mul_one α).symm
          _ ≤ α * α := Nat.mul_le_mul_left α h
    have h2 : α * α = α ^ 2 := (pow_two α).symm
    have h3 : α ^ 2 < 2 ^ p := lt_of_lt_of_le hαp (le_of_lt (Nat.lt_two_pow_self (n := p)))
    omega
  have hszm : isz (((egM p α : ℕ) : ℤ)) ≤ auSZ p := by
    have h1 : egM p α ≤ p + 1 := egM_le p α
    have h2 : (egM p α).size ≤ p + 1 :=
      Nat.size_le.mpr (lt_of_le_of_lt h1 (Nat.lt_two_pow_self (n := p + 1)))
    simp only [isz, Int.natAbs_natCast, auSZ]
    omega
  have hszn : isz (((egN p α s t : ℕ) : ℤ)) ≤ auSZ p := buKeys_isz_egN_le p α s t hs0 hsp (by omega)
  intro v hv
  simp only [buCB, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [Work.Fx.vsz_int] using isz_self_le_auSZ p
  · simpa only [Work.Fx.vsz_int] using isz_natCast_le_auSZ (p := p) hα2p
  · simpa only [Work.Fx.vsz_int] using isz_natCast_le_auSZ (p := p) hsp
  · simpa only [Work.Fx.vsz_int] using isz_natCast_le_auSZ (p := p) htp
  · simpa only [Work.Fx.vsz_int] using hszm
  · simpa only [Work.Fx.vsz_int] using hszn
  · simpa only [Work.Fx.vsz_int] using isz_auPi_le p


/-! ## The word -/

theorem buKeysWordB (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
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
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main prog (Work.Resample.buCB p α s t)
        (Work.Resample.buL8 p α s t :: Work.Resample.buCB p α s t)
        (K * (s + 1) * (p + 1) ^ K) := by
  obtain ⟨pkP, Kpk, hPk⟩ := KL.pick
  obtain ⟨psP, Kp, hPs⟩ := KL.pushVal
  obtain ⟨swP, Ksw, hSw⟩ := KL.swap
  obtain ⟨dpP, Kdr, hDp⟩ := KL.drop
  obtain ⟨mlP, Kml, hMl⟩ := KL.mapList
  obtain ⟨repP, Krep, hRep⟩ := LL.replicate
  obtain ⟨enuP, Kenu, hEnu⟩ := LL.enumerate
  let prg : Cmd := Cmd.seq (pkP 3) (Cmd.seq (pkP 3) (Cmd.seq (pkP 4) (Cmd.seq (psP Val.nil) (Cmd.seq swP (Cmd.seq repP (Cmd.seq enuP (Cmd.seq (mlP keyProg) (Cmd.seq swP (Cmd.seq dpP (Cmd.seq swP (dpP)))))))))))
  refine ⟨prg, (16 * (Kpk + Kp + Ksw + Krep + Kenu + Kml + Kdr + Kk + 10) + 2 * Kk + 10), ?_⟩
  intro main p α s t hs hst hα hp htp hαp
  have hsp : s < 2 ^ p := by omega
  have hs0 : 0 < s := by omega
  have hsis : isz ((s : ℤ)) ≤ auSZ p := isz_natCast_le_auSZ (p := p) hsp
  have hsit : isz ((t : ℤ)) ≤ auSZ p := isz_natCast_le_auSZ (p := p) htp
  have hBmem : ∀ v ∈ buCB p α s t, vsz v ≤ auSZ p := buKeysB_vsz_block hs hst hαp hp htp hα
  have hW1mem : ∀ v ∈ (Val.int (t : ℤ) :: buCB p α s t), vsz v ≤ auSZ p := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simpa only [Work.Fx.vsz_int] using isz_natCast_le_auSZ (p := p) htp
    · exact hBmem v hv
  have hW2mem : ∀ v ∈ (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t), vsz v ≤ auSZ p := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simpa only [Work.Fx.vsz_int] using isz_natCast_le_auSZ (p := p) hsp
    · exact hW1mem v hv
  have hszl1 : Work.Fx.szl (List.take 4 (buCB p α s t)) ≤ 4 * auSZ p :=
    le_trans (szl_le_len_mul (A := List.take 4 (buCB p α s t)) (n := auSZ p)
      (fun v hv => hBmem v (List.mem_of_mem_take hv)))
      (Nat.mul_le_mul_right _ (by simp [buCB]))
  have hszl2 : Work.Fx.szl (List.take 4 (Val.int (t : ℤ) :: buCB p α s t)) ≤ 4 * auSZ p :=
    le_trans (szl_le_len_mul (A := List.take 4 (Val.int (t : ℤ) :: buCB p α s t)) (n := auSZ p)
      (fun v hv => hW1mem v (List.mem_of_mem_take hv)))
      (Nat.mul_le_mul_right _ (by simp [buCB]))
  have hszl3 : Work.Fx.szl (List.take 5 (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t))
      ≤ 5 * auSZ p :=
    le_trans (szl_le_len_mul
      (A := List.take 5 (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)) (n := auSZ p)
      (fun v hv => hW2mem v (List.mem_of_mem_take hv)))
      (Nat.mul_le_mul_right _ (by simp [buCB]))
  have st1 : Pipe main (pkP 3) (buCB p α s t) (Val.int (t : ℤ) :: buCB p α s t)
      (Kpk * (16 * auSZ p + 4)) := by
    refine Pipe.le (Pipe.pickAt (main := main) hPk (A := buCB p α s t) (k := 3)
      (by simp [buCB]) (v := Val.int (t : ℤ)) (by simp [buCB])) ?_
    show Kpk * (3 + 1) * (Work.Fx.szl (List.take (3 + 1) (buCB p α s t)) + 1)
      ≤ Kpk * (16 * auSZ p + 4)
    rw [show (3 : ℕ) + 1 = 4 by omega,
      show Kpk * 4 * (Work.Fx.szl (List.take 4 (buCB p α s t)) + 1)
        = Kpk * (4 * (Work.Fx.szl (List.take 4 (buCB p α s t)) + 1)) by ring]
    exact mulK_le_mulK (by omega)
  have st2 : Pipe main (pkP 3) (Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t) (Kpk * (16 * auSZ p + 4)) := by
    refine Pipe.le (Pipe.pickAt (main := main) hPk (A := Val.int (t : ℤ) :: buCB p α s t)
      (k := 3) (by simp [buCB]) (v := Val.int (s : ℤ)) (by simp [buCB])) ?_
    show Kpk * (3 + 1) * (Work.Fx.szl (List.take (3 + 1) (Val.int (t : ℤ) :: buCB p α s t)) + 1)
      ≤ Kpk * (16 * auSZ p + 4)
    rw [show (3 : ℕ) + 1 = 4 by omega,
      show Kpk * 4 * (Work.Fx.szl (List.take 4 (Val.int (t : ℤ) :: buCB p α s t)) + 1)
        = Kpk * (4 * (Work.Fx.szl (List.take 4 (Val.int (t : ℤ) :: buCB p α s t)) + 1)) by ring]
    exact mulK_le_mulK (by omega)
  have st3 : Pipe main (pkP 4) (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (s : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Kpk * (25 * auSZ p + 5)) := by
    refine Pipe.le (Pipe.pickAt (main := main) hPk
      (A := Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t) (k := 4) (by simp [buCB])
      (v := Val.int (s : ℤ)) (by simp [buCB])) ?_
    show Kpk * (4 + 1) * (Work.Fx.szl
      (List.take (4 + 1) (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)) + 1)
      ≤ Kpk * (25 * auSZ p + 5)
    rw [show (4 : ℕ) + 1 = 5 by omega,
      show Kpk * 5 * (Work.Fx.szl
        (List.take 5 (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)) + 1)
        = Kpk * (5 * (Work.Fx.szl
          (List.take 5 (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)) + 1)) by ring]
    exact mulK_le_mulK (by omega)
  have st4 : Pipe main (psP Val.nil)
      (Val.int (s : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.nil :: Val.int (s : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Kp * 2) := by
    refine Pipe.le (Pipe.pushOnAny (T := Val.int (s : ℤ) :: Val.int (s : ℤ)
      :: Val.int (t : ℤ) :: buCB p α s t) (hPs main Val.nil)) ?_
    exact mulK_le_mulK (by simp [vsz, Val.enc])
  have st5 : Pipe main swP
      (Val.nil :: Val.int (s : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (s : ℤ) :: Val.nil :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Ksw * (auSZ p + 2)) := by
    refine Pipe.le (Pipe.appendTail (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Pipe.swap main hSw Val.nil (Val.int (s : ℤ)))) ?_
    exact mulK_le_mulK (by rw [show vsz Val.nil = 1 from rfl, vsz_int_eq]; omega)
  have st6 : Pipe main repP
      (Val.int (s : ℤ) :: Val.nil :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (ofList (buNilL s) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Krep * (2 * (s + 1) + auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (@Pipe.ofWordR main repP [Val.int (s : ℤ), Val.nil] [ofList (buNilL s)]
        (Krep * ((s + 1) * (vsz Val.nil + 1) + isz ((s : ℤ)) + 1)) (hRep main s Val.nil))) ?_
    exact mulK_le_mulK (by simp only [vsz, Val.enc, List.length_cons, List.length_nil]; omega)
  have st7 : Pipe main enuP
      (ofList (buNilL s) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (ofList (buIdxL s) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
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
    refine Pipe.le (Pipe.appendTail (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      hpipe2) ?_
    have h1 : vsz (ofList (buNilL s)) ≤ (s + 1) * 2 := vsz_ofList_buNilL s
    have h3 : s * (s.size + 1) ≤ s * (p + 1) :=
      Nat.mul_le_mul (le_refl s) (by have := Nat.size_le.mpr hsp; omega)
    refine mulK_le_mulK ?_
    simp only [buNilL, List.length_replicate] at h1 ⊢
    omega
  have st8 : Pipe main (mlP keyProg)
      (ofList (buIdxL s) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (ofList (buAnsL s t) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (s * (Kk * (p + 1) ^ Kk + Kml * (auSZ p + 3)) + Kml) := by
    intro rest'
    have hq : ∀ x, (∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil) →
        WordR main keyProg
          (fun vs => vs = x :: (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest'))
          (fun _ out => ∃ y, out = y ::
              (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest') ∧
            (∃ i : ℕ, i < s ∧ x = Val.cons (Val.int (i : ℤ)) Val.nil ∧
              y = Val.int (((t * i) % s : ℕ) : ℤ)) ∧ vsz y ≤ auSZ p + 2)
          (fun _ => Kk * (p + 1) ^ Kk) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hkey := keySpec main p s t (by omega) hsp htp i hi (buCB p α s t ++ rest')
      refine Work.Kernel.WordR_conseq hkey ?_ ?_ ?_
      · intro vs hv
        simpa only [List.cons_append, List.nil_append] using hv
      · intro vs out hv hpost
        obtain ⟨-, hout⟩ := hpost
        refine ⟨Val.int (((t * i) % s : ℕ) : ℤ), ?_, ⟨i, hi, rfl, rfl⟩, ?_⟩
        · simpa only [List.cons_append, List.nil_append] using hout
        · rw [vsz_int_eq]
          have hsm := Nat.mod_lt (t * i) hs0
          exact le_trans (isz_natCast_le_auSZ (p := p) (lt_trans hsm hsp)) (by simp only [auSZ]; omega)
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
      (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest')
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
  have st9 : Pipe main swP
      (ofList (buAnsL s t) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (s : ℤ) :: ofList (buAnsL s t) :: Val.int (t : ℤ) :: buCB p α s t)
      (Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail (Val.int (t : ℤ) :: buCB p α s t)
      (Pipe.swap main hSw (ofList (buAnsL s t)) (Val.int (s : ℤ)))) ?_
    have h1 : vsz (ofList (buAnsL s t)) ≤ (s + 1) * (auSZ p + 1) := vsz_ofList_buAnsL hsp
    have h2 : vsz (Val.int (s : ℤ)) ≤ auSZ p := by
      simpa only [Work.Fx.vsz_int] using hsis
    show Ksw * (vsz (ofList (buAnsL s t)) + vsz (Val.int (s : ℤ)) + 1)
      ≤ Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1)
    exact mulK_le_mulK (by omega)
  have st10 : Pipe main dpP
      (Val.int (s : ℤ) :: ofList (buAnsL s t) :: Val.int (t : ℤ) :: buCB p α s t)
      (ofList (buAnsL s t) :: Val.int (t : ℤ) :: buCB p α s t) (Kdr * (auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail (ofList (buAnsL s t) :: Val.int (t : ℤ) :: buCB p α s t)
      (Pipe.drop main hDp (Val.int (s : ℤ)))) ?_
    have h2 : vsz (Val.int (s : ℤ)) ≤ auSZ p := by
      simpa only [Work.Fx.vsz_int] using hsis
    show Kdr * (vsz (Val.int (s : ℤ)) + 1) ≤ Kdr * (auSZ p + 1)
    exact mulK_le_mulK (by omega)
  have st11 : Pipe main swP
      (ofList (buAnsL s t) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (t : ℤ) :: ofList (buAnsL s t) :: buCB p α s t)
      (Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail (buCB p α s t)
      (Pipe.swap main hSw (ofList (buAnsL s t)) (Val.int (t : ℤ)))) ?_
    have h1 : vsz (ofList (buAnsL s t)) ≤ (s + 1) * (auSZ p + 1) := vsz_ofList_buAnsL hsp
    have h2 : vsz (Val.int (t : ℤ)) ≤ auSZ p := by
      simpa only [Work.Fx.vsz_int] using hsit
    show Ksw * (vsz (ofList (buAnsL s t)) + vsz (Val.int (t : ℤ)) + 1)
      ≤ Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1)
    exact mulK_le_mulK (by omega)
  have st12 : Pipe main dpP
      (Val.int (t : ℤ) :: ofList (buAnsL s t) :: buCB p α s t)
      (ofList (buAnsL s t) :: buCB p α s t) (Kdr * (auSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail (ofList (buAnsL s t) :: buCB p α s t)
      (Pipe.drop main hDp (Val.int (t : ℤ)))) ?_
    have h2 : vsz (Val.int (t : ℤ)) ≤ auSZ p := by
      simpa only [Work.Fx.vsz_int] using hsit
    show Kdr * (vsz (Val.int (t : ℤ)) + 1) ≤ Kdr * (auSZ p + 1)
    exact mulK_le_mulK (by omega)
  have hchain : Pipe main
      (Cmd.seq (pkP 3) (Cmd.seq (pkP 3) (Cmd.seq (pkP 4) (Cmd.seq (psP Val.nil)
        (Cmd.seq swP (Cmd.seq repP (Cmd.seq enuP (Cmd.seq (mlP keyProg)
        (Cmd.seq swP (Cmd.seq dpP (Cmd.seq swP dpP)))))))))))
      (buCB p α s t) (ofList (buAnsL s t) :: buCB p α s t)
      (Kpk * (16 * auSZ p + 4) + (Kpk * (16 * auSZ p + 4) + (Kpk * (25 * auSZ p + 5) + (Kp * 2 + (Ksw * (auSZ p + 2) + (Krep * (2 * (s + 1) + auSZ p + 1) + (Kenu * (2 * (s + 1) + s * (p + 1) + 1) + (s * (Kk * (p + 1) ^ Kk + Kml * (auSZ p + 3)) + Kml + (Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1) + (Kdr * (auSZ p + 1) + (Ksw * ((s + 1) * (auSZ p + 1) + auSZ p + 1) + (Kdr * (auSZ p + 1))))))))))))) := by
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
    refine Pipe.comp st11 ?_
    exact st12
  refine Pipe.le (Pipe.rw hchain ?_) ?_
  · show ofList (buAnsL s t) :: buCB p α s t = buL8 p α s t :: buCB p α s t
    rw [show buL8 p α s t = ofList (buAnsL s t) from buL8_eq_ofList p s t]
  · have harith := buKeysBArith Kpk Kp Ksw Krep Kenu Kml Kdr Kk p s hp
    first
      | linarith [harith]
      | omega

end Work.Resample
