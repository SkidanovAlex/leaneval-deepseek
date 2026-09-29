import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buColsDefs
import Submission.Work.Resample.auMapListTail
import Submission.Work.Resample.buArithWord
import Submission.Work.Resample.buColWord
import Submission.Work.Resample.buQWhs

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-- The index labels `cons (int i) nil`, one for each retained shift. -/
def buIdxLbl (n : ℕ) : List Val :=
  (List.range n).map (fun i : ℕ => Val.cons (.int (i : ℤ)) .nil)

/-- The function implemented by the arithmetic element word: an index label `cons (int i) _`
becomes the shift `int (buHidx p α i)`. -/
def buIdxF (p α : ℕ) : Val → Val
  | .cons (.int i) _ => .int (buHidx p α i)
  | _ => .nil

theorem buIdxF_cons (p α : ℕ) (i : ℤ) (v : Val) :
    buIdxF p α (.cons (.int i) v) = .int (buHidx p α i) := rfl

theorem buIdxLbl_mem {n : ℕ} {x : Val} :
    x ∈ buIdxLbl n ↔ ∃ i : ℕ, i < n ∧ x = Val.cons (.int (i : ℤ)) .nil := by
  rw [buIdxLbl, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mpr hi, rfl⟩

/-- The index labels map onto the shift list: the `i`-th label (`i < 2m`) computes the shift
`buHidx p α i = i - m + 1 - [i < m]`, and `egHs m = [-m,…,-1] ++ [1,…,m]`. -/
theorem buIdxLbl_map (p α : ℕ) :
    (buIdxLbl (2 * egM p α)).map (buIdxF p α) = (egHs (egM p α)).map Val.int := by
  have hmm : 2 * egM p α = egM p α + egM p α := by ring
  rw [buIdxLbl, hmm, List.range_add, egHs]
  simp only [List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hlt : j < egM p α := List.mem_range.mp hj
    have hif : (j : ℤ) < (egM p α : ℤ) := by exact_mod_cast hlt
    show buIdxF p α (.cons (.int (j : ℤ)) .nil) = Val.int ((j : ℤ) - (egM p α : ℤ))
    rw [buIdxF_cons, buHidx_eq, if_pos hif]
    congr 1
    ring
  · apply List.map_congr_left
    intro j hj
    have hge : ¬ (((egM p α + j : ℕ) : ℤ) < (egM p α : ℤ)) := by
      intro hc
      have h2 : (((egM p α + j : ℕ) : ℤ)) = (egM p α : ℤ) + (j : ℤ) := by push_cast; ring
      have h3 : (0 : ℤ) ≤ (j : ℤ) := by positivity
      omega
    show buIdxF p α (.cons (.int ((egM p α + j : ℕ) : ℤ)) .nil) = Val.int ((j : ℤ) + 1)
    rw [buIdxF_cons, buHidx_eq, if_neg hge]
    congr 1
    push_cast
    ring

/-- The shift word: from the parameter block `buCB p α s t` it produces the list
`zl (egHs (egM p α))` of the `2·egM p α` retained shifts on top of the block.

Program: `m` (pick 4), `2m` (pick 0, add), `nil` (push), `swap`, `replicate 2m nil`,
`enumerate`, then `mapList` with the element word `uncons; buArithWord; drop`. -/
theorem buHsWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main prog (Work.Resample.buCB p α s t)
        (Work.Resample.zl (Work.Resample.egHs (Work.Resample.egM p α)) :: Work.Resample.buCB p α s t)
        (K * (Work.Resample.egM p α + 1) * (p + 1) ^ K) := by
  obtain ⟨arProg, KAR, hAr⟩ := buArithWord KL IL
  obtain ⟨uncProg, Kuc, hUc⟩ := KL.unconsV
  obtain ⟨pickProg, Kp, hPk⟩ := KL.pick
  obtain ⟨swapProg, Ksw, hSw⟩ := KL.swap
  obtain ⟨dropProg, Kdr, hDr⟩ := KL.drop
  obtain ⟨pushProg, Kpu, hPush⟩ := KL.pushVal
  obtain ⟨addProg, Kad, hAd⟩ := IL.add
  obtain ⟨combML, Kml, hML⟩ := MapListField.of_kernel KL
  obtain ⟨replProg, Kr, hRepl⟩ := LL.replicate
  obtain ⟨enumProg, Ke, hEnum⟩ := LL.enumerate
  refine ⟨Cmd.seq (pickProg 4) (Cmd.seq (pickProg 0) (Cmd.seq addProg (Cmd.seq
      (pushProg .nil) (Cmd.seq swapProg (Cmd.seq replProg (Cmd.seq enumProg
        (combML (Cmd.seq uncProg (Cmd.seq arProg (Cmd.seq swapProg dropProg)))))))))),
    buHsK KAR Kuc Kp Ksw Kdr Kpu Kad Kml Kr Ke, ?_⟩
  intro main p α s t hs hst hα hp htp hαp
  set Λ : ℕ := buHsK KAR Kuc Kp Ksw Kdr Kpu Kad Kml Kr Ke with hΛ
  let Bc : List Val := buCB p α s t
  let B : ℕ := buSZ p
  let N : ℕ := buSZ p + 2
  let W0 : List Val := .int (egM p α) :: Bc
  let W1 : List Val := .int (egM p α) :: W0
  let W2 : List Val := .int ((2 * egM p α : ℕ) : ℤ) :: Bc
  let W3 : List Val := .nil :: W2
  let W4 : List Val := .int ((2 * egM p α : ℕ) : ℤ) :: .nil :: Bc
  let W5 : List Val := ofList (List.replicate (2 * egM p α) Val.nil) :: Bc
  let W6 : List Val := ofList (buIdxLbl (2 * egM p α)) :: Bc
  let W7 : List Val := ofList ((buIdxLbl (2 * egM p α)).map (buIdxF p α)) :: Bc
  let cEl : ℕ := Kuc * (vsz (.nil) + 1)
    + (KAR * (N + 1) + (Ksw * (2 * N + 1) + Kdr * (vsz (.nil) + 1)))
  -- elementary bounds
  have hb : 2 ≤ p + 1 := by omega
  have hB4 : B + 1 ≤ (p + 1) ^ 4 := buSZ_add_one_le_four p hp
  have hmle : egM p α ≤ p + 1 := egM_le p α
  have hBm : isz (egM p α) ≤ B := isz_egM_le p α
  have hNB : B ≤ N := by simp only [N]; omega
  have hBmem : ∀ v ∈ Bc, vsz v ≤ B := fun v hv => vsz_buCB_le hs hst hα hp htp hαp hv
  have h2m : isz ((2 * egM p α : ℕ) : ℤ) ≤ B := isz_two_egM_le p α hp
  have hsz2m : ((2 * egM p α)).size + 1 ≤ 2 * (p + 1) := by
    have h := size_two_egM_le p α (by omega)
    omega
  have hnil : vsz (.nil) = 1 := Work.Fx.vsz_nil
  have hB1 : 1 ≤ B := by simp only [B, buSZ]; omega
  have hpB : p ≤ B := by simp only [B, buSZ]; omega
  -- the eight step costs
  have s1 : Pipe main (pickProg 4) Bc W0 (Kp * 5 * (Work.Fx.szl (Bc.take 5) + 1)) :=
    Pipe.pickAt (main := main) hPk (A := Bc) (k := 4) (by simp [Bc, buCB])
      (v := .int (egM p α)) (by simp [Bc, buCB])
  have s2 : Pipe main (pickProg 0) W0 W1 (Kp * 1 * (Work.Fx.szl (W0.take 1) + 1)) :=
    Pipe.pickAt (main := main) hPk (A := W0) (k := 0) (by simp [W0, Bc, buCB])
      (v := .int (egM p α)) (by rfl)
  have hcast : (egM p α : ℤ) + (egM p α : ℤ) = (((2 * egM p α : ℕ)) : ℤ) := by
    push_cast; ring
  have s3 : Pipe main addProg W1 W2 (Kad * (isz (egM p α) + isz (egM p α))) := by
    have h := Pipe.appendTail (main := main) Bc
      (Pipe.binOp (main := main) (hAd main) (a := (egM p α : ℤ)) (b := (egM p α : ℤ)) trivial)
    refine Pipe.rw h ?_
    dsimp only [W2]
    show Val.int ((egM p α : ℤ) + (egM p α : ℤ)) :: Bc
      = Val.int ((2 * egM p α : ℕ) : ℤ) :: Bc
    exact congrArg (fun v : Val => v :: Bc) (congrArg Val.int hcast)
  have s4 : Pipe main (pushProg .nil) W2 W3 (Kpu * (vsz (.nil) + 1)) :=
    Pipe.pushOnAny (T := W2) (prog := pushProg .nil) (v := .nil)
      (c := Kpu * (vsz (.nil) + 1)) (hPush main .nil)
  have s5 : Pipe main swapProg W3 W4
      (Ksw * (vsz (.nil) + vsz (.int ((2 * egM p α : ℕ) : ℤ)) + 1)) :=
    Pipe.appendTail (main := main) Bc
      (Pipe.swap (main := main) hSw .nil (.int ((2 * egM p α : ℕ) : ℤ)))
  have s6 : Pipe main replProg W4 W5
      (Kr * ((2 * egM p α + 1) * (vsz (.nil) + 1) + isz ((2 * egM p α : ℕ) : ℤ) + 1)) :=
    Pipe.appendTail (main := main) Bc
      (Pipe.replicate (main := main) hRepl (k := 2 * egM p α) (v := .nil))
  have s7 : Pipe main enumProg W5 W6
      (Ke * (vsz (ofList (List.replicate (2 * egM p α) Val.nil))
        + (List.replicate (2 * egM p α) Val.nil).length
          * (((List.replicate (2 * egM p α) Val.nil).length).size + 1) + 1)) := by
    have hen := Pipe.appendTail (main := main) Bc
      (Pipe.enumerate (main := main) hEnum (xs := List.replicate (2 * egM p α) Val.nil))
    refine Pipe.rw hen ?_
    show ofList ((List.range (List.replicate (2 * egM p α) Val.nil).length).map (fun i : ℕ =>
        Val.cons (.int (i : ℤ)) ((List.replicate (2 * egM p α) Val.nil).getD i .nil))) :: Bc
      = W6
    dsimp only [W6]
    rw [buIdxLbl]
    congr 1
    exact congrArg ofList (enumerate_replicate (2 * egM p α) Val.nil)
  have hElem : ∀ x ∈ buIdxLbl (2 * egM p α),
      Pipe main (Cmd.seq uncProg (Cmd.seq arProg (Cmd.seq swapProg dropProg))) (x :: Bc)
        (buIdxF p α x :: Bc) cEl := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := buIdxLbl_mem.mp hx
    have hsz_i : isz ((i : ℤ)) ≤ B :=
      isz_nat_le_buSZ_four_pow hp (le_trans (le_of_lt hi) (two_egM_le_four_pow α (by omega)))
    have hi2 : (i : ℤ) < 2 * (egM p α : ℤ) := by omega
    have hbhidx : isz (buHidx p α (i : ℤ)) ≤ B := isz_buHidx_le p α hp (by omega) hi2
    have h1 : Pipe main uncProg (.cons (.int (i : ℤ)) .nil :: Bc)
        (.int (i : ℤ) :: .nil :: Bc) Kuc :=
      Pipe.appendTail (main := main) Bc (Pipe.unconsVbu (main := main) hUc (.int (i : ℤ)) .nil)
    have h2 : Pipe main arProg (.int (i : ℤ) :: .nil :: Bc)
        (.int (buHidx p α (i : ℤ)) :: .nil :: Bc) (KAR * (N + 1)) :=
      hAr main p α s t hs hst hα hp htp hαp (i : ℤ) .nil N
        (by rw [hnil]; omega) (le_trans hsz_i hNB) hNB
    have h3 : Pipe main swapProg (.int (buHidx p α (i : ℤ)) :: .nil :: Bc)
        (.nil :: .int (buHidx p α (i : ℤ)) :: Bc)
        (Ksw * (vsz (.int (buHidx p α (i : ℤ))) + vsz (.nil) + 1)) :=
      Pipe.appendTail (main := main) Bc
        (Pipe.swap (main := main) hSw (.int (buHidx p α (i : ℤ))) .nil)
    have h4 : Pipe main dropProg (.nil :: .int (buHidx p α (i : ℤ)) :: Bc)
        (.int (buHidx p α (i : ℤ)) :: Bc) (Kdr * (vsz (.nil) + 1)) :=
      Pipe.appendTail (main := main) (.int (buHidx p α (i : ℤ)) :: Bc)
        (Pipe.drop (main := main) hDr .nil)
    refine Pipe.le (Pipe.comp h1 (Pipe.comp h2 (Pipe.comp h3 h4))) ?_
    have h5 : isz (buHidx p α (i : ℤ)) ≤ N := le_trans hbhidx hNB
    have h6 : Ksw * (isz (buHidx p α (i : ℤ)) + 1 + 1) ≤ Ksw * (2 * N + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    dsimp only [cEl]
    rw [hnil, Work.Fx.vsz_int]
    omega
  have hxmem : ∀ x ∈ buIdxLbl (2 * egM p α), vsz x ≤ N := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := buIdxLbl_mem.mp hx
    have hsz_i : isz ((i : ℤ)) ≤ B :=
      isz_nat_le_buSZ_four_pow hp (le_trans (le_of_lt hi) (two_egM_le_four_pow α (by omega)))
    rw [Work.Fx.vsz_cons, Work.Fx.vsz_int, hnil]
    simp only [N]
    omega
  have hymem : ∀ x ∈ buIdxLbl (2 * egM p α), vsz (buIdxF p α x) ≤ N := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := buIdxLbl_mem.mp hx
    have hi2 : (i : ℤ) < 2 * (egM p α : ℤ) := by omega
    have h := isz_buHidx_le p α hp (by omega) hi2
    rw [buIdxF_cons, Work.Fx.vsz_int]
    simp only [N]
    omega
  have hmap : Pipe main (combML (Cmd.seq uncProg (Cmd.seq arProg (Cmd.seq swapProg dropProg)))) W6 W7
      ((buIdxLbl (2 * egM p α)).length * (cEl + Kml * (N + 1)) + Kml) :=
    auMapListTail (main := main) (q := Cmd.seq uncProg (Cmd.seq arProg (Cmd.seq swapProg dropProg)))
      (T := Bc) (xs := buIdxLbl (2 * egM p α)) (F := buIdxF p α) (c := cEl) (L := N)
      hML hElem hxmem hymem
  have hlast : ofList ((buIdxLbl (2 * egM p α)).map (buIdxF p α)) = zl (egHs (egM p α)) := by
    rw [buIdxLbl_map, zl]
  -- the total
  have hszl5 : Work.Fx.szl (Bc.take 5) ≤ 5 * B := by
    refine le_trans (szl_le_length_mul' (l := Bc.take 5) (N := B) ?_)
      (Nat.mul_le_mul_right _ ?_)
    · intro v hv
      exact hBmem v (List.mem_of_mem_take hv)
    · rw [List.length_take]; exact Nat.min_le_left _ _
  have hz1 : Work.Fx.szl (Bc.take 5) + 1 ≤ (p + 1) ^ 6 := by
    have h1 : 5 * B + 1 ≤ 6 * (B + 1) := by omega
    calc Work.Fx.szl (Bc.take 5) + 1 ≤ 5 * B + 1 := by omega
      _ ≤ 6 * (B + 1) := h1
      _ ≤ (p + 1) ^ 2 * (p + 1) ^ 4 :=
          Nat.mul_le_mul (buCol_num_le hp (by norm_num)) hB4
      _ = (p + 1) ^ 6 := by rw [← pow_add]
  have hmemW0 : ∀ v ∈ W0, vsz v ≤ B := by
    intro v hv
    simp only [W0, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv
    · rw [Work.Fx.vsz_int]; exact hBm
    · exact hBmem v hv
  have hlenW0 : W0.length = 8 := by simp [W0, Bc, buCB]
  have hz2 : Work.Fx.szl (W0.take 1) + 1 ≤ (p + 1) ^ 6 := by
    have ha : Work.Fx.szl (W0.take 1) ≤ Work.Fx.szl W0 := szl_take_le W0 1
    have hb2 : Work.Fx.szl W0 ≤ W0.length * B := szl_le_length_mul' hmemW0
    have h1 : Work.Fx.szl (W0.take 1) ≤ 8 * B := by
      rw [hlenW0] at hb2
      exact le_trans ha hb2
    have h2 : 8 * B + 1 ≤ 9 * (B + 1) := by omega
    calc Work.Fx.szl (W0.take 1) + 1 ≤ 8 * B + 1 := by omega
      _ ≤ 9 * (B + 1) := h2
      _ ≤ (p + 1) ^ 2 * (p + 1) ^ 4 :=
          Nat.mul_le_mul (buCol_num_le hp (by norm_num)) hB4
      _ = (p + 1) ^ 6 := by rw [← pow_add]
  have hz3 : isz (egM p α) + isz (egM p α) ≤ (p + 1) ^ 5 := by
    have h1 : 2 * B ≤ 2 * (B + 1) := by omega
    calc isz (egM p α) + isz (egM p α) ≤ 2 * B := by omega
      _ ≤ 2 * (B + 1) := h1
      _ ≤ (p + 1) ^ 1 * (p + 1) ^ 4 :=
          Nat.mul_le_mul (by rw [pow_one]; omega) hB4
      _ = (p + 1) ^ 5 := by rw [← pow_add]
  have hz4 : vsz (.nil) + 1 ≤ (p + 1) ^ 1 := by
    rw [hnil, pow_one]; omega
  have hz5 : vsz (.nil) + vsz (.int ((2 * egM p α : ℕ) : ℤ)) + 1 ≤ (p + 1) ^ 5 := by
    rw [hnil, Work.Fx.vsz_int]
    have h1 : 1 + isz ((2 * egM p α : ℕ) : ℤ) + 1 ≤ 2 * (B + 1) := by omega
    calc 1 + isz ((2 * egM p α : ℕ) : ℤ) + 1 ≤ 2 * (B + 1) := h1
      _ ≤ (p + 1) ^ 1 * (p + 1) ^ 4 :=
          Nat.mul_le_mul (by rw [pow_one]; omega) hB4
      _ = (p + 1) ^ 5 := by rw [← pow_add]
  have hz6 : (2 * egM p α + 1) * (vsz (.nil) + 1) + isz ((2 * egM p α : ℕ) : ℤ) + 1
      ≤ (p + 1) ^ 5 := by
    rw [hnil]
    have h1 : (2 * egM p α + 1) * 2 ≤ 6 * (p + 1) := by
      have h2 : 2 * egM p α + 1 ≤ 3 * (p + 1) := by omega
      calc (2 * egM p α + 1) * 2 ≤ (3 * (p + 1)) * 2 := Nat.mul_le_mul h2 le_rfl
        _ = 6 * (p + 1) := by ring
    have h2 : (2 * egM p α + 1) * 2 + isz ((2 * egM p α : ℕ) : ℤ) + 1 ≤ 7 * (B + 1) := by
      omega
    calc (2 * egM p α + 1) * (1 + 1) + isz ((2 * egM p α : ℕ) : ℤ) + 1
        ≤ 7 * (B + 1) := h2
      _ ≤ (p + 1) ^ 1 * (p + 1) ^ 4 :=
          Nat.mul_le_mul (by rw [pow_one]; omega) hB4
      _ = (p + 1) ^ 5 := by rw [← pow_add]
  have hz7 : vsz (ofList (List.replicate (2 * egM p α) Val.nil))
        + (List.replicate (2 * egM p α) Val.nil).length
          * (((List.replicate (2 * egM p α) Val.nil).length).size + 1) + 1 ≤ (p + 1) ^ 4 := by
    rw [List.length_replicate]
    have hvsz : vsz (ofList (List.replicate (2 * egM p α) Val.nil)) ≤ 6 * (p + 1) := by
      have h := buCol_vsz_ofList_le (l := List.replicate (2 * egM p α) Val.nil) (B := 1)
        (fun x hx => by
          first
            | (rw [List.eq_of_mem_replicate hx, hnil]; omega)
            | rw [List.eq_of_mem_replicate hx, hnil])
      rw [List.length_replicate] at h
      refine le_trans h ?_
      have h2 : 2 * egM p α + 1 ≤ 3 * (p + 1) := by omega
      calc (2 * egM p α + 1) * (1 + 1) ≤ (3 * (p + 1)) * 2 := Nat.mul_le_mul h2 le_rfl
        _ = 6 * (p + 1) := by ring
    have hprod : (2 * egM p α) * (((2 * egM p α)).size + 1) ≤ 2 * (p + 1) * (2 * (p + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmle) hsz2m
    have hA : vsz (ofList (List.replicate (2 * egM p α) Val.nil))
        + (2 * egM p α) * (((2 * egM p α)).size + 1) + 1
        ≤ 6 * (p + 1) + 4 * ((p + 1) * (p + 1)) + 1 := by
      have h4 : 2 * (p + 1) * (2 * (p + 1)) = 4 * ((p + 1) * (p + 1)) := by ring
      linarith [hvsz, hprod, le_of_eq h4]
    have hB' : 6 * (p + 1) + 4 * ((p + 1) * (p + 1)) + 1 ≤ 11 * ((p + 1) * (p + 1)) := by
      have hp1 : 1 ≤ p + 1 := by omega
      have h1 : 6 * (p + 1) ≤ 6 * ((p + 1) * (p + 1)) := by
        calc 6 * (p + 1) = 6 * (p + 1) * 1 := by ring
          _ ≤ 6 * (p + 1) * (p + 1) := Nat.mul_le_mul_left _ hp1
          _ = 6 * ((p + 1) * (p + 1)) := by ring
      have h2 : 1 ≤ (p + 1) * (p + 1) := by nlinarith [hp1]
      linarith [h1, h2]
    have hC' : 11 * ((p + 1) * (p + 1)) ≤ (p + 1) ^ 4 := by
      have h11 : (11 : ℕ) ≤ (p + 1) * (p + 1) := by
        have := buCol_num_le (p := p) hp (C := 11) (d := 2) (by norm_num)
        simpa [pow_two] using this
      calc 11 * ((p + 1) * (p + 1)) ≤ ((p + 1) * (p + 1)) * ((p + 1) * (p + 1)) :=
            Nat.mul_le_mul_right _ h11
        _ = (p + 1) ^ 4 := by ring
    exact le_trans hA (le_trans hB' hC')
  have hc1 : Kp * 5 * (Work.Fx.szl (Bc.take 5) + 1) ≤ (p + 1) ^ (Kp + 7) :=
    mul3_le_pow_add (le_pow_self (p + 1) Kp hb) (by rw [pow_one]; omega) hz1
  have hc2 : Kp * 1 * (Work.Fx.szl (W0.take 1) + 1) ≤ (p + 1) ^ (Kp + 7) :=
    mul3_le_pow_add (le_pow_self (p + 1) Kp hb) (by rw [pow_one]; omega) hz2
  have hc3 : Kad * (isz (egM p α) + isz (egM p α)) ≤ (p + 1) ^ (Kad + 5) :=
    mul_le_pow_add (le_pow_self (p + 1) Kad hb) hz3
  have hc4 : Kpu * (vsz (.nil) + 1) ≤ (p + 1) ^ (Kpu + 1) :=
    mul_le_pow_add (le_pow_self (p + 1) Kpu hb) hz4
  have hc5 : Ksw * (vsz (.nil) + vsz (.int ((2 * egM p α : ℕ) : ℤ)) + 1)
      ≤ (p + 1) ^ (Ksw + 5) :=
    mul_le_pow_add (le_pow_self (p + 1) Ksw hb) hz5
  have hc6 : Kr * ((2 * egM p α + 1) * (vsz (.nil) + 1) + isz ((2 * egM p α : ℕ) : ℤ) + 1)
      ≤ (p + 1) ^ (Kr + 5) :=
    mul_le_pow_add (le_pow_self (p + 1) Kr hb) hz6
  have hc7 : Ke * (vsz (ofList (List.replicate (2 * egM p α) Val.nil))
        + (List.replicate (2 * egM p α) Val.nil).length
          * (((List.replicate (2 * egM p α) Val.nil).length).size + 1) + 1)
      ≤ (p + 1) ^ (Ke + 4) :=
    mul_le_pow_add (le_pow_self (p + 1) Ke hb) hz7
  have hN5 : N + 1 ≤ (p + 1) ^ 5 := by
    have h1 : N + 1 = B + 3 := by simp only [N]; omega
    calc N + 1 = B + 3 := h1
      _ ≤ 2 * (B + 1) := by omega
      _ ≤ (p + 1) ^ 1 * (p + 1) ^ 4 :=
          Nat.mul_le_mul (by rw [pow_one]; omega) hB4
      _ = (p + 1) ^ 5 := by rw [← pow_add]
  have h2N5 : 2 * N + 1 ≤ (p + 1) ^ 5 := by
    have h1 : 2 * N + 1 = 2 * B + 5 := by simp only [N]; omega
    calc 2 * N + 1 = 2 * B + 5 := h1
      _ ≤ 7 * (B + 1) := by omega
      _ ≤ (p + 1) ^ 1 * (p + 1) ^ 4 :=
          Nat.mul_le_mul (by rw [pow_one]; omega) hB4
      _ = (p + 1) ^ 5 := by rw [← pow_add]
  have hc8 : (buIdxLbl (2 * egM p α)).length * (cEl + Kml * (N + 1)) + Kml
      ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + Kml + 17) := by
    have hlen : (buIdxLbl (2 * egM p α)).length = 2 * egM p α := by
      simp only [buIdxLbl, List.length_map, List.length_range]
    have hA : Kuc * (vsz (.nil) + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 5) :=
      le_trans (mul_le_pow_add (le_pow_self (p + 1) Kuc hb) hz4)
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hB2 : KAR * (N + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 5) :=
      le_trans (mul_le_pow_add (le_pow_self (p + 1) KAR hb) hN5)
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hC2 : Ksw * (2 * N + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 5) :=
      le_trans (mul_le_pow_add (le_pow_self (p + 1) Ksw hb) h2N5)
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hD2 : Kdr * (vsz (.nil) + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 5) :=
      le_trans (mul_le_pow_add (le_pow_self (p + 1) Kdr hb) hz4)
        (Nat.pow_le_pow_right (by omega) (by omega))
    have h34 : Ksw * (2 * N + 1) + Kdr * (vsz (.nil) + 1)
        ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 7) := add_le_pow hb hC2 hD2
    have hB2b : KAR * (N + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 7) :=
      le_trans hB2 (Nat.pow_le_pow_right (by omega) (by omega))
    have h234 : KAR * (N + 1) + (Ksw * (2 * N + 1) + Kdr * (vsz (.nil) + 1))
        ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 9) := add_le_pow hb hB2b h34
    have hAb : Kuc * (vsz (.nil) + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 9) :=
      le_trans hA (Nat.pow_le_pow_right (by omega) (by omega))
    have hcEl : cEl ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + 11) := by
      have h := add_le_pow hb hAb h234
      dsimp only [cEl]
      exact h
    have hKml : Kml * (N + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + Kml + 11) :=
      le_trans (mul_le_pow_add (le_pow_self (p + 1) Kml hb) hN5)
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hcEl' : cEl ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + Kml + 11) :=
      le_trans hcEl (Nat.pow_le_pow_right (by omega) (by omega))
    have hsum' : cEl + Kml * (N + 1) ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + Kml + 13) :=
      add_le_pow hb hcEl' hKml
    have hlen' : 2 * egM p α ≤ (p + 1) ^ 2 := by
      calc 2 * egM p α ≤ 2 * (p + 1) := Nat.mul_le_mul_left 2 hmle
        _ ≤ (p + 1) * (p + 1) := by nlinarith [show (1:ℕ) ≤ p + 1 by omega]
        _ = (p + 1) ^ 2 := by ring
    have hmul : (2 * egM p α) * (cEl + Kml * (N + 1))
        ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + Kml + 15) :=
      le_trans (mul_le_pow_add (d := 2) (e := KAR + Kuc + Ksw + Kdr + Kml + 13) hlen' hsum')
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hKml2 : Kml ≤ (p + 1) ^ (KAR + Kuc + Ksw + Kdr + Kml + 15) :=
      le_trans (le_pow_self (p + 1) Kml hb) (Nat.pow_le_pow_right (by omega) (by omega))
    have hfin := add_le_pow hb hmul hKml2
    rw [hlen]
    exact hfin
  set T : ℕ := KAR + Kuc + Kp + Ksw + Kdr + Kpu + Kad + Kml + Kr + Ke + 17 with hT
  set P : ℕ := (p + 1) ^ T with hP
  have e1 : Kp * 5 * (Work.Fx.szl (Bc.take 5) + 1) ≤ P := by
    rw [hP]
    exact le_trans hc1 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have e2 : Kp * 1 * (Work.Fx.szl (W0.take 1) + 1) ≤ P := by
    rw [hP]
    exact le_trans hc2 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have e3 : Kad * (isz (egM p α) + isz (egM p α)) ≤ P := by
    rw [hP]
    exact le_trans hc3 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have e4 : Kpu * (vsz (.nil) + 1) ≤ P := by
    rw [hP]
    exact le_trans hc4 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have e5 : Ksw * (vsz (.nil) + vsz (.int ((2 * egM p α : ℕ) : ℤ)) + 1) ≤ P := by
    rw [hP]
    exact le_trans hc5 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have e6 : Kr * ((2 * egM p α + 1) * (vsz (.nil) + 1) + isz ((2 * egM p α : ℕ) : ℤ) + 1)
      ≤ P := by
    rw [hP]
    exact le_trans hc6 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have e7 : Ke * (vsz (ofList (List.replicate (2 * egM p α) Val.nil))
        + (List.replicate (2 * egM p α) Val.nil).length
          * (((List.replicate (2 * egM p α) Val.nil).length).size + 1) + 1) ≤ P := by
    rw [hP]
    exact le_trans hc7 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have e8 : (buIdxLbl (2 * egM p α)).length * (cEl + Kml * (N + 1)) + Kml ≤ P := by
    rw [hP]
    exact le_trans hc8 (Nat.pow_le_pow_right (by omega) (by rw [hT]; omega))
  have hsum : Kp * 5 * (Work.Fx.szl (Bc.take 5) + 1)
      + (Kp * 1 * (Work.Fx.szl (W0.take 1) + 1)
        + (Kad * (isz (egM p α) + isz (egM p α))
          + (Kpu * (vsz (.nil) + 1)
            + (Ksw * (vsz (.nil) + vsz (.int ((2 * egM p α : ℕ) : ℤ)) + 1)
              + (Kr * ((2 * egM p α + 1) * (vsz (.nil) + 1)
                  + isz ((2 * egM p α : ℕ) : ℤ) + 1)
                + (Ke * (vsz (ofList (List.replicate (2 * egM p α) Val.nil))
                    + (List.replicate (2 * egM p α) Val.nil).length
                      * (((List.replicate (2 * egM p α) Val.nil).length).size + 1) + 1)
                  + ((buIdxLbl (2 * egM p α)).length * (cEl + Kml * (N + 1)) + Kml)))))))
      ≤ 8 * P := by
    linarith [e1, e2, e3, e4, e5, e6, e7, e8]
  have hfin : 8 * P ≤ Λ * (egM p α + 1) * (p + 1) ^ Λ := by
    have hTlam : T + 1 ≤ Λ := by rw [hT, hΛ]; simp only [buHsK]; omega
    have hlam1 : 1 ≤ Λ := by rw [hΛ]; simp only [buHsK]; omega
    calc 8 * P = 8 * (p + 1) ^ T := by rw [hP]
      _ ≤ (p + 1) ^ 1 * (p + 1) ^ T :=
          Nat.mul_le_mul_right _ (by rw [pow_one]; omega)
      _ = (p + 1) ^ (1 + T) := (pow_add (p + 1) 1 T).symm
      _ = (p + 1) ^ (T + 1) := by rw [show 1 + T = T + 1 by omega]
      _ ≤ (p + 1) ^ Λ := Nat.pow_le_pow_right (by omega) hTlam
      _ ≤ (egM p α + 1) * (p + 1) ^ Λ := le_mul_succ (egM p α) ((p + 1) ^ Λ)
      _ ≤ Λ * ((egM p α + 1) * (p + 1) ^ Λ) := by
          calc (egM p α + 1) * (p + 1) ^ Λ = 1 * ((egM p α + 1) * (p + 1) ^ Λ) :=
                (one_mul _).symm
            _ ≤ Λ * ((egM p α + 1) * (p + 1) ^ Λ) := Nat.mul_le_mul_right _ hlam1
      _ = Λ * (egM p α + 1) * (p + 1) ^ Λ := by ring
  -- the eight steps as `Pipe`s
  intro rest0
  have g1 : WordR main (pickProg 4) (fun vs => vs = Bc ++ rest0) (fun _ out => out = W0 ++ rest0)
      (fun _ => Kp * 5 * (Work.Fx.szl (Bc.take 5) + 1)) := s1 rest0
  have g2 : WordR main (pickProg 0) (fun vs => vs = W0 ++ rest0) (fun _ out => out = W1 ++ rest0)
      (fun _ => Kp * 1 * (Work.Fx.szl (W0.take 1) + 1)) := s2 rest0
  have g3 : WordR main addProg (fun vs => vs = W1 ++ rest0) (fun _ out => out = W2 ++ rest0)
      (fun _ => Kad * (isz (egM p α) + isz (egM p α))) := s3 rest0
  have g4 : WordR main (pushProg .nil) (fun vs => vs = W2 ++ rest0)
      (fun _ out => out = W3 ++ rest0) (fun _ => Kpu * (vsz (.nil) + 1)) := s4 rest0
  have g5 : WordR main swapProg (fun vs => vs = W3 ++ rest0) (fun _ out => out = W4 ++ rest0)
      (fun _ => Ksw * (vsz (.nil) + vsz (.int ((2 * egM p α : ℕ) : ℤ)) + 1)) := s5 rest0
  have g6 : WordR main replProg (fun vs => vs = W4 ++ rest0) (fun _ out => out = W5 ++ rest0)
      (fun _ => Kr * ((2 * egM p α + 1) * (vsz (.nil) + 1)
        + isz ((2 * egM p α : ℕ) : ℤ) + 1)) := s6 rest0
  have g7 : WordR main enumProg (fun vs => vs = W5 ++ rest0) (fun _ out => out = W6 ++ rest0)
      (fun _ => Ke * (vsz (ofList (List.replicate (2 * egM p α) Val.nil))
        + (List.replicate (2 * egM p α) Val.nil).length
          * (((List.replicate (2 * egM p α) Val.nil).length).size + 1) + 1)) := s7 rest0
  have g8 : WordR main (combML (Cmd.seq uncProg (Cmd.seq arProg (Cmd.seq swapProg dropProg))))
      (fun vs => vs = W6 ++ rest0) (fun _ out => out = W7 ++ rest0)
      (fun _ => (buIdxLbl (2 * egM p α)).length * (cEl + Kml * (N + 1)) + Kml) := hmap rest0
  have gtot := buCol_comp g1 (buCol_comp g2 (buCol_comp g3 (buCol_comp g4 (buCol_comp g5
    (buCol_comp g6 (buCol_comp g7 g8))))))
  refine Work.Kernel.WordR_conseq gtot (fun vs hv => hv) ?_ (fun vs _ => le_trans hsum hfin)
  intro vs out hv hout
  rw [hout]
  have hW7 : W7 = zl (egHs (egM p α)) :: buCB p α s t := by
    dsimp only [W7, Bc]
    rw [hlast]
  rw [hW7]

/-- `(range l.length).map (fun i => l.getD i d) = l`. -/
theorem range_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have h1 : (List.range t.length).map ((fun i => (a :: t).getD i d) ∘ Nat.succ)
        = (List.range t.length).map (fun i => t.getD i d) := by
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      exact List.getD_cons_succ
    rw [h1, ih]
    rfl

/-- `(range l.length).map (fun i => g (l.getD i d)) = l.map g`. -/
theorem map_range_getD {α : Type} (l : List α) (g : α → Val) (d : α) :
    (List.range l.length).map (fun i => g (l.getD i d)) = l.map g := by
  conv_rhs => rw [← range_getD l d]
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  rfl

/-- The shift list read at an index (in `getD` form). -/
theorem getD_shift {m i : ℕ} (hi : i < (egHs m).length) :
    ((egHs m).map Val.int).getD i .nil = Val.int ((egHs m).getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    ← List.getD_eq_getElem _ _ hi]

/-- The index label read at an index (in `getD` form). -/
theorem getD_buIdxLbl {n i : ℕ} (hi : i < n) :
    (buIdxLbl n).getD i .nil = Val.cons (.int (i : ℤ)) .nil := by
  show ((List.range n).map (fun j : ℕ => Val.cons (.int (j : ℤ)) .nil)).getD i .nil
      = Val.cons (.int (i : ℤ)) .nil
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range (by simpa using hi)]

/-- The `i`-th retained shift is `buHidx p α i`, in `getD` form. -/
theorem buHidx_eq_getD (p α : ℕ) {i : ℕ} (hi : i < 2 * egM p α) :
    buHidx p α (i : ℤ) = (egHs (egM p α)).getD i 0 := by
  have h1 : i < ((buIdxLbl (2 * egM p α)).map (buIdxF p α)).length := by
    simp only [buIdxLbl, List.length_map, List.length_range]
    exact hi
  have h2 : i < ((egHs (egM p α)).map Val.int).length := by
    simp only [List.length_map, buQWhs_length]
    exact hi
  have h1' : i < (buIdxLbl (2 * egM p α)).length := by
    simp only [buIdxLbl, List.length_map, List.length_range]
    exact hi
  have h := congrArg (fun l : List Val => l.getD i .nil) (buIdxLbl_map p α)
  rw [List.getD_eq_getElem _ _ h1, List.getElem_map,
    ← List.getD_eq_getElem _ _ h1', getD_buIdxLbl hi, buIdxF_cons] at h
  rw [List.getD_eq_getElem _ _ h2, List.getElem_map,
    ← List.getD_eq_getElem _ _ (by rw [buQWhs_length]; exact hi)] at h
  exact Val.int.inj h

end Work.Resample
