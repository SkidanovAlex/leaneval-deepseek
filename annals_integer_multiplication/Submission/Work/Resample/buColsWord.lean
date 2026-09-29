import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buColsDefs
import Submission.Work.Resample.buHsWord
import Submission.Work.Resample.buColWord
import Submission.Work.Resample.buColsCostArith
import Submission.Work.Resample.auMapListTail
import Submission.Work.Resample.buQWhs

set_option autoImplicit false
set_option maxHeartbeats 50000000

namespace Work.Resample

open HvdH

/-- The function computed by one element of the outer `mapList`: a shift `h` becomes the column
`buCol p α s t h`. -/
noncomputable def buColF (p α s t : ℕ) : Val → Val
  | .int h => buCol p α s t h
  | _ => .nil

theorem buColF_int (p α s t : ℕ) (h : ℤ) : buColF p α s t (.int h) = buCol p α s t h := rfl

/-- The function computed by one element of the last `mapList`: the index label `i` is replaced by
the shift `buHidx p α i`, the column is kept. -/
def buLblF (p α : ℕ) : Val → Val
  | .cons (.int i) c => .cons (.int (buHidx p α i)) c
  | _ => .nil

theorem buLblF_cons (p α : ℕ) (i : ℤ) (c : Val) :
    buLblF p α (.cons (.int i) c) = .cons (.int (buHidx p α i)) c := rfl

/-- The column list read at an index. -/
theorem getD_cols (p α s t : ℕ) {i : ℕ} (hi : i < (egHs (egM p α)).length) :
    (((egHs (egM p α)).map Val.int).map (buColF p α s t)).getD i .nil
      = buCol p α s t ((egHs (egM p α)).getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    ← List.getD_eq_getElem _ _ (by simpa using hi), getD_shift hi]
  rfl

/-- The column word: from the parameter block `buCB p α s t` it produces the list of the `2·egM p α`
labelled weight columns `buL10 p α s t` on top of the block.

Program: `buHsWord` (the shift list), `mapList buColWord` (the columns), `enumerate` (label them by
their index), then `mapList` with the element word `uncons; buArithWord; consV`, which turns the
index `i` into the shift `buHidx p α i`. -/
theorem buColsWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (wtProg : HvdH.Cmd) (Kw : ℕ)
    (wtSpec : ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ h : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hh : h.natAbs ≤ Work.Resample.egM p α),
      ∀ rest : List HvdH.Val, HvdH.WordR main wtProg
        (fun vs => vs = [HvdH.Val.int ℓ, HvdH.Val.int h] ++ Work.Resample.buCB p α s t ++ rest)
        (fun vs out => vs = [HvdH.Val.int ℓ, HvdH.Val.int h] ++ Work.Resample.buCB p α s t ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.buWt p α s t ℓ h)] ++ Work.Resample.buCB p α s t ++ rest)
        (fun _ => Kw * (p + 1) ^ Kw)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main prog (Work.Resample.buCB p α s t)
        (Work.Resample.buL10 p α s t :: Work.Resample.buCB p α s t)
        (K * (Work.Resample.egM p α + 1) * (s + 1) * (p + 1) ^ K) := by
  obtain ⟨hsProg, Kl, hHs⟩ := buHsWord KL IL LL
  obtain ⟨colProg, Kc, hCol⟩ := buColWord KL IL LL wtProg Kw wtSpec
  obtain ⟨combML, Kml, hML⟩ := MapListField.of_kernel KL
  obtain ⟨enumProg, Ke, hEnum⟩ := LL.enumerate
  obtain ⟨uncProg, Kuc, hUc⟩ := KL.unconsV
  obtain ⟨arProg, KAR, hAr⟩ := buArithWord KL IL
  obtain ⟨consProg, Kcs, hCs⟩ := KL.consV
  refine ⟨Cmd.seq hsProg (Cmd.seq (combML colProg)
      (Cmd.seq enumProg (combML (Cmd.seq uncProg (Cmd.seq arProg consProg))))),
    buColsK Kl Kc Kml Ke KAR Kuc Kcs, ?_⟩
  intro main p α s t hs hst hα hp htp hαp
  set Λ : ℕ := buColsK Kl Kc Kml Ke KAR Kuc Kcs with hΛ
  let B : ℕ := buSZ p
  let L : ℕ := buLout p s
  let xs : List Val := (egHs (egM p α)).map Val.int
  let cols : List Val := xs.map (buColF p α s t)
  let lbls : List Val := (List.range (2 * egM p α)).map
    (fun i : ℕ => .cons (.int (i : ℤ)) (cols.getD i .nil))
  have hBL : B ≤ L := by simp only [B, L, buLout]; omega
  have hL1 : 1 ≤ L := le_trans (by simp only [B, buSZ]; omega) hBL
  -- 1. the shift list
  have s1 : Pipe main hsProg (buCB p α s t) (zl (egHs (egM p α)) :: buCB p α s t)
      (Kl * (egM p α + 1) * (p + 1) ^ Kl) := hHs main p α s t hs hst hα hp htp hαp
  -- 2. the columns
  have hx2 : ∀ x ∈ xs, vsz x ≤ L := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    have hnat : h.natAbs ≤ egM p α := ((buQWhs_egHs_mem_iff (egM p α) h).mp hh).2
    have hsz : isz h ≤ B := isz_le_buSZ_two_pow hp
      (le_trans hnat (le_trans (egM_le p α) (by have := Nat.lt_two_pow_self (n := p); omega)))
    rw [Work.Fx.vsz_int]
    simp only [L, buLout]
    omega
  have hy2 : ∀ x ∈ xs, vsz (buColF p α s t x) ≤ L := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    have hnat : h.natAbs ≤ egM p α := ((buQWhs_egHs_mem_iff (egM p α) h).mp hh).2
    have hsz := vsz_buCol_le h hs hst hα hp htp hαp hnat
    rw [buColF_int]
    simp only [L, buLout]
    omega
  have h2 : ∀ x ∈ xs, Pipe main colProg (x :: buCB p α s t) (buColF p α s t x :: buCB p α s t)
      (Kc * (s + 1) * (p + 1) ^ Kc) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    have hnat : h.natAbs ≤ egM p α := ((buQWhs_egHs_mem_iff (egM p α) h).mp hh).2
    exact hCol main p α s t hs hst hα hp htp hαp h hnat
  have s2 : Pipe main (combML colProg) (zl (egHs (egM p α)) :: buCB p α s t)
      (ofList cols :: buCB p α s t)
      (xs.length * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (L + 1)) + Kml) :=
    auMapListTail (main := main) (q := colProg) (T := buCB p α s t) (xs := xs)
      (F := buColF p α s t) (c := Kc * (s + 1) * (p + 1) ^ Kc) (L := L) hML h2 hx2 hy2
  have hxslen : xs.length = 2 * egM p α := by
    simp only [xs, List.length_map, buQWhs_length]
  have hcolslen : cols.length = 2 * egM p α := by
    simp only [cols, List.length_map, hxslen]
  -- 3. enumerate the columns
  have hvszcols : vsz (ofList cols) ≤ (2 * egM p α + 1) * (L + 1) := by
    have h := buCol_vsz_ofList_le (l := cols) (B := L) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hy2 y hy)
    rw [hcolslen] at h
    exact h
  have hsz2m : (2 * egM p α).size + 1 ≤ 2 * (p + 1) := by
    have h := size_two_egM_le p α (by omega)
    omega
  have h3poly : Ke * (vsz (ofList cols) + cols.length * (cols.length.size + 1) + 1)
      ≤ Ke * ((2 * egM p α + 1) * (L + 1) + (2 * egM p α) * (2 * (p + 1)) + 1) := by
    refine Nat.mul_le_mul_left _ ?_
    have h2 : cols.length * (cols.length.size + 1) ≤ (2 * egM p α) * (2 * (p + 1)) := by
      rw [hcolslen]
      exact Nat.mul_le_mul_left _ hsz2m
    omega
  have s3 : Pipe main enumProg (ofList cols :: buCB p α s t) (ofList lbls :: buCB p α s t)
      (Ke * ((2 * egM p α + 1) * (L + 1) + (2 * egM p α) * (2 * (p + 1)) + 1)) := by
    have hen := Pipe.appendTail (main := main) (buCB p α s t)
      (Pipe.enumerate (main := main) hEnum (xs := cols))
    refine Pipe.le (Pipe.rw hen ?_) h3poly
    show ofList ((List.range cols.length).map (fun i : ℕ => Val.cons (.int (i : ℤ))
      (cols.getD i .nil))) :: buCB p α s t = ofList lbls :: buCB p α s t
    dsimp only [lbls]
    rw [hcolslen]
  -- 4. label the columns
  have hcolval : ∀ i < 2 * egM p α, cols.getD i .nil = buCol p α s t (buHidx p α (i : ℤ)) := by
    intro i hi
    have hi' : i < (egHs (egM p α)).length := by rw [buQWhs_length]; exact hi
    dsimp only [cols, xs]
    rw [getD_cols p α s t hi', ← buHidx_eq_getD p α hi]
  have hcolsz : ∀ i < 2 * egM p α, vsz (cols.getD i .nil) ≤ L := by
    intro i hi
    have hh : (buHidx p α (i : ℤ)).natAbs ≤ egM p α := natAbs_buHidx_le p α (by omega) (by omega)
    rw [hcolval i hi]
    have h1 := vsz_buCol_le (buHidx p α (i : ℤ)) hs hst hα hp htp hαp hh
    simp only [L, buLout]
    omega
  have hcolsz' : ∀ i < 2 * egM p α, vsz (cols.getD i .nil) ≤ (s + 1) * (B + 1) := by
    intro i hi
    have hh : (buHidx p α (i : ℤ)).natAbs ≤ egM p α := natAbs_buHidx_le p α (by omega) (by omega)
    rw [hcolval i hi]
    exact vsz_buCol_le (buHidx p α (i : ℤ)) hs hst hα hp htp hαp hh
  have hisz2m : ∀ i < 2 * egM p α, isz ((i : ℤ)) ≤ L := by
    intro i hi
    have h1 : isz ((i : ℤ)) ≤ B := isz_nat_le_buSZ_four_pow hp
      (le_trans (le_of_lt hi) (two_egM_le_four_pow α (by omega)))
    simp only [L, B, buLout] at h1 ⊢
    omega
  have h4elem : ∀ x ∈ lbls, Pipe main (Cmd.seq uncProg (Cmd.seq arProg consProg))
      (x :: buCB p α s t) (buLblF p α x :: buCB p α s t) (Kuc + (KAR * (L + 1) + Kcs)) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi2 : i < 2 * egM p α := List.mem_range.mp hi
    have h5 : Pipe main uncProg (.cons (.int (i : ℤ)) (cols.getD i .nil) :: buCB p α s t)
        (.int (i : ℤ) :: cols.getD i .nil :: buCB p α s t) Kuc :=
      Pipe.appendTail (main := main) (buCB p α s t)
        (Pipe.unconsVbu (main := main) hUc (.int (i : ℤ)) (cols.getD i .nil))
    have h6 : Pipe main arProg (.int (i : ℤ) :: cols.getD i .nil :: buCB p α s t)
        (.int (buHidx p α (i : ℤ)) :: cols.getD i .nil :: buCB p α s t) (KAR * (L + 1)) :=
      hAr main p α s t hs hst hα hp htp hαp (i : ℤ) (cols.getD i .nil) L
        (hcolsz i hi2) (hisz2m i hi2) hBL
    have h7 : Pipe main consProg (.int (buHidx p α (i : ℤ)) :: cols.getD i .nil :: buCB p α s t)
        (.cons (.int (buHidx p α (i : ℤ))) (cols.getD i .nil) :: buCB p α s t) Kcs :=
      Pipe.appendTail (main := main) (buCB p α s t)
        (Pipe.consVbu (main := main) hCs (.int (buHidx p α (i : ℤ))) (cols.getD i .nil))
    exact Pipe.comp h5 (Pipe.comp h6 h7)
  have hx4 : ∀ x ∈ lbls, vsz x ≤ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi2 : i < 2 * egM p α := List.mem_range.mp hi
    have his : isz ((i : ℤ)) ≤ B := isz_nat_le_buSZ_four_pow hp
      (le_trans (le_of_lt hi2) (two_egM_le_four_pow α (by omega)))
    rw [Work.Fx.vsz_cons, Work.Fx.vsz_int]
    have h2 := hcolsz' i hi2
    simp only [L, B, buLout] at his h2 ⊢
    omega
  have hy4 : ∀ x ∈ lbls, vsz (buLblF p α x) ≤ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi2 : i < 2 * egM p α := List.mem_range.mp hi
    have hbhidx : isz (buHidx p α (i : ℤ)) ≤ B :=
      isz_buHidx_le p α hp (by omega) (by omega)
    rw [buLblF_cons, Work.Fx.vsz_cons, Work.Fx.vsz_int]
    have h2 := hcolsz' i hi2
    simp only [L, B, buLout] at hbhidx h2 ⊢
    omega
  have s4 : Pipe main (combML (Cmd.seq uncProg (Cmd.seq arProg consProg))) (ofList lbls :: buCB p α s t)
      (ofList (lbls.map (buLblF p α)) :: buCB p α s t)
      (lbls.length * ((Kuc + (KAR * (L + 1) + Kcs)) + Kml * (L + 1)) + Kml) :=
    auMapListTail (main := main) (q := Cmd.seq uncProg (Cmd.seq arProg consProg))
      (T := buCB p α s t) (xs := lbls) (F := buLblF p α)
      (c := Kuc + (KAR * (L + 1) + Kcs)) (L := L) hML h4elem hx4 hy4
  have hlblslen : lbls.length = 2 * egM p α := by
    simp only [lbls, List.length_map, List.length_range]
  -- the final list identity
  have hpoint : ∀ i ∈ List.range (2 * egM p α),
      cols.getD i .nil = buCol p α s t (buHidx p α (i : ℤ)) :=
    fun i hi => hcolval i (List.mem_range.mp hi)
  have hlast : lbls.map (buLblF p α)
      = (egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h)) := by
    have hL : lbls.map (buLblF p α)
        = (List.range (2 * egM p α)).map (fun i : ℕ => Val.cons (.int (buHidx p α (i : ℤ)))
            (cols.getD i .nil)) := by
      show (List.map (buLblF p α) ((List.range (2 * egM p α)).map
        (fun i : ℕ => Val.cons (.int (i : ℤ)) (cols.getD i .nil)))) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      rfl
    have hR : (egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h))
        = (List.range (2 * egM p α)).map (fun i : ℕ => Val.cons (.int (buHidx p α (i : ℤ)))
            (buCol p α s t (buHidx p α (i : ℤ)))) := by
      rw [← map_range_getD (egHs (egM p α)) (fun h => Val.cons (.int h) (buCol p α s t h)) 0,
        buQWhs_length]
      apply List.map_congr_left
      intro i hi
      rw [buHidx_eq_getD p α (List.mem_range.mp hi)]
    rw [hL, hR]
    apply List.map_congr_left
    intro i hi
    rw [hpoint i hi]
  -- the cost
  have h1cost : Kl * (egM p α + 1) * (p + 1) ^ Kl
      ≤ Kl * (egM p α + 1) * (p + 1) ^ Kl := le_rfl
  have h2cost : xs.length * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (L + 1)) + Kml
      ≤ (2 * egM p α) * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (buLout p s + 1)) + Kml := by
    rw [hxslen]
  have h3cost : Ke * ((2 * egM p α + 1) * (L + 1) + (2 * egM p α) * (2 * (p + 1)) + 1)
      ≤ Ke * ((2 * egM p α + 1) * (buLout p s + 1) + (2 * egM p α) * (2 * (p + 1)) + 1) :=
    le_of_eq rfl
  have h4cost : lbls.length * ((Kuc + (KAR * (L + 1) + Kcs)) + Kml * (L + 1)) + Kml
      ≤ (2 * egM p α) * (Kuc + (KAR * (buLout p s + 1) + Kcs) + Kml * (buLout p s + 1)) + Kml := by
    rw [hlblslen]
  have hcost := buColsCostArith p α s Kl Kc Kml Ke KAR Kuc Kcs
    (Kl * (egM p α + 1) * (p + 1) ^ Kl)
    (xs.length * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (L + 1)) + Kml)
    (Ke * ((2 * egM p α + 1) * (L + 1) + (2 * egM p α) * (2 * (p + 1)) + 1))
    (lbls.length * ((Kuc + (KAR * (L + 1) + Kcs)) + Kml * (L + 1)) + Kml)
    hs hp hα h1cost h2cost h3cost h4cost
  -- assembly
  intro rest0
  have g1 : WordR main hsProg (fun vs => vs = buCB p α s t ++ rest0)
      (fun _ out => out = (zl (egHs (egM p α)) :: buCB p α s t) ++ rest0)
      (fun _ => Kl * (egM p α + 1) * (p + 1) ^ Kl) := s1 rest0
  have g2 : WordR main (combML colProg)
      (fun vs => vs = (zl (egHs (egM p α)) :: buCB p α s t) ++ rest0)
      (fun _ out => out = (ofList cols :: buCB p α s t) ++ rest0)
      (fun _ => xs.length * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (L + 1)) + Kml) := s2 rest0
  have g3 : WordR main enumProg (fun vs => vs = (ofList cols :: buCB p α s t) ++ rest0)
      (fun _ out => out = (ofList lbls :: buCB p α s t) ++ rest0)
      (fun _ => Ke * ((2 * egM p α + 1) * (L + 1) + (2 * egM p α) * (2 * (p + 1)) + 1)) :=
    s3 rest0
  have g4 : WordR main (combML (Cmd.seq uncProg (Cmd.seq arProg consProg)))
      (fun vs => vs = (ofList lbls :: buCB p α s t) ++ rest0)
      (fun _ out => out = (ofList (lbls.map (buLblF p α)) :: buCB p α s t) ++ rest0)
      (fun _ => lbls.length * ((Kuc + (KAR * (L + 1) + Kcs)) + Kml * (L + 1)) + Kml) := s4 rest0
  have gtot := buCol_comp g1 (buCol_comp g2 (buCol_comp g3 g4))
  refine Work.Kernel.WordR_conseq gtot (fun vs hv => hv) ?_ ?_
  · intro vs out hv hout
    rw [hout]
    have hW : ofList (lbls.map (buLblF p α)) = buL10 p α s t :=
      congrArg ofList hlast
    rw [hW]
  · intro vs _
    exact hcost

end Work.Resample
