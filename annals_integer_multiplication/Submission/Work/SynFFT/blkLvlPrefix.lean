import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.hasSplitWord

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Small helper lemmas -/

/-- `m / 2` computed by the `Int` shift-right word is the natural-number quotient. -/
lemma tdiv_two (m : ℕ) : Int.tdiv (m : ℤ) ((2 : ℤ) ^ (1 : ℤ).toNat) = ((m / 2 : ℕ) : ℤ) := by
  have h1 : ((2:ℤ) ^ (1:ℤ).toNat) = 2 := by norm_num
  rw [h1, Int.tdiv_eq_ediv_of_nonneg (show (0:ℤ) ≤ (m:ℤ) by exact_mod_cast Nat.zero_le m)]
  exact (Int.natCast_ediv m 2).symm

/-- `m - m/2` is the `Int` difference of `m` and `m/2`. -/
lemma sub_div_two (m : ℕ) : (m : ℤ) - ((m / 2 : ℕ) : ℤ) = ((m - m / 2 : ℕ) : ℤ) := by
  rw [← Nat.cast_sub (Nat.div_le_self m 2)]

lemma isz_natCast (k : ℕ) : isz (k : ℤ) = k.size + 2 := by simp [isz]

lemma isz_natCast_le {k m : ℕ} (h : k ≤ m) : isz (k : ℤ) ≤ isz (m : ℤ) := by
  rw [isz_natCast, isz_natCast]; exact Nat.add_le_add_right (Nat.size_le_size h) 2

/-- Dropping entries of a list of values cannot increase the size of its encoding. -/
lemma vsz_ofList_take_le_pre (xs : List Val) (s : ℕ) : vsz (ofList (xs.take s)) ≤ vsz (ofList xs) := by
  rw [MrgKit.vsz_ofList, MrgKit.vsz_ofList, List.length_take]
  have h2 : ((xs.take s).map vsz).sum ≤ (xs.map vsz).sum := by
    have h := List.sum_take_add_sum_drop (xs.map vsz) s
    rw [← List.map_take, ← List.map_drop] at h
    omega
  have h1 : (xs.take s).length ≤ xs.length := by simp
  omega

/-- Generic `BinOp` word step: turn a `BinOp` specification into a `WordR` on a concrete stack. -/
lemma binOpStep' {main : Cmd} {p : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main p P f C) (a b : ℤ) (hab : P a b) (t : List Val) (D : ℕ)
    (hD : C a b ≤ D) :
    WordR main p (fun vs => vs = .int a :: .int b :: t)
      (fun _ out => out = .int (f a b) :: t) (fun _ => D) := by
  unfold BinOp at h
  refine MrgKit.WordR_conseqC h ⟨a, b, t, rfl, hab⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

/-- `a * b ≤ C * B` from `b ≤ n * B` and `a * n ≤ C`. -/
lemma costBound3 {a b n B C : ℕ} (h1 : b ≤ n * B) (h2 : a * n ≤ C) : a * b ≤ C * B := by
  calc a * b ≤ a * (n * B) := Nat.mul_le_mul_left a h1
    _ = (a * n) * B := by ring
    _ ≤ C * B := Nat.mul_le_mul_right B h2

/-- Reindexing word used by the block-level-pass prefix: from `int m :: X :: rest` it produces
`int (m - m/2) :: X :: int (m/2) :: X :: rest`, for an arbitrary value `X` (the tail `rest` is
untouched -- in particular the word must not pay for the values in `rest`, which is why it only
ever uses `X` and the two computed integers). -/
theorem blkLvlIdxSplit (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X : HvdH.Val) (rest : List HvdH.Val) (m : ℕ),
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (m : ℤ) :: X :: rest)
        (fun vs out => out = HvdH.Val.int ((m - m / 2 : ℕ) : ℤ) :: X ::
          HvdH.Val.int ((m / 2 : ℕ) : ℤ) :: X :: rest)
        (fun _ => K * (HvdH.vsz X + HvdH.isz (m : ℤ) + 1) + K) := by
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨shP, Ksh, hsh⟩ := hi.shrT
  obtain ⟨subP, Ksb, hsb⟩ := hi.sub
  refine ⟨dupP ;;; pushP (.int 1) ;;; rollP 1 ;;; shP ;;; dupP ;;; rollP 2 ;;; subP ;;; pickP 2 ;;; rollP 1,
    9 * (60 * (Kd + Kp + Kr + Kpv + Ksh + Ksb + 1)), ?_⟩
  intro main X rest m
  set C : ℕ := 60 * (Kd + Kp + Kr + Kpv + Ksh + Ksb + 1) with hC
  set B : ℕ := vsz X + isz (m : ℤ) + 1 with hB
  set D : ℕ := C * B with hD
  have h1 : isz (1:ℤ) = 3 := by simp [isz, Nat.size_one]
  have hiszm2 : 2 ≤ isz (m:ℤ) := by rw [isz_natCast]; omega
  have hisz2 : isz ((m / 2 : ℕ) : ℤ) ≤ isz (m : ℤ) := isz_natCast_le (Nat.div_le_self m 2)
  have hisz3 : isz ((m - m / 2 : ℕ) : ℤ) ≤ isz (m : ℤ) := isz_natCast_le (Nat.sub_le m (m / 2))
  have hB1 : 1 ≤ B := by rw [hB]; omega
  have e1 : WordR main dupP (fun vs => vs = .int (m:ℤ) :: X :: rest)
      (fun _ out => out = .int (m:ℤ) :: .int (m:ℤ) :: X :: rest) (fun _ => D) :=
    MrgKit.dupStep (hdup main) (.int (m:ℤ)) (X :: rest) D (by
      rw [hD]
      have hb : vsz (.int (m:ℤ)) + 1 ≤ 1 * B := by
        rw [one_mul, Work.SynFFT.MrgKit.vsz_int', hB]; omega
      have h2 : Kd * 1 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2)
  have e2 : WordR main (pushP (.int 1)) (fun vs => vs = .int (m:ℤ) :: .int (m:ℤ) :: X :: rest)
      (fun _ out => out = .int (1:ℤ) :: .int (m:ℤ) :: .int (m:ℤ) :: X :: rest) (fun _ => D) :=
    MrgKit.pushStep (fun v => hpush main v) (.int (1:ℤ)) (.int (m:ℤ) :: .int (m:ℤ) :: X :: rest) D (by
      rw [hD]
      have hb : vsz (.int (1:ℤ)) + 1 ≤ 4 * B := by
        rw [Work.SynFFT.MrgKit.vsz_int', h1, hB]; omega
      have h2 : Kpv * 4 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2)
  have e3 : WordR main (rollP 1) (fun vs => vs = .int (1:ℤ) :: .int (m:ℤ) :: .int (m:ℤ) :: X :: rest)
      (fun _ out => out = .int (m:ℤ) :: .int (1:ℤ) :: .int (m:ℤ) :: X :: rest) (fun _ => D) := by
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (fun k => hroll main k) 1
      (.int (1:ℤ) :: .int (m:ℤ) :: .int (m:ℤ) :: X :: rest) (by simp) D ?_) rfl ?_ le_rfl
    · rw [hD]
      have hb : (((.int (1:ℤ) :: .int (m:ℤ) :: .int (m:ℤ) :: X :: rest : List HvdH.Val).take (1+1)).map vsz).sum + 1 ≤ 4 * B := by
        rw [hB]
        simp only [Work.SynFFT.MrgKit.vsz_int', List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, h1]
        omega
      have h2 : (Kr * (1+1)) * 4 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2
    · intro out hout; rw [hout]; simp
  have e4 : WordR main shP (fun vs => vs = .int (m:ℤ) :: .int (1:ℤ) :: .int (m:ℤ) :: X :: rest)
      (fun _ out => out = .int ((m/2:ℕ):ℤ) :: .int (m:ℤ) :: X :: rest) (fun _ => D) := by
    have hcost : Ksh * (isz (m:ℤ) + isz (1:ℤ)) ≤ D := by
      rw [hD]
      have hb : isz (m:ℤ) + isz (1:ℤ) ≤ 2 * B := by rw [h1, hB]; omega
      have h2 : Ksh * 2 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2
    have h := binOpStep' (hsh main) (m:ℤ) (1:ℤ) (by norm_num) (.int (m:ℤ) :: X :: rest) D hcost
    simpa only [tdiv_two] using h
  have e5 : WordR main dupP (fun vs => vs = .int ((m/2:ℕ):ℤ) :: .int (m:ℤ) :: X :: rest)
      (fun _ out => out = .int ((m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: .int (m:ℤ) :: X :: rest) (fun _ => D) :=
    MrgKit.dupStep (hdup main) (.int ((m/2:ℕ):ℤ)) (.int (m:ℤ) :: X :: rest) D (by
      rw [hD]
      have hb : vsz (.int ((m/2:ℕ):ℤ)) + 1 ≤ 1 * B := by
        rw [one_mul, Work.SynFFT.MrgKit.vsz_int', hB]; omega
      have h2 : Kd * 1 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2)
  have e6 : WordR main (rollP 2) (fun vs => vs = .int ((m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: .int (m:ℤ) :: X :: rest)
      (fun _ out => out = .int (m:ℤ) :: .int ((m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest) (fun _ => D) := by
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (fun k => hroll main k) 2
      (.int ((m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: .int (m:ℤ) :: X :: rest) (by simp) D ?_) rfl ?_ le_rfl
    · rw [hD]
      have hb : (((.int ((m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: .int (m:ℤ) :: X :: rest : List HvdH.Val).take (2+1)).map vsz).sum + 1 ≤ 4 * B := by
        rw [hB]
        simp only [Work.SynFFT.MrgKit.vsz_int', List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]
        omega
      have h2 : (Kr * (2+1)) * 4 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2
    · intro out hout; rw [hout]; simp
  have e7 : WordR main subP (fun vs => vs = .int (m:ℤ) :: .int ((m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest)
      (fun _ out => out = .int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest) (fun _ => D) := by
    have hcost : Ksb * (isz (m:ℤ) + isz ((m/2:ℕ):ℤ)) ≤ D := by
      rw [hD]
      have hb : isz (m:ℤ) + isz ((m/2:ℕ):ℤ) ≤ 2 * B := by rw [hB]; omega
      have h2 : Ksb * 2 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2
    have h := binOpStep' (hsb main) (m:ℤ) ((m/2:ℕ):ℤ) trivial (.int ((m/2:ℕ):ℤ) :: X :: rest) D hcost
    simpa only [sub_div_two] using h
  have e8 : WordR main (pickP 2) (fun vs => vs = .int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest)
      (fun _ out => out = X :: .int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest) (fun _ => D) := by
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (fun k => hpick main k) 2
      (.int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest) (by simp) D ?_) rfl ?_ le_rfl
    · rw [hD]
      have hb : (((.int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest : List HvdH.Val).take (2+1)).map vsz).sum + 1 ≤ 4 * B := by
        rw [hB]
        simp only [Work.SynFFT.MrgKit.vsz_int', List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]
        omega
      have h2 : (Kp * (2+1)) * 4 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2
    · intro out hout; rw [hout]; simp
  have e9 : WordR main (rollP 1) (fun vs => vs = X :: .int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest)
      (fun _ out => out = .int ((m - m/2:ℕ):ℤ) :: X :: .int ((m/2:ℕ):ℤ) :: X :: rest) (fun _ => D) := by
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (fun k => hroll main k) 1
      (X :: .int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest) (by simp) D ?_) rfl ?_ le_rfl
    · rw [hD]
      have hb : (((X :: .int ((m - m/2:ℕ):ℤ) :: .int ((m/2:ℕ):ℤ) :: X :: rest : List HvdH.Val).take (1+1)).map vsz).sum + 1 ≤ 4 * B := by
        rw [hB]
        simp only [Work.SynFFT.MrgKit.vsz_int', List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]
        omega
      have h2 : (Kr * (1+1)) * 4 ≤ C := by rw [hC]; omega
      exact costBound3 hb h2
    · intro out hout; rw [hout]; simp
  have echain := MrgKit.WordR_seqC e1 (MrgKit.WordR_seqC e2 (MrgKit.WordR_seqC e3
    (MrgKit.WordR_seqC e4 (MrgKit.WordR_seqC e5 (MrgKit.WordR_seqC e6
    (MrgKit.WordR_seqC e7 (MrgKit.WordR_seqC e8 e9)))))))
  have htot : (D + (D + (D + (D + (D + (D + (D + (D + D)))))))) ≤ 9 * D := by omega
  have hfinal : 9 * D ≤ (9 * C) * B + 9 * C := by
    rw [hD]
    have : 9 * (C * B) = (9 * C) * B := by ring
    rw [this]
    exact Nat.le_add_right _ _
  exact MrgKit.WordR_weaken echain (fun vs hvs => hvs) (fun vs out hvs hout => hout)
    (fun vs hvs => le_trans htot hfinal)

/-- Enumerating the first `m - m/2` entries of `cvecs ws` gives the tagged list used by the
block-level-pass prefix. -/
theorem blkLvlEnumEq (ws : List (List (ℤ × ℤ))) (m : ℕ) (hm : ws.length = m) :
    (List.range ((Work.SynFFT.cvecs ws).take (m - m / 2)).length).map
        (fun i : ℕ => HvdH.Val.cons (HvdH.Val.int (i : ℤ))
          (((Work.SynFFT.cvecs ws).take (m - m / 2)).getD i HvdH.Val.nil))
      = (List.range (m - m / 2)).map
        (fun i : ℕ => HvdH.Val.cons (HvdH.Val.int (i : ℤ))
          ((Work.SynFFT.cvecs ws).getD i HvdH.Val.nil)) := by
  have hlen : (Work.SynFFT.cvecs ws).length = m := by
    rw [Work.SynFFT.cvecs, List.length_map, hm]
  have hlt : m - m / 2 ≤ (Work.SynFFT.cvecs ws).length := by omega
  rw [List.length_take, min_eq_left hlt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-- The prefix of the block level pass word: from `cvecVal`-list of the `m` input vectors it
produces the two halves of the `zipWith` of `blkLvlPairWord`, on whose stack the parameters are
left in the order `sh, sgn, r, p, m`.

`R` is `cvecs (ws.drop (m/2))` (the right elements of the pairs) and `L` is the list of the first
`m - m/2` elements, *tagged with their index* (`LayoutLib.enumerate`), so that the per-pair word
can read its twiddle index `i` off the tag. -/
theorem blkLvlPrefix (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p r m sh : ℕ) (sgn : ℤ)
      (ws : List (List (ℤ × ℤ))) (rest : List HvdH.Val),
      2 ≤ m → m * 2 ^ sh = 2 * r → 2 * r < 2 ^ p → ws.length = m →
      (∀ w ∈ ws, HvdH.InDiscVec p r w) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList (Work.SynFFT.cvecs ws) :: HvdH.Val.int (sh : ℤ) ::
          HvdH.Val.int sgn :: HvdH.Val.int (r : ℤ) ::
          HvdH.Val.int (p : ℤ) :: HvdH.Val.int (m : ℤ) :: rest)
        (fun vs out => ∃ (L R : List HvdH.Val),
          out = HvdH.ofList L :: HvdH.ofList R :: HvdH.Val.int (sh : ℤ) ::
            HvdH.Val.int sgn :: HvdH.Val.int (r : ℤ) ::
            HvdH.Val.int (p : ℤ) :: HvdH.Val.int (m : ℤ) :: rest ∧
          R = Work.SynFFT.cvecs (ws.drop (m / 2)) ∧
          L = (List.range (m - m / 2)).map
            (fun i : ℕ => HvdH.Val.cons (HvdH.Val.int (i : ℤ)) ((Work.SynFFT.cvecs ws).getD i HvdH.Val.nil)))
        (fun _ => K * (m * (r + 1) * (p + 1) + 1) + K) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨lenP, Kl, hlen⟩ := hl.length
  obtain ⟨tkP, Kt, htk⟩ := hl.take
  obtain ⟨drP, Kdr, hdr⟩ := hl.drop
  obtain ⟨enP, Ke, hen⟩ := hl.enumerate
  obtain ⟨idxP, Kidx, hidx⟩ := blkLvlIdxSplit hk hi
  set Cb : ℕ := 200 * (Kl + Kt + Kdr + Ke + Kr + Kidx + 1) with hCb
  refine ⟨lenP ;;; idxP ;;; tkP ;;; rollP 2 ;;; rollP 2 ;;; drP ;;; rollP 1 ;;; enP, 8 * Cb, ?_⟩
  intro main p r m sh sgn ws rest h2 hmul hp hwlen hdisc
  set M : ℕ := m * (r + 1) * (p + 1) + 1 with hM
  set V : ℕ := vsz (ofList (cvecs ws)) with hV
  set Vt : ℕ := vsz (ofList ((cvecs ws).take (m - m / 2))) with hVt
  set Vr : ℕ := vsz (ofList ((cvecs ws).drop (m / 2))) with hVr
  set nlen : ℕ := ((cvecs ws).take (m - m / 2)).length with hnlen
  set Q : List Val := .int (sh:ℤ) :: .int sgn :: .int (r:ℤ) :: .int (p:ℤ) :: .int (m:ℤ) :: rest with hQ
  have hlenC : (cvecs ws).length = m := by rw [Work.SynFFT.cvecs, List.length_map, hwlen]
  have hmle : m ≤ 2 * r := by
    have h1 : m ≤ m * 2 ^ sh := Nat.le_mul_of_pos_right m (by positivity : 0 < 2 ^ sh)
    rwa [hmul] at h1
  have hm2p : m < 2 ^ p := lt_of_le_of_lt hmle hp
  have hmsz : m.size ≤ p := (Nat.size_le).mpr hm2p
  have hmK1 : m ≤ m * (r + 1) := by
    have h := Nat.mul_le_mul_left m (show 1 ≤ r + 1 by omega)
    simpa using h
  have hmK : m ≤ m * (r + 1) * (p + 1) := by
    have h := Nat.mul_le_mul_left (m * (r + 1)) (show 1 ≤ p + 1 by omega)
    exact le_trans hmK1 (by simpa using h)
  have hM1 : 1 ≤ M := by rw [hM]; omega
  have hV15 : V ≤ 15 * M := by
    rw [hV, hM]
    have hbound := MrgKit.vsz_ofList_le_of_bound (cvecs ws) (13 * (r + 1) * (p + 1)) m
      (by
        intro v hv
        rw [Work.SynFFT.cvecs, List.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact MrgKit.vsz_cvecVal_le p r w (hdisc w hw).1 (hdisc w hw).2)
      (by rw [Work.SynFFT.cvecs, List.length_map, hwlen])
    nlinarith [hbound, hmK]
  have hVtV : Vt ≤ V := by rw [hVt, hV]; exact vsz_ofList_take_le_pre (cvecs ws) (m - m / 2)
  have hVrV : Vr ≤ V := by rw [hVr, hV]; exact vsz_ofList_drop_le (cvecs ws) (m / 2)
  have hPz2 : isz (m:ℤ) ≤ 2 * M := by
    rw [hM, isz_natCast]
    have hmK2 : 2 * (p + 1) ≤ m * (r + 1) * (p + 1) := by
      have h2m : 2 ≤ m * (r + 1) := le_trans h2 hmK1
      exact Nat.mul_le_mul_right (p + 1) h2m
    linarith [hmsz, hmK2]
  have hPh2 : isz ((m / 2 : ℕ) : ℤ) ≤ 2 * M := le_trans (isz_natCast_le (Nat.div_le_self m 2)) hPz2
  have hPm2 : isz ((m - m / 2 : ℕ) : ℤ) ≤ 2 * M :=
    le_trans (isz_natCast_le (Nat.sub_le m (m / 2))) hPz2
  have hnlen_eq : nlen = m - m / 2 := by
    rw [hnlen, List.length_take, hlenC, min_eq_left (Nat.sub_le m (m / 2))]
  have hnlM : nlen * (nlen.size + 1) ≤ M := by
    have hn1 : nlen ≤ m := by omega
    have hn2 : nlen.size ≤ p := le_trans (Nat.size_le_size hn1) hmsz
    have h3 : nlen * (nlen.size + 1) ≤ m * (p + 1) := Nat.mul_le_mul hn1 (by omega)
    have h4 : m * (p + 1) ≤ m * (r + 1) * (p + 1) := Nat.mul_le_mul_right (p + 1) hmK1
    rw [hM]; linarith [h3, h4]
  have hMpos : 0 < M := by rw [hM]; positivity
  -- ### step 1: length of the list gives `m`
  have eL : WordR main lenP
      (fun vs => vs = ofList (cvecs ws) :: Q)
      (fun _ out => out = .int (m:ℤ) :: ofList (cvecs ws) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Kl * (vsz (ofList (cvecs ws)) + 1) ≤ Cb * M := by
      have h1 : vsz (ofList (cvecs ws)) + 1 ≤ 16 * M := by rw [← hV]; linarith [hV15, hM1]
      calc Kl * (vsz (ofList (cvecs ws)) + 1) ≤ Kl * (16 * M) := Nat.mul_le_mul_left Kl h1
        _ = (Kl * 16) * M := by ring
        _ ≤ Cb * M := Nat.mul_le_mul_right M (by rw [hCb]; omega)
    refine MrgKit.WordR_conseqC (hlen main (cvecs ws)) ⟨Q, rfl⟩ ?_ hcost
    intro out hout
    obtain ⟨r0, hv0, hout0⟩ := hout
    simp only [List.cons.injEq] at hv0
    obtain ⟨-, hr0⟩ := hv0
    rw [hout0, hr0, hlenC]
  -- ### step 2: reindex
  have eIdx : WordR main idxP
      (fun vs => vs = .int (m:ℤ) :: ofList (cvecs ws) :: Q)
      (fun _ out => out = .int ((m - m/2:ℕ):ℤ) :: ofList (cvecs ws) ::
        .int ((m/2:ℕ):ℤ) :: ofList (cvecs ws) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Kidx * (vsz (ofList (cvecs ws)) + isz (m:ℤ) + 1) + Kidx ≤ Cb * M := by
      have h1 : vsz (ofList (cvecs ws)) + isz (m:ℤ) + 1 ≤ 18 * M := by
        rw [← hV]; linarith [hV15, hPz2, hM1]
      have h2 : Kidx * 18 + Kidx ≤ Cb := by rw [hCb]; omega
      calc Kidx * (vsz (ofList (cvecs ws)) + isz (m:ℤ) + 1) + Kidx
          ≤ Kidx * (18 * M) + Kidx := Nat.add_le_add_right (Nat.mul_le_mul_left Kidx h1) _
        _ = (Kidx * 18) * M + Kidx := by ring
        _ ≤ (Kidx * 18) * M + Kidx * M :=
            Nat.add_le_add_left (Nat.le_mul_of_pos_right Kidx hMpos) _
        _ = (Kidx * 18 + Kidx) * M := by ring
        _ ≤ Cb * M := Nat.mul_le_mul_right M h2
    exact MrgKit.WordR_conseqC (hidx main (ofList (cvecs ws)) Q m) rfl (fun out hout => hout) hcost
  -- ### step 3: take the first `m - m/2` entries
  have eTk : WordR main tkP
      (fun vs => vs = .int ((m - m/2:ℕ):ℤ) :: ofList (cvecs ws) ::
        .int ((m/2:ℕ):ℤ) :: ofList (cvecs ws) :: Q)
      (fun _ out => out = ofList ((cvecs ws).take (m - m/2)) ::
        .int ((m/2:ℕ):ℤ) :: ofList (cvecs ws) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Kt * (vsz (ofList (cvecs ws)) + isz ((m - m/2:ℕ):ℤ) + 1) ≤ Cb * M := by
      have h1 : vsz (ofList (cvecs ws)) + isz ((m - m/2:ℕ):ℤ) + 1 ≤ 18 * M := by
        rw [← hV]; linarith [hV15, hPm2, hM1]
      exact costBound3 h1 (by rw [hCb]; omega)
    refine MrgKit.WordR_conseqC (htk main (m - m/2) (cvecs ws)) ⟨_, rfl⟩ ?_ hcost
    intro out hout
    obtain ⟨r0, hv0, hout0⟩ := hout
    simp only [List.cons.injEq, Val.int.injEq] at hv0
    obtain ⟨-, -, hr0⟩ := hv0
    rw [hout0, hr0]
  -- ### step 4: bring the second half list to the top
  have eR1 : WordR main (rollP 2)
      (fun vs => vs = ofList ((cvecs ws).take (m - m/2)) :: .int ((m/2:ℕ):ℤ) ::
        ofList (cvecs ws) :: Q)
      (fun _ out => out = ofList (cvecs ws) :: ofList ((cvecs ws).take (m - m/2)) ::
        .int ((m/2:ℕ):ℤ) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Kr * (2+1) * ((((ofList ((cvecs ws).take (m - m/2)) :: .int ((m/2:ℕ):ℤ) ::
        ofList (cvecs ws) :: Q : List Val).take (2+1)).map vsz).sum + 1) ≤ Cb * M := by
      have hs : (((ofList ((cvecs ws).take (m - m/2)) :: .int ((m/2:ℕ):ℤ) ::
          ofList (cvecs ws) :: Q : List Val).take (2+1)).map vsz).sum
          = vsz (ofList ((cvecs ws).take (m - m/2))) + (isz ((m/2:ℕ):ℤ) + vsz (ofList (cvecs ws))) := by
        simp only [Work.SynFFT.MrgKit.vsz_int', List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [hs, ← hVt, ← hV]
      have h1 : Vt + (isz ((m/2:ℕ):ℤ) + V) + 1 ≤ 33 * M := by
        linarith [hVtV, hV15, hPh2, hM1]
      exact costBound3 h1 (by rw [hCb]; omega)
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (fun k => hroll main k) 2
      (ofList ((cvecs ws).take (m - m/2)) :: .int ((m/2:ℕ):ℤ) :: ofList (cvecs ws) :: Q)
      (by simp) (Cb * M) hcost) rfl ?_ le_rfl
    intro out hout; rw [hout]; simp
  -- ### step 5: bring the second half's index to the top
  have eR2 : WordR main (rollP 2)
      (fun vs => vs = ofList (cvecs ws) :: ofList ((cvecs ws).take (m - m/2)) ::
        .int ((m/2:ℕ):ℤ) :: Q)
      (fun _ out => out = .int ((m/2:ℕ):ℤ) :: ofList (cvecs ws) ::
        ofList ((cvecs ws).take (m - m/2)) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Kr * (2+1) * ((((ofList (cvecs ws) :: ofList ((cvecs ws).take (m - m/2)) ::
        .int ((m/2:ℕ):ℤ) :: Q : List Val).take (2+1)).map vsz).sum + 1) ≤ Cb * M := by
      have hs : (((ofList (cvecs ws) :: ofList ((cvecs ws).take (m - m/2)) ::
          .int ((m/2:ℕ):ℤ) :: Q : List Val).take (2+1)).map vsz).sum
          = vsz (ofList (cvecs ws)) + (vsz (ofList ((cvecs ws).take (m - m/2))) + isz ((m/2:ℕ):ℤ)) := by
        simp only [Work.SynFFT.MrgKit.vsz_int', List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [hs, ← hV, ← hVt]
      have h1 : V + (Vt + isz ((m/2:ℕ):ℤ)) + 1 ≤ 33 * M := by
        linarith [hV15, hVtV, hPh2, hM1]
      exact costBound3 h1 (by rw [hCb]; omega)
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (fun k => hroll main k) 2
      (ofList (cvecs ws) :: ofList ((cvecs ws).take (m - m/2)) :: .int ((m/2:ℕ):ℤ) :: Q)
      (by simp) (Cb * M) hcost) rfl ?_ le_rfl
    intro out hout; rw [hout]; simp
  -- ### step 6: split off the right half
  have eDr : WordR main drP
      (fun vs => vs = .int ((m/2:ℕ):ℤ) :: ofList (cvecs ws) ::
        ofList ((cvecs ws).take (m - m/2)) :: Q)
      (fun _ out => out = ofList ((cvecs ws).drop (m/2)) ::
        ofList ((cvecs ws).take (m - m/2)) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Kdr * (vsz (ofList (cvecs ws)) + isz ((m/2:ℕ):ℤ) + 1) ≤ Cb * M := by
      have h1 : vsz (ofList (cvecs ws)) + isz ((m/2:ℕ):ℤ) + 1 ≤ 18 * M := by
        rw [← hV]; linarith [hV15, hPh2, hM1]
      exact costBound3 h1 (by rw [hCb]; omega)
    refine MrgKit.WordR_conseqC (hdr main (m/2) (cvecs ws)) ⟨_, rfl⟩ ?_ hcost
    intro out hout
    obtain ⟨r0, hv0, hout0⟩ := hout
    simp only [List.cons.injEq, Val.int.injEq] at hv0
    obtain ⟨-, -, hr0⟩ := hv0
    rw [hout0, hr0]
  -- ### step 7: bring the left half back on top
  have eR3 : WordR main (rollP 1)
      (fun vs => vs = ofList ((cvecs ws).drop (m/2)) :: ofList ((cvecs ws).take (m - m/2)) :: Q)
      (fun _ out => out = ofList ((cvecs ws).take (m - m/2)) ::
        ofList ((cvecs ws).drop (m/2)) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Kr * (1+1) * ((((ofList ((cvecs ws).drop (m/2)) ::
        ofList ((cvecs ws).take (m - m/2)) :: Q : List Val).take (1+1)).map vsz).sum + 1) ≤ Cb * M := by
      have hs : (((ofList ((cvecs ws).drop (m/2)) :: ofList ((cvecs ws).take (m - m/2)) :: Q
          : List Val).take (1+1)).map vsz).sum
          = vsz (ofList ((cvecs ws).drop (m/2))) + vsz (ofList ((cvecs ws).take (m - m/2))) := by
        simp only [Work.SynFFT.MrgKit.vsz_int', List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [hs, ← hVr, ← hVt]
      have h1 : Vr + Vt + 1 ≤ 31 * M := by linarith [hVrV, hVtV, hV15, hM1]
      exact costBound3 h1 (by rw [hCb]; omega)
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (fun k => hroll main k) 1
      (ofList ((cvecs ws).drop (m/2)) :: ofList ((cvecs ws).take (m - m/2)) :: Q)
      (by simp) (Cb * M) hcost) rfl ?_ le_rfl
    intro out hout; rw [hout]; simp
  -- ### step 8: tag the left half with its indices
  have eEn : WordR main enP
      (fun vs => vs = ofList ((cvecs ws).take (m - m/2)) :: ofList ((cvecs ws).drop (m/2)) :: Q)
      (fun _ out => out = ofList ((List.range ((cvecs ws).take (m - m/2)).length).map
          (fun i : ℕ => Val.cons (.int (i:ℤ)) (((cvecs ws).take (m - m/2)).getD i .nil))) ::
        ofList ((cvecs ws).drop (m/2)) :: Q)
      (fun _ => Cb * M) := by
    have hcost : Ke * (vsz (ofList ((cvecs ws).take (m - m/2)))
        + ((cvecs ws).take (m - m/2)).length * (((cvecs ws).take (m - m/2)).length.size + 1) + 1)
        ≤ Cb * M := by
      rw [← hVt, ← hnlen]
      have h1 : Vt + nlen * (nlen.size + 1) + 1 ≤ 17 * M := by
        linarith [hVtV, hV15, hnlM, hM1]
      exact costBound3 h1 (by rw [hCb]; omega)
    refine MrgKit.WordR_conseqC (hen main ((cvecs ws).take (m - m/2))) ⟨_, rfl⟩ ?_ hcost
    intro out hout
    obtain ⟨r0, hv0, hout0⟩ := hout
    simp only [List.cons.injEq] at hv0
    obtain ⟨-, hr0⟩ := hv0
    rw [hout0, hr0]
  have echain := MrgKit.WordR_seqC eL (MrgKit.WordR_seqC eIdx (MrgKit.WordR_seqC eTk
    (MrgKit.WordR_seqC eR1 (MrgKit.WordR_seqC eR2 (MrgKit.WordR_seqC eDr
    (MrgKit.WordR_seqC eR3 eEn))))))
  have htot : ((Cb*M) + ((Cb*M) + ((Cb*M) + ((Cb*M) + ((Cb*M) + ((Cb*M) + ((Cb*M) + (Cb*M))))))))
      = 8 * (Cb * M) := by ring
  have hfinal : 8 * (Cb * M) ≤ (8 * Cb) * (m * (r + 1) * (p + 1) + 1) + 8 * Cb := by
    rw [hM]
    have he : 8 * (Cb * (m * (r + 1) * (p + 1) + 1)) = (8 * Cb) * (m * (r + 1) * (p + 1) + 1) := by ring
    rw [he]
    exact Nat.le_add_right _ _
  refine MrgKit.WordR_weaken
    (P' := fun vs => vs = ofList (cvecs ws) :: Q)
    (Q' := fun (vs : List Val) (out : List Val) => ∃ (L R : List Val),
        out = ofList L :: ofList R :: Q ∧
        R = cvecs (ws.drop (m / 2)) ∧
        L = (List.range (m - m / 2)).map (fun i : ℕ => Val.cons (.int (i:ℤ)) ((cvecs ws).getD i .nil)))
    (C' := fun _ => (8 * Cb) * (m * (r + 1) * (p + 1) + 1) + 8 * Cb)
    echain (fun vs hvs => hvs) ?_ (fun vs hvs => ?_)
  · intro vs out hvs hout
    refine ⟨_, _, hout, ?_, ?_⟩
    · exact (cvecs_drop (m / 2) ws).symm
    · exact blkLvlEnumEq ws m hwlen
  · exact le_trans (le_of_eq htot) hfinal

end Work.SynFFT

