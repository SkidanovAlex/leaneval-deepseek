import Mathlib
import Submission.Work.SynFFT.mrgBlkHelper

/-!
# SynFFT, interleave block pass: the zip + flatten phase

Maps the two halves `cvecs (ws.drop s)` (on top) and `cvecs (ws.take s)` to the interleaved
block `cvecs (mrgBlkL s ws)`: zip the two lists building the two-element lists
`ofList [take_i, drop_i]`, then flatten.  Cost `O(s (r+1) (p+1))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-- `getD` of a mapped list of `ofList`s, with the `nil` default. -/
lemma map_ofList_getD (xss : List (List Val)) (i : ℕ) :
    (xss.map ofList).getD i .nil = ofList (xss.getD i ([] : List Val)) := by
  rw [show (Val.nil : Val) = ofList ([] : List Val) from rfl, List.getD_map]

/-- The pair-building word `(x, y) ↦ cons y (cons x nil)` used by the zip phase. -/
def pairProg (pushP : Val → Cmd) (swapP consP : Cmd) : Cmd :=
  Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pushP .nil) swapP) consP) swapP) consP

theorem mrgBlk_zipW (hk : KLib) (hl : LayoutLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (s : ℕ) (ws : List (List (ℤ × ℤ))) (r p : ℕ)
      (rest : List Val),
      0 < s → ws.length = 2 * s → (∀ w ∈ ws, InDiscVec p r w) →
      WordR main prog
        (fun vs => vs = ofList (cvecs (ws.drop s)) :: ofList (cvecs (ws.take s)) ::
          .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun vs out => out = ofList (cvecs (mrgBlkL s ws)) ::
          .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ => K * s * (r + 1) * (p + 1) + K) := by
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨consP, Kcv, hcons⟩ := hk.consV
  obtain ⟨zipP, Kzw, hzip⟩ := hk.zipWith
  obtain ⟨flatP, Kfl, hflat⟩ := hl.flatten
  refine ⟨((zipP (pairProg pushP swapP consP)) ;;; flatP),
    1000000 * (1000 * (Kpv + Ksw + Kcv + Kzw + Kfl + 1)), ?_⟩
  intro main s ws r p rest hs hlen hdisc
  set Kx : ℕ := 1000 * (Kpv + Ksw + Kcv + Kzw + Kfl + 1) with hKx
  set U : ℕ := s * (r + 1) * (p + 1) with hU
  set Lel : ℕ := 13 * (r + 1) * (p + 1) with hLel
  set Lz : ℕ := 2 * Lel + 3 with hLz
  set c : ℕ := 50 * Kx * (Lel + 1) with hc
  set Cs : ℕ := 100000 * Kx * U with hCs
  have hKpv : Kpv ≤ Kx := by rw [hKx]; omega
  have hKsw : Ksw ≤ Kx := by rw [hKx]; omega
  have hKcv : Kcv ≤ Kx := by rw [hKx]; omega
  have hKzw : Kzw ≤ Kx := by rw [hKx]; omega
  have hKfl : Kfl ≤ Kx := by rw [hKx]; omega
  have hU1 : 1 ≤ U := by rw [hU]; exact one_le_sX hs
  have hLel1 : 1 ≤ Lel + 1 := by omega
  -- element size bounds
  have helT : ∀ v ∈ cvecs (ws.take s), vsz v ≤ Lel := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hd := hdisc w (List.mem_of_mem_take hw)
    rw [hLel]
    exact MrgKit.vsz_cvecVal_le p r w hd.1 hd.2
  have helD : ∀ v ∈ cvecs (ws.drop s), vsz v ≤ Lel := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hd := hdisc w (List.mem_of_mem_drop hw)
    rw [hLel]
    exact MrgKit.vsz_cvecVal_le p r w hd.1 hd.2
  have hlenT : (cvecs (ws.take s)).length = s := by
    simp [cvecs, List.length_take, hlen]; omega
  have hlenD : (cvecs (ws.drop s)).length = s := by
    simp [cvecs, List.length_drop, hlen]; omega
  -- the inner pair-building word
  have hin : ∀ x y : Val, vsz x ≤ Lel ∧ vsz y ≤ Lel →
      WordR main (pairProg pushP swapP consP)
        (fun vs => vs = x :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ out => ∃ z, out = z :: (.int (r : ℤ) :: .int (p : ℤ) :: rest) ∧
          z = .cons y (.cons x .nil) ∧ vsz z ≤ Lz)
        (fun _ => c) := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := hxy
    set Ds : ℕ := 10 * Kx * (Lel + 1) with hDs
    have hDs_c : Ds * 5 ≤ c := by
      rw [hDs, hc]
      have h : (10 * Kx * (Lel + 1)) * 5 = 50 * Kx * (Lel + 1) := by ring
      rw [h]
    have hDs1 : 1 ≤ Ds := by rw [hDs]; nlinarith [hKx]
    have hnil : vsz (.nil : Val) = 1 := rfl
    have s0 : WordR main (pushP .nil)
        (fun vs => vs = x :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ out => out = .nil :: x :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ => Ds) := by
      refine MrgKit.pushStep (hpush main) .nil _ _ ?_
      rw [hDs, hnil]
      nlinarith [hKpv, hLel1, Nat.zero_le Kx]
    have s1 : WordR main swapP
        (fun vs => vs = .nil :: x :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ out => out = x :: .nil :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ => Ds) := by
      refine MrgKit.swapStep (hswap main) _ (by simp) _ ?_
      simp only [List.getD_cons_zero, List.getD_cons_succ, hnil]
      rw [hDs]
      nlinarith [hKsw, hLel1, Nat.zero_le Kx]
    have s2 : WordR main consP
        (fun vs => vs = x :: .nil :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ out => out = .cons x .nil :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ => Ds) := by
      refine MrgKit.consStep (hcons main) x .nil _ _ ?_
      rw [hDs]
      nlinarith [hKcv, hLel1, Nat.zero_le Kx]
    have s3 : WordR main swapP
        (fun vs => vs = .cons x .nil :: y :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ out => out = y :: .cons x .nil :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ => Ds) := by
      refine MrgKit.swapStep (hswap main) _ (by simp) _ ?_
      simp only [List.getD_cons_zero, List.getD_cons_succ, MrgKit.vsz_cons', hnil]
      rw [hDs]
      nlinarith [hKsw, hx, hy, hLel1, Nat.zero_le Kx]
    have s4 : WordR main consP
        (fun vs => vs = y :: .cons x .nil :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ out => out = .cons y (.cons x .nil) :: (.int (r : ℤ) :: .int (p : ℤ) :: rest))
        (fun _ => Ds) := by
      refine MrgKit.consStep (hcons main) y _ _ _ ?_
      rw [hDs]
      nlinarith [hKcv, hLel1, Nat.zero_le Kx]
    have e01 := MrgKit.WordR_seqC s0 s1
    have e012 := MrgKit.WordR_seqC e01 s2
    have e0123 := MrgKit.WordR_seqC e012 s3
    have e01234 := MrgKit.WordR_seqC e0123 s4
    have hszz : vsz (.cons y (.cons x .nil)) ≤ Lz := by
      have hn : vsz (.nil : Val) = 1 := rfl
      have h : vsz (.cons y (.cons x .nil)) = vsz y + vsz x + 3 := by
        rw [MrgKit.vsz_cons', MrgKit.vsz_cons', hn]; ring
      rw [h, hLz]; omega
    refine MrgKit.WordR_weaken e01234 (fun vs hvs => hvs) ?_ (fun vs _ => ?_)
    · intro vs out hvs hQ
      exact ⟨.cons y (.cons x .nil), hQ, rfl, hszz⟩
    · have h5 : Ds + Ds + Ds + Ds + Ds = Ds * 5 := by ring
      rw [h5]
      exact hDs_c
  -- the zip step
  have hA : ∀ i < (cvecs (ws.drop s)).length, vsz ((cvecs (ws.drop s)).getD i .nil) ≤ Lel ∧
      vsz ((cvecs (ws.take s)).getD i .nil) ≤ Lel := by
    intro i hi
    have his : i < s := by rw [hlenD] at hi; exact hi
    refine ⟨helD _ (getD_mem _ _ (by rw [hlenD]; exact his)),
      helT _ (getD_mem _ _ (by rw [hlenT]; exact his))⟩
  have hAP : ∀ v ∈ cvecs (ws.drop s) ++ cvecs (ws.take s), vsz v ≤ Lz := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have h := helD v hv
      rw [hLz]; omega
    · have h := helT v hv
      rw [hLz]; omega
  have hbz : s * (c + Kzw * (Lz + 1)) + Kzw ≤ Cs := by
    rw [hCs]
    have h1 : c + Kzw * (Lz + 1) ≤ 51 * Kx * (Lz + 1) := by
      rw [hc]
      have hLzge : Lel + 1 ≤ Lz + 1 := by rw [hLz]; omega
      calc 50 * Kx * (Lel + 1) + Kzw * (Lz + 1)
          ≤ 50 * Kx * (Lz + 1) + Kx * (Lz + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left (50 * Kx) hLzge)
              (Nat.mul_le_mul_right _ hKzw)
        _ = 51 * Kx * (Lz + 1) := by ring
    have h2 : Lz + 1 ≤ 30 * (r + 1) * (p + 1) := by
      rw [hLz, hLel]
      nlinarith [one_le_sX (r := r) (p := p) hs]
    have h3 : 51 * Kx * (Lz + 1) ≤ 51 * Kx * (30 * (r + 1) * (p + 1)) :=
      Nat.mul_le_mul_left _ h2
    have h4 : s * (51 * Kx * (30 * (r + 1) * (p + 1))) = 1530 * Kx * U := by
      rw [hU]; ring
    calc s * (c + Kzw * (Lz + 1)) + Kzw
        ≤ s * (51 * Kx * (Lz + 1)) + Kzw := Nat.add_le_add_right (Nat.mul_le_mul_left s h1) _
      _ ≤ s * (51 * Kx * (30 * (r + 1) * (p + 1))) + Kx :=
          Nat.add_le_add (Nat.mul_le_mul_left s h3) hKzw
      _ = 1530 * Kx * U + Kx := by rw [h4]
      _ ≤ 100000 * Kx * U := by nlinarith [hU1, Nat.zero_le Kx]
  -- the zip specification
  have eZ : WordR main (zipP (pairProg pushP swapP consP))
      (fun vs => vs = ofList (cvecs (ws.drop s)) :: ofList (cvecs (ws.take s)) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (((List.range s).map
        (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil])).map ofList) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => Cs) := by
    refine zipStep_xmrgBlkHelper (hzip main) (pairProg pushP swapP consP)
      (.int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun x y => vsz x ≤ Lel ∧ vsz y ≤ Lel)
      (fun x y z => z = .cons y (.cons x .nil)) c Lz hin
      (cvecs (ws.drop s)) (cvecs (ws.take s)) (by rw [hlenD, hlenT]) hA hAP _ ?_ Cs ?_
    · intro zs hzlen hzget
      refine ofList_congr (xs := zs) (ys := ((List.range s).map
        (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil])).map ofList) ?_ ?_
      · rw [hzlen, hlenD]; simp
      · intro i hi
        have his : i < s := by rw [hzlen, hlenD] at hi; exact hi
        rw [hzget i (by rw [hlenD]; exact his)]
        have hb : i < ((List.range s).map
            (fun j => [(cvecs (ws.take s)).getD j .nil, (cvecs (ws.drop s)).getD j .nil])).length := by
          rw [List.length_map, List.length_range]; exact his
        have hp : ((List.range s).map
            (fun j => [(cvecs (ws.take s)).getD j .nil, (cvecs (ws.drop s)).getD j .nil])).getD i []
            = [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil] := by
          rw [List.getD_eq_getElem _ [] hb,
            List.getElem_map (f := fun j => [(cvecs (ws.take s)).getD j .nil,
              (cvecs (ws.drop s)).getD j .nil]) (h := hb),
            List.getElem_range (by simpa using his)]
        rw [map_ofList_getD, hp, ofList_pair]
    · rw [hlenD]; exact hbz
  -- the flatten step
  have hsz : vsz (ofList (((List.range s).map
      (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil])).map ofList))
      ≤ 31 * U := by
    rw [MrgKit.vsz_ofList]
    have hlen2 : (((List.range s).map (fun i => [(cvecs (ws.take s)).getD i .nil,
        (cvecs (ws.drop s)).getD i .nil])).map ofList).length = s := by simp
    have hsum : ∀ v ∈ (((List.range s).map (fun i => [(cvecs (ws.take s)).getD i .nil,
        (cvecs (ws.drop s)).getD i .nil])).map ofList), vsz v ≤ Lz := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hi' : i < s := List.mem_range.mp hi
      have h1 : vsz ((cvecs (ws.take s)).getD i .nil) ≤ Lel :=
        helT _ (getD_mem _ _ (by rw [hlenT]; exact hi'))
      have h2 : vsz ((cvecs (ws.drop s)).getD i .nil) ≤ Lel :=
        helD _ (getD_mem _ _ (by rw [hlenD]; exact hi'))
      rw [vsz_ofList_pair, hLz]
      omega
    have h3 : ((((List.range s).map (fun i => [(cvecs (ws.take s)).getD i .nil,
        (cvecs (ws.drop s)).getD i .nil])).map ofList).map vsz).sum ≤ s * Lz := by
      refine le_trans (MrgKit.sum_le_of_forall vsz _ Lz hsum) ?_
      rw [hlen2]
    rw [hlen2]
    have h5 : Lz + 1 ≤ 30 * (r + 1) * (p + 1) := by
      rw [hLz, hLel]
      nlinarith [one_le_sX (r := r) (p := p) hs]
    have h6 : s * Lz + s ≤ 30 * U := by
      have h7 : s * (Lz + 1) ≤ s * (30 * (r + 1) * (p + 1)) := Nat.mul_le_mul_left s h5
      have h8 : s * (Lz + 1) = s * Lz + s := by ring
      have h9 : 30 * U = s * (30 * (r + 1) * (p + 1)) := by rw [hU]; ring
      linarith
    omega
  have eF : WordR main flatP
      (fun vs => vs = ofList (((List.range s).map
        (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil])).map ofList) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (((List.range s).map
        (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil])).flatten) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => Cs) := by
    have h := flattenStep_xmrgBlkHelper (fun xss => hflat main xss)
      ((List.range s).map (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil]))
      (.int (r : ℤ) :: .int (p : ℤ) :: rest) Cs ?_
    · exact h
    · rw [hCs]
      have hK : Kfl * (31 * U + 1) ≤ Kx * (32 * U) := by nlinarith [hKfl, hU1]
      have h1 : Kfl * (vsz (ofList (((List.range s).map (fun i => [(cvecs (ws.take s)).getD i .nil,
          (cvecs (ws.drop s)).getD i .nil])).map ofList)) + 1) ≤ Kfl * (31 * U + 1) :=
        Nat.mul_le_mul_left Kfl (by omega)
      have h2 : Kx * (32 * U) ≤ 100000 * Kx * U := by nlinarith [hU1, Nat.zero_le Kx]
      linarith
  -- the final identity
  have hident : ((List.range s).map
      (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil])).flatten
      = cvecs (mrgBlkL s ws) := by
    have hf : ∀ i, i < s → [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil]
        = [cvecVal (ws.getD i []), cvecVal (ws.getD (i + s) [])] := by
      intro i hi
      have h1 : (cvecs (ws.take s)).getD i .nil = cvecVal (ws.getD i []) := by
        rw [getD_cvecs_xmrgBlkHelper (by rw [List.length_take]; omega), getD_take_of_lt (ws) [] hi]
      have h2 : (cvecs (ws.drop s)).getD i .nil = cvecVal (ws.getD (i + s) []) := by
        rw [getD_cvecs_xmrgBlkHelper (by rw [List.length_drop]; omega), getD_drop_lt]
      rw [h1, h2]
    have hmap : (List.range s).map
        (fun i => [(cvecs (ws.take s)).getD i .nil, (cvecs (ws.drop s)).getD i .nil])
        = (List.range s).map (fun i => [cvecVal (ws.getD i []), cvecVal (ws.getD (i + s) [])]) :=
      List.map_congr_left (fun i hi => hf i (List.mem_range.mp hi))
    rw [hmap]
    have h2 : (List.range s).map (fun i => [cvecVal (ws.getD i []), cvecVal (ws.getD (i + s) [])])
        = ((List.range s).map (fun i => [ws.getD i [], ws.getD (i + s) []])).map (List.map cvecVal) := by
      rw [List.map_map]
      rfl
    rw [h2, ← List.map_flatten, mrgBlkL, cvecs]
  refine MrgKit.WordR_weaken (MrgKit.WordR_seqC eZ eF) (fun vs hvs => hvs) ?_ (fun vs _ => ?_)
  · intro vs out hvs hQ
    rw [hQ, hident]
  · set S : ℕ := 1000 * (Kpv + Ksw + Kcv + Kzw + Kfl + 1) with hS
    have h1 : Cs + Cs ≤ 200000 * Kx * U := by rw [hCs]; nlinarith [hU1, Nat.zero_le Kx]
    have h2 : 200000 * Kx * U = 200000 * S * s * (r + 1) * (p + 1) := by rw [hU, hKx, hS]; ring
    have h3 : 200000 * S * s * (r + 1) * (p + 1) ≤ 1000000 * S * s * (r + 1) * (p + 1) := by
      calc 200000 * S * s * (r + 1) * (p + 1)
          = (200000 * S) * (s * (r + 1) * (p + 1)) := by ring
        _ ≤ (1000000 * S) * (s * (r + 1) * (p + 1)) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right S (by norm_num))
        _ = 1000000 * S * s * (r + 1) * (p + 1) := by ring
    have h4 : 200000 * S * s * (r + 1) * (p + 1)
        ≤ 1000000 * S * s * (r + 1) * (p + 1) + 1000000 * S :=
      le_trans h3 (Nat.le_add_right _ _)
    rw [h2] at h1
    exact le_trans h1 h4

end Work.SynFFT
