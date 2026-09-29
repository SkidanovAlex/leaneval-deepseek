import Mathlib
import Submission.Work.Resample.auCWDefs
import Submission.Work.Resample.auCWKit
import Submission.Work.Resample.auCWSetup
import Submission.Work.Resample.auCWRound
import Submission.Work.Resample.auCWCount
import Submission.Work.Resample.auCWExtract
import Submission.Work.Resample.auCWFinal

/-!
# The chunk word `q` of paper Lemma 4.9 (`Work.Resample.auChunkWord`)

The assembly: the setup word `auCWSetup` produces the list of pairs `AwPair (W i) (x i) (y i)`
together with the accumulator `p, lo_r = 0, lo_i = 0, chain = nil`; `KernelLib.foldList` runs
`auCWRound` once per pair (two recursive multiplications per round, plus the carry arithmetic and
one small record per round); `auCWExtract` turns the chain of records into the two carry counts and
the round count; `auCWFinal` performs the final shift and division.  The telescoping identity
`awLor_add_sum` identifies the result with `tdiv (Σ_i W_i z_i) 2^p`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH

theorem cfxVal_inj' {u v : ℤ × ℤ} (h : HvdH.cfxVal u = HvdH.cfxVal v) : u = v := by
  have h' := HvdH.Val.cons.inj h
  exact Prod.ext (HvdH.Val.int.inj h'.1) (HvdH.Val.int.inj h'.2)

theorem auChunkWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm →
      ∀ (p α s t L : ℕ) (W : ℕ → ℤ) (z : ℕ → ℤ × ℤ) (WTS WIN : List HvdH.Val)
        (rest : List HvdH.Val), K * p < N → 1 ≤ p → s < t → t < 2 ^ p → α ^ 2 < p →
      WTS.length = L → WIN.length = L →
      (∀ i < L, WTS.getD i .nil = HvdH.Val.int (W i)) →
      (∀ i < L, WIN.getD i .nil = HvdH.cfxVal (z i)) →
      (∀ i < L, (W i).natAbs ≤ 2 ^ p) →
      (∀ i < L, HvdH.inDisc p (z i)) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN) :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ out => out = HvdH.cfxVal (Int.tdiv (∑ i ∈ Finset.range L, W i * (z i).1) ((2:ℤ)^p),
            Int.tdiv (∑ i ∈ Finset.range L, W i * (z i).2) ((2:ℤ)^p)) :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ => K * (L + 1) * (Cm (K * p) + p + 1)) := by
  obtain ⟨setupP, K1, hSetup⟩ := auCWSetup hk
  obtain ⟨roundP, K2, hRound⟩ := auCWRound hk hi
  obtain ⟨extP, K3, hExt⟩ := auCWExtract hk hi
  obtain ⟨finalP, K4, hFinal⟩ := auCWFinal hk hi
  obtain ⟨foldComb, Kf, hFold⟩ := hk.foldList
  refine ⟨Cmd.seq (Cmd.seq setupP (foldComb roundP)) (Cmd.seq extP finalP),
    2 ^ 40 * (K1 + K2 + K3 + K4 + Kf + 1) ^ 2, ?_⟩
  intro main N Cm hmono hmul p α s t L W z WTS WIN rest hKN hp hst htp hαp
    hlen1 hlen2 hWTS hWIN hWsz hdisc
  set KK : ℕ := 2 ^ 40 * (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 with hKK
  have hKS1 : K1 + K2 + K3 + K4 + Kf + 1 ≤ KK := by
    rw [hKK]
    have h1 : (1 : ℕ) ≤ K1 + K2 + K3 + K4 + Kf + 1 := by omega
    have h2 : K1 + K2 + K3 + K4 + Kf + 1 ≤ (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 := by
      nlinarith
    calc K1 + K2 + K3 + K4 + Kf + 1 ≤ (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 := h2
      _ ≤ 2 ^ 40 * (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 :=
          Nat.le_mul_of_pos_left _ (by norm_num)
  have hK1 : K1 ≤ KK := by omega
  have hK2 : K2 ≤ KK := by omega
  have hK3 : K3 ≤ KK := by omega
  have hK4 : K4 ≤ KK := by omega
  have hKf : Kf ≤ KK := by omega
  have hKN2 : K2 * p < N := by
    have h : K2 * p ≤ KK * p := Nat.mul_le_mul_right p hK2
    omega
  -- the summands
  set A : ℕ → ℤ := fun j => W j * (z j).1 + awSh p with hA
  set B : ℕ → ℤ := fun j => W j * (z j).2 + awSh p with hB
  set pairs : List HvdH.Val := (List.range L).map (fun i => AwPair (W i) (z i).1 (z i).2) with hpairs
  set zr : ℕ → ℤ := fun j => awZr p A j with hzr
  set zi : ℕ → ℤ := fun j => awZi p B j with hzi
  set qs : List (ℤ × ℤ) := awQs zr zi L with hqs
  set BK : ℕ := 3 * p + 12 with hBK
  set cR : ℕ := K2 * (Cm (K2 * p) + p + 1) with hcR
  -- the sizes
  have hiszW : ∀ i < L, isz (W i) ≤ p + 3 := by
    intro i hi
    have h := hWsz i hi
    have h2 : ((W i).natAbs).size ≤ p + 1 := by
      rw [Nat.size_le]
      calc (W i).natAbs ≤ 2 ^ p := h
        _ < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h3 : isz (W i) = ((W i).natAbs).size + 2 := rfl
    rw [h3]
    omega
  have hcoord : ∀ i < L, ∀ w : ℤ, w ^ 2 ≤ 4 ^ p → w.natAbs ≤ 2 ^ p := by
    intro i hi w hw
    have h4 : (4 : ℤ) ^ p = ((2 : ℤ) ^ p) ^ 2 := by
      rw [show (4 : ℤ) = 2 * 2 from rfl, mul_pow]; ring
    have hsq : ((w.natAbs : ℤ)) ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by
      rw [h4] at hw
      rwa [Int.natAbs_sq]
    have h6 : |(w.natAbs : ℤ)| ≤ |((2 : ℤ) ^ p)| := sq_le_sq.mp hsq
    have h7 : (w.natAbs : ℤ) ≤ (2 : ℤ) ^ p := by
      rwa [abs_of_nonneg (Int.natCast_nonneg _), abs_of_nonneg (by positivity)] at h6
    exact_mod_cast h7
  have hdiscA : ∀ i < L, (z i).1.natAbs ≤ 2 ^ p ∧ (z i).2.natAbs ≤ 2 ^ p := by
    intro i hi
    have h := hdisc i hi
    simp only [HvdH.inDisc] at h
    refine ⟨hcoord i hi _ ?_, hcoord i hi _ ?_⟩
    · have h2 : 0 ≤ (z i).2 ^ 2 := sq_nonneg _
      linarith
    · have h2 : 0 ≤ (z i).1 ^ 2 := sq_nonneg _
      linarith
  have hsz_of : ∀ w : ℤ, w.natAbs ≤ 2 ^ p → isz w ≤ p + 3 := by
    intro w hw
    have h2 : (w.natAbs).size ≤ p + 1 := by
      rw [Nat.size_le]
      calc w.natAbs ≤ 2 ^ p := hw
        _ < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h3 : isz w = (w.natAbs).size + 2 := rfl
    rw [h3]
    omega
  have hiszz : ∀ i < L, isz (z i).1 ≤ p + 3 ∧ isz (z i).2 ≤ p + 3 := by
    intro i hi
    exact ⟨hsz_of _ (hdiscA i hi).1, hsz_of _ (hdiscA i hi).2⟩
  -- the round hypotheses
  have hA0 : ∀ i < L, 0 ≤ A i := by
    intro i hi
    have h1 := hWsz i hi
    have h2 := (hdiscA i hi).1
    have h3 : |W i * (z i).1| ≤ awSh p := abs_mul_le_awSh (p := p) (a := W i) (b := (z i).1) h1 h2
    show 0 ≤ W i * (z i).1 + awSh p
    have := abs_le.mp h3
    linarith [this.1]
  have hAle : ∀ i < L, A i ≤ awMod p := by
    intro i hi
    have h1 := hWsz i hi
    have h2 := (hdiscA i hi).1
    have h3 : |W i * (z i).1| ≤ awSh p := abs_mul_le_awSh (p := p) (a := W i) (b := (z i).1) h1 h2
    show W i * (z i).1 + awSh p ≤ awMod p
    have := abs_le.mp h3
    have h6 := awMod_eq_shift p
    linarith [this.2, h6]
  have hB0 : ∀ i < L, 0 ≤ B i := by
    intro i hi
    have h1 := hWsz i hi
    have h2 := (hdiscA i hi).2
    have h3 : |W i * (z i).2| ≤ awSh p := abs_mul_le_awSh (p := p) (a := W i) (b := (z i).2) h1 h2
    show 0 ≤ W i * (z i).2 + awSh p
    have := abs_le.mp h3
    linarith [this.1]
  have hBle : ∀ i < L, B i ≤ awMod p := by
    intro i hi
    have h1 := hWsz i hi
    have h2 := (hdiscA i hi).2
    have h3 : |W i * (z i).2| ≤ awSh p := abs_mul_le_awSh (p := p) (a := W i) (b := (z i).2) h1 h2
    show W i * (z i).2 + awSh p ≤ awMod p
    have := abs_le.mp h3
    have h6 := awMod_eq_shift p
    linarith [this.2, h6]
  -- the carries are 0 or 1
  have hzr01 : ∀ j < L, zr j = 0 ∨ zr j = 1 := by
    intro j hj
    have h1 := awCar_nonneg (p := p) (lo := awLor p A j) (A := A j)
        (awLor_nonneg_lt p A j (fun k hk => hA0 k (lt_trans hk hj)))
        (hA0 j hj)
    have h2 := awCar_le_one (p := p) (lo := awLor p A j) (A := A j)
        (awLor_nonneg_lt p A j (fun k hk => hA0 k (lt_trans hk hj)))
        (hA0 j hj)
        (awLor_lt_lt p A j (fun k hk => hA0 k (lt_trans hk hj)))
        (hAle j hj)
    show awCar p (awLor p A j) (A j) = 0 ∨ awCar p (awLor p A j) (A j) = 1
    omega
  have hzi01 : ∀ j < L, zi j = 0 ∨ zi j = 1 := by
    intro j hj
    have h1 := awCar_nonneg (p := p) (lo := awLoi p B j) (A := B j)
        (awLoi_nonneg_lt p B j (fun k hk => hB0 k (lt_trans hk hj)))
        (hB0 j hj)
    have h2 := awCar_le_one (p := p) (lo := awLoi p B j) (A := B j)
        (awLoi_nonneg_lt p B j (fun k hk => hB0 k (lt_trans hk hj)))
        (hB0 j hj)
        (awLoi_lt_lt p B j (fun k hk => hB0 k (lt_trans hk hj)))
        (hBle j hj)
    show awCar p (awLoi p B j) (B j) = 0 ∨ awCar p (awLoi p B j) (B j) = 1
    omega
  -- the pairs
  have hpairs_len : pairs.length = L := by rw [hpairs]; simp
  have hpairs_get : ∀ i < L, pairs.getD i .nil = AwPair (W i) (z i).1 (z i).2 := by
    intro i hi
    rw [hpairs, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  have hvsz : ∀ x ∈ pairs, vsz x ≤ BK := by
    intro x hx
    rw [hpairs] at hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have h1 := hiszW i hi
    have h2 := (hiszz i hi).1
    have h3 := (hiszz i hi).2
    rw [vsz_AwPair, hBK]
    omega
  -- the accumulator invariant
  let I : ℕ → List HvdH.Val → Prop := awInv p α s t A B zr zi rest
  have hinit : I 0 (HvdH.Val.int (p : ℤ) :: HvdH.Val.int 0 :: HvdH.Val.int 0 :: HvdH.Val.nil
      :: auPvals p α s t ++ rest) := by
    refine ⟨0, 0, HvdH.Val.nil, rfl, le_rfl, awMod_pos p, le_rfl, awMod_pos p, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
  -- the fold body
  have hbody : ∀ i acc, i < pairs.length → I i acc → HvdH.WordR main roundP
      (fun vs => vs = pairs.getD i .nil :: acc) (fun _ out => I (i + 1) out)
      (fun _ => cR) := by
    intro i acc hi hIac
    obtain ⟨lo_r, lo_i, CH, hacc, hlo0, hloM, hli0, hliM, hlor, hloi, hCH⟩ := hIac
    have hiL : i < L := by rw [hpairs_len] at hi; exact hi
    have helem := hpairs_get i hiL
    have hR := hRound main N Cm hmono hmul p (W i) (z i).1 (z i).2 lo_r lo_i CH
      (auPvals p α s t ++ rest) hp hKN2 (hWsz i hiL) (hdisc i hiL) hlo0 hloM hli0 hliM
    refine hk.conseq (main := main) (p := roundP)
      (P := fun vs => vs = AwPair (W i) (z i).1 (z i).2 :: HvdH.Val.int (p : ℤ)
        :: HvdH.Val.int lo_r :: HvdH.Val.int lo_i :: CH :: (auPvals p α s t ++ rest))
      (P' := fun vs => vs = pairs.getD i .nil :: acc)
      (Q := fun _ out => out = HvdH.Val.int (p : ℤ)
        :: HvdH.Val.int (awLow p lo_r (W i * (z i).1 + awSh p))
        :: HvdH.Val.int (awLow p lo_i (W i * (z i).2 + awSh p))
        :: HvdH.Val.cons (awRec (awCar p lo_r (W i * (z i).1 + awSh p))
            (awCar p lo_i (W i * (z i).2 + awSh p))) CH :: (auPvals p α s t ++ rest))
      (Q' := fun _ out => I (i + 1) out)
      (C := fun _ => cR) (C' := fun _ => cR) hR ?_ ?_ ?_
    · intro vs hvs
      simpa [hvs, helem, hacc]
    · intro vs out hvs hpost
      rw [hpost]
      refine ⟨awLow p lo_r (W i * (z i).1 + awSh p),
        awLow p lo_i (W i * (z i).2 + awSh p),
        HvdH.Val.cons (awRec (awCar p lo_r (W i * (z i).1 + awSh p))
            (awCar p lo_i (W i * (z i).2 + awSh p))) CH, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact awLow_nonneg hlo0 (hA0 i hiL)
      · exact awLow_lt hlo0 (hA0 i hiL)
      · exact awLow_nonneg hli0 (hB0 i hiL)
      · exact awLow_lt hli0 (hB0 i hiL)
      · rw [hlor]
        rfl
      · rw [hloi]
        rfl
      · rw [hCH]
        show HvdH.Val.cons (awRec (awCar p lo_r (W i * (z i).1 + awSh p))
              (awCar p lo_i (W i * (z i).2 + awSh p))) (HvdH.ofList (awRecs zr zi i))
            = HvdH.Val.cons (awRec (zr i) (zi i)) (HvdH.ofList (awRecs zr zi i))
        rw [hlor, hloi]
        rfl
    · intro vs hvs
      exact le_rfl
  -- the fold over the pairs
  have hFoldRes := hFold main roundP pairs I cR BK hvsz hbody
  rw [hpairs_len] at hFoldRes
  -- the composition helper
  have hstep1 : ∀ vs mid, (fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
        :: auPvals p α s t ++ rest) vs →
      (fun _ out => out = HvdH.ofList pairs :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int 0
        :: HvdH.Val.int 0 :: HvdH.Val.nil :: auPvals p α s t ++ rest) vs mid →
      (fun vs => ∃ acc, vs = HvdH.ofList pairs :: acc ∧ I 0 acc) mid ∧
        (L * (cR + Kf * (BK + 1)) + Kf) ≤ (L * (cR + Kf * (BK + 1)) + Kf) := by
    intro vs mid _hvs hmid
    refine ⟨⟨HvdH.Val.int (p : ℤ) :: HvdH.Val.int 0 :: HvdH.Val.int 0 :: HvdH.Val.nil
      :: auPvals p α s t ++ rest, ?_, hinit⟩, le_rfl⟩
    rw [hmid]
    try rfl
  have hP1 := hSetup main p α s t L W z WTS WIN rest hp hst htp hαp hlen1 hlen2 hWTS hWIN hWsz hdisc
  have hS12 : HvdH.WordR main (Cmd.seq setupP (foldComb roundP))
      (fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN) :: auPvals p α s t ++ rest)
      (fun _ out => I L out)
      (fun _ => K1 * (L + 1) * (p + 1) + (L * (cR + Kf * (BK + 1)) + Kf)) := by
    refine hk.conseq (main := main) (p := Cmd.seq setupP (foldComb roundP))
      (P := fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
        :: auPvals p α s t ++ rest)
      (P' := fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
        :: auPvals p α s t ++ rest)
      (Q := fun vs out => ∃ mid, mid = HvdH.ofList pairs :: HvdH.Val.int (p : ℤ)
        :: HvdH.Val.int 0 :: HvdH.Val.int 0 :: HvdH.Val.nil :: auPvals p α s t ++ rest ∧ I L out)
      (Q' := fun _ out => I L out)
      (C := fun _ => K1 * (L + 1) * (p + 1) + (L * (cR + Kf * (BK + 1)) + Kf))
      (C' := fun _ => K1 * (L + 1) * (p + 1) + (L * (cR + Kf * (BK + 1)) + Kf))
      (hk.seq (main := main) (p := setupP) (q := foldComb roundP)
        (P := fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
          :: auPvals p α s t ++ rest)
        (Q := fun _ out => out = HvdH.ofList pairs :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int 0
          :: HvdH.Val.int 0 :: HvdH.Val.nil :: auPvals p α s t ++ rest)
        (C := fun _ => K1 * (L + 1) * (p + 1))
        (P' := fun vs => ∃ acc, vs = HvdH.ofList pairs :: acc ∧ I 0 acc)
        (Q' := fun _ out => I L out)
        (C' := fun _ => L * (cR + Kf * (BK + 1)) + Kf)
        (B := fun _ => L * (cR + Kf * (BK + 1)) + Kf) hP1 hFoldRes hstep1)
      (fun _ h => h) (fun _ _ _ hq => by obtain ⟨_, _, hI⟩ := hq; exact hI) (fun _ _ => le_rfl)
  have hQs1 : ∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1 := by
    intro q hq
    rw [hqs] at hq
    obtain ⟨j, hj, rfl⟩ := awQs_mem zr zi hq
    exact hzr01 j hj
  have hQs2 : ∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1 := by
    intro q hq
    rw [hqs] at hq
    obtain ⟨j, hj, rfl⟩ := awQs_mem zr zi hq
    exact hzi01 j hj
  have hqslen : qs.length = L := by rw [hqs]; exact awQs_length zr zi L
  have hqsmap : HvdH.ofList (qs.map fun q => awRec q.1 q.2) = HvdH.ofList (awRecs zr zi L) := by
    rw [hqs, awQs_map_awRec]
  -- the counts
  set Cr : ℤ := (qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum with hCr
  set Ci : ℤ := (qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum with hCi
  set LL : ℤ := ((qs.length : ℕ) : ℤ) with hLL
  have hLL0 : 0 ≤ LL := by rw [hLL]; positivity
  have hLLnat : LL.toNat = L := by rw [hLL, hqslen]; simp
  have hLl : LL = (L : ℤ) := by rw [hLL, hqslen]
  have hCr0 : 0 ≤ Cr := by
    rw [hCr]
    exact list_sum_nonneg _ (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      by_cases h : q.1 = 1 <;> simp [h])
  have hCrL : Cr ≤ LL := by
    rw [hCr, hLL]
    refine le_trans (list_sum_le_length _ (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      by_cases h : q.1 = 1 <;> simp [h])) ?_
    simp
  have hCi0 : 0 ≤ Ci := by
    rw [hCi]
    exact list_sum_nonneg _ (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      by_cases h : q.2 = 1 <;> simp [h])
  have hCiL : Ci ≤ LL := by
    rw [hCi, hLL]
    refine le_trans (list_sum_le_length _ (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      by_cases h : q.2 = 1 <;> simp [h])) ?_
    simp
  -- the extract word
  have hExtW := hExt main p (awLor p A L) (awLoi p B L) qs (auPvals p α s t ++ rest)
    (awLor_nonneg_lt p A L (fun k hk => hA0 k hk)) (awLor_lt_lt p A L (fun k hk => hA0 k hk))
    (awLoi_nonneg_lt p B L (fun k hk => hB0 k hk)) (awLoi_lt_lt p B L (fun k hk => hB0 k hk))
    hQs1 hQs2
  -- the final word
  have hFinW := hFinal main p α s t (awLor p A L) (awLoi p B L) Cr Ci LL rest hp
    (awLor_nonneg_lt p A L (fun k hk => hA0 k hk)) (awLor_lt_lt p A L (fun k hk => hA0 k hk))
    (awLoi_nonneg_lt p B L (fun k hk => hB0 k hk)) (awLoi_lt_lt p B L (fun k hk => hB0 k hk))
    hCr0 hCrL hCi0 hCiL hLL0
  -- composition of extract and final
  have hEF : HvdH.WordR main (Cmd.seq extP finalP)
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.ofList (qs.map fun q => awRec q.1 q.2)
        :: auPvals p α s t ++ rest)
      (fun _ out => out = HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
        :: auPvals p α s t ++ rest)
      (fun _ => K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1)) := by
    refine hk.conseq (main := main) (p := Cmd.seq extP finalP)
      (P := fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.ofList (qs.map fun q => awRec q.1 q.2)
        :: auPvals p α s t ++ rest)
      (P' := fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.ofList (qs.map fun q => awRec q.1 q.2)
        :: auPvals p α s t ++ rest)
      (Q := fun vs out => ∃ mid, mid = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
          :: HvdH.Val.int (awLoi p B L) :: HvdH.Val.int Cr :: HvdH.Val.int Ci
          :: HvdH.Val.int LL :: auPvals p α s t ++ rest ∧
          out = HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
            :: auPvals p α s t ++ rest)
      (Q' := fun _ out => out = HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
        :: auPvals p α s t ++ rest)
      (C := fun _ => K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1))
      (C' := fun _ => K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1))
      (hk.seq (main := main) (p := extP) (q := finalP)
      (P := fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.ofList (qs.map fun q => awRec q.1 q.2)
        :: auPvals p α s t ++ rest)
      (Q := fun _ out => out = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.Val.int Cr :: HvdH.Val.int Ci
        :: HvdH.Val.int LL :: auPvals p α s t ++ rest)
      (C := fun _ => K3 * (qs.length + 1) * (p + 1))
      (P' := fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.Val.int Cr :: HvdH.Val.int Ci
        :: HvdH.Val.int LL :: auPvals p α s t ++ rest)
      (Q' := fun _ out => out = HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
        :: auPvals p α s t ++ rest)
      (C' := fun _ => K4 * (p + 1) * (LL.toNat + 1))
      (B := fun _ => K4 * (p + 1) * (LL.toNat + 1)) hExtW hFinW ?_)
      (fun _ h => h) (fun _ _ _ hq => by obtain ⟨_, _, hI⟩ := hq; exact hI) (fun _ _ => le_rfl)
    intro vs mid _hvs hmid
    refine ⟨?_, le_rfl⟩
    rw [hmid]
    try rfl
  -- the composition of the fold and the extraction/final phases
  have hstep2 : ∀ vs mid,
      (fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
        :: auPvals p α s t ++ rest) vs →
      (fun _ out => I L out) vs mid →
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.ofList (qs.map fun q => awRec q.1 q.2)
        :: auPvals p α s t ++ rest) mid ∧
      (K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1))
        ≤ (K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1)) := by
    intro vs mid _hvs hIac
    obtain ⟨lo_r, lo_i, CH, hacc, hlo0, hloM, hli0, hliM, hlor, hloi, hCH⟩ := hIac
    refine ⟨?_, le_rfl⟩
    rw [hacc, hlor, hloi, hCH, hqsmap]
    try rfl
  -- the full program
  have hAll : HvdH.WordR main (Cmd.seq (Cmd.seq setupP (foldComb roundP)) (Cmd.seq extP finalP))
      (fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN) :: auPvals p α s t ++ rest)
      (fun vs out => ∃ mid, I L mid ∧
        out = HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
          :: auPvals p α s t ++ rest)
      (fun _ => (K1 * (L + 1) * (p + 1) + (L * (cR + Kf * (BK + 1)) + Kf))
        + (K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1))) := by
    refine hk.seq (main := main) (p := Cmd.seq setupP (foldComb roundP)) (q := Cmd.seq extP finalP)
      (P := fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
        :: auPvals p α s t ++ rest)
      (Q := fun _ out => I L out)
      (C := fun _ => K1 * (L + 1) * (p + 1) + (L * (cR + Kf * (BK + 1)) + Kf))
      (P' := fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (awLor p A L)
        :: HvdH.Val.int (awLoi p B L) :: HvdH.ofList (qs.map fun q => awRec q.1 q.2)
        :: auPvals p α s t ++ rest)
      (Q' := fun _ out => out = HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
        :: auPvals p α s t ++ rest)
      (C' := fun _ => K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1))
      (B := fun _ => K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1))
      hS12 hEF hstep2
  -- the algebra
  have hsumA : (∑ j ∈ Finset.range L, A j)
      = (∑ j ∈ Finset.range L, W j * (z j).1) + (L : ℤ) * awSh p := by
    have h1 : ∀ j ∈ Finset.range L, A j = W j * (z j).1 + awSh p := by
      intro j _
      rw [hA]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hsumB : (∑ j ∈ Finset.range L, B j)
      = (∑ j ∈ Finset.range L, W j * (z j).2) + (L : ℤ) * awSh p := by
    have h1 : ∀ j ∈ Finset.range L, B j = W j * (z j).2 + awSh p := by
      intro j _
      rw [hB]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hCrEq : Cr = ∑ j ∈ Finset.range L, awZr p A j := by
    rw [hCr, hqs, awQs_first zr zi L]
    rw [show (∑ j ∈ Finset.range L, (if zr j = 1 then (1 : ℤ) else 0))
        = ∑ j ∈ Finset.range L, (if awZr p A j = 1 then (1 : ℤ) else 0) from rfl]
    rw [sum_if_eq_lt (fun j => awZr p A j) L (fun j hj => hzr01 j hj)]
  have hCiEq : Ci = ∑ j ∈ Finset.range L, awZi p B j := by
    rw [hCi, hqs, awQs_second zr zi L]
    rw [show (∑ j ∈ Finset.range L, (if zi j = 1 then (1 : ℤ) else 0))
        = ∑ j ∈ Finset.range L, (if awZi p B j = 1 then (1 : ℤ) else 0) from rfl]
    rw [sum_if_eq_lt (fun j => awZi p B j) L (fun j hj => hzi01 j hj)]
  have hkey : (∑ j ∈ Finset.range L, W j * (z j).1)
      = awLor p A L + (2 * Cr - LL) * awSh p := by
    have htel := awLor_add_sum p A L
    have hmod := awMod_eq_shift p
    rw [← hCrEq] at htel
    rw [hmod] at htel
    rw [hLl]
    linarith [htel, hsumA]
  have hkey2 : (∑ j ∈ Finset.range L, W j * (z j).2)
      = awLoi p B L + (2 * Ci - LL) * awSh p := by
    have htel := awLoi_add_sum p B L
    have hmod := awMod_eq_shift p
    rw [← hCiEq] at htel
    rw [hmod] at htel
    rw [hLl]
    linarith [htel, hsumB]
  have hmain1 : awAns p (awLor p A L) Cr LL
      = Int.tdiv (∑ j ∈ Finset.range L, W j * (z j).1) ((2 : ℤ) ^ p) := by
    rw [awAns, hkey]
    try rfl
  have hmain2 : awAns p (awLoi p B L) Ci LL
      = Int.tdiv (∑ j ∈ Finset.range L, W j * (z j).2) ((2 : ℤ) ^ p) := by
    rw [awAns, hkey2]
    try rfl
  -- the final conversion
  refine hk.conseq (main := main)
    (p := Cmd.seq (Cmd.seq setupP (foldComb roundP)) (Cmd.seq extP finalP))
    (P := fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
      :: auPvals p α s t ++ rest)
    (P' := fun vs => vs = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList WIN)
      :: auPvals p α s t ++ rest)
    (Q := fun vs out => ∃ mid, I L mid ∧
      out = HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
        :: auPvals p α s t ++ rest)
    (Q' := fun _ out => out = HvdH.cfxVal (Int.tdiv (∑ i ∈ Finset.range L, W i * (z i).1) ((2 : ℤ) ^ p),
        Int.tdiv (∑ i ∈ Finset.range L, W i * (z i).2) ((2 : ℤ) ^ p)) :: auPvals p α s t ++ rest)
    (C := fun _ => (K1 * (L + 1) * (p + 1) + (L * (cR + Kf * (BK + 1)) + Kf))
      + (K3 * (qs.length + 1) * (p + 1) + K4 * (p + 1) * (LL.toNat + 1)))
    (C' := fun _ => KK * (L + 1) * (Cm (KK * p) + p + 1)) hAll ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out _hvs hout
    obtain ⟨_m, _hm, hout⟩ := hout
    rw [hout]
    have h1 : HvdH.cfxVal (awAns p (awLor p A L) Cr LL, awAns p (awLoi p B L) Ci LL)
        = HvdH.cfxVal (Int.tdiv (∑ i ∈ Finset.range L, W i * (z i).1) ((2 : ℤ) ^ p),
            Int.tdiv (∑ i ∈ Finset.range L, W i * (z i).2) ((2 : ℤ) ^ p)) := by
      rw [hmain1, hmain2]
    rw [h1]
    try rfl
  · intro vs _hvs
    rw [hqslen, hLLnat, hcR, hBK]
    refine auCWCostBound K1 K2 K3 K4 Kf L p Cm KK ?_ (hmono (Nat.mul_le_mul_right p hK2))
    rw [hKK]
    have hS : (1 : ℕ) ≤ K1 + K2 + K3 + K4 + Kf + 1 := by omega
    have h1 : K1 + K2 + K3 + K4 + Kf + 1 ≤ (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 := by
      calc K1 + K2 + K3 + K4 + Kf + 1 = (K1 + K2 + K3 + K4 + Kf + 1) * 1 := by ring
        _ ≤ (K1 + K2 + K3 + K4 + Kf + 1) * (K1 + K2 + K3 + K4 + Kf + 1) :=
            Nat.mul_le_mul_left _ hS
        _ = (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 := by ring
    calc 20 * (K1 + K2 + K3 + K4 + Kf + 1)
        ≤ 20 * (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 := Nat.mul_le_mul_left 20 h1
      _ ≤ 2 ^ 40 * (K1 + K2 + K3 + K4 + Kf + 1) ^ 2 := Nat.mul_le_mul_right _ (by norm_num)

end Work.Resample
