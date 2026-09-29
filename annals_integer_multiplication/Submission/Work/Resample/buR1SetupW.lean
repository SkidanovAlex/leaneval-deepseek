import Mathlib
import Submission.Work.Resample.buQWstepKit

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-- The preparation of one Neumann round: build the window `[COLS, Z0, σ, v, acc, s, p, COLS, s, p]`
from `[σ, v, acc, COLS, s, p]`, where the last three entries are copies of `COLS, s, p` that survive
the round. -/
def buR1SetupProg (pickP : ℕ → Cmd) (rollP : ℕ → Cmd) (pushP : Val → Cmd) (repP : Cmd) : Cmd :=
  Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))))))))

theorem buR1SetupW
    (pickP : ℕ → Cmd) (rollP : ℕ → Cmd) (pushP : Val → Cmd) (repP : Cmd)
    (Kpick Kroll Kpush Krep KS : ℕ)
    (hKpick : Kpick ≤ KS) (hKroll : Kroll ≤ KS) (hKpush : Kpush ≤ KS) (hKrep : Krep ≤ KS)
    (hKS1 : 1 ≤ KS)
    (hpick : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpick * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hroll : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hpush : ∀ (m : Cmd) (vv : Val), WordR m (pushP vv) (fun _ => True)
      (fun vs out => out = vv :: vs) (fun _ => Kpush * (vsz vv + 1)))
    (hrep : ∀ (m : Cmd) (k : ℕ) (vv : Val), WordR m repP
      (fun vs => ∃ rest, vs = .int (k : ℤ) :: vv :: rest)
      (fun vs out => ∃ rest, vs = .int (k : ℤ) :: vv :: rest ∧
        out = ofList (List.replicate k vv) :: rest)
      (fun _ => Krep * ((k + 1) * (vsz vv + 1) + isz (k : ℤ) + 1))) :
    ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p) (σ : ℤ)
      (v acc : List (ℤ × ℤ)) (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
      (hv : v.length = s) (ha : acc.length = s) (hbv : buInV B v) (hbacc : buInV B2 acc)
      (hσ : σ = 1 ∨ σ = -1)
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
        |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ)),
      Pipe main (buR1SetupProg pickP rollP pushP repP)
        [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]
        [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]
        (2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1))) := by
  intro main p α s t hs hα hp σ v acc B B2 hB hB2 hv ha hbv hbacc hσ hrow
  have hM1 : 1 ≤ egM p α + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hp1 : 1 ≤ p + 1 := by omega
  have hY1 : 1 ≤ (egM p α + 1) * (s + 1) * (p + 1) := by
    calc (1 : ℕ) = 1 * 1 * 1 := by ring
      _ ≤ (egM p α + 1) * (s + 1) * (p + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul hM1 (by omega)) hp1
  have hsY : s + 1 ≤ (egM p α + 1) * (s + 1) * (p + 1) := by
    calc s + 1 = (s + 1) * 1 := by ring
      _ ≤ (s + 1) * ((egM p α + 1) * (p + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hM1 hp1)
      _ = (egM p α + 1) * (s + 1) * (p + 1) := by ring
  have hzvsz : vsz (cfxVal ((0 : ℤ), (0 : ℤ))) = 5 := by decide
  have hSB1 : 1 ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by nlinarith [hY1]
  have hSg : vsz (Val.int σ) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    have h3 : isz σ ≤ 3 := by rcases hσ with h | h <;> rw [h] <;> decide
    have h4 : vsz (Val.int σ) ≤ 3 := by rw [Work.Fx.vsz_int]; exact h3
    have h5 : (3 : ℕ) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by nlinarith [hY1]
    omega
  have hVV : vsz (cvecVal v) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    have h1 : ∀ z ∈ v, isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 := buQW_isz_of_buInV hB hbv
    have h2 := buQT_vsz_cvecVal (u := v) (M := p + 5) h1
    rw [hv] at h2
    nlinarith [h2, hY1, Nat.zero_le s, Nat.zero_le p]
  have hAV : vsz (cvecVal acc) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    have h1 : ∀ z ∈ acc, isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 := buQW_isz_of_buInV hB2 hbacc
    have h2 := buQT_vsz_cvecVal (u := acc) (M := p + 5) h1
    rw [ha] at h2
    nlinarith [h2, hY1, Nat.zero_le s, Nat.zero_le p]
  have hBT : vsz (buColsT p α s t) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    have h2 := buQW_colsT_vsz_le p α s t hs hα hp hrow
    have h3 : 1000 * (egM p α + 1) * (s + 1) * (p + 1) = (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by ring
    rwa [h3] at h2
  have hSh : vsz (Val.int (s : ℤ)) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    have h1 : isz (s : ℤ) ≤ 2 * (s + 1) := by
      have hs2 : s < 2 ^ (s + 1) := by
        have := Nat.lt_two_pow_self (n := s + 1); omega
      have hsz : s.size ≤ s + 1 := Nat.size_le.mpr hs2
      simp only [isz, Int.natAbs_natCast]
      omega
    rw [Work.Fx.vsz_int]
    nlinarith [h1, hsY]
  have hPh : vsz (Val.int (p : ℤ)) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    have h1 : isz (p : ℤ) ≤ 2 * (p + 1) := by
      have hp2 : p < 2 ^ (p + 1) := by
        have := Nat.lt_two_pow_self (n := p + 1); omega
      have hsz : p.size ≤ p + 1 := Nat.size_le.mpr hp2
      simp only [isz, Int.natAbs_natCast]
      omega
    rw [Work.Fx.vsz_int]
    have hpY : p + 1 ≤ (egM p α + 1) * (s + 1) * (p + 1) := by
      have hs1 : 1 ≤ (egM p α + 1) * (s + 1) := by
        calc (1 : ℕ) = 1 * 1 := by ring
          _ ≤ (egM p α + 1) * (s + 1) := Nat.mul_le_mul hM1 (by omega)
      calc p + 1 = (p + 1) * 1 := by ring
        _ ≤ (p + 1) * ((egM p α + 1) * (s + 1)) := Nat.mul_le_mul_left _ hs1
        _ = (egM p α + 1) * (s + 1) * (p + 1) := by ring
    nlinarith [h1, hpY]
  have hzv : vsz (cfxVal ((0 : ℤ), (0 : ℤ))) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    rw [hzvsz]; nlinarith [hY1]
  have hZ0 : vsz (ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ))))) ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    rw [buQT_vsz_ofList, List.length_replicate, List.map_replicate, List.sum_replicate, nsmul_eq_mul, hzvsz]
    nlinarith [hsY, hY1, Nat.zero_le s]

  have hW0 : ∀ x ∈ ([Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP0 : Pipe main (rollP 5) [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]) (k := 5) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 5) (by omega) (buQW_szl_succ_le hW0 (k := 5) (by omega))
  have hW1 : ∀ x ∈ ([Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP1 : Pipe main (rollP 5) [Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ)] [Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ)]) (k := 5) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 5) (by omega) (buQW_szl_succ_le hW1 (k := 5) (by omega))
  have hW2 : ∀ x ∈ ([Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP2 : Pipe main (rollP 5) [Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t] [buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t]) (k := 5) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 5) (by omega) (buQW_szl_succ_le hW2 (k := 5) (by omega))
  have hW3 : ∀ x ∈ ([buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP3 : Pipe main (pickP 2) [buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.pick main hpick (A := [buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc]) (k := 2) (by simp)) ?_
    exact buQW_opc_le hKpick hSB1 (k := 2) (by omega) (buQW_szl_succ_le hW3 (k := 2) (by omega))
  have hW4 : ∀ x ∈ ([Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP4 : Pipe main (pickP 2) [Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.pick main hpick (A := [Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc]) (k := 2) (by simp)) ?_
    exact buQW_opc_le hKpick hSB1 (k := 2) (by omega) (buQW_szl_succ_le hW4 (k := 2) (by omega))
  have hW5 : ∀ x ∈ ([Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP5 : Pipe main (rollP 7) [Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc]) (k := 7) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 7) (by omega) (buQW_szl_succ_le hW5 (k := 7) (by omega))
  have hW6 : ∀ x ∈ ([cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP6 : Pipe main (rollP 7) [cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v] [cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v]) (k := 7) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 7) (by omega) (buQW_szl_succ_le hW6 (k := 7) (by omega))
  have hW7 : ∀ x ∈ ([cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP7 : Pipe main (rollP 7) [cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ] [Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ]) (k := 7) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 7) (by omega) (buQW_szl_succ_le hW7 (k := 7) (by omega))
  have hW8 : ∀ x ∈ ([Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP8 : Pipe main (pickP 5) [Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.pick main hpick (A := [Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]) (k := 5) (by simp)) ?_
    exact buQW_opc_le hKpick hSB1 (k := 5) (by omega) (buQW_szl_succ_le hW8 (k := 5) (by omega))
  have hW9 : ∀ x ∈ ([buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP9 : Pipe main (pickP 4) [buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.pick main hpick (A := [buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]) (k := 4) (by simp)) ?_
    exact buQW_opc_le hKpick hSB1 (k := 4) (by omega) (buQW_szl_succ_le hW9 (k := 4) (by omega))
  have hW10 : ∀ x ∈ ([Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP10 : Pipe main (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) [Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [cfxVal ((0 : ℤ), (0 : ℤ)), Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.pushOnAny (hpush main (cfxVal ((0 : ℤ), (0 : ℤ))))) ?_
    rw [hzvsz]
    calc Kpush * (5 + 1) ≤ KS * (5 + 1) := Nat.mul_le_mul_right _ hKpush
      _ ≤ KS * (100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := Nat.mul_le_mul_left _ (by nlinarith [hY1])
      _ = (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by ring
  have hW11 : ∀ x ∈ ([cfxVal ((0 : ℤ), (0 : ℤ)), Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP11 : Pipe main (rollP 1) [cfxVal ((0 : ℤ), (0 : ℤ)), Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [Val.int (s : ℤ), cfxVal ((0 : ℤ), (0 : ℤ)), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [cfxVal ((0 : ℤ), (0 : ℤ)), Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]) (k := 1) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 1) (by omega) (buQW_szl_succ_le hW11 (k := 1) (by omega))
  have hW12 : ∀ x ∈ ([Val.int (s : ℤ), cfxVal ((0 : ℤ), (0 : ℤ)), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP12 : Pipe main (repP) [Val.int (s : ℤ), cfxVal ((0 : ℤ), (0 : ℤ)), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    intro rest vs hvs st0 R hR
    have hv2 : vs = .int (s : ℤ) :: cfxVal ((0 : ℤ), (0 : ℤ)) :: ([buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] ++ rest) := by rw [hvs]; rfl
    obtain ⟨out, st1, n1, ⟨r', hr', hout⟩, hev, hn, hstk, hoth⟩ :=
      (hrep main s (cfxVal ((0 : ℤ), (0 : ℤ)))) vs ⟨[buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] ++ rest, hv2⟩ st0 R hR
    have h3 : r' = [buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] ++ rest := (List.cons.inj (List.cons.inj (hr'.symm.trans hv2)).2).2
    refine ⟨out, st1, n1, ?_, hev, ?_, hstk, hoth⟩
    · rw [hout, h3]; rfl
    · have h9 : (s + 1) * (vsz (cfxVal ((0 : ℤ), (0 : ℤ))) + 1) + isz (s : ℤ) + 1 ≤ 9 * (s + 1) := by
        rw [hzvsz]
        have h1 : isz (s : ℤ) ≤ 2 * (s + 1) := by
          have hs2 : s < 2 ^ (s + 1) := by
            have := Nat.lt_two_pow_self (n := s + 1); omega
          have hsz : s.size ≤ s + 1 := Nat.size_le.mpr hs2
          simp only [isz, Int.natAbs_natCast]
          omega
        omega
      calc n1 ≤ Krep * ((s + 1) * (vsz (cfxVal ((0 : ℤ), (0 : ℤ))) + 1) + isz (s : ℤ) + 1) := hn
        _ ≤ KS * (9 * (s + 1)) := Nat.mul_le_mul hKrep h9
        _ ≤ KS * (100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := Nat.mul_le_mul_left _ (by nlinarith [hsY])
        _ = (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by ring
  have hW13 : ∀ x ∈ ([ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] : List Val), vsz x ≤ (1000 * ((egM p α + 1) * (s + 1) * (p + 1))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hSg | exact hVV | exact hAV | exact hBT | exact hSh | exact hPh | exact hzv | exact hZ0
  have hP13 : Pipe main (rollP 1) [ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) := by
    refine Pipe.le (Pipe.roll main hroll (A := [ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]) (k := 1) (by simp)) ?_
    exact buQW_opc_le hKroll hSB1 (k := 1) (by omega) (buQW_szl_succ_le hW13 (k := 1) (by omega))
  have hskip : Pipe main Cmd.skip [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] 1 := by
    intro rest vs hvs s0 R hR
    exact ⟨vs, s0, 1, hvs, Eval.skip s0, le_rfl, hR, fun k _ => rfl⟩
  have g13 : Pipe main (Cmd.seq (rollP 1) (Cmd.skip)) [ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)) := by
    show Pipe main (Cmd.seq (rollP 1) Cmd.skip) [ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))
    exact Pipe.comp hP13 hskip
  have g12 : Pipe main (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))) [Val.int (s : ℤ), cfxVal ((0 : ℤ), (0 : ℤ)), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))) := by
    show Pipe main (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))) [Val.int (s : ℤ), cfxVal ((0 : ℤ), (0 : ℤ)), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))
    exact Pipe.comp hP12 g13
  have g11 : Pipe main (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))) [cfxVal ((0 : ℤ), (0 : ℤ)), Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))) := by
    show Pipe main (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))) [cfxVal ((0 : ℤ), (0 : ℤ)), Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))
    exact Pipe.comp hP11 g12
  have g10 : Pipe main (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))) [Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))) := by
    show Pipe main (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))) [Val.int (s : ℤ), buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))
    exact Pipe.comp hP10 g11
  have g9 : Pipe main (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))) [buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))) := by
    show Pipe main (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))) [buColsT p α s t, Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))
    exact Pipe.comp hP9 g10
  have g8 : Pipe main (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))) [Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))) := by
    show Pipe main (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))) [Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))
    exact Pipe.comp hP8 g9
  have g7 : Pipe main (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))) [cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))) := by
    show Pipe main (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))) [cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))
    exact Pipe.comp hP7 g8
  have g6 : Pipe main (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))) [cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))) := by
    show Pipe main (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))) [cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))))
    exact Pipe.comp hP6 g7
  have g5 : Pipe main (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))))) [Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))))) := by
    show Pipe main (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))))) [Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))
    exact Pipe.comp hP5 g6
  have g4 : Pipe main (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))))) [Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))) := by
    show Pipe main (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))))) [Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))))))
    exact Pipe.comp hP4 g5
  have g3 : Pipe main (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))))))) [buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))))))) := by
    show Pipe main (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))))))) [buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))))
    exact Pipe.comp hP3 g4
  have g2 : Pipe main (Cmd.seq (rollP 5) (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))))))) [Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))))) := by
    show Pipe main (Cmd.seq (rollP 5) (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))))))) [Val.int (s : ℤ), Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))))))))
    exact Pipe.comp hP2 g3
  have g1 : Pipe main (Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))))))))) [Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))))))))) := by
    show Pipe main (Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip)))))))))))))) [Val.int (p : ℤ), Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))))))
    exact Pipe.comp hP1 g2
  have g0 : Pipe main (Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))))))))) [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))))))) := by
    show Pipe main (Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (rollP 5) (Cmd.seq (pickP 2) (Cmd.seq (pickP 2) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (Cmd.seq (pickP 5) (Cmd.seq (pickP 4) (Cmd.seq (pushP (cfxVal ((0 : ℤ), (0 : ℤ)))) (Cmd.seq (rollP 1) (Cmd.seq (repP) (Cmd.seq (rollP 1) (Cmd.skip))))))))))))))) [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1)))))))))))))))
    exact Pipe.comp hP0 g1
  refine Pipe.le (show Pipe main (buR1SetupProg pickP rollP pushP repP) [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), Val.int σ, cvecVal v, cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ), buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))))))) from g0) ?_
  calc ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + ((KS * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1)))) + 1))))))))))))))
      = 1400000 * (KS * ((egM p α + 1) * (s + 1) * (p + 1))) + 1 := by ring
    _ ≤ 2000000 * (KS * ((egM p α + 1) * (s + 1) * (p + 1))) := by
        have h2 : 1 ≤ KS * ((egM p α + 1) * (s + 1) * (p + 1)) := by
          have h3 : 1 * 1 ≤ KS * ((egM p α + 1) * (s + 1) * (p + 1)) := Nat.mul_le_mul hKS1 hY1
          simpa using h3
        calc 1400000 * (KS * ((egM p α + 1) * (s + 1) * (p + 1))) + 1
            ≤ 1400000 * (KS * ((egM p α + 1) * (s + 1) * (p + 1))) + (KS * ((egM p α + 1) * (s + 1) * (p + 1))) := Nat.add_le_add_left h2 _ 
          _ = 1400001 * (KS * ((egM p α + 1) * (s + 1) * (p + 1))) := by ring
          _ ≤ 2000000 * (KS * ((egM p α + 1) * (s + 1) * (p + 1))) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1)) := by ring

end Work.Resample
