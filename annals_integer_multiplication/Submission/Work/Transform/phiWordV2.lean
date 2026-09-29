import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.phiAux
import Submission.Work.Transform.phiChunkDefs
import Submission.Work.Transform.chunkArrFacts
import Submission.Work.Transform.ofListChunkVals
import Submission.Work.Transform.phiZipWord
import Submission.Work.Transform.phiDrop
import Submission.Work.Kernel.Raw

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Work.Transform

open HvdH

/-! ## Small arithmetic helpers (kept separate so that the big `WordR` assemblies only
use cheap tactics on tiny goals) -/

/-- Sum of the sizes of the first three values of a list starting `a :: b :: int r`. -/
theorem take3_sum_eq (a b : Val) (r : ℕ) (tl : List Val) :
    (((a :: b :: Val.int (r : ℤ) :: tl).take 3).map vsz).sum = vsz a + vsz b + isz (r : ℤ) := by
  simp [vsz_int]
  omega

theorem p_sq_ge (p : ℕ) (hp : 100 ≤ p) : 10000 ≤ p ^ 2 := by nlinarith [hp]

/-- `(M+1) * (r+2)` is dominated by `3·M·r·p² + 2(r+1)` for `p ≥ 100`, `r ≥ 2`. -/
theorem succ_mul_le (M r p : ℕ) (hp : 100 ≤ p) (hr : 2 ≤ r) :
    (M + 1) * (r + 2) ≤ 3 * (M * r * p ^ 2) + 2 * (r + 1) := by
  have hp2 : 10000 ≤ p ^ 2 := p_sq_ge p hp
  have hpr : r + 2 ≤ r * p ^ 2 := by
    calc r + 2 ≤ r * 10000 := by omega
      _ ≤ r * p ^ 2 := Nat.mul_le_mul_left r hp2
  have hm1 : M * (r + 2) ≤ M * (r * p ^ 2) := Nat.mul_le_mul_left M hpr
  have haux : M * (r * p ^ 2) = M * r * p ^ 2 := by ring
  nlinarith [hm1, haux, hr]

/-- Cost of the `pick 2` step (`KernelLib.pick`); both operand bounds are `400` (the coarse
estimates from `vsz_rarrVal_le`), so the constant is `3000`. -/
theorem pickCost (K M r p A B : ℕ) (hA : A ≤ 400 * (M * r * p ^ 2 + 1))
    (hB : B ≤ 400 * (M * r * p ^ 2 + 1)) (hsz : isz (r : ℤ) ≤ r + 2) :
    K * 3 * (A + B + isz (r : ℤ) + 1) ≤ 3000 * K * (M * r * p ^ 2 + r + 1) := by
  have hX : 0 ≤ M * r * p ^ 2 := Nat.zero_le _
  have h1 : A + B + isz (r : ℤ) + 1 ≤ 1000 * (M * r * p ^ 2 + r + 1) := by omega
  calc K * 3 * (A + B + isz (r : ℤ) + 1) = K * (3 * (A + B + isz (r : ℤ) + 1)) := by ring
    _ ≤ K * (3 * (1000 * (M * r * p ^ 2 + r + 1))) :=
        Nat.mul_le_mul_left K (Nat.mul_le_mul_left 3 h1)
    _ = 3000 * K * (M * r * p ^ 2 + r + 1) := by ring

/-- Cost of a `LayoutLib.chunksOf` step. -/
theorem chunkCost (K M r p A : ℕ) (hA : A ≤ 200 * (M * r * p ^ 2 + 1))
    (hsz : isz (r : ℤ) ≤ r + 2)
    (hmul : (M + 1) * isz (r : ℤ) ≤ 3 * (M * r * p ^ 2) + 2 * (r + 1)) :
    K * (A + (M + 1) * isz (r : ℤ) + 1) ≤ 1000 * K * (M * r * p ^ 2 + r + 1) := by
  have hX : 0 ≤ M * r * p ^ 2 := Nat.zero_le _
  have h1 : A + (M + 1) * isz (r : ℤ) + 1 ≤ 1000 * (M * r * p ^ 2 + r + 1) := by omega
  calc K * (A + (M + 1) * isz (r : ℤ) + 1) ≤ K * (1000 * (M * r * p ^ 2 + r + 1)) :=
        Nat.mul_le_mul_left K h1
    _ = 1000 * K * (M * r * p ^ 2 + r + 1) := by ring

/-- Cost of a `KernelLib.swap` step (two `400`-bounded operands). -/
theorem swapCost (K M r p C B : ℕ) (hC : C ≤ 400 * (M * r * p ^ 2 + 1))
    (hB : B ≤ 400 * (M * r * p ^ 2 + 1)) :
    K * (C + B + 1) ≤ 1000 * K * (M * r * p ^ 2 + r + 1) := by
  have hX : 0 ≤ M * r * p ^ 2 := Nat.zero_le _
  have h1 : C + B + 1 ≤ 1000 * (M * r * p ^ 2 + r + 1) := by omega
  calc K * (C + B + 1) ≤ K * (1000 * (M * r * p ^ 2 + r + 1)) := Nat.mul_le_mul_left K h1
    _ = 1000 * K * (M * r * p ^ 2 + r + 1) := by ring

/-- Cost of the `KernelLib.roll 2` step (two `400`-bounded operands). -/
theorem rollCost (K M r p C D : ℕ) (hC : C ≤ 400 * (M * r * p ^ 2 + 1))
    (hD : D ≤ 400 * (M * r * p ^ 2 + 1)) (hsz : isz (r : ℤ) ≤ r + 2) :
    K * 3 * (C + D + isz (r : ℤ) + 1) ≤ 3000 * K * (M * r * p ^ 2 + r + 1) := by
  have hX : 0 ≤ M * r * p ^ 2 := Nat.zero_le _
  have h1 : C + D + isz (r : ℤ) + 1 ≤ 1000 * (M * r * p ^ 2 + r + 1) := by omega
  calc K * 3 * (C + D + isz (r : ℤ) + 1) = K * (3 * (C + D + isz (r : ℤ) + 1)) := by ring
    _ ≤ K * (3 * (1000 * (M * r * p ^ 2 + r + 1))) :=
        Nat.mul_le_mul_left K (Nat.mul_le_mul_left 3 h1)
    _ = 3000 * K * (M * r * p ^ 2 + r + 1) := by ring

/-- Cost of the final `KernelLib.drop`. -/
theorem dropCost (K M r p : ℕ) (hsz : isz (r : ℤ) ≤ r + 2) :
    K * (isz (r : ℤ) + 1) ≤ 500 * K * (M * r * p ^ 2 + r + 1) := by
  have hX : 0 ≤ M * r * p ^ 2 := Nat.zero_le _
  have h1 : isz (r : ℤ) + 1 ≤ 500 * (M * r * p ^ 2 + r + 1) := by omega
  calc K * (isz (r : ℤ) + 1) ≤ K * (500 * (M * r * p ^ 2 + r + 1)) := Nat.mul_le_mul_left K h1
    _ = 500 * K * (M * r * p ^ 2 + r + 1) := by ring

/-- Combination of the eight step costs of the chunking phase. -/
theorem costSum8 (Kpk Kck Ksw Krl Kdr X Y n1 n2 n3 n4 n5 n6 n7 n8 : ℕ) (hXY : X ≤ Y)
    (h1 : n1 ≤ 3000 * Kpk * X) (h2 : n2 ≤ 1000 * Kck * X) (h3 : n3 ≤ 1000 * Ksw * X)
    (h4 : n4 ≤ 3000 * Kpk * X) (h5 : n5 ≤ 1000 * Kck * X) (h6 : n6 ≤ 1000 * Ksw * X)
    (h7 : n7 ≤ 3000 * Krl * X) (h8 : n8 ≤ 500 * Kdr * X) :
    n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + n8))))))
      ≤ 14000 * (Kpk + Kck + Ksw + Krl + Kdr) * Y := by
  have e1 : n1 ≤ 3000 * Kpk * Y := le_trans h1 (Nat.mul_le_mul_left (3000 * Kpk) hXY)
  have e2 : n2 ≤ 1000 * Kck * Y := le_trans h2 (Nat.mul_le_mul_left (1000 * Kck) hXY)
  have e3 : n3 ≤ 1000 * Ksw * Y := le_trans h3 (Nat.mul_le_mul_left (1000 * Ksw) hXY)
  have e4 : n4 ≤ 3000 * Kpk * Y := le_trans h4 (Nat.mul_le_mul_left (3000 * Kpk) hXY)
  have e5 : n5 ≤ 1000 * Kck * Y := le_trans h5 (Nat.mul_le_mul_left (1000 * Kck) hXY)
  have e6 : n6 ≤ 1000 * Ksw * Y := le_trans h6 (Nat.mul_le_mul_left (1000 * Ksw) hXY)
  have e7 : n7 ≤ 3000 * Krl * Y := le_trans h7 (Nat.mul_le_mul_left (3000 * Krl) hXY)
  have e8 : n8 ≤ 500 * Kdr * Y := le_trans h8 (Nat.mul_le_mul_left (500 * Kdr) hXY)
  nlinarith [e1, e2, e3, e4, e5, e6, e7, e8]

/-- Final absorption of the eight-fold cost bound into `K * P + K`. -/
theorem costFinal (Ksum P : ℕ) :
    14000 * Ksum * P ≤ (20000 * Ksum + 20000) * P + (20000 * Ksum + 20000) := by
  have h1 : 14000 * Ksum ≤ 20000 * Ksum + 20000 := by omega
  calc 14000 * Ksum * P ≤ (20000 * Ksum + 20000) * P := Nat.mul_le_mul_right P h1
    _ ≤ (20000 * Ksum + 20000) * P + (20000 * Ksum + 20000) := Nat.le_add_right _ _

/-- The complete cost bound of the chunking phase: the eight individual step costs (in the form
delivered by `step1` … `step8` of `phiChunkWordAll`) add up to the stated `K * (… ) + K`. -/
theorem chunkCostTotal (Kpk Kck Ksw Krl Kdr M r p n1 n2 n3 n4 n5 n6 n7 n8 : ℕ)
    (hn1 : n1 ≤ 3000 * Kpk * (M * r * p ^ 2 + r + 1))
    (hn2 : n2 ≤ 1000 * Kck * (M * r * p ^ 2 + r + 1))
    (hn3 : n3 ≤ 1000 * Ksw * (M * r * p ^ 2 + r + 1))
    (hn4 : n4 ≤ 3000 * Kpk * (M * r * p ^ 2 + r + 1))
    (hn5 : n5 ≤ 1000 * Kck * (M * r * p ^ 2 + r + 1))
    (hn6 : n6 ≤ 1000 * Ksw * (M * r * p ^ 2 + r + 1))
    (hn7 : n7 ≤ 3000 * Krl * (M * r * p ^ 2 + r + 1))
    (hn8 : n8 ≤ 500 * Kdr * (M * r * p ^ 2 + r + 1)) :
    n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + n8))))))
      ≤ (20000 * (Kpk + Kck + Ksw + Krl + Kdr) + 20000) * ((M * r) * p ^ 2 + r + 1)
        + (20000 * (Kpk + Kck + Ksw + Krl + Kdr) + 20000) := by
  have esum := costSum8 Kpk Kck Ksw Krl Kdr (M * r * p ^ 2 + r + 1) (M * r * p ^ 2 + r + 1)
    n1 n2 n3 n4 n5 n6 n7 n8 le_rfl hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8
  exact le_trans esum (costFinal (Kpk + Kck + Ksw + Krl + Kdr) (M * r * p ^ 2 + r + 1))

/-! ## The chunking phase, valid for every `M` -/

/-- Chunking phase of paper Prop 3.5's `T̃`, valid for **every** `M` (in particular `M = 0`), with
the cost bound that also pays for erasing the parameter `int r`.

Intended program: `KernelLib.pick 2` (copy `int r` to the top); `LayoutLib.chunksOf r` (applied to
`cvecVal x`); `KernelLib.swap`; `KernelLib.pick 2`; `LayoutLib.chunksOf r` (applied to `cvecVal zt`);
`KernelLib.swap`; `KernelLib.roll 2`; `KernelLib.drop` (removing the leftover `int r`).

This is `Work.Transform.phiChunkWord` with the hypothesis `1 ≤ M` dropped and the cost bound
strengthened to `K * ((M*r)*p^2 + r + 1) + K`.  At `M = 0` the length hypotheses force
`x = zt = []`, so `cvecVal x = cvecVal zt = Val.nil` and the run costs `O(isz r)`; the extra
`+ r + 1` covers that (and is harmless for `M ≥ 1`). -/
theorem phiChunkWordAll : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib →
    ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p r M : ℕ) (x zt : List (ℤ × ℤ)) (R : List Val),
      x.length = M * r → zt.length = M * r → InDiscVec p (M * r) x → InDiscVec p (M * r) zt →
      100 ≤ p → 2 ≤ r →
      WordR main prog
        (fun vs => vs = cvecVal x :: cvecVal zt :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
        (fun vs out => ∃ (a b : List (List (ℤ × ℤ))),
            out = rarrVal a :: rarrVal b :: Val.int (p : ℤ) :: R ∧
            a.length = M ∧ b.length = M ∧
            (∀ i < M, (a.getD i []).length = r) ∧ (∀ i < M, (b.getD i []).length = r) ∧
            (∀ i < M, ∀ c < r, (a.getD i []).getD c (0, 0) = x.getD (i * r + c) (0, 0)) ∧
            (∀ i < M, ∀ c < r, (b.getD i []).getD c (0, 0) = zt.getD (i * r + c) (0, 0)))
        (fun _ => K * ((M * r) * p ^ 2 + r + 1) + K) := by
  intro Kl Il La
  obtain ⟨pickP, Kpk, hpick⟩ := Kl.pick
  obtain ⟨swapP, Ksw, hswap⟩ := Kl.swap
  obtain ⟨rollP, Krl, hroll⟩ := Kl.roll
  obtain ⟨drpP, Kdr, hdrop⟩ := Kl.drop
  obtain ⟨chunkP, Kck, hck⟩ := La.chunksOf
  refine ⟨Cmd.seq (pickP 2) (Cmd.seq chunkP (Cmd.seq swapP (Cmd.seq (pickP 2)
      (Cmd.seq chunkP (Cmd.seq swapP (Cmd.seq (rollP 2) drpP)))))),
    20000 * (Kpk + Kck + Ksw + Krl + Kdr) + 20000, ?_⟩
  intro main p r M x zt R hx hzt hdx hdzt hp hr
  -- ## auxiliary bounds
  have hA : vsz (cvecVal x) ≤ 200 * (M * r * p ^ 2 + 1) := vsz_cvecVal_le hdx hp
  have hB : vsz (cvecVal zt) ≤ 200 * (M * r * p ^ 2 + 1) := vsz_cvecVal_le hdzt hp
  have hA' : vsz (ofList (x.map cfxVal)) ≤ 200 * (M * r * p ^ 2 + 1) := hA
  have hB' : vsz (ofList (zt.map cfxVal)) ≤ 200 * (M * r * p ^ 2 + 1) := hB
  have hszr : isz (r : ℤ) ≤ r + 2 := by simpa using isz_le (r : ℤ)
  have hA400 : vsz (cvecVal x) ≤ 400 * (M * r * p ^ 2 + 1) :=
    le_trans hA (Nat.mul_le_mul_right (M * r * p ^ 2 + 1) (by omega))
  have hB400 : vsz (cvecVal zt) ≤ 400 * (M * r * p ^ 2 + 1) :=
    le_trans hB (Nat.mul_le_mul_right (M * r * p ^ 2 + 1) (by omega))
  have hmr : (M + 1) * (r + 2) ≤ 3 * (M * r * p ^ 2) + 2 * (r + 1) := succ_mul_le M r p hp hr
  have hmul : (M + 1) * isz (r : ℤ) ≤ 3 * (M * r * p ^ 2) + 2 * (r + 1) :=
    calc (M + 1) * isz (r : ℤ) ≤ (M + 1) * (r + 2) := Nat.mul_le_mul_left _ hszr
      _ ≤ _ := hmr
  -- ## facts about the chunks
  have hcxlen : (chunkArr M r x).length = M := chunkArr_length M r x
  have hczlen : (chunkArr M r zt).length = M := chunkArr_length M r zt
  have hcl : ∀ i < M, ((chunkArr M r x).getD i []).length = r := by
    intro i hi
    rw [chunkArr_getD hi, List.length_take, List.length_drop]
    have h1 : i * r + r ≤ x.length := by
      rw [hx]
      calc i * r + r = (i + 1) * r := by ring
        _ ≤ M * r := Nat.mul_le_mul_right r (by omega)
    omega
  have hcl2 : ∀ i < M, ((chunkArr M r zt).getD i []).length = r := by
    intro i hi
    rw [chunkArr_getD hi, List.length_take, List.length_drop]
    have h1 : i * r + r ≤ zt.length := by
      rw [hzt]
      calc i * r + r = (i + 1) * r := by ring
        _ ≤ M * r := Nat.mul_le_mul_right r (by omega)
    omega
  have hv : ∀ i < M, ∀ c < r, ((chunkArr M r x).getD i []).getD c (0, 0)
      = x.getD (i * r + c) (0, 0) := by
    intro i hi c hc
    rw [chunkArr_getD hi]
    exact getD_drop_take x (i * r) r c (0, 0) hc
  have hv2 : ∀ i < M, ∀ c < r, ((chunkArr M r zt).getD i []).getD c (0, 0)
      = zt.getD (i * r + c) (0, 0) := by
    intro i hi c hc
    rw [chunkArr_getD hi]
    exact getD_drop_take zt (i * r) r c (0, 0) hc
  have hIAx : InDiscArr p M r (chunkArr M r x) := inDiscArr_of_chunks hdx hcxlen hcl hv
  have hIAz : InDiscArr p M r (chunkArr M r zt) := inDiscArr_of_chunks hdzt hczlen hcl2 hv2
  have hCx : vsz (ofList (chunkVals r x)) ≤ 400 * (M * r * p ^ 2 + 1) := by
    rw [ofListChunkVals hx (by omega)]
    exact vsz_rarrVal_le hIAx hp hr
  have hCz : vsz (ofList (chunkVals r zt)) ≤ 400 * (M * r * p ^ 2 + 1) := by
    rw [ofListChunkVals hzt (by omega)]
    exact vsz_rarrVal_le hIAz hp hr
  -- ## the eight steps
  have step1 : WordR main (pickP 2)
      (fun vs => vs = cvecVal x :: cvecVal zt :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = Val.int (r : ℤ) :: cvecVal x :: cvecVal zt
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ => 3000 * Kpk * (M * r * p ^ 2 + r + 1)) := by
    refine Work.Kernel.WordR_conseq (hpick main 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      rw [hvs]
      rw [take3_sum_eq]
      exact pickCost Kpk M r p (vsz (cvecVal x)) (vsz (cvecVal zt)) hA400 hB400 hszr
  have step2 : WordR main chunkP
      (fun vs => vs = Val.int (r : ℤ) :: cvecVal x :: cvecVal zt
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = ofList (chunkVals r x) :: cvecVal zt
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ => 1000 * Kck * (M * r * p ^ 2 + r + 1)) := by
    have hdvd : r ∣ (x.map cfxVal).length := by
      rw [List.length_map, hx]
      exact ⟨M, Nat.mul_comm M r⟩
    refine Work.Kernel.WordR_conseq (hck main r (x.map cfxVal) (by omega) hdvd) ?_ ?_ ?_
    · intro vs hvs
      exact ⟨cvecVal zt :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R, by rw [hvs]; rfl⟩
    · intro vs out hvs hout
      obtain ⟨rest, hvs', hout'⟩ := hout
      rw [hvs] at hvs'
      have hrest : rest = cvecVal zt :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R := by
        have h2 := (List.cons.inj hvs').2
        exact ((List.cons.inj h2).2).symm
      rw [hout', hrest]
      rfl
    · intro vs hvs
      have hdiv : (x.map cfxVal).length / r = M := by
        rw [List.length_map, hx]
        exact Nat.mul_div_left M (by omega)
      rw [hdiv]
      exact chunkCost Kck M r p (vsz (ofList (x.map cfxVal))) hA' hszr hmul
  have step3 : WordR main swapP
      (fun vs => vs = ofList (chunkVals r x) :: cvecVal zt
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = cvecVal zt :: ofList (chunkVals r x)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ => 1000 * Ksw * (M * r * p ^ 2 + r + 1)) := by
    refine Work.Kernel.WordR_conseq (hswap main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      obtain ⟨a, b, rest, hvs', hout'⟩ := hout
      rw [hvs] at hvs'
      obtain ⟨ha, h2⟩ := List.cons.inj hvs'
      obtain ⟨hb, hrest⟩ := List.cons.inj h2
      rw [← ha, ← hb, ← hrest] at hout'
      exact hout'
    · intro vs hvs
      rw [hvs]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      exact swapCost Ksw M r p (vsz (ofList (chunkVals r x))) (vsz (cvecVal zt)) hCx hB400
  have step4 : WordR main (pickP 2)
      (fun vs => vs = cvecVal zt :: ofList (chunkVals r x)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = Val.int (r : ℤ) :: cvecVal zt :: ofList (chunkVals r x)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ => 3000 * Kpk * (M * r * p ^ 2 + r + 1)) := by
    refine Work.Kernel.WordR_conseq (hpick main 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      rw [hvs]
      rw [take3_sum_eq]
      exact pickCost Kpk M r p (vsz (cvecVal zt)) (vsz (ofList (chunkVals r x))) hB400 hCx hszr
  have step5 : WordR main chunkP
      (fun vs => vs = Val.int (r : ℤ) :: cvecVal zt :: ofList (chunkVals r x)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = ofList (chunkVals r zt) :: ofList (chunkVals r x)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ => 1000 * Kck * (M * r * p ^ 2 + r + 1)) := by
    have hdvd : r ∣ (zt.map cfxVal).length := by
      rw [List.length_map, hzt]
      exact ⟨M, Nat.mul_comm M r⟩
    refine Work.Kernel.WordR_conseq (hck main r (zt.map cfxVal) (by omega) hdvd) ?_ ?_ ?_
    · intro vs hvs
      exact ⟨ofList (chunkVals r x) :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R,
        by rw [hvs]; rfl⟩
    · intro vs out hvs hout
      obtain ⟨rest, hvs', hout'⟩ := hout
      rw [hvs] at hvs'
      have hrest : rest = ofList (chunkVals r x) :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R := by
        have h2 := (List.cons.inj hvs').2
        exact ((List.cons.inj h2).2).symm
      rw [hout', hrest]
      rfl
    · intro vs hvs
      have hdiv : (zt.map cfxVal).length / r = M := by
        rw [List.length_map, hzt]
        exact Nat.mul_div_left M (by omega)
      rw [hdiv]
      exact chunkCost Kck M r p (vsz (ofList (zt.map cfxVal))) hB' hszr hmul
  have step6 : WordR main swapP
      (fun vs => vs = ofList (chunkVals r zt) :: ofList (chunkVals r x)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = ofList (chunkVals r x) :: ofList (chunkVals r zt)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ => 1000 * Ksw * (M * r * p ^ 2 + r + 1)) := by
    refine Work.Kernel.WordR_conseq (hswap main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      obtain ⟨a, b, rest, hvs', hout'⟩ := hout
      rw [hvs] at hvs'
      obtain ⟨ha, h2⟩ := List.cons.inj hvs'
      obtain ⟨hb, hrest⟩ := List.cons.inj h2
      rw [← ha, ← hb, ← hrest] at hout'
      exact hout'
    · intro vs hvs
      rw [hvs]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      exact swapCost Ksw M r p (vsz (ofList (chunkVals r zt))) (vsz (ofList (chunkVals r x))) hCz hCx
  have step7 : WordR main (rollP 2)
      (fun vs => vs = ofList (chunkVals r x) :: ofList (chunkVals r zt)
        :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = Val.int (r : ℤ) :: ofList (chunkVals r x)
        :: ofList (chunkVals r zt) :: Val.int (p : ℤ) :: R)
      (fun _ => 3000 * Krl * (M * r * p ^ 2 + r + 1)) := by
    refine Work.Kernel.WordR_conseq (hroll main 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      rw [hvs]
      rw [take3_sum_eq]
      exact rollCost Krl M r p (vsz (ofList (chunkVals r x))) (vsz (ofList (chunkVals r zt)))
        hCx hCz hszr
  have step8 : WordR main drpP
      (fun vs => vs = Val.int (r : ℤ) :: ofList (chunkVals r x)
        :: ofList (chunkVals r zt) :: Val.int (p : ℤ) :: R)
      (fun _ out => out = ofList (chunkVals r x) :: ofList (chunkVals r zt)
        :: Val.int (p : ℤ) :: R)
      (fun _ => 500 * Kdr * (M * r * p ^ 2 + r + 1)) := by
    refine Work.Kernel.WordR_conseq (hdrop main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp
    · intro vs out hvs hout
      obtain ⟨v, rest, hvs', hout'⟩ := hout
      rw [hvs] at hvs'
      obtain ⟨hv, hrest⟩ := List.cons.inj hvs'
      rw [hout', ← hrest]
    · intro vs hvs
      rw [hvs]
      simp only [List.headD_cons, vsz_int]
      exact dropCost Kdr M r p hszr
  -- ## composition
  intro vs hvs s Rg hstk
  obtain ⟨out1, s1, n1, hout1, he1, hn1, hstk1, hoth1⟩ := step1 vs hvs s Rg hstk
  obtain ⟨out2, s2, n2, hout2, he2, hn2, hstk2, hoth2⟩ := step2 out1 hout1 s1 Rg hstk1
  obtain ⟨out3, s3, n3, hout3, he3, hn3, hstk3, hoth3⟩ := step3 out2 hout2 s2 Rg hstk2
  obtain ⟨out4, s4, n4, hout4, he4, hn4, hstk4, hoth4⟩ := step4 out3 hout3 s3 Rg hstk3
  obtain ⟨out5, s5, n5, hout5, he5, hn5, hstk5, hoth5⟩ := step5 out4 hout4 s4 Rg hstk4
  obtain ⟨out6, s6, n6, hout6, he6, hn6, hstk6, hoth6⟩ := step6 out5 hout5 s5 Rg hstk5
  obtain ⟨out7, s7, n7, hout7, he7, hn7, hstk7, hoth7⟩ := step7 out6 hout6 s6 Rg hstk6
  obtain ⟨out8, s8, n8, hout8, he8, hn8, hstk8, hoth8⟩ := step8 out7 hout7 s7 Rg hstk7
  refine ⟨out8, s8, n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + n8)))))), ?_, ?_, ?_, hstk8, ?_⟩
  · refine ⟨chunkArr M r x, chunkArr M r zt, ?_, hcxlen, hczlen, hcl, hcl2, hv, hv2⟩
    rw [hout8, ofListChunkVals hx (by omega), ofListChunkVals hzt (by omega)]
  · exact Eval.seq he1 (Eval.seq he2 (Eval.seq he3 (Eval.seq he4
      (Eval.seq he5 (Eval.seq he6 (Eval.seq he7 he8))))))
  · exact chunkCostTotal Kpk Kck Ksw Krl Kdr M r p n1 n2 n3 n4 n5 n6 n7 n8
      hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8
  · intro k hk
    rw [hoth8 k hk, hoth7 k hk, hoth6 k hk, hoth5 k hk, hoth4 k hk, hoth3 k hk,
      hoth2 k hk, hoth1 k hk]

/-! ## Cost combination for `phiWordV2` -/

theorem phiWordCostCombine (KC KZ KD S p r n1 n2 n3 : ℕ)
    (hn1 : n1 ≤ KC * (S + r + 1) + KC) (hn2 : n2 ≤ KZ * S + KZ)
    (hn3 : n3 ≤ KD * (400 * (S + 1) + p + 3)) :
    n1 + (n2 + n3) ≤ (3 * (2 * KC + KZ + 2000 * KD + 3)) * (S + p + r + 1)
      + 3 * (2 * KC + KZ + 2000 * KD + 3) := by
  have hC1 : n1 ≤ (2 * KC + KZ + 2000 * KD + 3) * (S + p + r + 1)
      + (2 * KC + KZ + 2000 * KD + 3) := by
    have a : (S + r + 1) * KC ≤ (S + r + 1) * (2 * KC + KZ + 2000 * KD + 3) :=
      Nat.mul_le_mul_left (S + r + 1) (by omega)
    have b : (S + r + 1) * (2 * KC + KZ + 2000 * KD + 3)
        ≤ (S + p + r + 1) * (2 * KC + KZ + 2000 * KD + 3) :=
      Nat.mul_le_mul_right (2 * KC + KZ + 2000 * KD + 3) (by omega)
    linarith [hn1, a, b]
  have hC2 : n2 ≤ (2 * KC + KZ + 2000 * KD + 3) * (S + p + r + 1)
      + (2 * KC + KZ + 2000 * KD + 3) := by
    have a : KZ * S ≤ (2 * KC + KZ + 2000 * KD + 3) * S :=
      Nat.mul_le_mul_right S (by omega)
    have b : (2 * KC + KZ + 2000 * KD + 3) * S
        ≤ (2 * KC + KZ + 2000 * KD + 3) * (S + p + r + 1) :=
      Nat.mul_le_mul_left (2 * KC + KZ + 2000 * KD + 3) (by omega)
    linarith [hn2, a, b]
  have hC3 : n3 ≤ (2 * KC + KZ + 2000 * KD + 3) * (S + p + r + 1)
      + (2 * KC + KZ + 2000 * KD + 3) := by
    have ha : 400 * (S + 1) + p + 3 ≤ 403 * (S + p + r + 1) := by omega
    have hb : KD * (400 * (S + 1) + p + 3) ≤ KD * (403 * (S + p + r + 1)) :=
      Nat.mul_le_mul_left KD ha
    have hc : KD * (403 * (S + p + r + 1))
        ≤ (2 * KC + KZ + 2000 * KD + 3) * (S + p + r + 1) := by
      rw [show KD * (403 * (S + p + r + 1)) = (403 * KD) * (S + p + r + 1) from by ring]
      exact Nat.mul_le_mul_right (S + p + r + 1) (by omega)
    linarith [hn3, hb, hc]
  linarith [hC1, hC2, hC3]

/-- The map `T̃` of Prop 3.5 as an array word: apply `w ↦ Σ_j ζ^j w_j y^j` (which on
coefficient vectors is the pointwise scaling `c ↦ ζ^c w_c`) to each block of `r` consecutive
entries of the input vector `x` (length `M*r`, in `C̃◦`), where `zt` (length `M*r`, in `C̃◦`) is
the stretched `ζ` table.  Intended implementation: `LayoutLib.chunksOf r` on `cvecVal x`, then
`Kernel.mapList` with `Kernel.zipWith` + `FxLib.mulS` against the table, producing the `R`-array
`rarrVal us`.  The `+ p + r + 1` in the cost bound is needed: even at `M = 0` the program must
delete the `int r` and `int p` on the stack (cf. `Submission/Work/Transform/mulWord_refute.lean`). -/
theorem phiWordV2 : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r M : ℕ) (x zt : List (ℤ × ℤ)) (R : List HvdH.Val),
      x.length = M * r → zt.length = M * r → HvdH.InDiscVec p (M * r) x →
      HvdH.InDiscVec p (M * r) zt → 100 ≤ p → 2 ≤ r →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal x :: HvdH.cvecVal zt :: HvdH.Val.int r ::
          HvdH.Val.int p :: R)
        (fun vs out => ∃ us : List (List (ℤ × ℤ)), out = HvdH.rarrVal us :: R ∧
          us.length = M ∧ HvdH.InDiscArr p M r us ∧ (∀ a < M, (us.getD a []).length = r) ∧
          ∀ a < M, ∀ c < r, (2 : ℝ) ^ p * ‖HvdH.fxC p ((us.getD a []).getD c (0, 0))
            - HvdH.fxC p (zt.getD (a * r + c) (0, 0)) * HvdH.fxC p (x.getD (a * r + c) (0, 0))‖ < 2)
        (fun _ => K * ((M * r) * p ^ 2 + p + r + 1) + K) := by
  intro Kl Il La Fl
  obtain ⟨progC, KC, hC⟩ := phiChunkWordAll Kl Il La
  obtain ⟨progZ, KZ, hZ⟩ := phiZipWord Kl Il Fl
  obtain ⟨progD, KD, hD⟩ := dropParamWord Kl
  refine ⟨Cmd.seq progC (Cmd.seq progZ progD), 3 * (2 * KC + KZ + 2000 * KD + 3), ?_⟩
  intro main p r M x zt R hx hzt hdx hdzt hp hr
  intro vs hvs s Rg hstk
  -- phase 1: chunking
  obtain ⟨mid2, s1, n1, hQ1, he1, hn1, hstk1, hoth1⟩ :=
    hC main p r M x zt R hx hzt hdx hdzt hp hr vs hvs s Rg hstk
  obtain ⟨a, b, hmid1, ha, hb, hla, hlb, hva, hvb⟩ := hQ1
  have hda : InDiscArr p M r a := inDiscArr_of_chunks hdx ha hla hva
  have hdb : InDiscArr p M r b := inDiscArr_of_chunks hdzt hb hlb hvb
  -- phase 2: pointwise products
  obtain ⟨mid3, s2, n2, hQ2, he2, hn2, hstk2, hoth2⟩ :=
    hZ main p r M a b R ha hb hda hdb hp hr mid2 hmid1 s1 Rg hstk1
  obtain ⟨us, hmid2, huslen, hdus, hlenus, herr⟩ := hQ2
  -- phase 3: drop the precision parameter
  obtain ⟨out, s3, n3, hQ3, he3, hn3, hstk3, hoth3⟩ :=
    hD main p (rarrVal us) R mid3 hmid2 s2 Rg hstk2
  have hn3' : n3 ≤ KD * (400 * (M * r * p ^ 2 + 1) + p + 3) := by
    refine le_trans hn3 (Nat.mul_le_mul_left KD ?_)
    have h1 : mid3.getD 0 Val.nil = rarrVal us := by rw [hmid2]; rfl
    have h2 : mid3.getD 1 Val.nil = Val.int (p : ℤ) := by rw [hmid2]; rfl
    have h3 : vsz (rarrVal us) ≤ 400 * (M * r * p ^ 2 + 1) := vsz_rarrVal_le hdus hp hr
    have h4 : isz (p : ℤ) ≤ p + 2 := isz_le _
    rw [h1, h2, vsz_int]
    omega
  refine ⟨out, s3, n1 + (n2 + n3), ?_, ?_, ?_, hstk3, ?_⟩
  · refine ⟨us, hQ3, huslen, hdus, hlenus, ?_⟩
    intro i hi c hc
    rw [← hvb i hi c hc, ← hva i hi c hc]
    exact herr i hi c hc
  · exact Eval.seq he1 (Eval.seq he2 he3)
  · exact phiWordCostCombine KC KZ KD (M * r * p ^ 2) p r n1 n2 n3 hn1 hn2 hn3'
  · intro k hk
    rw [hoth3 k hk, hoth2 k hk, hoth1 k hk]

end Work.Transform
