import Mathlib
import Submission.Work.Fx.LogTwoDefs
import Submission.Work.Fx.LogTwoAux
import Submission.Work.Fx.LogTwoProg
import Submission.Work.Fx.FxAdapt
import Submission.Work.Fx.scaleSteps

/-!
# The `log 2` prologue and epilogue

`logPrologueAux`: from the precision `p₀` build the initial loop window
`[2^logP p₀, 0, 0, logM p₀, p₀]`.
`logEpilogueAux`: from the final loop window `[D, S, c, M, p₀]` (with `S = logS p₀ (logM p₀+1)`)
round the accumulator and leave `[logU p₀]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Fx

open HvdH

/-- Prologue: `[p₀] ↦ [2^logP p₀, 0, 0, logM p₀, p₀]`. -/
theorem logPrologueAux (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (Kp : ℕ), ∀ (main : HvdH.Cmd) (p₀ : ℕ), 100 ≤ p₀ →
      Spec main prog 1 (fun t => t = [.int (p₀ : ℤ)])
        (fun _ o => o = [.int ((logD p₀ 0 : ℕ) : ℤ), .int ((logS p₀ 0 : ℕ) : ℤ), .int 0,
          .int ((logM p₀ : ℕ) : ℤ), .int (p₀ : ℤ)])
        (fun _ => Kp * (p₀ + 1) ^ 2) := by
  obtain ⟨cDup, KDup, hDup⟩ := hk.dup
  obtain ⟨cRoll, KRoll, hRoll⟩ := hk.roll
  obtain ⟨cSwap, KSwap, hSwap⟩ := hk.swap
  obtain ⟨cPush, KPush, hPush⟩ := hk.pushVal
  obtain ⟨cPick, KPick, hPick⟩ := hk.pick
  obtain ⟨cAdd, KAdd, hAdd⟩ := hi.add
  obtain ⟨cPow, KPow, hPow⟩ := hi.pow2
  set prog : Cmd := .seq cDup (.seq (cPick 1) (.seq cAdd (.seq (cPush (.int 21)) (.seq cSwap (.seq cAdd (.seq cDup (.seq cPow (.seq (cPush (.int 0)) (.seq (cPush (.int 0)) ((cRoll 2))))))))))) with hprog
  set Ks : ℕ := 100 * (KDup + KRoll + KSwap + KPush + KPick + KAdd + KPow + 1) with hKs
  refine ⟨prog, 12 * Ks, ?_⟩
  intro main p₀ hp0
  let pz : ℤ := (p₀ : ℤ)
  have hpz1 : isz pz ≤ 2 * p₀ + 25 := by
    simp only [pz]; have := p_isz_le p₀; simp only [logSZ] at this; omega
  have h2pz : isz (pz + pz) ≤ 2 * p₀ + 26 := by
    have h := isz_add_le pz pz
    have h2 : max (isz pz) (isz pz) ≤ 2 * p₀ + 25 := by omega
    omega
  have h0isz : isz (0 : ℤ) ≤ 2 := isz_natCast_le_self 0
  have h21isz : isz (21 : ℤ) ≤ 23 := isz_natCast_le_self 21
  let M : ℤ := (pz + pz) + 21
  have hMisz : isz M ≤ 2 * p₀ + 27 := by
    have h := isz_add_le (pz + pz) 21
    have h2 : max (isz (pz + pz)) (isz (21 : ℤ)) ≤ 2 * p₀ + 26 := by omega
    simp only [M]
    omega
  let W : ℤ := (2 : ℤ) ^ M.toNat
  have hMt : M.toNat = 2 * p₀ + 21 := by
    have h : M = ((2 * p₀ + 21 : ℕ) : ℤ) := by simp only [M, pz]; push_cast; ring
    rw [h]; exact Int.toNat_natCast _
  have hWisz : isz W ≤ 2 * p₀ + 24 := by
    have hza : ((2 : ℤ) ^ M.toNat).natAbs = 2 ^ M.toNat := by
      rw [Int.natAbs_pow]; norm_num
    have h1 : (((2 : ℤ) ^ M.toNat)).natAbs ≤ 2 ^ (2 * p₀ + 21) := by
      rw [hza, hMt]
    have h10 : isz W ≤ 2 * p₀ + 21 + 3 :=
      isz_le_of_natAbs_le (z := (2 : ℤ) ^ M.toNat) (k := 2 * p₀ + 21) h1
    omega
  let V0 : List Val := [.int pz]
  let V1 : List Val := [.int pz, .int pz]
  let V2 : List Val := [.int pz, .int pz, .int pz]
  let V3 : List Val := [.int (pz + pz), .int pz]
  let V4 : List Val := [.int 21, .int (pz + pz), .int pz]
  let V5 : List Val := [.int (pz + pz), .int 21, .int pz]
  let V6 : List Val := [.int M, .int pz]
  let V7 : List Val := [.int M, .int M, .int pz]
  let V8 : List Val := [.int W, .int M, .int pz]
  let V9 : List Val := [.int 0, .int W, .int M, .int pz]
  let V10 : List Val := [.int 0, .int 0, .int W, .int M, .int pz]
  let V11 : List Val := [.int W, .int 0, .int 0, .int M, .int pz]
  have e1 : Spec main cDup 1 (fun t => t = V0) (fun _ o => o = V1) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dupStep hk (hDup main) (a := .int pz) (E := []) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDup) (c := 4) (n := vsz (.int pz) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [V0, V1] using h
  have e2 : Spec main (cPick 1) 2 (fun t => t = V1) (fun _ o => o = V2)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int pz, .int pz] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.pickStep hk (k := 1) (hPick main 1) (A := [.int pz, .int pz]) (by simp) (E := [])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KPick) (k := 2) (c := 20) (n := szl [.int pz, .int pz] + 1)
        (by simp only [hKs]; omega) hsz)
    simpa [V1, V2] using h
  have e3 : Spec main cAdd 3 (fun t => t = V2) (fun _ o => o = V3) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hAdd main) (a := pz) (b := pz) (hab := trivial) (E := [.int pz])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KAdd) (c := 8) (n := isz pz + isz pz) (by simp only [hKs]; omega)
        (by omega))
    simpa [V2, V3] using h
  have e4 : Spec main (cPush (.int 21)) 2 (fun t => t = V3) (fun _ o => o = V4)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pushStep hk (hPush main (.int 21)) (E := V3) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPush) (c := 8) (n := vsz (.int 21) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [V3, V4] using h
  have e5 : Spec main cSwap 3 (fun t => t = V4) (fun _ o => o = V5) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int 21) (.int (pz + pz)) (E := [.int pz])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int 21) + vsz (.int (pz + pz)) + 1)
        (by simp only [hKs]; omega) (by simp only [vsz_int]; omega))
    simpa [V4, V5] using h
  have e6 : Spec main cAdd 3 (fun t => t = V5) (fun _ o => o = V6) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hAdd main) (a := pz + pz) (b := 21) (hab := trivial) (E := [.int pz])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KAdd) (c := 8) (n := isz (pz + pz) + isz (21 : ℤ))
        (by simp only [hKs]; omega) (by omega))
    simpa [V5, V6, M] using h
  have e7 : Spec main cDup 2 (fun t => t = V6) (fun _ o => o = V7) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dupStep hk (hDup main) (a := .int M) (E := [.int pz])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDup) (c := 4) (n := vsz (.int M) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [V6, V7] using h
  have e8 : Spec main cPow 3 (fun t => t = V7) (fun _ o => o = V8) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.unStep hk (hPow main) (a := M) (ha := by simp only [M, pz]; omega)
      (E := [.int M, .int pz]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPow) (c := 8) (n := M.toNat + isz M) (by simp only [hKs]; omega)
        (by omega))
    simpa [V7, V8, W] using h
  have e9 : Spec main (cPush (.int 0)) 3 (fun t => t = V8) (fun _ o => o = V9)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pushStep hk (hPush main (.int 0)) (E := V8) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPush) (c := 4) (n := vsz (.int 0) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [V8, V9] using h
  have e10 : Spec main (cPush (.int 0)) 4 (fun t => t = V9) (fun _ o => o = V10)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pushStep hk (hPush main (.int 0)) (E := V9) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPush) (c := 4) (n := vsz (.int 0) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [V9, V10] using h
  have e11 : Spec main (cRoll 2) 5 (fun t => t = V10) (fun _ o => o = V11)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int 0, .int 0, .int W] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 2) (hRoll main 2)
      (A := [.int 0, .int 0, .int W]) (by simp) (E := [.int M, .int pz])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 3) (c := 20) (n := szl [.int 0, .int 0, .int W] + 1)
        (by simp only [hKs]; omega) hsz)
    simpa [V10, V11] using h
  have c10 := Spec.seq_det_quad hk e10 e11 (by simp [V10])
  have c9 := Spec.seq_det_quad hk e9 c10 (by simp [V9])
  have c8 := Spec.seq_det_quad hk e8 c9 (by simp [V8])
  have c7 := Spec.seq_det_quad hk e7 c8 (by simp [V7])
  have c6 := Spec.seq_det_quad hk e6 c7 (by simp [V6])
  have c5 := Spec.seq_det_quad hk e5 c6 (by simp [V5])
  have c4 := Spec.seq_det_quad hk e4 c5 (by simp [V4])
  have c3 := Spec.seq_det_quad hk e3 c4 (by simp [V3])
  have c2 := Spec.seq_det_quad hk e2 c3 (by simp [V2])
  have h := Spec.seq_det_quad hk e1 c2 (by simp [V1])
  refine Spec.mono hk (by rw [hprog]; exact h) ?_ ?_ ?_
  · intro t ht hP
    rw [hP]
  · intro t o ht hP hQ
    rw [hQ]
    simp only [V11]
    have hM : M = ((logM p₀ : ℕ) : ℤ) := by
      simp only [M, pz, logM]; push_cast; ring
    have hW : W = ((logD p₀ 0 : ℕ) : ℤ) := by
      simp only [W]
      rw [hM, logD_zero]
      simp only [logP, logM]
      push_cast
      rfl
    have hS : ((logS p₀ 0 : ℕ) : ℤ) = (0 : ℤ) := by simp [logS_zero]
    rw [hW, hS, hM]
  · intro t ht hP
    rw [show (12 : ℕ) * Ks * (p₀ + 1) ^ 2 = 12 * (Ks * (p₀ + 1) ^ 2) by ring]
    omega

/-- Epilogue: `[D,S,c,M,p₀] ↦ [logU p₀]` when `S = logS p₀ (logM p₀ + 1)`. -/
theorem logEpilogueAux (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (Ke : ℕ), ∀ (main : HvdH.Cmd) (p₀ : ℕ) (D S c M : ℤ), 100 ≤ p₀ →
      S = ((logS p₀ (logM p₀ + 1) : ℕ) : ℤ) →
      isz D ≤ logSZ p₀ → isz S ≤ logSZ p₀ → isz c ≤ logSZ p₀ → isz M ≤ logSZ p₀ →
      Spec main prog 5 (fun t => t = [.int D, .int S, .int c, .int M, .int (p₀ : ℤ)])
        (fun _ o => o = [.int ((logU p₀ : ℕ) : ℤ)]) (fun _ => Ke * (p₀ + 1) ^ 2) := by
  obtain ⟨cDup, KDup, hDup⟩ := hk.dup
  obtain ⟨cRoll, KRoll, hRoll⟩ := hk.roll
  obtain ⟨cSwap, KSwap, hSwap⟩ := hk.swap
  obtain ⟨cDrop, KDrop, hDrop⟩ := hk.drop
  obtain ⟨cPush, KPush, hPush⟩ := hk.pushVal
  obtain ⟨cAdd, KAdd, hAdd⟩ := hi.add
  obtain ⟨cPow, KPow, hPow⟩ := hi.pow2
  obtain ⟨cShl, KShl, hShl⟩ := hi.shl
  obtain ⟨cFdiv, KFdiv, hFdiv⟩ := hi.fdiv
  set prog : Cmd := .seq (cRoll 4) (.seq (cPush (.int 20)) (.seq cSwap (.seq cAdd (.seq cDup (.seq cPow (.seq cDup (.seq (cPush (.int 1)) (.seq cSwap (.seq cShl (.seq (cRoll 1) (.seq (cRoll 4) (.seq cAdd (.seq cFdiv (.seq cSwap (.seq cDrop (.seq cSwap (.seq cDrop (.seq cSwap (.seq cDrop (.seq cSwap (cDrop))))))))))))))))))))) with hprog
  set Ks : ℕ := 100 * (KDup + KRoll + KSwap + KDrop + KPush + KAdd + KPow + KShl + KFdiv + 1) with hKs
  refine ⟨prog, 23 * Ks, ?_⟩
  intro main p₀ D S c M hp0 hSeq hD hS hc hM
  let pz : ℤ := (p₀ : ℤ)
  have hpz1 : isz pz ≤ 2 * p₀ + 25 := by
    simp only [pz]; exact le_trans (p_isz_le p₀) (by simp only [logSZ]; omega)
  have hD1 : isz D ≤ 2 * p₀ + 25 := by have := hD; simp only [logSZ] at this; omega
  have hS1 : isz S ≤ 2 * p₀ + 25 := by have := hS; simp only [logSZ] at this; omega
  have hc1 : isz c ≤ 2 * p₀ + 25 := by have := hc; simp only [logSZ] at this; omega
  have hM1 : isz M ≤ 2 * p₀ + 25 := by have := hM; simp only [logSZ] at this; omega
  have h20isz : isz (20 : ℤ) ≤ 22 := isz_natCast_le_self 20
  have h1isz : isz (1 : ℤ) ≤ 3 := isz_natCast_le_self 1
  have h2isz : isz (2 : ℤ) ≤ 4 := isz_natCast_le_self 2
  let G : ℤ := pz + 20
  have hGisz : isz G ≤ 2 * p₀ + 26 := by
    have h := isz_add_le pz 20
    have h2 : max (isz pz) (isz (20 : ℤ)) ≤ 2 * p₀ + 25 := by omega
    simp only [G]; omega
  have hGt : G.toNat = p₀ + 20 := by
    have h : G = ((p₀ + 20 : ℕ) : ℤ) := by simp only [G, pz]; push_cast; ring
    rw [h]; exact Int.toNat_natCast _
  let W : ℤ := (2 : ℤ) ^ G.toNat
  have hWisz : isz W ≤ p₀ + 24 := by
    have hza : ((2 : ℤ) ^ G.toNat).natAbs = 2 ^ G.toNat := by
      rw [Int.natAbs_pow]; norm_num
    have h1 : (((2 : ℤ) ^ G.toNat)).natAbs ≤ 2 ^ (p₀ + 20) := by
      rw [hza, hGt]
    have h10 : isz W ≤ p₀ + 20 + 3 :=
      isz_le_of_natAbs_le (z := (2 : ℤ) ^ G.toNat) (k := p₀ + 20) h1
    omega
  let W2 : ℤ := W * 2 ^ (1 : ℤ).toNat
  have hW2isz : isz W2 ≤ 2 * p₀ + 26 := by
    have h := isz_mul_le W ((2 : ℤ) ^ (1 : ℤ).toNat)
    have h5 : ((2 : ℤ) ^ (1 : ℤ).toNat) = 2 := by norm_num
    have h6 : isz ((2 : ℤ) ^ (1 : ℤ).toNat) ≤ 4 := by rw [h5]; exact h2isz
    simp only [W2]
    omega
  let T : ℤ := S + W
  have hTisz : isz T ≤ 2 * p₀ + 26 := by
    have h := isz_add_le S W
    have h2 : max (isz S) (isz W) ≤ 2 * p₀ + 25 := by omega
    simp only [T]; omega
  let u : ℤ := T.fdiv W2
  have hW2pos : (0 : ℤ) < W2 := by
    have h1 : (0 : ℤ) < W := by simp only [W]; positivity
    have h5 : (0 : ℤ) < 2 ^ (1 : ℤ).toNat := by norm_num
    simp only [W2]; positivity
  have huisz : isz u ≤ 2 * p₀ + 26 := by
    have h1 : (0 : ℤ) ≤ W2 := le_of_lt hW2pos
    have h2 : T.fdiv W2 = T / W2 := Int.fdiv_eq_ediv_of_nonneg T h1
    simp only [u]
    rw [h2]
    have h3 := Int.natAbs_ediv_le_natAbs T W2
    have h4 := Nat.size_mono' h3
    simp only [isz] at hTisz ⊢
    omega
  let F0 : List Val := [.int D, .int S, .int c, .int M, .int pz]
  let F1 : List Val := [.int pz, .int D, .int S, .int c, .int M]
  let F2 : List Val := [.int 20, .int pz, .int D, .int S, .int c, .int M]
  let F3 : List Val := [.int pz, .int 20, .int D, .int S, .int c, .int M]
  let F4 : List Val := [.int G, .int D, .int S, .int c, .int M]
  let F5 : List Val := [.int G, .int G, .int D, .int S, .int c, .int M]
  let F6 : List Val := [.int W, .int G, .int D, .int S, .int c, .int M]
  let F7 : List Val := [.int W, .int W, .int G, .int D, .int S, .int c, .int M]
  let F8 : List Val := [.int 1, .int W, .int W, .int G, .int D, .int S, .int c, .int M]
  let F9 : List Val := [.int W, .int 1, .int W, .int G, .int D, .int S, .int c, .int M]
  let F10 : List Val := [.int W2, .int W, .int G, .int D, .int S, .int c, .int M]
  let F11 : List Val := [.int W, .int W2, .int G, .int D, .int S, .int c, .int M]
  let F12 : List Val := [.int S, .int W, .int W2, .int G, .int D, .int c, .int M]
  let F13 : List Val := [.int T, .int W2, .int G, .int D, .int c, .int M]
  let F14 : List Val := [.int u, .int G, .int D, .int c, .int M]
  let F15 : List Val := [.int G, .int u, .int D, .int c, .int M]
  let F16 : List Val := [.int u, .int D, .int c, .int M]
  let F17 : List Val := [.int D, .int u, .int c, .int M]
  let F18 : List Val := [.int u, .int c, .int M]
  let F19 : List Val := [.int c, .int u, .int M]
  let F20 : List Val := [.int u, .int M]
  let F21 : List Val := [.int M, .int u]
  let F22 : List Val := [.int u]
  have e1 : Spec main (cRoll 4) 5 (fun t => t = F0) (fun _ o => o = F1) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int D, .int S, .int c, .int M, .int pz] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 4) (hRoll main 4)
      (A := [.int D, .int S, .int c, .int M, .int pz]) (by simp) (E := [])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 5) (c := 20)
        (n := szl [.int D, .int S, .int c, .int M, .int pz] + 1) (by simp only [hKs]; omega) hsz)
    simpa [F0, F1] using h
  have e2 : Spec main (cPush (.int 20)) 5 (fun t => t = F1) (fun _ o => o = F2)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pushStep hk (hPush main (.int 20)) (E := F1) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPush) (c := 8) (n := vsz (.int 20) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F1, F2] using h
  have e3 : Spec main cSwap 6 (fun t => t = F2) (fun _ o => o = F3) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int 20) (.int pz) (E := [.int D, .int S, .int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int 20) + vsz (.int pz) + 1)
        (by simp only [hKs]; omega) (by simp only [vsz_int]; omega))
    simpa [F2, F3] using h
  have e4 : Spec main cAdd 6 (fun t => t = F3) (fun _ o => o = F4) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hAdd main) (a := pz) (b := 20) (hab := trivial)
      (E := [.int D, .int S, .int c, .int M]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KAdd) (c := 8) (n := isz pz + isz (20 : ℤ)) (by simp only [hKs]; omega)
        (by omega))
    simpa [F3, F4, G] using h
  have e5 : Spec main cDup 5 (fun t => t = F4) (fun _ o => o = F5) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dupStep hk (hDup main) (a := .int G) (E := [.int D, .int S, .int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDup) (c := 4) (n := vsz (.int G) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F4, F5] using h
  have e6 : Spec main cPow 6 (fun t => t = F5) (fun _ o => o = F6) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.unStep hk (hPow main) (a := G) (ha := by simp only [G, pz]; omega)
      (E := [.int G, .int D, .int S, .int c, .int M]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPow) (c := 8) (n := G.toNat + isz G) (by simp only [hKs]; omega)
        (by omega))
    simpa [F5, F6, W] using h
  have e7 : Spec main cDup 6 (fun t => t = F6) (fun _ o => o = F7) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dupStep hk (hDup main) (a := .int W) (E := [.int G, .int D, .int S, .int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDup) (c := 4) (n := vsz (.int W) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F6, F7] using h
  have e8 : Spec main (cPush (.int 1)) 7 (fun t => t = F7) (fun _ o => o = F8)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pushStep hk (hPush main (.int 1)) (E := F7) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPush) (c := 8) (n := vsz (.int 1) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F7, F8] using h
  have e9 : Spec main cSwap 8 (fun t => t = F8) (fun _ o => o = F9) (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int 1) (.int W)
      (E := [.int W, .int G, .int D, .int S, .int c, .int M]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int 1) + vsz (.int W) + 1)
        (by simp only [hKs]; omega) (by simp only [vsz_int]; omega))
    simpa [F8, F9] using h
  have e10 : Spec main cShl 8 (fun t => t = F9) (fun _ o => o = F10)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hShl main) (a := W) (b := 1) (hab := by norm_num)
      (E := [.int W, .int G, .int D, .int S, .int c, .int M]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KShl) (c := 8) (n := isz W + (1 : ℤ).toNat + isz (1 : ℤ))
        (by simp only [hKs]; omega) (by omega))
    simpa [F9, F10, W2] using h
  have e11 : Spec main (cRoll 1) 7 (fun t => t = F10) (fun _ o => o = F11)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int W2, .int W] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 1) (hRoll main 1)
      (A := [.int W2, .int W]) (by simp) (E := [.int G, .int D, .int S, .int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 2) (c := 20) (n := szl [.int W2, .int W] + 1)
        (by simp only [hKs]; omega) hsz)
    simpa [F10, F11, List.cons_append, List.nil_append] using h
  have e12 : Spec main (cRoll 4) 7 (fun t => t = F11) (fun _ o => o = F12)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int W, .int W2, .int G, .int D, .int S] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 4) (hRoll main 4)
      (A := [.int W, .int W2, .int G, .int D, .int S]) (by simp) (E := [.int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 5) (c := 20)
        (n := szl [.int W, .int W2, .int G, .int D, .int S] + 1) (by simp only [hKs]; omega) hsz)
    simpa [F11, F12, List.cons_append, List.nil_append] using h
  have e13 : Spec main cAdd 7 (fun t => t = F12) (fun _ o => o = F13)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hAdd main) (a := S) (b := W) (hab := trivial)
      (E := [.int W2, .int G, .int D, .int c, .int M]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KAdd) (c := 8) (n := isz S + isz W) (by simp only [hKs]; omega)
        (by omega))
    simpa [F12, F13, T, List.cons_append, List.nil_append] using h
  have e14 : Spec main cFdiv 6 (fun t => t = F13) (fun _ o => o = F14)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hFdiv main) (a := T) (b := W2) (hab := hW2pos)
      (E := [.int G, .int D, .int c, .int M]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound2 (K := KFdiv) (a := isz T) (b := isz W2) (ca := 4) (cb := 4)
        (by simp only [hKs]; omega) (by omega) (by omega))
    simpa [F13, F14, u, List.cons_append, List.nil_append] using h
  have e15 : Spec main cSwap 5 (fun t => t = F14) (fun _ o => o = F15)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int u) (.int G) (E := [.int D, .int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int u) + vsz (.int G) + 1)
        (by simp only [hKs]; omega) (by simp only [vsz_int]; omega))
    simpa [F14, F15] using h
  have e16 : Spec main cDrop 5 (fun t => t = F15) (fun _ o => o = F16)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dropStep hk (hDrop main) (a := .int G) (E := [.int u, .int D, .int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDrop) (c := 4) (n := vsz (.int G) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F15, F16] using h
  have e17 : Spec main cSwap 4 (fun t => t = F16) (fun _ o => o = F17)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int u) (.int D) (E := [.int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int u) + vsz (.int D) + 1)
        (by simp only [hKs]; omega) (by simp only [vsz_int]; omega))
    simpa [F16, F17] using h
  have e18 : Spec main cDrop 4 (fun t => t = F17) (fun _ o => o = F18)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dropStep hk (hDrop main) (a := .int D) (E := [.int u, .int c, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDrop) (c := 4) (n := vsz (.int D) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F17, F18] using h
  have e19 : Spec main cSwap 3 (fun t => t = F18) (fun _ o => o = F19)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int u) (.int c) (E := [.int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int u) + vsz (.int c) + 1)
        (by simp only [hKs]; omega) (by simp only [vsz_int]; omega))
    simpa [F18, F19] using h
  have e20 : Spec main cDrop 3 (fun t => t = F19) (fun _ o => o = F20)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dropStep hk (hDrop main) (a := .int c) (E := [.int u, .int M])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDrop) (c := 4) (n := vsz (.int c) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F19, F20] using h
  have e21 : Spec main cSwap 2 (fun t => t = F20) (fun _ o => o = F21)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int u) (.int M) (E := [])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int u) + vsz (.int M) + 1)
        (by simp only [hKs]; omega) (by simp only [vsz_int]; omega))
    simpa [F20, F21] using h
  have e22 : Spec main cDrop 2 (fun t => t = F21) (fun _ o => o = F22)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dropStep hk (hDrop main) (a := .int M) (E := [.int u])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDrop) (c := 4) (n := vsz (.int M) + 1) (by simp only [hKs]; omega)
        (by simp only [vsz_int]; omega))
    simpa [F21, F22] using h
  have c21 := Spec.seq_det_quad hk e21 e22 (by simp [F21])
  have c20 := Spec.seq_det_quad hk e20 c21 (by simp [F20])
  have c19 := Spec.seq_det_quad hk e19 c20 (by simp [F19])
  have c18 := Spec.seq_det_quad hk e18 c19 (by simp [F18])
  have c17 := Spec.seq_det_quad hk e17 c18 (by simp [F17])
  have c16 := Spec.seq_det_quad hk e16 c17 (by simp [F16])
  have c15 := Spec.seq_det_quad hk e15 c16 (by simp [F15])
  have c14 := Spec.seq_det_quad hk e14 c15 (by simp [F14])
  have c13 := Spec.seq_det_quad hk e13 c14 (by simp [F13])
  have c12 := Spec.seq_det_quad hk e12 c13 (by simp [F12])
  have c11 := Spec.seq_det_quad hk e11 c12 (by simp [F11])
  have c10 := Spec.seq_det_quad hk e10 c11 (by simp [F10])
  have c9 := Spec.seq_det_quad hk e9 c10 (by simp [F9])
  have c8 := Spec.seq_det_quad hk e8 c9 (by simp [F8])
  have c7 := Spec.seq_det_quad hk e7 c8 (by simp [F7])
  have c6 := Spec.seq_det_quad hk e6 c7 (by simp [F6])
  have c5 := Spec.seq_det_quad hk e5 c6 (by simp [F5])
  have c4 := Spec.seq_det_quad hk e4 c5 (by simp [F4])
  have c3 := Spec.seq_det_quad hk e3 c4 (by simp [F3])
  have c2 := Spec.seq_det_quad hk e2 c3 (by simp [F2])
  have h := Spec.seq_det_quad hk e1 c2 (by simp [F1])
  refine Spec.mono hk (by rw [hprog]; exact h) ?_ ?_ ?_
  · intro t ht hP
    rw [hP]
  · intro t o ht hP hQ
    rw [hQ]
    simp only [F22]
    have hG : G = ((p₀ + 20 : ℕ) : ℤ) := by simp only [G, pz]; push_cast; ring
    have hW : W = (2 : ℤ) ^ (p₀ + 20) := by
      simp only [W]; rw [hGt]
    have hW2 : W2 = (2 : ℤ) ^ (p₀ + 21) := by
      simp only [W2, hW]
      have h1 : ((2 : ℤ) ^ (1 : ℤ).toNat) = 2 := by norm_num
      rw [h1, ← pow_succ]
    have hT : T = ((logS p₀ (logM p₀ + 1) : ℕ) : ℤ) + (2 : ℤ) ^ (p₀ + 20) := by
      simp only [T, hSeq, hW]
    have hu : u = ((logU p₀ : ℕ) : ℤ) := by
      simp only [u]
      rw [hT, hW2, logU_cast p₀]
    rw [hu]
  · intro t ht hP
    ring_nf
    rw [show Ks * 22 + Ks * p₀ * 44 + Ks * p₀ ^ 2 * 22 = Ks * (p₀ + 1) ^ 2 * 22 by ring,
      show Ks * 23 + Ks * p₀ * 46 + Ks * p₀ ^ 2 * 23 = Ks * (p₀ + 1) ^ 2 * 23 by ring]
    exact Nat.mul_le_mul_left _ (by norm_num)

end Work.Fx
