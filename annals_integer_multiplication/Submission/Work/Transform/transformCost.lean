import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.SeqUtil
import Submission.Work.Transform.costKit
import Submission.Work.Transform.costShapes
import Submission.Work.Transform.costAbsorb

/-!
# The cost bound of Theorem 3.1, isolated

This is the arithmetic core of the `Transform` cost proof: given

* the twenty raw cost bounds `hc1 … hc20` of the pipeline steps (in the exact shape produced by
  the area word lemmas -- the roll steps are expressed through the prefix sums `R3, …, R17`),
* the size facts (`S`, `VB` bookkeeping, the per-value `vsz` bounds, the roll prefix-sum bounds),

it produces the announced bound `4 * (T/r) * Cm (3rp) + K * T * p² + K * Σtᵢ (p+1)^K`.

Keeping this in a module of its own means the nonlinear arithmetic is done in a *small* context,
which is essential: in the assembly (with the twenty `WordR` hypotheses in scope) the unifier
becomes prohibitively slow.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Transform

open HvdH

theorem transformCost
    (p T r M KB S VB : ℕ) (ts : List ℕ) (Cm : ℕ → ℕ)
    (Kp Kz Kc Ks Ka Km Kph Kps Kr KR : ℕ)
    (ZL VTS VTS' VIP VIR VZst VZstie VZs VA VAb : ℕ)
    (R3 R4 R10 R11 R12 R13 R15 R16 R17 : ℕ)
    (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 : ℕ)
    (hKB : KB = 2 ^ (Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR + 100))
    (hSA : S = T * p ^ 2 + ts.sum * (p + 1) ^ KB)
    (hS1 : 1 ≤ S) (hVBS : VB ≤ 100 * S) (hSle : S ≤ 3000000 * S)
    (hTpS : T * p ^ 2 ≤ S) (hsumS : ts.sum * (p + 1) ^ KB ≤ S)
    (hpS : p ≤ S) (hrS : r ≤ S) (hMrS : (M * r) * p ^ 2 ≤ S) (hrsum : r ≤ ts.sum)
    (hpwP : (p + 1) ^ Kp ≤ (p + 1) ^ KB) (hpwZ : (p + 1) ^ Kz ≤ (p + 1) ^ KB)
    (hpwC : (p + 1) ^ Kc ≤ (p + 1) ^ KB)
    (h2a : ZL * p ^ 2 ≤ S)
    (hTS : VTS ≤ VB) (hTS' : VTS' ≤ VB) (hIP : VIP ≤ VB) (hIR : VIR ≤ VB)
    (hZst : VZst ≤ VB) (hZstie : VZstie ≤ VB) (hZs : VZs ≤ VB) (hAa : VA ≤ VB) (hAbb : VAb ≤ VB)
    (hroll3 : R3 ≤ (5 + 1) * VB) (hroll4 : R4 ≤ (3 + 1) * VB)
    (hroll10 : R10 ≤ (4 + 1) * VB) (hroll11 : R11 ≤ (4 + 1) * VB)
    (hroll12 : R12 ≤ (4 + 1) * VB) (hroll13 : R13 ≤ (4 + 1) * VB)
    (hroll15 : R15 ≤ (8 + 1) * VB) (hroll16 : R16 ≤ (8 + 1) * VB) (hroll17 : R17 ≤ (8 + 1) * VB)
    (hc1 : n1 ≤ Kp * (ts.sum * (p + 1) ^ Kp) + Kp)
    (hc2 : n2 ≤ Kz * (ZL * p ^ 2 + r * (p + 1) ^ Kz + VTS' + VTS + 1) + Kz)
    (hc3 : n3 ≤ Kr * (5 + 1) * (R3 + 1))
    (hc4 : n4 ≤ Kr * (3 + 1) * (R4 + 1))
    (hc5 : n5 ≤ Kc * (T * p ^ 2 + ts.sum * (p + 1) ^ Kc) + Kc)
    (hc6 : n6 ≤ Ks * (VA + VAb + VIP + VZst + VZstie + 1) + Ks)
    (hc7 : n7 ≤ Ka * ((((VZst + VZstie) + VA) + VAb + VZs + VIP + VIR + VTS') * 3000 + 1) + Ka)
    (hc8 : n8 ≤ Km * (T * p ^ 2 + p + 1) + Km)
    (hc9 : n9 ≤ Kph * ((M * r) * p ^ 2 + p + r + 1) + Kph)
    (hc10 : n10 ≤ Kr * (4 + 1) * (R10 + 1))
    (hc11 : n11 ≤ Kr * (4 + 1) * (R11 + 1))
    (hc12 : n12 ≤ Kr * (4 + 1) * (R12 + 1))
    (hc13 : n13 ≤ Kr * (4 + 1) * (R13 + 1))
    (hc14 : n14 ≤ Kph * ((M * r) * p ^ 2 + p + r + 1) + Kph)
    (hc15 : n15 ≤ Kr * (8 + 1) * (R15 + 1))
    (hc16 : n16 ≤ Kr * (8 + 1) * (R16 + 1))
    (hc17 : n17 ≤ Kr * (8 + 1) * (R17 + 1))
    (hc18 : n18 ≤ 4 * M * Cm (3 * r * p) + KR * (M * r) * p ^ 2 + KR)
    (hc19 : n19 ≤ Kps * ((M * r) * p ^ 2 + p + r + 1) + Kps)
    (hc20 : n20 ≤ Km * (T * p ^ 2 + p + 1) + Km) :
    csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18,
        n19, n20] ≤
      4 * M * Cm (3 * r * p) + KB * T * p ^ 2 + KB * ts.sum * (p + 1) ^ KB := by
  have hn1 : n1 ≤ Kp * (3000000 * S) + Kp :=
    le_trans hc1 (shapeOne (le_trans (Nat.mul_le_mul_left ts.sum hpwP) hsumS))
  have h2b : r * (p + 1) ^ Kz ≤ S := le_trans (Nat.mul_le_mul hrsum hpwZ) hsumS
  have hn2 : n2 ≤ Kz * (3000000 * S) + Kz :=
    le_trans hc2 (shapeSum4 (K := Kz) (a := ZL * p ^ 2) (b := r * (p + 1) ^ Kz)
      (c := VTS') (d := VTS) (S := S) (V := VB) h2a h2b hTS' hTS hVBS hS1)
  have hX3 : Kr * (5 + 1) * (R3 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R3) (S := S) (k := 5 + 1) (by norm_num) hroll3 hVBS hS1
  have hn3 : n3 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc3 (le_trans hX3 (Nat.le_add_right _ Kr))
  have hX4 : Kr * (3 + 1) * (R4 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R4) (S := S) (k := 3 + 1) (by norm_num) hroll4 hVBS hS1
  have hn4 : n4 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc4 (le_trans hX4 (Nat.le_add_right _ Kr))
  have h5v : T * p ^ 2 + ts.sum * (p + 1) ^ Kc ≤ 2 * S := by
    rw [two_mul]
    exact add_le_add hTpS (le_trans (Nat.mul_le_mul_left ts.sum hpwC) hsumS)
  have hn5 : n5 ≤ Kc * (3000000 * S) + Kc := le_trans hc5 (shapeTwo h5v)
  have hn6 : n6 ≤ Ks * (3000000 * S) + Ks :=
    le_trans hc6 (shapeAdd5 (Kr := Ks) (V := VB) (a := VA) (b := VAb) (c := VIP) (d := VZst)
      (e := VZstie) (S := S) hAa hAbb hIP hZst hZstie hVBS hS1)
  have hn7 : n7 ≤ Ka * (3000000 * S) + Ka :=
    le_trans hc7 (shapeArr (Ka := Ka) (V := VB) (a := VZst) (b := VZstie) (c := VA) (d := VAb)
      (e := VZs) (f := VIP) (g := VIR) (h := VTS') (S := S) hZst hZstie hAa hAbb hZs hIP hIR hTS'
      hVBS hS1)
  have hn8 : n8 ≤ Km * (3000000 * S) + Km :=
    le_trans hc8 (shapeMul (K := Km) (T := T) (p := p) (S := S) hTpS hpS hS1)
  have hn9 : n9 ≤ Kph * (3000000 * S) + Kph :=
    le_trans hc9 (shapePhi (K := Kph) (M := M) (r := r) (p := p) (S := S) hMrS hpS hrS hS1)
  have hX10 : Kr * (4 + 1) * (R10 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R10) (S := S) (k := 4 + 1) (by norm_num) hroll10 hVBS hS1
  have hn10 : n10 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc10 (le_trans hX10 (Nat.le_add_right _ Kr))
  have hX11 : Kr * (4 + 1) * (R11 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R11) (S := S) (k := 4 + 1) (by norm_num) hroll11 hVBS hS1
  have hn11 : n11 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc11 (le_trans hX11 (Nat.le_add_right _ Kr))
  have hX12 : Kr * (4 + 1) * (R12 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R12) (S := S) (k := 4 + 1) (by norm_num) hroll12 hVBS hS1
  have hn12 : n12 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc12 (le_trans hX12 (Nat.le_add_right _ Kr))
  have hX13 : Kr * (4 + 1) * (R13 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R13) (S := S) (k := 4 + 1) (by norm_num) hroll13 hVBS hS1
  have hn13 : n13 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc13 (le_trans hX13 (Nat.le_add_right _ Kr))
  have hn14 : n14 ≤ Kph * (3000000 * S) + Kph :=
    le_trans hc14 (shapePhi (K := Kph) (M := M) (r := r) (p := p) (S := S) hMrS hpS hrS hS1)
  have hX15 : Kr * (8 + 1) * (R15 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R15) (S := S) (k := 8 + 1) (by norm_num) hroll15 hVBS hS1
  have hn15 : n15 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc15 (le_trans hX15 (Nat.le_add_right _ Kr))
  have hX16 : Kr * (8 + 1) * (R16 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R16) (S := S) (k := 8 + 1) (by norm_num) hroll16 hVBS hS1
  have hn16 : n16 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc16 (le_trans hX16 (Nat.le_add_right _ Kr))
  have hX17 : Kr * (8 + 1) * (R17 + 1) ≤ Kr * (3000000 * S) :=
    shapeRoll (Kr := Kr) (V := VB) (R := R17) (S := S) (k := 8 + 1) (by norm_num) hroll17 hVBS hS1
  have hn17 : n17 ≤ Kr * (3000000 * S) + Kr :=
    le_trans hc17 (le_trans hX17 (Nat.le_add_right _ Kr))
  have h18x : KR * (M * r) * p ^ 2 ≤ KR * (3000000 * S) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left KR (le_trans hMrS hSle)
  have hn18 : n18 ≤ 4 * M * Cm (3 * r * p) + KR * (3000000 * S) + KR :=
    le_trans hc18 (by
      rw [mul_assoc]
      exact add_le_add (add_le_add (le_refl _) h18x) (le_refl KR))
  have hn19 : n19 ≤ Kps * (3000000 * S) + Kps :=
    le_trans hc19 (shapePhi (K := Kps) (M := M) (r := r) (p := p) (S := S) hMrS hpS hrS hS1)
  have hn20 : n20 ≤ Km * (3000000 * S) + Km :=
    le_trans hc20 (shapeMul (K := Km) (T := T) (p := p) (S := S) hTpS hpS hS1)
  exact costAbsorb (p := p) (T := T) (r := r) (M := M) (K := KB)
    (Sg := Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR) (ts := ts) (Cm := Cm)
    (Kp := Kp) (Kz := Kz) (Kc := Kc) (Ks := Ks) (Ka := Ka) (Km := Km) (Kph := Kph)
    (Kps := Kps) (Kr := Kr) (KR := KR)
    (le_sum_1 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_sum_2 Kp Kz Kc Ks Ka Km Kph Kps Kr KR)
    (le_sum_3 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_sum_4 Kp Kz Kc Ks Ka Km Kph Kps Kr KR)
    (le_sum_5 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_sum_6 Kp Kz Kc Ks Ka Km Kph Kps Kr KR)
    (le_sum_7 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_sum_8 Kp Kz Kc Ks Ka Km Kph Kps Kr KR)
    (le_sum_9 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_sum_10 Kp Kz Kc Ks Ka Km Kph Kps Kr KR)
    (le_of_eq hKB.symm) (hSA ▸ hS1)
    n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20
    (hSA ▸ hn1) (hSA ▸ hn2) (hSA ▸ hn3) (hSA ▸ hn4) (hSA ▸ hn5) (hSA ▸ hn6) (hSA ▸ hn7) (hSA ▸ hn8) (hSA ▸ hn9) (hSA ▸ hn10) (hSA ▸ hn11) (hSA ▸ hn12) (hSA ▸ hn13) (hSA ▸ hn14) (hSA ▸ hn15) (hSA ▸ hn16) (hSA ▸ hn17) (hSA ▸ hn18) (hSA ▸ hn19) (hSA ▸ hn20)

end Work.Transform
