import Mathlib
import Submission.Work.Fx.ExpPosDefs
import Submission.Work.Fx.ExpPosKit
import Submission.Work.Fx.ExpPosCost
import Submission.Work.Fx.FxExpCore
import Submission.Work.Fx.ExpPosZData
import Submission.Work.Fx.ExpPosBridge
import Submission.Work.Fx.ExpPosFinal

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.Fx
open HvdH

theorem expPosField (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (h : Work.Fx.NumWords hk hi) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p j k σ : ℕ), 100 ≤ p → 1 ≤ k →
      Real.exp (Real.pi * j / k) ≤ 2 ^ σ → σ ≤ 2 * p →
      HvdH.WordR main prog (fun vs => ∃ (rest : List HvdH.Val),
          vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (j : ℤ) :: HvdH.Val.int (k : ℤ) :: HvdH.Val.int (σ : ℤ) :: rest)
      (fun vs out => ∃ (rest : List HvdH.Val) (w : ℤ × ℤ),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (j : ℤ) :: HvdH.Val.int (k : ℤ) :: HvdH.Val.int (σ : ℤ) :: rest ∧
        out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧
        (2 : ℝ) ^ p * ‖HvdH.fxC p w - (((2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * j / k) : ℝ) : ℂ)‖ < 2)
      (fun _ => K * (p + HvdH.isz j + HvdH.isz k + HvdH.isz σ) ^ K) := by
  obtain ⟨piP, Kpi, hpi⟩ := h.pi
  obtain ⟨logP, Klog, hlog⟩ := h.log2
  obtain ⟨expP, Kexp, hexp⟩ := h.expc
  obtain ⟨mulP, Kmul, hmul⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  obtain ⟨tdivP, Ktdiv, htdiv⟩ := hi.tdiv
  obtain ⟨maxP, Kmax, hmax⟩ := hi.max
  obtain ⟨shrP, Kshr, hshr⟩ := hi.shrT
  obtain ⟨pickP, Kpk, hpick⟩ := hk.pick
  obtain ⟨rollP, Krl, hroll⟩ := hk.roll
  obtain ⟨dupP, Kdu, hdup⟩ := hk.dup
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨consP, Kcv, hcons⟩ := hk.consV
  let KE : ℕ := max 4 (max Kpi (max Klog (max Kexp 2)))
  let KSm : ℕ := Kpk + Krl + Kdu + Kdr + Kmul + Kadd + Ksub + Ktdiv + Kmax + Kshr + Kpv + Kcv
    + Kpi + Klog + Kexp + KE + 1
  let c1 : Cmd := pushP (.int (60))
  let c2 : Cmd := addP
  let c3 : Cmd := dupP
  let c4 : Cmd := pushP (.int (2))
  let c5 : Cmd := mulP
  let c6 : Cmd := pushP (.int (60))
  let c7 : Cmd := rollP 1
  let c8 : Cmd := subP
  let c9 : Cmd := pickP 1
  let c10 : Cmd := pushP (.int (32))
  let c11 : Cmd := mulP
  let c12 : Cmd := pickP 1
  let c13 : Cmd := piP
  let c14 : Cmd := pickP 2
  let c15 : Cmd := logP
  let c16 : Cmd := rollP 1
  let c17 : Cmd := rollP 5
  let c18 : Cmd := mulP
  let c19 : Cmd := rollP 5
  let c20 : Cmd := rollP 1
  let c21 : Cmd := tdivP
  let c22 : Cmd := pickP 1
  let c23 : Cmd := pickP 6
  let c24 : Cmd := mulP
  let c25 : Cmd := pickP 1
  let c26 : Cmd := rollP 1
  let c27 : Cmd := subP
  let c28 : Cmd := pickP 1
  let c29 : Cmd := pickP 3
  let c30 : Cmd := pushP (.int (1))
  let c31 : Cmd := rollP 1
  let c32 : Cmd := subP
  let c33 : Cmd := rollP 2
  let c34 : Cmd := addP
  let c35 : Cmd := pickP 3
  let c36 : Cmd := rollP 1
  let c37 : Cmd := tdivP
  let c38 : Cmd := pushP (.int (0))
  let c39 : Cmd := maxP
  let c40 : Cmd := pickP 7
  let c41 : Cmd := subP
  let c42 : Cmd := pickP 0
  let c43 : Cmd := pickP 7
  let c44 : Cmd := pickP 9
  let c45 : Cmd := rollP 1
  let c46 : Cmd := addP
  let c47 : Cmd := subP
  let c48 : Cmd := pickP 4
  let c49 : Cmd := rollP 2
  let c50 : Cmd := mulP
  let c51 : Cmd := rollP 2
  let c52 : Cmd := subP
  let c53 : Cmd := rollP 4
  let c54 : Cmd := rollP 1
  let c55 : Cmd := subP
  let c56 : Cmd := pickP 4
  let c57 : Cmd := pushP (.int (0))
  let c58 : Cmd := rollP 2
  let c59 : Cmd := rollP 2
  let c60 : Cmd := expP
  let c61 : Cmd := rollP 2
  let c62 : Cmd := dupP
  let c63 : Cmd := rollP 2
  let c64 : Cmd := shrP
  let c65 : Cmd := rollP 2
  let c66 : Cmd := rollP 2
  let c67 : Cmd := rollP 1
  let c68 : Cmd := shrP
  let c69 : Cmd := rollP 1
  let c70 : Cmd := consP
  let c71 : Cmd := rollP 5
  let c72 : Cmd := dropP
  let c73 : Cmd := rollP 4
  let c74 : Cmd := dropP
  let c75 : Cmd := rollP 3
  let c76 : Cmd := dropP
  let c77 : Cmd := rollP 2
  let c78 : Cmd := dropP
  let c79 : Cmd := rollP 1
  let c80 : Cmd := dropP
  let SA : Cmd := (pushP (.int (60))).seq ((addP).seq ((dupP).seq ((pushP (.int (2))).seq ((mulP).seq ((pushP (.int (60))).seq ((rollP 1).seq ((subP).seq ((pickP 1).seq ((pushP (.int (32))).seq ((mulP).seq ((pickP 1))))))))))))
  let SB : Cmd := c13
  let SC : Cmd := c14
  let SD : Cmd := c15
  let SE : Cmd := (rollP 1).seq ((rollP 5).seq ((mulP).seq ((rollP 5).seq ((rollP 1).seq ((tdivP).seq ((pickP 1).seq ((pickP 6).seq ((mulP).seq ((pickP 1).seq ((rollP 1).seq ((subP).seq ((pickP 1).seq ((pickP 3).seq ((pushP (.int (1))).seq ((rollP 1).seq ((subP).seq ((rollP 2).seq ((addP).seq ((pickP 3).seq ((rollP 1).seq ((tdivP).seq ((pushP (.int (0))).seq ((maxP).seq ((pickP 7).seq ((subP).seq ((pickP 0).seq ((pickP 7).seq ((pickP 9).seq ((rollP 1).seq ((addP).seq ((subP).seq ((pickP 4).seq ((rollP 2).seq ((mulP).seq ((rollP 2).seq ((subP).seq ((rollP 4).seq ((rollP 1).seq ((subP).seq ((pickP 4).seq ((pushP (.int (0))).seq ((rollP 2).seq ((rollP 2))))))))))))))))))))))))))))))))))))))))))))
  let SF : Cmd := c60
  let SG : Cmd := (rollP 2).seq ((dupP).seq ((rollP 2).seq ((shrP).seq ((rollP 2).seq ((rollP 2).seq ((rollP 1).seq ((shrP).seq ((rollP 1).seq ((consP).seq ((rollP 5).seq ((dropP).seq ((rollP 4).seq ((dropP).seq ((rollP 3).seq ((dropP).seq ((rollP 2).seq ((dropP).seq ((rollP 1).seq ((dropP))))))))))))))))))))
  let PROG : Cmd := ((((((SA.seq SB).seq SC).seq SD).seq SE).seq SF).seq SG)
  refine ⟨PROG, 80 * KSm * 1000000000000 * 1002 ^ KE + KE + 1, ?_⟩
  intro main p j k σ hp hk1 he hσ
  let pa : ℤ := (p : ℤ)
  let ja : ℤ := (j : ℤ)
  let ka : ℤ := (k : ℤ)
  let sa : ℤ := (σ : ℤ)
  let A : ℤ := 60 + pa
  let Q : ℤ := 2 * A - 60
  let E : ℤ := 32 * A
  let Qn : ℕ := 2 * p + 60
  set N : ℕ := 2 * p + isz ja + isz ka + isz sa + 40000 with hNdef
  let B0 : ℕ := p + isz ja + isz ka + isz sa
  let CRT : ℕ := KSm * (1000000000000 * N ^ KE)
  have hKN : 30000 ≤ N := by rw [hNdef]; omega
  have hKEE : 4 ≤ KE := by simp only [KE]; omega
  have hCRT : CRT = KSm * (1000000000000 * N ^ KE) := rfl
  have hKSmCRT : KSm ≤ CRT := by
    rw [hCRT]
    exact Nat.le_mul_of_pos_right KSm (Nat.mul_pos (by norm_num) (pow_pos (by omega) KE))
  have hKEKSm : KE ≤ KSm := by simp only [KSm]; omega
  have hKpk : Kpk ≤ KSm := by simp only [KSm]; omega
  have hKrl : Krl ≤ KSm := by simp only [KSm]; omega
  have hKdu : Kdu ≤ KSm := by simp only [KSm]; omega
  have hKdr : Kdr ≤ KSm := by simp only [KSm]; omega
  have hKmul : Kmul ≤ KSm := by simp only [KSm]; omega
  have hKadd : Kadd ≤ KSm := by simp only [KSm]; omega
  have hKsub : Ksub ≤ KSm := by simp only [KSm]; omega
  have hKtdiv : Ktdiv ≤ KSm := by simp only [KSm]; omega
  have hKmax : Kmax ≤ KSm := by simp only [KSm]; omega
  have hKshr : Kshr ≤ KSm := by simp only [KSm]; omega
  have hKpv : Kpv ≤ KSm := by simp only [KSm]; omega
  have hKcv : Kcv ≤ KSm := by simp only [KSm]; omega
  have hKpiKE : Kpi ≤ KE := by simp only [KE]; omega
  have hKlogKE : Klog ≤ KE := by simp only [KE]; omega
  have hKexpKE : Kexp ≤ KE := by simp only [KE]; omega
  have hc0 : isz (0 : ℤ) = 2 := by decide
  have hc1 : isz (1 : ℤ) = 3 := by decide
  have hc2 : isz (2 : ℤ) = 4 := by decide
  have hc32 : isz (32 : ℤ) = 8 := by decide
  have hc60 : isz (60 : ℤ) = 8 := by decide
  have hQnN : Qn ≤ N := by simp only [Qn, N]; omega
  have hQge : 100 ≤ Qn := by simp only [Qn]; omega
  have hQn_epQ : (Qn : ℤ) = epQ p := by simp only [Qn, epQ]; push_cast; ring
  have hQeq : Q = (Qn : ℤ) := by simp only [Q, A, pa, Qn]; push_cast; ring
  have hQ0 : 0 ≤ Q := by rw [hQeq]; exact Int.natCast_nonneg _
  -- top windows
  let W0 : List Val := [.int (pa), .int (ja), .int (ka), .int (sa)]
  let W1 : List Val := [.int (60), .int (pa), .int (ja), .int (ka), .int (sa)]
  let W2 : List Val := [.int (A), .int (ja), .int (ka), .int (sa)]
  let W3 : List Val := [.int (A), .int (A), .int (ja), .int (ka), .int (sa)]
  let W4 : List Val := [.int (2), .int (A), .int (A), .int (ja), .int (ka), .int (sa)]
  let W5 : List Val := [.int ((2 * A)), .int (A), .int (ja), .int (ka), .int (sa)]
  let W6 : List Val := [.int (60), .int ((2 * A)), .int (A), .int (ja), .int (ka), .int (sa)]
  let W7 : List Val := [.int ((2 * A)), .int (60), .int (A), .int (ja), .int (ka), .int (sa)]
  let W8 : List Val := [.int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  let W9 : List Val := [.int (A), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  let W10 : List Val := [.int (32), .int (A), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  let W11 : List Val := [.int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  let W12 : List Val := [.int (Q), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  -- boundary window functions
  let w13 : ℤ → List Val := fun P => [.int (P), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  let w14 : ℤ → List Val := fun P => [.int (Q), .int (P), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  let w15 : ℤ → ℤ → List Val := fun P L => [.int (L), .int (P), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
  let w57 : ℤ → ℤ → List Val := fun P L => [.int (Q), .int (epZw p σ j k P L), .int (0), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
  let w58 : ℤ → ℤ → ℤ → ℤ → List Val := fun P L U V => [.int (U), .int (V), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
  let w78 : ℤ → ℤ → ℤ → ℤ → List Val := fun P L U V => [(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V)))]
  have hc0 : isz (0 : ℤ) = 2 := by decide
  have hc1 : isz (1 : ℤ) = 3 := by decide
  have hc2 : isz (2 : ℤ) = 4 := by decide
  have hc32 : isz (32 : ℤ) = 8 := by decide
  have hc60 : isz (60 : ℤ) = 8 := by decide
  have hN1 : (1 : ℕ) ≤ N := by
    rw [hNdef]
    show 1 ≤ 2 * p + isz ja + isz ka + isz sa + 40000
    omega
  have hN4 : (30000 : ℕ) ≤ N := by
    rw [hNdef]
    show 30000 ≤ 2 * p + isz ja + isz ka + isz sa + 40000
    omega
  have hmul10 : N ≤ 10 * N := Nat.le_mul_of_pos_left (n := 10) N (by norm_num)
  have hmul20 : N ≤ 20 * N := Nat.le_mul_of_pos_left (n := 20) N (by norm_num)
  have hmul200 : N ≤ 200 * N := Nat.le_mul_of_pos_left (n := 200) N (by norm_num)
  have hmul300 : N ≤ 300 * N := Nat.le_mul_of_pos_left (n := 300) N (by norm_num)
  have h20C : (20 : ℕ) ≤ 20 * N := by
    have h := Nat.mul_le_mul_left 20 hN1
    rwa [Nat.mul_one] at h
  have hNpa : isz pa ≤ N := by
    rw [hNdef]
    show isz (p : ℤ) ≤ 2 * p + isz ja + isz ka + isz sa + 40000
    have h := isz_natCast_le p
    omega
  have hNja : isz ja ≤ N := by
    rw [hNdef]
    show isz ja ≤ 2 * p + isz ja + isz ka + isz sa + 40000
    omega
  have hNka : isz ka ≤ N := by
    rw [hNdef]
    show isz ka ≤ 2 * p + isz ja + isz ka + isz sa + 40000
    omega
  have hNsa : isz sa ≤ N := by
    rw [hNdef]
    show isz sa ≤ 2 * p + isz ja + isz ka + isz sa + 40000
    omega
  have hNP : 2 * p + 100 ≤ N := by
    rw [hNdef]
    show 2 * p + 100 ≤ 2 * p + isz ja + isz ka + isz sa + 40000
    omega
  -- size facts
  have hsz_pa : isz pa ≤ 10 * N := le_trans hNpa hmul10
  have hsz_pa4 : isz pa ≤ 4000 * N := le_trans hsz_pa (coeff_le_mono (by norm_num))
  have hsz_ja : isz ja ≤ 10 * N := le_trans hNja hmul10
  have hsz_ja4 : isz ja ≤ 4000 * N := le_trans hsz_ja (coeff_le_mono (by norm_num))
  have hsz_ka : isz ka ≤ 10 * N := le_trans hNka hmul10
  have hsz_ka4 : isz ka ≤ 4000 * N := le_trans hsz_ka (coeff_le_mono (by norm_num))
  have hsz_sa : isz sa ≤ 10 * N := le_trans hNsa hmul10
  have hsz_sa4 : isz sa ≤ 4000 * N := le_trans hsz_sa (coeff_le_mono (by norm_num))
  have hsz_c0 : isz (0 : ℤ) ≤ 20 * N := le_trans (le_of_eq hc0) (le_trans (by norm_num) h20C)
  have hsz_c04 : isz (0 : ℤ) ≤ 4000 * N := le_trans hsz_c0 (coeff_le_mono (by norm_num))
  have hsz_c1 : isz (1 : ℤ) ≤ 20 * N := le_trans (le_of_eq hc1) (le_trans (by norm_num) h20C)
  have hsz_c14 : isz (1 : ℤ) ≤ 4000 * N := le_trans hsz_c1 (coeff_le_mono (by norm_num))
  have hsz_c2 : isz (2 : ℤ) ≤ 20 * N := le_trans (le_of_eq hc2) (le_trans (by norm_num) h20C)
  have hsz_c24 : isz (2 : ℤ) ≤ 4000 * N := le_trans hsz_c2 (coeff_le_mono (by norm_num))
  have hsz_c32 : isz (32 : ℤ) ≤ 20 * N := le_trans (le_of_eq hc32) (le_trans (by norm_num) h20C)
  have hsz_c324 : isz (32 : ℤ) ≤ 4000 * N := le_trans hsz_c32 (coeff_le_mono (by norm_num))
  have hsz_c60 : isz (60 : ℤ) ≤ 20 * N := le_trans (le_of_eq hc60) (le_trans (by norm_num) h20C)
  have hsz_c604 : isz (60 : ℤ) ≤ 4000 * N := le_trans hsz_c60 (coeff_le_mono (by norm_num))
  have hsz_A : isz (A) ≤ 30 * N := le_trans (isz_le_add_of hsz_c60 hsz_pa) (coeff_add_le (by norm_num))
  have hsz_A4 : isz (A) ≤ 4000 * N := le_trans hsz_A (coeff_le_mono (by norm_num))
  have hsz_2A : isz (2 * A) ≤ 60 * N := le_trans (isz_le_mul_of hsz_c2 hsz_A) (coeff_add_le (by norm_num))
  have hsz_2A4 : isz (2 * A) ≤ 4000 * N := le_trans hsz_2A (coeff_le_mono (by norm_num))
  have hsz_Q : isz (Q) ≤ 100 * N := le_trans (isz_le_sub_of hsz_2A hsz_c60) (coeff_add_le (by norm_num))
  have hsz_Q4 : isz (Q) ≤ 4000 * N := le_trans hsz_Q (coeff_le_mono (by norm_num))
  have hsz_E : isz (E) ≤ 100 * N := le_trans (isz_le_mul_of hsz_c32 hsz_A) (coeff_add_le (by norm_num))
  have hsz_E4 : isz (E) ≤ 4000 * N := le_trans hsz_E (coeff_le_mono (by norm_num))
  have hA : Spec main SA 4 (fun t => t = W0) (fun _ o => o = W12) (fun _ => 12 * CRT) := by
    have hszl6 : szl W6 ≤ N * N := by
      have h : szl W6 ≤ 30000 * N := by
        change szl ([.int (60), .int ((2 * A)), .int (A), .int (ja), .int (ka), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl8 : szl W8 ≤ N * N := by
      have h : szl W8 ≤ 30000 * N := by
        change szl ([.int (Q), .int (A), .int (ja), .int (ka), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl11 : szl W11 ≤ N * N := by
      have h : szl W11 ≤ 30000 * N := by
        change szl ([.int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have e1 : Spec main (c1) W0.length (fun t => t = W0) (fun _ o => o = W1) (fun _ => 1 * CRT) :=
      Spec.pushValStep (hpush main) (.int (60)) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (60)) + 1)
          (Kc := Kpv) hKN hKEE hCRT hKpv (by rw [vsz_int]; have := hsz_c60; omega)))

    have e2 : Spec main (c2) W1.length (fun t => t = W1) (fun _ o => o = W2) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hadd main) trivial (E := [.int (ja), .int (ka), .int (sa)]) (B := W2) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (60)) (b := isz (pa))
          (Kc := Kadd) hKN hKEE hCRT hKadd (le_4000N_of hsz_c60 (by norm_num)) (le_4000N_of hsz_pa (by norm_num))))

    have e3 : Spec main (c3) W2.length (fun t => t = W2) (fun _ o => o = W3) (fun _ => 1 * CRT) :=
      Spec.dupStep_x1 (hdup main) (.int (A)) ([.int (ja), .int (ka), .int (sa)]) (B := W3) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (A)) + 1)
          (Kc := Kdu) hKN hKEE hCRT hKdu (by rw [vsz_int]; have := hsz_A; omega)))

    have e4 : Spec main (c4) W3.length (fun t => t = W3) (fun _ o => o = W4) (fun _ => 1 * CRT) :=
      Spec.pushValStep (hpush main) (.int (2)) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (2)) + 1)
          (Kc := Kpv) hKN hKEE hCRT hKpv (by rw [vsz_int]; have := hsz_c2; omega)))

    have e5 : Spec main (c5) W4.length (fun t => t = W4) (fun _ o => o = W5) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hmul main) trivial (E := [.int (A), .int (ja), .int (ka), .int (sa)]) (B := W5) (by rfl)
        (le_one_mul (epCostMul (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (2)) (b := isz (A))
          (Kc := Kmul) hKN hKEE hCRT hKmul (le_4000N_of hsz_c2 (by norm_num)) (le_4000N_of hsz_A (by norm_num))))

    have e6 : Spec main (c6) W5.length (fun t => t = W5) (fun _ o => o = W6) (fun _ => 1 * CRT) :=
      Spec.pushValStep (hpush main) (.int (60)) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (60)) + 1)
          (Kc := Kpv) hKN hKEE hCRT hKpv (by rw [vsz_int]; have := hsz_c60; omega)))

    have e7 : Spec main (c7) W6.length (fun t => t = W6) (fun _ o => o = W7) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W6) (B := W7) (k := 1) (by rw [show W6.length = 6 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W6)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl6)))

    have e8 : Spec main (c8) W7.length (fun t => t = W7) (fun _ o => o = W8) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hsub main) trivial (E := [.int (A), .int (ja), .int (ka), .int (sa)]) (B := W8) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (2 * A)) (b := isz (60))
          (Kc := Ksub) hKN hKEE hCRT hKsub (le_4000N_of hsz_2A (by norm_num)) (le_4000N_of hsz_c60 (by norm_num))))

    have e9 : Spec main (c9) W8.length (fun t => t = W8) (fun _ o => o = W9) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W8) (B := W9) (k := 1) (by rw [show W8.length = 5 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W8)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl8)))

    have e10 : Spec main (c10) W9.length (fun t => t = W9) (fun _ o => o = W10) (fun _ => 1 * CRT) :=
      Spec.pushValStep (hpush main) (.int (32)) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (32)) + 1)
          (Kc := Kpv) hKN hKEE hCRT hKpv (by rw [vsz_int]; have := hsz_c32; omega)))

    have e11 : Spec main (c11) W10.length (fun t => t = W10) (fun _ o => o = W11) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hmul main) trivial (E := [.int (Q), .int (A), .int (ja), .int (ka), .int (sa)]) (B := W11) (by rfl)
        (le_one_mul (epCostMul (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (32)) (b := isz (A))
          (Kc := Kmul) hKN hKEE hCRT hKmul (le_4000N_of hsz_c32 (by norm_num)) (le_4000N_of hsz_A (by norm_num))))

    have e12 : Spec main (c12) W11.length (fun t => t = W11) (fun _ o => o = W12) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W11) (B := W12) (k := 1) (by rw [show W11.length = 6 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W11)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl11)))

    have cc12 : Spec main (c12) W11.length (fun t => t = W11) (fun _ o => o = W12) (fun _ => 1 * CRT) :=
      e12
    have cc11 := Spec.seqAdd hk e11 cc12 (by rfl)
    have cc10 := Spec.seqAdd hk e10 cc11 (by rfl)
    have cc9 := Spec.seqAdd hk e9 cc10 (by rfl)
    have cc8 := Spec.seqAdd hk e8 cc9 (by rfl)
    have cc7 := Spec.seqAdd hk e7 cc8 (by rfl)
    have cc6 := Spec.seqAdd hk e6 cc7 (by rfl)
    have cc5 := Spec.seqAdd hk e5 cc6 (by rfl)
    have cc4 := Spec.seqAdd hk e4 cc5 (by rfl)
    have cc3 := Spec.seqAdd hk e3 cc4 (by rfl)
    have cc2 := Spec.seqAdd hk e2 cc3 (by rfl)
    have cc1 := Spec.seqAdd hk e1 cc2 (by rfl)
    have ccz1 : Spec main SA W0.length (fun t => t = W0) (fun _ o => o = W12) (fun _ => 12 * CRT) := by
      refine Spec.mono hk cc1 (fun t _ h => h) (fun t o _ _ h => h) (fun t ht h => ?_)
      exact le_rfl

    exact ccz1

  have hB : Spec main SB 7 (fun t => t = W12)
      (fun _ o => ∃ P : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ o = w13 P) (fun _ => CRT) := by
    refine Spec.mono hk (Spec.wordStep (Kc := Kpi) (Q := Qn)
      (φ := fun u : ℤ => |(u : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1)
      (E := [.int E, .int Q, .int A, .int ja, .int ka, .int sa])
      (hpi main Qn hQge)
      (epCostPow (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (Kc := Kpi) (Q := Qn)
        hKN hKEE hCRT hKpiKE hKEKSm (by have := hQnN; omega))) ?_ ?_ ?_
    · intro t ht h
      rw [h]
      simp only [W12, List.singleton_append, List.cons_append, List.nil_append, hQeq]
    · intro t o ht h hQ
      rcases hQ with ⟨u, hu, ho⟩
      exact ⟨u, hu, by rw [ho]; simp only [w13, List.singleton_append, List.cons_append, List.nil_append]⟩
    · intro t ht h
      exact le_rfl

  have hC : Spec main SC 7 (fun t => ∃ P : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ t = w13 P)
      (fun _ o => ∃ P : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ o = w14 P) (fun _ => CRT) := by
    intro top rest ht hP
    rcases hP with ⟨P, hPc, rfl⟩
    have hsz_P : isz P ≤ 200 * N := by
      have h := isz_le_of_pi_approx (q := 2 * p + 60) hPc
      have h3 : 2 * p + 60 + 5 ≤ N := le_trans (by omega) hNP
      exact le_trans (le_trans h h3) hmul200
    have hszl13 : szl (w13 P) ≤ N * N := by
      have h : szl (w13 P) ≤ 4000 * N := by
        change szl ([.int (P), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]) ≤ 4000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N (le_trans (by norm_num : 4000 ≤ 30000) hN4))
    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
      (Spec.pickStep_x1 (K := Kpk) (hpick main) (A := w13 P) (B := w14 P) (k := 2)
        (by rw [show (w13 P).length = 7 from rfl]; omega) (by rfl)
        (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 3) (b := szl (w13 P))
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) hszl13)) (w13 P) rest rfl rfl vs hvs s R hR
    obtain ⟨o, ho, hw⟩ := hpost
    exact ⟨out, s', n, ⟨o, ho, ⟨P, hPc, hw⟩⟩, hev, hn, hstk, hfr⟩

  have hD : Spec main SD 8 (fun t => ∃ P : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ t = w14 P)
      (fun _ o => ∃ P L : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ o = w15 P L) (fun _ => CRT) := by
    have key : ∀ (P : ℤ), (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) → Spec main SD 8 (fun t => t = w14 P)
        (fun _ o => ∃ L : ℤ, (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ o = w15 P L) (fun _ => CRT) := by
      intro P hPc
      refine Spec.mono hk (Spec.wordStep (Kc := Klog) (Q := Qn)
        (φ := fun u : ℤ => |(u : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1)
        (E := [.int P, .int E, .int Q, .int A, .int ja, .int ka, .int sa])
        (hlog main Qn hQge)
        (epCostPow (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (Kc := Klog) (Q := Qn)
          hKN hKEE hCRT hKlogKE hKEKSm (by have := hQnN; omega))) ?_ ?_ ?_
      · intro t ht h
        rw [h]
        simp only [w14, List.singleton_append, List.cons_append, List.nil_append, hQeq]
      · intro t o ht h hQ
        rcases hQ with ⟨u, hu, ho⟩
        exact ⟨u, hu, by rw [ho]; simp only [w15, List.singleton_append, List.cons_append, List.nil_append]⟩
      · intro t ht h
        exact le_rfl
    intro top rest ht hP
    rcases hP with ⟨P, hPc, rfl⟩
    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := (key P hPc) (w14 P) rest rfl rfl vs hvs s R hR
    obtain ⟨o, ho, L, hL, hw⟩ := hpost
    exact ⟨out, s', n, ⟨o, ho, ⟨P, L, hPc, hL, hw⟩⟩, hev, hn, hstk, hfr⟩

  have hE : Spec main SE 8 (fun t => ∃ P L : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ t = w15 P L)
      (fun _ o => ∃ P L : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ o = w57 P L) (fun _ => 44 * CRT) := by
    intro top rest ht hP
    rcases hP with ⟨P, L, hPc, hLc, rfl⟩
    have hsz_P : isz P ≤ 200 * N := by
      have h := isz_le_of_pi_approx (q := 2 * p + 60) hPc
      have h3 : 2 * p + 60 + 5 ≤ N := le_trans (by omega) hNP
      exact le_trans (le_trans h h3) hmul200
    have hsz_L : isz L ≤ 200 * N := by
      have h := isz_le_of_log_approx (q := 2 * p + 60) hLc
      have h3 : 2 * p + 60 + 5 ≤ N := le_trans (by omega) hNP
      exact le_trans (le_trans h h3) hmul200
    have hsz_jaP : isz (ja * P) ≤ 400 * N :=
      le_trans (isz_le_mul_of hsz_ja hsz_P) (coeff_add_le (by norm_num))
    have hsz_X : isz (epXw j k P) ≤ 400 * N := by
      change isz (Int.tdiv (ja * P) ka) ≤ 400 * N
      exact isz_le_tdiv_of hsz_jaP
    have hsz_saL : isz (sa * L) ≤ 400 * N :=
      le_trans (isz_le_mul_of hsz_sa hsz_L) (coeff_add_le (by norm_num))
    have hsz_Al : isz (epAlw σ j k P L) ≤ 800 * N := by
      change isz (sa * L - epXw j k P) ≤ 800 * N
      exact le_trans (isz_le_sub_of hsz_saL hsz_X) (coeff_add_le (by norm_num))
    have hsz_Lm1 : isz (L - 1) ≤ 400 * N :=
      le_trans (isz_le_sub_of hsz_L hsz_c1) (coeff_add_le (by norm_num))
    have hsz_Alt : isz (epAlw σ j k P L + (L - 1)) ≤ 1200 * N :=
      le_trans (isz_le_add_of hsz_Al hsz_Lm1) (coeff_add_le (by norm_num))
    have hsz_T : isz (epTw σ j k P L) ≤ 1200 * N := by
      change isz (Int.tdiv (epAlw σ j k P L + (L - 1)) L) ≤ 1200 * N
      exact isz_le_tdiv_of hsz_Alt
    have hsz_Tau : isz (epTauw σ j k P L) ≤ 1200 * N := by
      change isz (max 0 (epTw σ j k P L)) ≤ 1200 * N
      exact isz_le_max0_of hsz_T
    have hsz_K0 : isz (epK0w σ j k P L) ≤ 1400 * N := by
      change isz (sa - epTauw σ j k P L) ≤ 1400 * N
      exact le_trans (isz_le_sub_of hsz_sa hsz_Tau) (coeff_add_le (by norm_num))
    have hsz_Asa : isz (A + sa) ≤ 50 * N :=
      le_trans (isz_le_add_of hsz_A hsz_sa) (coeff_add_le (by norm_num))
    have hsz_S : isz (epSw p σ j k P L) ≤ 1600 * N := by
      change isz ((60 + (p : ℤ)) + (σ : ℤ) - epK0w σ j k P L) ≤ 1600 * N
      exact le_trans (isz_le_sub_of hsz_Asa hsz_K0) (coeff_add_le (by norm_num))
    have hsz_K0L : isz (epK0w σ j k P L * L) ≤ 1600 * N :=
      le_trans (isz_le_mul_of hsz_K0 hsz_L) (coeff_add_le (by norm_num))
    have hsz_XK0L : isz (epXw j k P - epK0w σ j k P L * L) ≤ 2000 * N :=
      le_trans (isz_le_sub_of hsz_X hsz_K0L) (coeff_add_le (by norm_num))
    have hsz_Z : isz (epZw p σ j k P L) ≤ 2200 * N := by
      change isz ((epXw j k P - epK0w σ j k P L * L) - 32 * (60 + (p : ℤ))) ≤ 2200 * N
      exact le_trans (isz_le_sub_of hsz_XK0L hsz_E) (coeff_add_le (by norm_num))
    let W15 : List Val := [.int (L), .int (P), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
    let W16 : List Val := [.int (P), .int (L), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]
    let W17 : List Val := [.int (ja), .int (P), .int (L), .int (E), .int (Q), .int (A), .int (ka), .int (sa)]
    let W18 : List Val := [.int ((ja * P)), .int (L), .int (E), .int (Q), .int (A), .int (ka), .int (sa)]
    let W19 : List Val := [.int (ka), .int ((ja * P)), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W20 : List Val := [.int ((ja * P)), .int (ka), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W21 : List Val := [.int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W22 : List Val := [.int (L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W23 : List Val := [.int (sa), .int (L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W24 : List Val := [.int ((sa * L)), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W25 : List Val := [.int (epXw j k P), .int ((sa * L)), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W26 : List Val := [.int ((sa * L)), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W27 : List Val := [.int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W28 : List Val := [.int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W29 : List Val := [.int (L), .int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W30 : List Val := [.int (1), .int (L), .int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W31 : List Val := [.int (L), .int (1), .int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W32 : List Val := [.int ((L - 1)), .int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W33 : List Val := [.int (epAlw σ j k P L), .int ((L - 1)), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W34 : List Val := [.int ((epAlw σ j k P L + (L - 1))), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W35 : List Val := [.int (L), .int ((epAlw σ j k P L + (L - 1))), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W36 : List Val := [.int ((epAlw σ j k P L + (L - 1))), .int (L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W37 : List Val := [.int (epTw σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W38 : List Val := [.int (0), .int (epTw σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W39 : List Val := [.int (epTauw σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W40 : List Val := [.int (sa), .int (epTauw σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W41 : List Val := [.int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W42 : List Val := [.int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W43 : List Val := [.int (A), .int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W44 : List Val := [.int (sa), .int (A), .int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W45 : List Val := [.int (A), .int (sa), .int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W46 : List Val := [.int ((A + sa)), .int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W47 : List Val := [.int (epSw p σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W48 : List Val := [.int (L), .int (epSw p σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W49 : List Val := [.int (epK0w σ j k P L), .int (L), .int (epSw p σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W50 : List Val := [.int ((epK0w σ j k P L * L)), .int (epSw p σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W51 : List Val := [.int (epXw j k P), .int ((epK0w σ j k P L * L)), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W52 : List Val := [.int ((epXw j k P - epK0w σ j k P L * L)), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]
    let W53 : List Val := [.int (E), .int ((epXw j k P - epK0w σ j k P L * L)), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W54 : List Val := [.int ((epXw j k P - epK0w σ j k P L * L)), .int (E), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W55 : List Val := [.int (epZw p σ j k P L), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W56 : List Val := [.int (Q), .int (epZw p σ j k P L), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W57 : List Val := [.int (0), .int (Q), .int (epZw p σ j k P L), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W58 : List Val := [.int (epZw p σ j k P L), .int (0), .int (Q), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W59 : List Val := [.int (Q), .int (epZw p σ j k P L), .int (0), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    have hszl15 : szl W15 ≤ N * N := by
      have h : szl W15 ≤ 30000 * N := by
        change szl ([.int (L), .int (P), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl16 : szl W16 ≤ N * N := by
      have h : szl W16 ≤ 30000 * N := by
        change szl ([.int (P), .int (L), .int (E), .int (Q), .int (A), .int (ja), .int (ka), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl18 : szl W18 ≤ N * N := by
      have h : szl W18 ≤ 30000 * N := by
        change szl ([.int ((ja * P)), .int (L), .int (E), .int (Q), .int (A), .int (ka), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl19 : szl W19 ≤ N * N := by
      have h : szl W19 ≤ 30000 * N := by
        change szl ([.int (ka), .int ((ja * P)), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl21 : szl W21 ≤ N * N := by
      have h : szl W21 ≤ 30000 * N := by
        change szl ([.int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl22 : szl W22 ≤ N * N := by
      have h : szl W22 ≤ 30000 * N := by
        change szl ([.int (L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl24 : szl W24 ≤ N * N := by
      have h : szl W24 ≤ 30000 * N := by
        change szl ([.int ((sa * L)), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl25 : szl W25 ≤ N * N := by
      have h : szl W25 ≤ 30000 * N := by
        change szl ([.int (epXw j k P), .int ((sa * L)), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl27 : szl W27 ≤ N * N := by
      have h : szl W27 ≤ 30000 * N := by
        change szl ([.int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl28 : szl W28 ≤ N * N := by
      have h : szl W28 ≤ 30000 * N := by
        change szl ([.int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl30 : szl W30 ≤ N * N := by
      have h : szl W30 ≤ 30000 * N := by
        change szl ([.int (1), .int (L), .int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl32 : szl W32 ≤ N * N := by
      have h : szl W32 ≤ 30000 * N := by
        change szl ([.int ((L - 1)), .int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl34 : szl W34 ≤ N * N := by
      have h : szl W34 ≤ 30000 * N := by
        change szl ([.int ((epAlw σ j k P L + (L - 1))), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl35 : szl W35 ≤ N * N := by
      have h : szl W35 ≤ 30000 * N := by
        change szl ([.int (L), .int ((epAlw σ j k P L + (L - 1))), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl39 : szl W39 ≤ N * N := by
      have h : szl W39 ≤ 30000 * N := by
        change szl ([.int (epTauw σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl41 : szl W41 ≤ N * N := by
      have h : szl W41 ≤ 30000 * N := by
        change szl ([.int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl42 : szl W42 ≤ N * N := by
      have h : szl W42 ≤ 30000 * N := by
        change szl ([.int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl43 : szl W43 ≤ N * N := by
      have h : szl W43 ≤ 30000 * N := by
        change szl ([.int (A), .int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl44 : szl W44 ≤ N * N := by
      have h : szl W44 ≤ 30000 * N := by
        change szl ([.int (sa), .int (A), .int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl47 : szl W47 ≤ N * N := by
      have h : szl W47 ≤ 30000 * N := by
        change szl ([.int (epSw p σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl48 : szl W48 ≤ N * N := by
      have h : szl W48 ≤ 30000 * N := by
        change szl ([.int (L), .int (epSw p σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl50 : szl W50 ≤ N * N := by
      have h : szl W50 ≤ 30000 * N := by
        change szl ([.int ((epK0w σ j k P L * L)), .int (epSw p σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl52 : szl W52 ≤ N * N := by
      have h : szl W52 ≤ 30000 * N := by
        change szl ([.int ((epXw j k P - epK0w σ j k P L * L)), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl53 : szl W53 ≤ N * N := by
      have h : szl W53 ≤ 30000 * N := by
        change szl ([.int (E), .int ((epXw j k P - epK0w σ j k P L * L)), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl55 : szl W55 ≤ N * N := by
      have h : szl W55 ≤ 30000 * N := by
        change szl ([.int (epZw p σ j k P L), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl57 : szl W57 ≤ N * N := by
      have h : szl W57 ≤ 30000 * N := by
        change szl ([.int (0), .int (Q), .int (epZw p σ j k P L), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl58 : szl W58 ≤ N * N := by
      have h : szl W58 ≤ 30000 * N := by
        change szl ([.int (epZw p σ j k P L), .int (0), .int (Q), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have e16 : Spec main (c16) W15.length (fun t => t = W15) (fun _ o => o = W16) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W15) (B := W16) (k := 1) (by rw [show W15.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W15)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl15)))

    have e17 : Spec main (c17) W16.length (fun t => t = W16) (fun _ o => o = W17) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W16) (B := W17) (k := 5) (by rw [show W16.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 5 + 1) (b := szl W16)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl16)))

    have e18 : Spec main (c18) W17.length (fun t => t = W17) (fun _ o => o = W18) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hmul main) trivial (E := [.int (L), .int (E), .int (Q), .int (A), .int (ka), .int (sa)]) (B := W18) (by rfl)
        (le_one_mul (epCostMul (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (ja)) (b := isz (P))
          (Kc := Kmul) hKN hKEE hCRT hKmul (le_4000N_of hsz_ja (by norm_num)) (le_4000N_of hsz_P (by norm_num))))

    have e19 : Spec main (c19) W18.length (fun t => t = W18) (fun _ o => o = W19) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W18) (B := W19) (k := 5) (by rw [show W18.length = 7 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 5 + 1) (b := szl W18)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl18)))

    have e20 : Spec main (c20) W19.length (fun t => t = W19) (fun _ o => o = W20) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W19) (B := W20) (k := 1) (by rw [show W19.length = 7 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W19)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl19)))

    have e21 : Spec main (c21) W20.length (fun t => t = W20) (fun _ o => o = W21) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (htdiv main) (by have hh := hk1; simp only [ka]; omega) (E := [.int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W21) (by rfl)
        (le_one_mul (epCostMul (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (ja * P)) (b := isz (ka))
          (Kc := Ktdiv) hKN hKEE hCRT hKtdiv (le_4000N_of hsz_jaP (by norm_num)) (le_4000N_of hsz_ka (by norm_num))))

    have e22 : Spec main (c22) W21.length (fun t => t = W21) (fun _ o => o = W22) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W21) (B := W22) (k := 1) (by rw [show W21.length = 6 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W21)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl21)))

    have e23 : Spec main (c23) W22.length (fun t => t = W22) (fun _ o => o = W23) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W22) (B := W23) (k := 6) (by rw [show W22.length = 7 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 6 + 1) (b := szl W22)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl22)))

    have e24 : Spec main (c24) W23.length (fun t => t = W23) (fun _ o => o = W24) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hmul main) trivial (E := [.int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W24) (by rfl)
        (le_one_mul (epCostMul (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (sa)) (b := isz (L))
          (Kc := Kmul) hKN hKEE hCRT hKmul (le_4000N_of hsz_sa (by norm_num)) (le_4000N_of hsz_L (by norm_num))))

    have e25 : Spec main (c25) W24.length (fun t => t = W24) (fun _ o => o = W25) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W24) (B := W25) (k := 1) (by rw [show W24.length = 7 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W24)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl24)))

    have e26 : Spec main (c26) W25.length (fun t => t = W25) (fun _ o => o = W26) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W25) (B := W26) (k := 1) (by rw [show W25.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W25)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl25)))

    have e27 : Spec main (c27) W26.length (fun t => t = W26) (fun _ o => o = W27) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hsub main) trivial (E := [.int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W27) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (sa * L)) (b := isz (epXw j k P))
          (Kc := Ksub) hKN hKEE hCRT hKsub (le_4000N_of hsz_saL (by norm_num)) (le_4000N_of hsz_X (by norm_num))))

    have e28 : Spec main (c28) W27.length (fun t => t = W27) (fun _ o => o = W28) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W27) (B := W28) (k := 1) (by rw [show W27.length = 7 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W27)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl27)))

    have e29 : Spec main (c29) W28.length (fun t => t = W28) (fun _ o => o = W29) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W28) (B := W29) (k := 3) (by rw [show W28.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 3 + 1) (b := szl W28)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl28)))

    have e30 : Spec main (c30) W29.length (fun t => t = W29) (fun _ o => o = W30) (fun _ => 1 * CRT) :=
      Spec.pushValStep (hpush main) (.int (1)) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (1)) + 1)
          (Kc := Kpv) hKN hKEE hCRT hKpv (by rw [vsz_int]; have := hsz_c1; omega)))

    have e31 : Spec main (c31) W30.length (fun t => t = W30) (fun _ o => o = W31) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W30) (B := W31) (k := 1) (by rw [show W30.length = 10 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W30)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl30)))

    have e32 : Spec main (c32) W31.length (fun t => t = W31) (fun _ o => o = W32) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hsub main) trivial (E := [.int (epXw j k P), .int (epAlw σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W32) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (L)) (b := isz (1))
          (Kc := Ksub) hKN hKEE hCRT hKsub (le_4000N_of hsz_L (by norm_num)) (le_4000N_of hsz_c1 (by norm_num))))

    have e33 : Spec main (c33) W32.length (fun t => t = W32) (fun _ o => o = W33) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W32) (B := W33) (k := 2) (by rw [show W32.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W32)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl32)))

    have e34 : Spec main (c34) W33.length (fun t => t = W33) (fun _ o => o = W34) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hadd main) trivial (E := [.int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W34) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (epAlw σ j k P L)) (b := isz (L - 1))
          (Kc := Kadd) hKN hKEE hCRT hKadd (le_4000N_of hsz_Al (by norm_num)) (le_4000N_of hsz_Lm1 (by norm_num))))

    have e35 : Spec main (c35) W34.length (fun t => t = W34) (fun _ o => o = W35) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W34) (B := W35) (k := 3) (by rw [show W34.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 3 + 1) (b := szl W34)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl34)))

    have e36 : Spec main (c36) W35.length (fun t => t = W35) (fun _ o => o = W36) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W35) (B := W36) (k := 1) (by rw [show W35.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W35)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl35)))

    have e37 : Spec main (c37) W36.length (fun t => t = W36) (fun _ o => o = W37) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (htdiv main) (ne_zero_of_log_approx (q := Qn) (by omega) hLc) (E := [.int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W37) (by rfl)
        (le_one_mul (epCostMul (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (epAlw σ j k P L + (L - 1))) (b := isz (L))
          (Kc := Ktdiv) hKN hKEE hCRT hKtdiv (le_4000N_of hsz_Alt (by norm_num)) (le_4000N_of hsz_L (by norm_num))))

    have e38 : Spec main (c38) W37.length (fun t => t = W37) (fun _ o => o = W38) (fun _ => 1 * CRT) :=
      Spec.pushValStep (hpush main) (.int (0)) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (0)) + 1)
          (Kc := Kpv) hKN hKEE hCRT hKpv (by rw [vsz_int]; have := hsz_c0; omega)))

    have e39 : Spec main (c39) W38.length (fun t => t = W38) (fun _ o => o = W39) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hmax main) trivial (E := [.int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W39) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (0)) (b := isz (epTw σ j k P L))
          (Kc := Kmax) hKN hKEE hCRT hKmax (le_4000N_of hsz_c0 (by norm_num)) (le_4000N_of hsz_T (by norm_num))))

    have e40 : Spec main (c40) W39.length (fun t => t = W39) (fun _ o => o = W40) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W39) (B := W40) (k := 7) (by rw [show W39.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 7 + 1) (b := szl W39)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl39)))

    have e41 : Spec main (c41) W40.length (fun t => t = W40) (fun _ o => o = W41) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hsub main) trivial (E := [.int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W41) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (sa)) (b := isz (epTauw σ j k P L))
          (Kc := Ksub) hKN hKEE hCRT hKsub (le_4000N_of hsz_sa (by norm_num)) (le_4000N_of hsz_Tau (by norm_num))))

    have e42 : Spec main (c42) W41.length (fun t => t = W41) (fun _ o => o = W42) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W41) (B := W42) (k := 0) (by rw [show W41.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 0 + 1) (b := szl W41)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl41)))

    have e43 : Spec main (c43) W42.length (fun t => t = W42) (fun _ o => o = W43) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W42) (B := W43) (k := 7) (by rw [show W42.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 7 + 1) (b := szl W42)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl42)))

    have e44 : Spec main (c44) W43.length (fun t => t = W43) (fun _ o => o = W44) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W43) (B := W44) (k := 9) (by rw [show W43.length = 10 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 9 + 1) (b := szl W43)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl43)))

    have e45 : Spec main (c45) W44.length (fun t => t = W44) (fun _ o => o = W45) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W44) (B := W45) (k := 1) (by rw [show W44.length = 11 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W44)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl44)))

    have e46 : Spec main (c46) W45.length (fun t => t = W45) (fun _ o => o = W46) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hadd main) trivial (E := [.int (epK0w σ j k P L), .int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W46) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (A)) (b := isz (sa))
          (Kc := Kadd) hKN hKEE hCRT hKadd (le_4000N_of hsz_A (by norm_num)) (le_4000N_of hsz_sa (by norm_num))))

    have e47 : Spec main (c47) W46.length (fun t => t = W46) (fun _ o => o = W47) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hsub main) trivial (E := [.int (epK0w σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W47) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (A + sa)) (b := isz (epK0w σ j k P L))
          (Kc := Ksub) hKN hKEE hCRT hKsub (le_4000N_of hsz_Asa (by norm_num)) (le_4000N_of hsz_K0 (by norm_num))))

    have e48 : Spec main (c48) W47.length (fun t => t = W47) (fun _ o => o = W48) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W47) (B := W48) (k := 4) (by rw [show W47.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 4 + 1) (b := szl W47)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl47)))

    have e49 : Spec main (c49) W48.length (fun t => t = W48) (fun _ o => o = W49) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W48) (B := W49) (k := 2) (by rw [show W48.length = 10 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W48)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl48)))

    have e50 : Spec main (c50) W49.length (fun t => t = W49) (fun _ o => o = W50) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hmul main) trivial (E := [.int (epSw p σ j k P L), .int (epXw j k P), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W50) (by rfl)
        (le_one_mul (epCostMul (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (epK0w σ j k P L)) (b := isz (L))
          (Kc := Kmul) hKN hKEE hCRT hKmul (le_4000N_of hsz_K0 (by norm_num)) (le_4000N_of hsz_L (by norm_num))))

    have e51 : Spec main (c51) W50.length (fun t => t = W50) (fun _ o => o = W51) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W50) (B := W51) (k := 2) (by rw [show W50.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W50)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl50)))

    have e52 : Spec main (c52) W51.length (fun t => t = W51) (fun _ o => o = W52) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hsub main) trivial (E := [.int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (E), .int (Q), .int (A), .int (sa)]) (B := W52) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (epXw j k P)) (b := isz (epK0w σ j k P L * L))
          (Kc := Ksub) hKN hKEE hCRT hKsub (le_4000N_of hsz_X (by norm_num)) (le_4000N_of hsz_K0L (by norm_num))))

    have e53 : Spec main (c53) W52.length (fun t => t = W52) (fun _ o => o = W53) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W52) (B := W53) (k := 4) (by rw [show W52.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 4 + 1) (b := szl W52)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl52)))

    have e54 : Spec main (c54) W53.length (fun t => t = W53) (fun _ o => o = W54) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W53) (B := W54) (k := 1) (by rw [show W53.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W53)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl53)))

    have e55 : Spec main (c55) W54.length (fun t => t = W54) (fun _ o => o = W55) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hsub main) trivial (E := [.int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) (B := W55) (by rfl)
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (epXw j k P - epK0w σ j k P L * L)) (b := isz (E))
          (Kc := Ksub) hKN hKEE hCRT hKsub (le_4000N_of hsz_XK0L (by norm_num)) (le_4000N_of hsz_E (by norm_num))))

    have e56 : Spec main (c56) W55.length (fun t => t = W55) (fun _ o => o = W56) (fun _ => 1 * CRT) :=
      Spec.pickStep_x1 (K := Kpk) (hpick main) (A := W55) (B := W56) (k := 4) (by rw [show W55.length = 7 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 4 + 1) (b := szl W55)
          (Kc := Kpk) hKN hKEE hCRT hKpk (by omega) (by exact hszl55)))

    have e57 : Spec main (c57) W56.length (fun t => t = W56) (fun _ o => o = W57) (fun _ => 1 * CRT) :=
      Spec.pushValStep (hpush main) (.int (0)) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (0)) + 1)
          (Kc := Kpv) hKN hKEE hCRT hKpv (by rw [vsz_int]; have := hsz_c0; omega)))

    have e58 : Spec main (c58) W57.length (fun t => t = W57) (fun _ o => o = W58) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W57) (B := W58) (k := 2) (by rw [show W57.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W57)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl57)))

    have e59 : Spec main (c59) W58.length (fun t => t = W58) (fun _ o => o = W59) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W58) (B := W59) (k := 2) (by rw [show W58.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W58)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl58)))

    have cc59 : Spec main (c59) W58.length (fun t => t = W58) (fun _ o => o = W59) (fun _ => 1 * CRT) :=
      e59
    have cc58 := Spec.seqAdd hk e58 cc59 (by rfl)
    have cc57 := Spec.seqAdd hk e57 cc58 (by rfl)
    have cc56 := Spec.seqAdd hk e56 cc57 (by rfl)
    have cc55 := Spec.seqAdd hk e55 cc56 (by rfl)
    have cc54 := Spec.seqAdd hk e54 cc55 (by rfl)
    have cc53 := Spec.seqAdd hk e53 cc54 (by rfl)
    have cc52 := Spec.seqAdd hk e52 cc53 (by rfl)
    have cc51 := Spec.seqAdd hk e51 cc52 (by rfl)
    have cc50 := Spec.seqAdd hk e50 cc51 (by rfl)
    have cc49 := Spec.seqAdd hk e49 cc50 (by rfl)
    have cc48 := Spec.seqAdd hk e48 cc49 (by rfl)
    have cc47 := Spec.seqAdd hk e47 cc48 (by rfl)
    have cc46 := Spec.seqAdd hk e46 cc47 (by rfl)
    have cc45 := Spec.seqAdd hk e45 cc46 (by rfl)
    have cc44 := Spec.seqAdd hk e44 cc45 (by rfl)
    have cc43 := Spec.seqAdd hk e43 cc44 (by rfl)
    have cc42 := Spec.seqAdd hk e42 cc43 (by rfl)
    have cc41 := Spec.seqAdd hk e41 cc42 (by rfl)
    have cc40 := Spec.seqAdd hk e40 cc41 (by rfl)
    have cc39 := Spec.seqAdd hk e39 cc40 (by rfl)
    have cc38 := Spec.seqAdd hk e38 cc39 (by rfl)
    have cc37 := Spec.seqAdd hk e37 cc38 (by rfl)
    have cc36 := Spec.seqAdd hk e36 cc37 (by rfl)
    have cc35 := Spec.seqAdd hk e35 cc36 (by rfl)
    have cc34 := Spec.seqAdd hk e34 cc35 (by rfl)
    have cc33 := Spec.seqAdd hk e33 cc34 (by rfl)
    have cc32 := Spec.seqAdd hk e32 cc33 (by rfl)
    have cc31 := Spec.seqAdd hk e31 cc32 (by rfl)
    have cc30 := Spec.seqAdd hk e30 cc31 (by rfl)
    have cc29 := Spec.seqAdd hk e29 cc30 (by rfl)
    have cc28 := Spec.seqAdd hk e28 cc29 (by rfl)
    have cc27 := Spec.seqAdd hk e27 cc28 (by rfl)
    have cc26 := Spec.seqAdd hk e26 cc27 (by rfl)
    have cc25 := Spec.seqAdd hk e25 cc26 (by rfl)
    have cc24 := Spec.seqAdd hk e24 cc25 (by rfl)
    have cc23 := Spec.seqAdd hk e23 cc24 (by rfl)
    have cc22 := Spec.seqAdd hk e22 cc23 (by rfl)
    have cc21 := Spec.seqAdd hk e21 cc22 (by rfl)
    have cc20 := Spec.seqAdd hk e20 cc21 (by rfl)
    have cc19 := Spec.seqAdd hk e19 cc20 (by rfl)
    have cc18 := Spec.seqAdd hk e18 cc19 (by rfl)
    have cc17 := Spec.seqAdd hk e17 cc18 (by rfl)
    have cc16 := Spec.seqAdd hk e16 cc17 (by rfl)
    have ccz16 : Spec main SE W15.length (fun t => t = W15) (fun _ o => o = W59) (fun _ => 44 * CRT) := by
      refine Spec.mono hk cc16 (fun t _ h => h) (fun t o _ _ h => h) (fun t ht h => ?_)
      exact le_rfl

    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := ccz16 W15 rest rfl rfl vs hvs s R hR
    obtain ⟨o, ho, hw⟩ := hpost
    exact ⟨out, s', n, ⟨o, ho, ⟨P, L, hPc, hLc, hw⟩⟩, hev, hn, hstk, hfr⟩

  have hF : Spec main SF 9 (fun t => ∃ P L : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ t = w57 P L)
      (fun _ o => ∃ P L U V : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ (|(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn) ∧ (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ o = w58 P L U V)
      (fun _ => CRT) := by
    intro top rest ht hP
    rcases hP with ⟨P, L, hPc, hLc, rfl⟩
    have hPr : |(P : ℝ) - (2 : ℝ) ^ (epQ p) * Real.pi| ≤ 1 := by
      rw [← hQn_epQ]; simpa using hPc
    have hLr : |(L : ℝ) - (2 : ℝ) ^ (epQ p) * Real.log 2| ≤ 1 := by
      rw [← hQn_epQ]; simpa using hLc
    have hσR : (σ : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hσ
    obtain ⟨hZ1, hZ2, hZ3⟩ := ExpPosZDataOp p j k σ P L hp hk1 he hσR hPr hLr
    have h3 : (32 : ℝ) * (2 : ℝ) ^ (epQ p) = 32 * (2 : ℝ) ^ Qn := by
      rw [← hQn_epQ, zpow_natCast]
    rw [h3] at hZ1
    have hZb : |(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn := hZ1
    have hpre : ((epZw p σ j k P L : ℝ)) ^ 2 + (((0 : ℤ) : ℝ)) ^ 2 ≤ (32 * 2 ^ Qn) ^ 2 := by
      have h0 : ((((0 : ℤ) : ℝ))) ^ 2 = 0 := by norm_num
      rw [h0, add_zero, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hZb 2
    have key : Spec main SF 9 (fun t => t = w57 P L)
        (fun _ o => ∃ U V : ℤ, (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ o = w58 P L U V) (fun _ => CRT) := by
      refine Spec.mono hk (Spec.expWordStep (Kc := Kexp) (Q := Qn) (Z := epZw p σ j k P L) (Y := 0)
        (φ := fun U V : ℤ => ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn)
        (E := [.int (epSw p σ j k P L), .int (epXw j k P), .int L, .int Q, .int A, .int sa])
        (hexp main Qn (epZw p σ j k P L) 0 hQge hpre)
        (epCostPow (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (Kc := Kexp) (Q := Qn)
          hKN hKEE hCRT hKexpKE hKEKSm (by have := hQnN; omega))) ?_ ?_ ?_
      · intro t ht h
        rw [h]
        simp only [w57, List.singleton_append, List.cons_append, List.nil_append, hQeq]
      · intro t o ht h hQ
        rcases hQ with ⟨u, v, huv, ho⟩
        exact ⟨u, v, huv, by rw [ho]; simp only [w58, List.singleton_append, List.cons_append, List.nil_append]⟩
      · intro t ht h
        exact le_rfl
    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := key (w57 P L) rest rfl rfl vs hvs s R hR
    obtain ⟨o, ho, U, V, hUc, hw⟩ := hpost
    exact ⟨out, s', n, ⟨o, ho, ⟨P, L, U, V, hPc, hLc, hZb, hUc, hw⟩⟩, hev, hn, hstk, hfr⟩

  have hG : Spec main SG 8
      (fun t => ∃ P L U V : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ (|(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn) ∧ (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ t = w58 P L U V)
      (fun _ o => ∃ P L U V : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ (|(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn) ∧ (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ o = w78 P L U V)
      (fun _ => 20 * CRT) := by
    intro top rest ht hP
    rcases hP with ⟨P, L, U, V, hPc, hLc, hZb, hUc, rfl⟩
    have hsz_P : isz P ≤ 200 * N := by
      have h := isz_le_of_pi_approx (q := 2 * p + 60) hPc
      have h3 : 2 * p + 60 + 5 ≤ N := le_trans (by omega) hNP
      exact le_trans (le_trans h h3) hmul200
    have hsz_L : isz L ≤ 200 * N := by
      have h := isz_le_of_log_approx (q := 2 * p + 60) hLc
      have h3 : 2 * p + 60 + 5 ≤ N := le_trans (by omega) hNP
      exact le_trans (le_trans h h3) hmul200
    have hsz_jaP : isz (ja * P) ≤ 400 * N :=
      le_trans (isz_le_mul_of hsz_ja hsz_P) (coeff_add_le (by norm_num))
    have hsz_X : isz (epXw j k P) ≤ 400 * N := by
      change isz (Int.tdiv (ja * P) ka) ≤ 400 * N
      exact isz_le_tdiv_of hsz_jaP
    have hsz_saL : isz (sa * L) ≤ 400 * N :=
      le_trans (isz_le_mul_of hsz_sa hsz_L) (coeff_add_le (by norm_num))
    have hsz_Al : isz (epAlw σ j k P L) ≤ 800 * N := by
      change isz (sa * L - epXw j k P) ≤ 800 * N
      exact le_trans (isz_le_sub_of hsz_saL hsz_X) (coeff_add_le (by norm_num))
    have hsz_Lm1 : isz (L - 1) ≤ 400 * N :=
      le_trans (isz_le_sub_of hsz_L hsz_c1) (coeff_add_le (by norm_num))
    have hsz_Alt : isz (epAlw σ j k P L + (L - 1)) ≤ 1200 * N :=
      le_trans (isz_le_add_of hsz_Al hsz_Lm1) (coeff_add_le (by norm_num))
    have hsz_T : isz (epTw σ j k P L) ≤ 1200 * N := by
      change isz (Int.tdiv (epAlw σ j k P L + (L - 1)) L) ≤ 1200 * N
      exact isz_le_tdiv_of hsz_Alt
    have hsz_Tau : isz (epTauw σ j k P L) ≤ 1200 * N := by
      change isz (max 0 (epTw σ j k P L)) ≤ 1200 * N
      exact isz_le_max0_of hsz_T
    have hsz_K0 : isz (epK0w σ j k P L) ≤ 1400 * N := by
      change isz (sa - epTauw σ j k P L) ≤ 1400 * N
      exact le_trans (isz_le_sub_of hsz_sa hsz_Tau) (coeff_add_le (by norm_num))
    have hsz_Asa : isz (A + sa) ≤ 50 * N :=
      le_trans (isz_le_add_of hsz_A hsz_sa) (coeff_add_le (by norm_num))
    have hsz_S : isz (epSw p σ j k P L) ≤ 1600 * N := by
      change isz ((60 + (p : ℤ)) + (σ : ℤ) - epK0w σ j k P L) ≤ 1600 * N
      exact le_trans (isz_le_sub_of hsz_Asa hsz_K0) (coeff_add_le (by norm_num))
    have hsz_K0L : isz (epK0w σ j k P L * L) ≤ 1600 * N :=
      le_trans (isz_le_mul_of hsz_K0 hsz_L) (coeff_add_le (by norm_num))
    have hsz_XK0L : isz (epXw j k P - epK0w σ j k P L * L) ≤ 2000 * N :=
      le_trans (isz_le_sub_of hsz_X hsz_K0L) (coeff_add_le (by norm_num))
    have hsz_Z : isz (epZw p σ j k P L) ≤ 2200 * N := by
      change isz ((epXw j k P - epK0w σ j k P L * L) - 32 * (60 + (p : ℤ))) ≤ 2200 * N
      exact le_trans (isz_le_sub_of hsz_XK0L hsz_E) (coeff_add_le (by norm_num))
    have hUcn : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp ((epZw p σ j k P L : ℂ) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn := by
      simpa only [Int.cast_zero, zero_mul, add_zero] using hUc
    have hsz_U : isz U ≤ 300 * N := by
      have h := (isz_le_of_exp_approx (q := 2 * p + 60) hUcn hZb).1
      have h3 : 2 * p + 60 + 65 ≤ N := by rw [hNdef]; omega
      exact le_trans (le_trans h h3) hmul300
    have hsz_V : isz V ≤ 300 * N := by
      have h := (isz_le_of_exp_approx (q := 2 * p + 60) hUcn hZb).2
      have h3 : 2 * p + 60 + 65 ≤ N := by rw [hNdef]; omega
      exact le_trans (le_trans h h3) hmul300
    obtain ⟨hsz_w1, hsz_w2, hsz_cns⟩ := segG_sizes p σ j k P L U V hN1 hsz_U hsz_V
    have hSw0 : (0:ℤ) ≤ epSw p σ j k P L := by
      simp only [epSw, epK0w, epTauw]
      have h : (0:ℤ) ≤ max 0 (epTw σ j k P L) := le_max_left _ _
      omega

    let W60 : List Val := [.int (U), .int (V), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W61 : List Val := [.int (epSw p σ j k P L), .int (U), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W62 : List Val := [.int (epSw p σ j k P L), .int (epSw p σ j k P L), .int (U), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W63 : List Val := [.int (U), .int (epSw p σ j k P L), .int (epSw p σ j k P L), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W64 : List Val := [.int (epW1w p σ j k P L U), .int (epSw p σ j k P L), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W65 : List Val := [.int (V), .int (epW1w p σ j k P L U), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W66 : List Val := [.int (epSw p σ j k P L), .int (V), .int (epW1w p σ j k P L U), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W67 : List Val := [.int (V), .int (epSw p σ j k P L), .int (epW1w p σ j k P L U), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W68 : List Val := [.int (epW1w p σ j k P L V), .int (epW1w p σ j k P L U), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W69 : List Val := [.int (epW1w p σ j k P L U), .int (epW1w p σ j k P L V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W70 : List Val := [(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]
    let W71 : List Val := [.int (sa), (.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q), .int (A)]
    let W72 : List Val := [(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q), .int (A)]
    let W73 : List Val := [.int (A), (.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q)]
    let W74 : List Val := [(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q)]
    let W75 : List Val := [.int (Q), (.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L)]
    let W76 : List Val := [(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L)]
    let W77 : List Val := [.int (L), (.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P)]
    let W78 : List Val := [(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P)]
    let W79 : List Val := [.int (epXw j k P), (.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V)))]
    let W80 : List Val := [(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V)))]
    have hszl60 : szl W60 ≤ N * N := by
      have h : szl W60 ≤ 30000 * N := by
        change szl ([.int (U), .int (V), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl62 : szl W62 ≤ N * N := by
      have h : szl W62 ≤ 30000 * N := by
        change szl ([.int (epSw p σ j k P L), .int (epSw p σ j k P L), .int (U), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl64 : szl W64 ≤ N * N := by
      have h : szl W64 ≤ 30000 * N := by
        change szl ([.int (epW1w p σ j k P L U), .int (epSw p σ j k P L), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl65 : szl W65 ≤ N * N := by
      have h : szl W65 ≤ 30000 * N := by
        change szl ([.int (V), .int (epW1w p σ j k P L U), .int (epSw p σ j k P L), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl66 : szl W66 ≤ N * N := by
      have h : szl W66 ≤ 30000 * N := by
        change szl ([.int (epSw p σ j k P L), .int (V), .int (epW1w p σ j k P L U), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl68 : szl W68 ≤ N * N := by
      have h : szl W68 ≤ 30000 * N := by
        change szl ([.int (epW1w p σ j k P L V), .int (epW1w p σ j k P L U), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl70 : szl W70 ≤ N * N := by
      have h : szl W70 ≤ 30000 * N := by
        change szl ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl72 : szl W72 ≤ N * N := by
      have h : szl W72 ≤ 30000 * N := by
        change szl ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q), .int (A)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl74 : szl W74 ≤ N * N := by
      have h : szl W74 ≤ 30000 * N := by
        change szl ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl76 : szl W76 ≤ N * N := by
      have h : szl W76 ≤ 30000 * N := by
        change szl ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have hszl78 : szl W78 ≤ N * N := by
      have h : szl W78 ≤ 30000 * N := by
        change szl ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P)]) ≤ 30000 * N
        simp only [szl_cons, szl_nil, vsz_int]
        omega
      exact le_trans h (Nat.mul_le_mul_right N hN4)

    have e61 : Spec main (c61) W60.length (fun t => t = W60) (fun _ o => o = W61) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W60) (B := W61) (k := 2) (by rw [show W60.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W60)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl60)))

    have e62 : Spec main (c62) W61.length (fun t => t = W61) (fun _ o => o = W62) (fun _ => 1 * CRT) :=
      Spec.dupStep_x1 (hdup main) (.int (epSw p σ j k P L)) ([.int (U), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) (B := W62) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (epSw p σ j k P L)) + 1)
          (Kc := Kdu) hKN hKEE hCRT hKdu (by rw [vsz_int]; have := hsz_S; omega)))

    have e63 : Spec main (c63) W62.length (fun t => t = W62) (fun _ o => o = W63) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W62) (B := W63) (k := 2) (by rw [show W62.length = 9 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W62)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl62)))

    have e64 : Spec main (c64) W63.length (fun t => t = W63) (fun _ o => o = W64) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hshr main) hSw0 (E := [.int (epSw p σ j k P L), .int (V), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) (B := W64) (by simp only [W64, epW1w])
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (U)) (b := isz (epSw p σ j k P L))
          (Kc := Kshr) hKN hKEE hCRT hKshr (le_4000N_of hsz_U (by norm_num)) (le_4000N_of hsz_S (by norm_num))))

    have e65 : Spec main (c65) W64.length (fun t => t = W64) (fun _ o => o = W65) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W64) (B := W65) (k := 2) (by rw [show W64.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W64)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl64)))

    have e66 : Spec main (c66) W65.length (fun t => t = W65) (fun _ o => o = W66) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W65) (B := W66) (k := 2) (by rw [show W65.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W65)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl65)))

    have e67 : Spec main (c67) W66.length (fun t => t = W66) (fun _ o => o = W67) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W66) (B := W67) (k := 1) (by rw [show W66.length = 8 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W66)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl66)))

    have e68 : Spec main (c68) W67.length (fun t => t = W67) (fun _ o => o = W68) (fun _ => 1 * CRT) :=
      Spec.binOpStep hk (hshr main) hSw0 (E := [.int (epW1w p σ j k P L U), .int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) (B := W68) (by simp only [W68, epW1w])
        (le_one_mul (epCostLin (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := isz (V)) (b := isz (epSw p σ j k P L))
          (Kc := Kshr) hKN hKEE hCRT hKshr (le_4000N_of hsz_V (by norm_num)) (le_4000N_of hsz_S (by norm_num))))

    have e69 : Spec main (c69) W68.length (fun t => t = W68) (fun _ o => o = W69) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W68) (B := W69) (k := 1) (by rw [show W68.length = 7 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W68)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl68)))

    have e70 : Spec main (c70) W69.length (fun t => t = W69) (fun _ o => o = W70) (fun _ => 1 * CRT) :=
      Spec.consVStep (hcons main) (E := [.int (epXw j k P), .int (L), .int (Q), .int (A), .int (sa)]) (B := W70) (by rfl)
        (le_one_mul (le_trans hKcv hKSmCRT))

    have e71 : Spec main (c71) W70.length (fun t => t = W70) (fun _ o => o = W71) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W70) (B := W71) (k := 5) (by rw [show W70.length = 6 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 5 + 1) (b := szl W70)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl70)))

    have e72 : Spec main (c72) W71.length (fun t => t = W71) (fun _ o => o = W72) (fun _ => 1 * CRT) :=
      Spec.dropStep_x1 (hdrop main) (.int (sa)) ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q), .int (A)]) (B := W72) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (sa)) + 1)
          (Kc := Kdr) hKN hKEE hCRT hKdr (by rw [vsz_int]; have := hsz_sa; omega)))

    have e73 : Spec main (c73) W72.length (fun t => t = W72) (fun _ o => o = W73) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W72) (B := W73) (k := 4) (by rw [show W72.length = 5 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 4 + 1) (b := szl W72)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl72)))

    have e74 : Spec main (c74) W73.length (fun t => t = W73) (fun _ o => o = W74) (fun _ => 1 * CRT) :=
      Spec.dropStep_x1 (hdrop main) (.int (A)) ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L), .int (Q)]) (B := W74) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (A)) + 1)
          (Kc := Kdr) hKN hKEE hCRT hKdr (by rw [vsz_int]; have := hsz_A; omega)))

    have e75 : Spec main (c75) W74.length (fun t => t = W74) (fun _ o => o = W75) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W74) (B := W75) (k := 3) (by rw [show W74.length = 4 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 3 + 1) (b := szl W74)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl74)))

    have e76 : Spec main (c76) W75.length (fun t => t = W75) (fun _ o => o = W76) (fun _ => 1 * CRT) :=
      Spec.dropStep_x1 (hdrop main) (.int (Q)) ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P), .int (L)]) (B := W76) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (Q)) + 1)
          (Kc := Kdr) hKN hKEE hCRT hKdr (by rw [vsz_int]; have := hsz_Q; omega)))

    have e77 : Spec main (c77) W76.length (fun t => t = W76) (fun _ o => o = W77) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W76) (B := W77) (k := 2) (by rw [show W76.length = 3 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 2 + 1) (b := szl W76)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl76)))

    have e78 : Spec main (c78) W77.length (fun t => t = W77) (fun _ o => o = W78) (fun _ => 1 * CRT) :=
      Spec.dropStep_x1 (hdrop main) (.int (L)) ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))), .int (epXw j k P)]) (B := W78) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (L)) + 1)
          (Kc := Kdr) hKN hKEE hCRT hKdr (by rw [vsz_int]; have := hsz_L; omega)))

    have e79 : Spec main (c79) W78.length (fun t => t = W78) (fun _ o => o = W79) (fun _ => 1 * CRT) :=
      Spec.rollStep_x1 (K := Krl) (hroll main) (A := W78) (B := W79) (k := 1) (by rw [show W78.length = 2 from rfl]; omega) (by rfl)
        (le_one_mul (epCostPick (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := 1 + 1) (b := szl W78)
          (Kc := Krl) hKN hKEE hCRT hKrl (by omega) (by exact hszl78)))

    have e80 : Spec main (c80) W79.length (fun t => t = W79) (fun _ o => o = W80) (fun _ => 1 * CRT) :=
      Spec.dropStep_x1 (hdrop main) (.int (epXw j k P)) ([(.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V)))]) (B := W80) (by rfl)
        (le_one_mul (epCostSmall (N := N) (KSm := KSm) (KE := KE) (CRT := CRT) (a := vsz (.int (epXw j k P)) + 1)
          (Kc := Kdr) hKN hKEE hCRT hKdr (by rw [vsz_int]; have := hsz_X; omega)))

    have cc80 : Spec main (c80) W79.length (fun t => t = W79) (fun _ o => o = W80) (fun _ => 1 * CRT) :=
      e80
    have cc79 := Spec.seqAdd hk e79 cc80 (by rfl)
    have cc78 := Spec.seqAdd hk e78 cc79 (by rfl)
    have cc77 := Spec.seqAdd hk e77 cc78 (by rfl)
    have cc76 := Spec.seqAdd hk e76 cc77 (by rfl)
    have cc75 := Spec.seqAdd hk e75 cc76 (by rfl)
    have cc74 := Spec.seqAdd hk e74 cc75 (by rfl)
    have cc73 := Spec.seqAdd hk e73 cc74 (by rfl)
    have cc72 := Spec.seqAdd hk e72 cc73 (by rfl)
    have cc71 := Spec.seqAdd hk e71 cc72 (by rfl)
    have cc70 := Spec.seqAdd hk e70 cc71 (by rfl)
    have cc69 := Spec.seqAdd hk e69 cc70 (by rfl)
    have cc68 := Spec.seqAdd hk e68 cc69 (by rfl)
    have cc67 := Spec.seqAdd hk e67 cc68 (by rfl)
    have cc66 := Spec.seqAdd hk e66 cc67 (by rfl)
    have cc65 := Spec.seqAdd hk e65 cc66 (by rfl)
    have cc64 := Spec.seqAdd hk e64 cc65 (by rfl)
    have cc63 := Spec.seqAdd hk e63 cc64 (by rfl)
    have cc62 := Spec.seqAdd hk e62 cc63 (by rfl)
    have cc61 := Spec.seqAdd hk e61 cc62 (by rfl)
    have ccz61 : Spec main SG W60.length (fun t => t = W60) (fun _ o => o = W80) (fun _ => 20 * CRT) := by
      refine Spec.mono hk cc61 (fun t _ h => h) (fun t o _ _ h => h) (fun t ht h => ?_)
      exact le_rfl

    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := ccz61 W60 rest rfl rfl vs hvs s R hR
    obtain ⟨o, ho, hw⟩ := hpost
    exact ⟨out, s', n, ⟨o, ho, ⟨P, L, U, V, hPc, hLc, hZb, hUc, hw⟩⟩, hev, hn, hstk, hfr⟩

  have hAB : Spec main (SA.seq SB) 4 (fun t => t = W0)
      (fun _ o => ∃ P : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ o = w13 P) (fun _ => 13 * CRT) := by
    have h := Spec.seq hk hA hB
      (by intro t o ht hp hq; rw [hq]; rfl)
      (by intro t o ht hp hq; exact hq)
      (by intro t o ht hp hq; exact le_rfl)
    refine Spec.mono hk h (fun t _ h => h) ?_ ?_
    · intro t o ht hp hq
      rcases hq with ⟨o1, ho1, P, hPc, ho2⟩
      exact ⟨P, hPc, ho2⟩
    · intro t ht h
      show 12 * CRT + CRT ≤ 13 * CRT
      omega

  have hABC : Spec main ((SA.seq SB).seq SC) 4 (fun t => t = W0)
      (fun _ o => ∃ P : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ o = w14 P) (fun _ => 14 * CRT) := by
    have h := Spec.seq hk hAB hC
      (by intro t o ht hp hq; rcases hq with ⟨P, hPc, ho⟩; rw [ho]; rfl)
      (by intro t o ht hp hq; exact hq)
      (by intro t o ht hp hq; exact le_rfl)
    refine Spec.mono hk h (fun t _ h => h) ?_ ?_
    · intro t o ht hp hq
      rcases hq with ⟨o1, ho1, P, hPc, ho2⟩
      exact ⟨P, hPc, ho2⟩
    · intro t ht h
      show 13 * CRT + CRT ≤ 14 * CRT
      omega

  have hABCD : Spec main (((SA.seq SB).seq SC).seq SD) 4 (fun t => t = W0)
      (fun _ o => ∃ P L : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ o = w15 P L) (fun _ => 15 * CRT) := by
    have h := Spec.seq hk hABC hD
      (by intro t o ht hp hq; rcases hq with ⟨P, hPc, ho⟩; rw [ho]; rfl)
      (by intro t o ht hp hq; exact hq)
      (by intro t o ht hp hq; exact le_rfl)
    refine Spec.mono hk h (fun t _ h => h) ?_ ?_
    · intro t o ht hp hq
      rcases hq with ⟨o1, ho1, P, L, hPc, hLc, ho2⟩
      exact ⟨P, L, hPc, hLc, ho2⟩
    · intro t ht h
      show 14 * CRT + CRT ≤ 15 * CRT
      omega

  have hABCDE : Spec main ((((SA.seq SB).seq SC).seq SD).seq SE) 4 (fun t => t = W0)
      (fun _ o => ∃ P L : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ o = w57 P L) (fun _ => 59 * CRT) := by
    have h := Spec.seq hk hABCD hE
      (by intro t o ht hp hq; rcases hq with ⟨P, L, hPc, hLc, ho⟩; rw [ho]; rfl)
      (by intro t o ht hp hq; exact hq)
      (by intro t o ht hp hq; exact le_rfl)
    refine Spec.mono hk h (fun t _ h => h) ?_ ?_
    · intro t o ht hp hq
      rcases hq with ⟨o1, ho1, P, L, hPc, hLc, ho2⟩
      exact ⟨P, L, hPc, hLc, ho2⟩
    · intro t ht h
      show 15 * CRT + 44 * CRT ≤ 59 * CRT
      omega

  have hABCDEF : Spec main (((((SA.seq SB).seq SC).seq SD).seq SE).seq SF) 4 (fun t => t = W0)
      (fun _ o => ∃ P L U V : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ (|(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn) ∧ (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ o = w58 P L U V) (fun _ => 60 * CRT) := by
    have h := Spec.seq hk hABCDE hF
      (by intro t o ht hp hq; rcases hq with ⟨P, L, hPc, hLc, ho⟩; rw [ho]; rfl)
      (by intro t o ht hp hq; exact hq)
      (by intro t o ht hp hq; exact le_rfl)
    refine Spec.mono hk h (fun t _ h => h) ?_ ?_
    · intro t o ht hp hq
      rcases hq with ⟨o1, ho1, P, L, U, V, hPc, hLc, hZ, hU, ho2⟩
      exact ⟨P, L, U, V, hPc, hLc, hZ, hU, ho2⟩
    · intro t ht h
      show 59 * CRT + CRT ≤ 60 * CRT
      omega

  have hfull : Spec main ((((((SA.seq SB).seq SC).seq SD).seq SE).seq SF).seq SG) 4 (fun t => t = W0)
      (fun _ o => ∃ P L U V : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ (|(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn) ∧ (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ o = w78 P L U V) (fun _ => 80 * CRT) := by
    have h := Spec.seq hk hABCDEF hG
      (by intro t o ht hp hq; rcases hq with ⟨P, L, U, V, hPc, hLc, hZ, hU, ho⟩; rw [ho];
          rfl)
      (by intro t o ht hp hq; exact hq)
      (by intro t o ht hp hq; exact le_rfl)
    refine Spec.mono hk h (fun t _ h => h) ?_ ?_
    · intro t o ht hp hq
      rcases hq with ⟨o1, ho1, P, L, U, V, hPc, hLc, hZ, hU, ho2⟩
      exact ⟨P, L, U, V, hPc, hLc, hZ, hU, ho2⟩
    · intro t ht h
      show 60 * CRT + 20 * CRT ≤ 80 * CRT
      omega

  have hw : WordR main PROG (fun vs => ∃ R : List Val, vs = W0 ++ R)
      (fun vs out => ∃ R o : List Val, vs = W0 ++ R ∧ out = o ++ R ∧
        ∃ P L U V : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ (|(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn) ∧ (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ o = w78 P L U V) (fun _ => 80 * CRT) := by
    intro vs hvs s R hR
    obtain ⟨R0, hR0⟩ := hvs
    have h := Spec.use hfull (top := W0) (rest := R0) rfl rfl
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h vs (by rw [hR0]) s R hR
    obtain ⟨o, ho, hQ⟩ := hpost
    exact ⟨out, s', n, ⟨R0, o, hR0, ho, hQ⟩, hev, hn, hstk, hfr⟩

  refine hk.conseq (main := main) (p := PROG)
    (P := fun vs => ∃ R : List Val, vs = W0 ++ R)
    (Q := fun vs out => ∃ R o : List Val, vs = W0 ++ R ∧ out = o ++ R ∧
      ∃ P L U V : ℤ, (|(P : ℝ) - (2 : ℝ) ^ Qn * Real.pi| ≤ 1) ∧ (|(L : ℝ) - (2 : ℝ) ^ Qn * Real.log 2| ≤ 1) ∧ (|(epZw p σ j k P L : ℝ)| ≤ 32 * (2 : ℝ) ^ Qn) ∧ (‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ Qn - Complex.exp (((epZw p σ j k P L : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ Qn)‖ ≤ 4 / (2 : ℝ) ^ Qn) ∧ o = w78 P L U V)
    (C := fun _ => 80 * CRT)
    (P' := fun vs => ∃ (rest : List Val),
      vs = .int pa :: .int ja :: .int ka :: .int sa :: rest)
    (Q' := fun vs out => ∃ (rest : List Val) (w : ℤ × ℤ),
      vs = .int pa :: .int ja :: .int ka :: .int sa :: rest ∧
      out = cfxVal w :: rest ∧ inDisc p w ∧
      (2 : ℝ) ^ p * ‖fxC p w - (((2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * j / k) : ℝ) : ℂ)‖ < 2)
    (C' := fun _ => (80 * KSm * 1000000000000 * 1002 ^ KE + KE + 1) *
      (p + isz ja + isz ka + isz sa) ^ (80 * KSm * 1000000000000 * 1002 ^ KE + KE + 1))
    hw ?_ ?_ ?_
  · intro vs hv
    obtain ⟨rest, rfl⟩ := hv
    exact ⟨rest, rfl⟩
  · intro vs out hvs hQ
    obtain ⟨rest0, hvs0⟩ := hvs
    rcases hQ with ⟨R, o, hvsR, hout, P, L, U, V, hPc, hLc, hZb, hUc, ho⟩
    subst ho
    have hR : R = rest0 := List.append_cancel_left (hvsR.symm.trans hvs0)
    have hPr : |(P : ℝ) - (2 : ℝ) ^ (epQ p) * Real.pi| ≤ 1 := by
      rw [← hQn_epQ]; simpa using hPc
    have hLr : |(L : ℝ) - (2 : ℝ) ^ (epQ p) * Real.log 2| ≤ 1 := by
      rw [← hQn_epQ]; simpa using hLc
    have hσR : (σ : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hσ
    obtain ⟨hZ1, h2', h3'⟩ := ExpPosZDataOp p j k σ P L hp hk1 he hσR hPr hLr
    have hsrel : epSw p σ j k P L = epA p + epTauw σ j k P L := by
      simp only [epSw, epK0w, epA]
      ring
    have hUc' : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (epQ p) -
        Complex.exp ((epZw p σ j k P L : ℂ) / (2 : ℂ) ^ (epQ p))‖ ≤ 4 / (2 : ℝ) ^ (epQ p) := by
      have h1 : (2 : ℂ) ^ (epQ p) = (2 : ℂ) ^ Qn := by rw [← hQn_epQ, zpow_natCast]
      have h2 : (2 : ℝ) ^ (epQ p) = (2 : ℝ) ^ Qn := by rw [← hQn_epQ, zpow_natCast]
      rw [h1, h2]
      simpa only [Int.cast_zero, zero_mul, add_zero] using hUc
    have hτ0 : 0 ≤ epTauw σ j k P L := by
      simp only [epTauw]; exact le_max_left _ _
    have hfin := ExpPosFinal p j k σ (epTauw σ j k P L) (epZw p σ j k P L)
      (epSw p σ j k P L) U V hp hτ0 hsrel h2' h3' hUc'
    refine ⟨rest0, (epW1w p σ j k P L U, epW1w p σ j k P L V), hvs0, ?_, hfin.1, hfin.2⟩
    rw [hout, hR]
    simp only [w78, cfxVal, List.singleton_append]
  · intro vs _
    refine epCostTotal (B := B0) (N := N) (KSm := KSm) (KE := KE) (T := 80)
      (K := 80 * KSm * 1000000000000 * 1002 ^ KE + KE + 1) ?_ ?_ ?_ rfl
    · simp only [B0]; omega
    · simp only [N, B0]; omega
    · simp only [KE]; omega

end Work.Fx
