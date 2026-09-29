import Submission.Work.Fx.FxAdapt

/-!
# The 16-step fixed-point program for `(f u v)/2`

A single chain of exact-window `Spec`s, parametrised by a binary operation `f` (used with
`f = (· + ·)` for `addHalf` and `f = (· - ·)` for `subHalf`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Fx

open HvdH

theorem isz_add_le' (a b : ℤ) : isz (a + b) ≤ isz a + isz b := by
  have h := isz_add_le a b
  have ha : 2 ≤ isz a := by simp [isz]
  have hb : 2 ≤ isz b := by simp [isz]
  omega

theorem isz_sub_le' (a b : ℤ) : isz (a - b) ≤ isz a + isz b := by
  have h := isz_sub_le a b
  have ha : 2 ≤ isz a := by simp [isz]
  have hb : 2 ≤ isz b := by simp [isz]
  omega

/-- `BinOp` on a window extended by a carried block, with a constant given by the extended window. -/
theorem Spec.binOpExt (hk : KernelLib) {main cOp : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main cOp P f C) {A0 B0 : ℤ} (hP : P A0 B0) {E : List Val} {k : ℕ}
    (hE : E.length = k) {KK : ℕ}
    (hC : ∀ t, t = [.int A0, .int B0] ++ E → C A0 B0 ≤ linCost KK t) :
    Spec main cOp (2 + k) (fun t => t = [.int A0, .int B0] ++ E)
      (fun _ o => o = [.int (f A0 B0)] ++ E) (linCost KK) := by
  have h1 : Spec main cOp 2 (fun t => t = [.int A0, .int B0])
      (fun _ o => o = [.int (f A0 B0)]) (binCost C) := by
    refine Spec.mono hk (Spec.binOp hk h) ?_ ?_ ?_
    · intro t ht hq
      rw [hq]
      exact ⟨A0, B0, rfl, hP⟩
    · intro t o ht hq hQ
      rcases hQ with ⟨a, b, hab, ho⟩
      have e1 : ([.int a, .int b] : List Val) = [.int A0, .int B0] := Eq.trans (Eq.symm hab) hq
      have e2 := List.cons.inj e1
      have e3 := List.cons.inj e2.2
      rw [ho, Val.int.inj e2.1, Val.int.inj e3.1]
    · intro t ht hq
      rw [hq]
  have h2 : Spec main cOp (2 + k) (fun t => t = [.int A0, .int B0] ++ E)
      (fun _ o => o = [.int (f A0 B0)] ++ E) (fun _ => binCost C [.int A0, .int B0]) :=
    Spec.extend_exact hk h1 hE
  exact Spec.mono hk h2 (fun t _ h => h) (fun t o _ _ h => h) (fun t _ hq => hC t hq)

/-- The chain: given a binary operation word `cOp`, compute `(f u.1 v.1, f u.2 v.2)` rounded half. -/
theorem halfChain (hk : KernelLib) (hi : IntLib) (cOp : Cmd) (KOp : ℕ)
    (f : ℤ → ℤ → ℤ)
    (hOp : ∀ main : Cmd, BinOp main cOp (fun _ _ => True) f (fun a b => KOp * (isz a + isz b)))
    (hf : ∀ a b : ℤ, isz (f a b) ≤ isz a + isz b)
    (hdisc : ∀ (p : ℕ) (u v : ℤ × ℤ), inDisc p u → inDisc p v →
      inDisc p ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2))
    (tv : ℕ → ℤ → ℤ → ℤ → ℤ → ℂ)
    (herr : ∀ (p : ℕ) (a b c d : ℤ), (2 : ℝ) ^ p *
      ‖fxC p ((f a c).tdiv 2, (f b d).tdiv 2) - tv p a b c d‖ < 1) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), WordR main prog
      (fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val),
        vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
      (fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
        vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧ inDisc p w ∧
        w = ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2) ∧
        (2 : ℝ) ^ p * ‖fxC p w - tv p u.1 u.2 v.1 v.2‖ < 1)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil))) := by
  obtain ⟨cU, KU, hU⟩ := hk.unconsV
  obtain ⟨cR, KR, hR⟩ := hk.roll
  obtain ⟨cP, KP, hPv⟩ := hk.pushVal
  obtain ⟨cS, KS, hS⟩ := hk.swap
  obtain ⟨cC, KC, hCv⟩ := hk.consV
  obtain ⟨cT, KT, hT⟩ := hi.tdiv
  -- per-step cost constants
  let s2 : ℕ := KR * (2 + 1)
  let s6 : ℕ := KP * (vsz (.int 2) + 1)
  let s9 : ℕ := KR * (1 + 1)
  let Kt : ℕ := 0
  let prog : Cmd := .seq cU (.seq (cR 2) (.seq cU (.seq (cR 2) (.seq cOp (.seq (cP (.int 2))
    (.seq cS (.seq cT (.seq (cR 1) (.seq (cR 2) (.seq cOp (.seq (cP (.int 2)) (.seq cS
    (.seq cT (.seq cS cC))))))))))))))
  let K16 : ℕ := KC
  let K15 : ℕ := 3 * KS + K16 * 10
  let K14 : ℕ := 4 * KT + K15 * 10
  let K13 : ℕ := 3 * KS + K14 * 10
  let K12 : ℕ := s6 + K13 * 10
  let K11 : ℕ := KOp + K12 * 10
  let K10 : ℕ := s2 + K11 * 10
  let K9 : ℕ := s9 + K10 * 10
  let K8 : ℕ := 4 * KT + K9 * 10
  let K7 : ℕ := 3 * KS + K8 * 10
  let K6 : ℕ := s6 + K7 * 10
  let K5 : ℕ := KOp + K6 * 10
  let K4 : ℕ := s2 + K5 * 10
  let K3 : ℕ := KU + K4 * 10
  let K2 : ℕ := s2 + K3 * 10
  let K1 : ℕ := KU + K2 * 10
  refine ⟨prog, 2 * K1, ?_⟩
  intro main p
  have hchain : ∀ (u v : ℤ × ℤ), Spec main prog 2 (fun t => t = [cfxVal u, cfxVal v])
      (fun _ o => o = [cfxVal ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2)]) (linCost K1) := by
    intro u v
    -- windows
    let T0 : List Val := [cfxVal u, cfxVal v]
    let T1 : List Val := [.int u.1, .int u.2, cfxVal v]
    let T2 : List Val := [cfxVal v, .int u.1, .int u.2]
    let T3 : List Val := [.int v.1, .int v.2, .int u.1, .int u.2]
    let T4 : List Val := [.int u.1, .int v.1, .int v.2, .int u.2]
    let T5 : List Val := [.int (f u.1 v.1), .int v.2, .int u.2]
    let T6 : List Val := [.int 2, .int (f u.1 v.1), .int v.2, .int u.2]
    let T7 : List Val := [.int (f u.1 v.1), .int 2, .int v.2, .int u.2]
    let T8 : List Val := [.int ((f u.1 v.1).tdiv 2), .int v.2, .int u.2]
    let T9 : List Val := [.int v.2, .int ((f u.1 v.1).tdiv 2), .int u.2]
    let T10 : List Val := [.int u.2, .int v.2, .int ((f u.1 v.1).tdiv 2)]
    let T11 : List Val := [.int (f u.2 v.2), .int ((f u.1 v.1).tdiv 2)]
    let T12 : List Val := [.int 2, .int (f u.2 v.2), .int ((f u.1 v.1).tdiv 2)]
    let T13 : List Val := [.int (f u.2 v.2), .int 2, .int ((f u.1 v.1).tdiv 2)]
    let T14 : List Val := [.int ((f u.2 v.2).tdiv 2), .int ((f u.1 v.1).tdiv 2)]
    let T15 : List Val := [.int ((f u.1 v.1).tdiv 2), .int ((f u.2 v.2).tdiv 2)]
    let T16 : List Val := [cfxVal ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2)]
    -- size bookkeeping
    have hsz : ∀ (i : ℕ), True := fun _ => trivial
    have e1 : Spec main cU 2 (fun t => t = T0) (fun _ o => o = T1) (linCost KU) :=
      Spec.extendLin hk (Spec.unconsVEx hk (hU main) (.int u.1) (.int u.2))
        (E := [cfxVal v]) (k := 1) (by simp)
    have hsz12 : szl T1 ≤ 9 * (szl T0 + 1) := by
      simp only [T0, T1, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, vsz_cfxVal]
      omega
    have e2 : Spec main (cR 2) 3 (fun t => t = T1) (fun _ o => o = T2) (linCost (KR * (2 + 1))) :=
      Spec.rollEx hk (k := 2) (hR main 2) (W := T1) (B := T2) (by simp [T1]) (by rfl)
    have hsz23 : szl T2 ≤ 9 * (szl T1 + 1) := by
      simp only [T1, T2, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, vsz_cfxVal]
      omega
    have e3 : Spec main cU 3 (fun t => t = T2) (fun _ o => o = T3) (linCost KU) :=
      Spec.extendLin hk (Spec.unconsVEx hk (hU main) (.int v.1) (.int v.2))
        (E := [.int u.1, .int u.2]) (k := 2) (by simp)
    have hsz34 : szl T3 ≤ 9 * (szl T2 + 1) := by
      simp only [T2, T3, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, vsz_cfxVal]
      omega
    have e4 : Spec main (cR 2) 4 (fun t => t = T3) (fun _ o => o = T4) (linCost (KR * (2 + 1))) :=
      Spec.extendLin hk (Spec.rollEx hk (k := 2) (hR main 2) (W := [.int v.1, .int v.2, .int u.1])
        (B := [.int u.1, .int v.1, .int v.2]) (by simp) (by rfl)) (E := [.int u.2]) (k := 1) (by simp)
    have hsz45 : szl T4 ≤ 9 * (szl T3 + 1) := by
      simp only [T3, T4, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, vsz_cfxVal]
      omega
    have e5 : Spec main cOp 4 (fun t => t = T4) (fun _ o => o = T5) (linCost KOp) :=
      Spec.binOpExt hk (hOp main) (A0 := u.1) (B0 := v.1) (hP := trivial) (E := [.int v.2, .int u.2])
        (k := 2) (by simp) (by
          intro t ht
          rw [ht, linCost_int_pair]
          exact Nat.mul_le_mul_left KOp (by omega))
    have hsz56 : szl T5 ≤ 9 * (szl T4 + 1) := by
      have h := hf u.1 v.1
      simp only [T4, T5, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, vsz_cfxVal] at h ⊢
      omega
    have e6 : Spec main (cP (.int 2)) 3 (fun t => t = T5) (fun _ o => o = T6)
        (linCost (KP * (vsz (.int 2) + 1))) :=
      Spec.extendLin hk (Spec.pushValEx' hk (hPv main (.int 2))) (n := 0) (E := T5) (k := 3) (by simp [T5])
    have hsz67 : szl T6 ≤ 9 * (szl T5 + 1) := by
      simp only [T5, T6, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, vsz_cfxVal,
        isz_two]
      omega
    have e7 : Spec main cS 4 (fun t => t = T6) (fun _ o => o = T7) (linCost (3 * KS)) :=
      Spec.extendLin hk (Spec.swapEx hk (hS main) (.int 2) (.int (f u.1 v.1)))
        (E := [.int v.2, .int u.2]) (k := 2) (by simp)
    have hsz78 : szl T7 ≤ 9 * (szl T6 + 1) := by
      simp only [T6, T7, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have e8 : Spec main cT 4 (fun t => t = T7) (fun _ o => o = T8) (linCost (4 * KT)) :=
      Spec.binOpExt hk (hT main) (A0 := f u.1 v.1) (B0 := 2) (hP := by norm_num)
        (E := [.int v.2, .int u.2]) (k := 2) (by simp) (by
          intro t ht
          have h1 : vsz (.int (f u.1 v.1)) ≤ szl t := by rw [ht]; exact le_szl (by simp)
          show KT * isz (f u.1 v.1) * isz (2 : ℤ) ≤ linCost (4 * KT) t
          rw [linCost, isz_two]
          have h3 : isz (f u.1 v.1) ≤ szl t + 1 := by
            have e1 : isz (f u.1 v.1) = vsz (.int (f u.1 v.1)) := (vsz_int _).symm
            omega
          nlinarith [h3])
    have hsz89 : szl T8 ≤ 9 * (szl T7 + 1) := by
      simp only [T7, T8, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, isz_two]
      have h := isz_tdiv_le (f u.1 v.1) 2
      omega
    have e9 : Spec main (cR 1) 3 (fun t => t = T8) (fun _ o => o = T9) (linCost (KR * (1 + 1))) :=
      Spec.extendLin hk (Spec.rollEx hk (k := 1) (hR main 1)
        (W := [.int ((f u.1 v.1).tdiv 2), .int v.2]) (B := [.int v.2, .int ((f u.1 v.1).tdiv 2)])
        (by simp) (by rfl)) (E := [.int u.2]) (k := 1) (by simp)
    have hsz910 : szl T9 ≤ 9 * (szl T8 + 1) := by
      simp only [T8, T9, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have e10 : Spec main (cR 2) 3 (fun t => t = T9) (fun _ o => o = T10) (linCost (KR * (2 + 1))) :=
      Spec.rollEx hk (k := 2) (hR main 2) (W := T9) (B := T10) (by simp [T9]) (by rfl)
    have hsz1011 : szl T10 ≤ 9 * (szl T9 + 1) := by
      simp only [T9, T10, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have e11 : Spec main cOp 3 (fun t => t = T10) (fun _ o => o = T11) (linCost KOp) :=
      Spec.binOpExt hk (hOp main) (A0 := u.2) (B0 := v.2) (hP := trivial)
        (E := [.int ((f u.1 v.1).tdiv 2)]) (k := 1) (by simp) (by
          intro t ht
          rw [ht, linCost_int_pair]
          exact Nat.mul_le_mul_left KOp (by omega))
    have hsz1112 : szl T11 ≤ 9 * (szl T10 + 1) := by
      have h := hf u.2 v.2
      simp only [T10, T11, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int] at h ⊢
      omega
    have e12 : Spec main (cP (.int 2)) 2 (fun t => t = T11) (fun _ o => o = T12)
        (linCost (KP * (vsz (.int 2) + 1))) :=
      Spec.extendLin hk (Spec.pushValEx' hk (hPv main (.int 2))) (n := 0) (E := T11) (k := 2) (by simp [T11])
    have hsz1213 : szl T12 ≤ 9 * (szl T11 + 1) := by
      simp only [T11, T12, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, isz_two]
      omega
    have e13 : Spec main cS 3 (fun t => t = T12) (fun _ o => o = T13) (linCost (3 * KS)) :=
      Spec.extendLin hk (Spec.swapEx hk (hS main) (.int 2) (.int (f u.2 v.2)))
        (E := [.int ((f u.1 v.1).tdiv 2)]) (k := 1) (by simp)
    have hsz1314 : szl T13 ≤ 9 * (szl T12 + 1) := by
      simp only [T12, T13, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have e14 : Spec main cT 3 (fun t => t = T13) (fun _ o => o = T14) (linCost (4 * KT)) :=
      Spec.binOpExt hk (hT main) (A0 := f u.2 v.2) (B0 := 2) (hP := by norm_num)
        (E := [.int ((f u.1 v.1).tdiv 2)]) (k := 1) (by simp) (by
          intro t ht
          have h1 : vsz (.int (f u.2 v.2)) ≤ szl t := by rw [ht]; exact le_szl (by simp)
          show KT * isz (f u.2 v.2) * isz (2 : ℤ) ≤ linCost (4 * KT) t
          rw [linCost, isz_two]
          have h3 : isz (f u.2 v.2) ≤ szl t + 1 := by
            have e1 : isz (f u.2 v.2) = vsz (.int (f u.2 v.2)) := (vsz_int _).symm
            omega
          nlinarith [h3])
    have hsz1415 : szl T14 ≤ 9 * (szl T13 + 1) := by
      simp only [T13, T14, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, isz_two]
      have h := isz_tdiv_le (f u.2 v.2) 2
      omega
    have e15 : Spec main cS 2 (fun t => t = T14) (fun _ o => o = T15) (linCost (3 * KS)) :=
      Spec.swapEx hk (hS main) (.int ((f u.2 v.2).tdiv 2)) (.int ((f u.1 v.1).tdiv 2))
    have hsz1516 : szl T15 ≤ 9 * (szl T14 + 1) := by
      simp only [T14, T15, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have e16 : Spec main cC 2 (fun t => t = T15) (fun _ o => o = T16) (linCost KC) :=
      Spec.consVEx hk (hCv main) (.int ((f u.1 v.1).tdiv 2)) (.int ((f u.2 v.2).tdiv 2))
    -- composition, from the end
    have c15 := Spec.seq_det_lin hk e15 e16 (by simp [T15]) hsz1516
    have c14 := Spec.seq_det_lin hk e14 c15 (by simp [T14]) hsz1415
    have c13 := Spec.seq_det_lin hk e13 c14 (by simp [T13]) hsz1314
    have c12 := Spec.seq_det_lin hk e12 c13 (by simp [T12]) hsz1213
    have c11 := Spec.seq_det_lin hk e11 c12 (by simp [T11]) hsz1112
    have c10 := Spec.seq_det_lin hk e10 c11 (by simp [T10]) hsz1011
    have c9 := Spec.seq_det_lin hk e9 c10 (by simp [T9]) hsz910
    have c8 := Spec.seq_det_lin hk e8 c9 (by simp [T8]) hsz89
    have c7 := Spec.seq_det_lin hk e7 c8 (by simp [T7]) hsz78
    have c6 := Spec.seq_det_lin hk e6 c7 (by simp [T6]) hsz67
    have c5 := Spec.seq_det_lin hk e5 c6 (by simp [T5]) hsz56
    have c4 := Spec.seq_det_lin hk e4 c5 (by simp [T4]) hsz45
    have c3 := Spec.seq_det_lin hk e3 c4 (by simp [T3]) hsz34
    have c2 := Spec.seq_det_lin hk e2 c3 (by simp [T2]) hsz23
    have c1 := Spec.seq_det_lin hk e1 c2 (by simp [T1]) hsz12
    exact Spec.mono hk c1 (fun t _ h => h) (fun t o _ _ h => h) (fun t _ _ => le_rfl)
  -- final assembly
  have W : WordR main prog
      (fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val), vs = cfxVal u :: cfxVal v :: rest)
      (fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (o : List Val),
        vs = cfxVal u :: cfxVal v :: rest ∧ out = o ++ rest ∧
          o = [cfxVal ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2)])
      (fun vs => linCost K1 [vs.getD 0 .nil, vs.getD 1 .nil]) := by
    intro vs hvs
    rcases hvs with ⟨u, v, rest, rfl⟩
    intro s R hR
    obtain ⟨out, s', n, ⟨o, hout, ho⟩, hEv, hCost, hStk, hOth⟩ :=
      (hchain u v) [cfxVal u, cfxVal v] rest (by simp) rfl
        (cfxVal u :: cfxVal v :: rest) rfl s R hR
    exact ⟨out, s', n, ⟨u, v, rest, o, rfl, hout, ho⟩, hEv, hCost, hStk, hOth⟩
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val), vs = cfxVal u :: cfxVal v :: rest)
    (P' := fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val), vs = cfxVal u :: cfxVal v :: rest ∧
      inDisc p u ∧ inDisc p v)
    (Q := fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (o : List Val),
      vs = cfxVal u :: cfxVal v :: rest ∧ out = o ++ rest ∧
        o = [cfxVal ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2)])
    (Q' := fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
      vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧ inDisc p w ∧
      w = ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2) ∧
      (2 : ℝ) ^ p * ‖fxC p w - tv p u.1 u.2 v.1 v.2‖ < 1)
    (C := fun vs => linCost K1 [vs.getD 0 .nil, vs.getD 1 .nil])
    (C' := fun vs => (2 * K1) * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil)))
    W ?_ ?_ ?_
  · intro vs hvs
    rcases hvs with ⟨u, v, rest, rfl, hu, hv⟩
    exact ⟨u, v, rest, rfl⟩
  · intro vs out hvs hQ
    rcases hvs with ⟨u, v, rest, hvs_eq, hu, hv⟩
    rcases hQ with ⟨u', v', rest', o, hvs_eq', hout, ho⟩
    have hE1 : cfxVal u' :: cfxVal v' :: rest' = cfxVal u :: cfxVal v :: rest :=
      hvs_eq'.symm.trans hvs_eq
    have h1 := List.cons.inj hE1
    have h2 := List.cons.inj h1.2
    have hc1 := Val.cons.inj h1.1
    have hc2 := Val.cons.inj h2.1
    have huu : u' = u := Prod.ext (Val.int.inj hc1.1) (Val.int.inj hc1.2)
    have hvv : v' = v := Prod.ext (Val.int.inj hc2.1) (Val.int.inj hc2.2)
    have hrest : rest' = rest := h2.2
    rw [huu, hvv] at ho
    rw [hrest] at hout
    refine ⟨u, v, rest, ((f u.1 v.1).tdiv 2, (f u.2 v.2).tdiv 2), hvs_eq, ?_,
      hdisc p u v hu hv, rfl, herr p u.1 u.2 v.1 v.2⟩
    rw [hout, ho]
    rfl
  · intro vs hvs
    rcases hvs with ⟨u, v, rest, rfl, hu, hv⟩
    show linCost K1 [cfxVal u, cfxVal v] ≤
      (2 * K1) * (vsz (cfxVal u) + vsz (cfxVal v))
    simp only [linCost, szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h : 1 ≤ vsz (cfxVal u) + vsz (cfxVal v) := by
      have := one_le_vsz (cfxVal u)
      omega
    nlinarith

end Work.Fx
