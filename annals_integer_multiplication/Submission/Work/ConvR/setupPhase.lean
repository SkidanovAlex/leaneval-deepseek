import Mathlib
import Submission.Work.ConvR.basic

/-!
# ConvR: the setup phase of the convolution pipeline

Paper Harvey–van der Hoeven, Proposition 3.4 / Lemma 2.5.  The convolution over
`ℝ = ℂ[y]/(y^r+1)` is assembled from words that all read their parameters `p`, `r`, `ts` from the
top of the value stack (and, for the second operand, `ws`).  The very first thing the pipeline has
to do is therefore to *replicate* the parameters, turning

`[p, r, ts, us, ws] ++ rest`

into

`[p, r, ts, us, p, r, ts, ws, p, r, ts, p, r, ts, p] ++ rest`

(the copies being consumed left to right by the `SynFFT`/pointwise/`scale` stages).

The word is a straight-line composition of 14 moves of `KernelLib.roll` / `KernelLib.pick`
(the intermediate windows are listed in the proof of `setupPhaseGen`); every value occurring at
any time is one of the five input values, so each move costs at most `200 · (size of the input
window)` and the whole word costs `14 · 200 · size`, i.e. `O(size)`.

The proof only uses the `pick`, `roll` and `conseq` fields of `KernelLib` (never `loop`), so it is
robust with respect to the repair of `Interfaces.lean` announced in
`Submission/Work/Kernel/kernelLib.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.ConvR

open HvdH

/-! ## Windows of the value stack -/

/-- `WSpec main p A B c`: on every value stack of the shape `A ++ rest`, the word `p` terminates
with the stack `B ++ rest`, at cost at most `c` (`WordR` already includes the frame condition,
i.e. all other stacks and the part of stack 0 below the window are restored). -/
def WSpec (main p : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val, WordR main p (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest)
    (fun _ => c)

theorem WSpec.mono {main p : Cmd} {A B : List Val} {c c' : ℕ} (h : WSpec main p A B c)
    (hcc : c ≤ c') : WSpec main p A B c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hQ, he, le_trans hn hcc, hstk, hoth⟩

/-- Sequential composition of two window words. -/
theorem WSpec.seq {main p q : Cmd} {A B D : List Val} {c c' : ℕ}
    (h1 : WSpec main p A B c) (h2 : WSpec main q B D c') :
    WSpec main (.seq p q) A D (c + c') := by
  intro rest vs hvs s R hR
  obtain ⟨out1, s1, n1, hq1, he1, hn1, hstk1, hoth1⟩ := h1 rest vs hvs s R hR
  subst hq1
  obtain ⟨out2, s2, n2, hq2, he2, hn2, hstk2, hoth2⟩ := h2 rest (B ++ rest) rfl s1 R hstk1
  exact ⟨out2, s2, n1 + n2, hq2, Eval.seq he1 he2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

/-- Consequence rule with implicit arguments (the form of `KernelLib.conseq` with `main` and the
programs supplied by unification). -/
theorem wordR_conseq (hK : KernelLib) {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ} (h : WordR main p P Q C)
    (hP : ∀ vs, P' vs → P vs) (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out)
    (hC : ∀ vs, P' vs → C vs ≤ C' vs) : WordR main p P' Q' C' :=
  hK.conseq main p P P' Q Q' C C' h hP hQ hC

/-! ## List bookkeeping for windows -/

/-- `getD` at a position inside the window is not affected by what lies below it. -/
theorem setup_getD_append_of_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).getD k .nil = l.getD k .nil := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ j =>
      rw [List.getD_cons_succ, List.cons_append, List.getD_cons_succ, ih]
      simpa using h

/-- `eraseIdx` at a position inside the window commutes with appending below it. -/
theorem setup_eraseIdx_append_of_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).eraseIdx k = l.eraseIdx k ++ rest := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ j =>
      rw [List.cons_append, List.eraseIdx_cons_succ, ih (by simpa using h),
        List.eraseIdx_cons_succ, List.cons_append]

theorem setup_getD_eraseIdx_append {l rest : List Val} {k : ℕ} (h : k < l.length) :
    ((l ++ rest).getD k .nil) :: ((l ++ rest).eraseIdx k) =
      (l.getD k .nil :: l.eraseIdx k) ++ rest := by
  rw [setup_getD_append_of_lt h, setup_eraseIdx_append_of_lt h]
  rfl

/-! ## Sizes of windows -/

theorem sum_take_le_nat (l : List ℕ) (m : ℕ) : (l.take m).sum ≤ l.sum := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [List.take_succ_cons, List.sum_cons, List.sum_cons]
      exact Nat.add_le_add_left (ih m) a

private theorem szl_take_le (L : List Val) (m : ℕ) : ((L.take m).map vsz).sum ≤ (L.map vsz).sum := by
  rw [List.map_take]
  exact sum_take_le_nat _ m

/-! ## One move -/

/-- A single `pick k`: it copies the `k`-th value of the window to the front. -/
theorem wspec_pick (hK : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {KP : ℕ}
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => KP * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k c : ℕ} (hk : k < L.length) (hL' : L.getD k .nil :: L = L')
    (hc : KP * (k + 1) * ((L.map vsz).sum + 1) ≤ c) : WSpec main (pickP k) L L' c := by
  intro rest
  refine wordR_conseq hK (hpick main k) ?_ ?_ ?_
  · intro vs hvs
    rw [hvs, List.length_append]; omega
  · intro vs out hvs hQ
    rw [hvs] at hQ
    rw [hQ, setup_getD_append_of_lt hk, ← List.cons_append, hL']
  · intro vs hvs
    rw [hvs, List.take_append_of_le_length (by omega : k + 1 ≤ L.length)]
    exact le_trans (Nat.mul_le_mul_left (KP * (k + 1))
      (Nat.add_le_add_right (szl_take_le L (k + 1)) 1)) hc

/-- A single `roll k`: it moves the `k`-th value of the window to the front. -/
theorem wspec_roll (hK : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {KR : ℕ}
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k c : ℕ} (hk : k < L.length)
    (hL' : L.getD k .nil :: L.eraseIdx k = L')
    (hc : KR * (k + 1) * ((L.map vsz).sum + 1) ≤ c) : WSpec main (rollP k) L L' c := by
  intro rest
  refine wordR_conseq hK (hroll main k) ?_ ?_ ?_
  · intro vs hvs
    rw [hvs, List.length_append]; omega
  · intro vs out hvs hQ
    rw [hvs] at hQ
    rw [hQ, setup_getD_eraseIdx_append hk, hL']
  · intro vs hvs
    rw [hvs, List.take_append_of_le_length (by omega : k + 1 ≤ L.length)]
    exact le_trans (Nat.mul_le_mul_left (KR * (k + 1))
      (Nat.add_le_add_right (szl_take_le L (k + 1)) 1)) hc

/-- Uniform cost bound for one move: a window of size at most `15 M` and a move index at most `11`
cost at most `200 (M+1)`. -/
theorem move_bound {k M : ℕ} {L : List Val} (hk : k + 1 ≤ 12)
    (hL : (L.map vsz).sum ≤ 15 * M) : (k + 1) * ((L.map vsz).sum + 1) ≤ 200 * (M + 1) := by
  calc (k + 1) * ((L.map vsz).sum + 1) ≤ 12 * ((L.map vsz).sum + 1) :=
        Nat.mul_le_mul_right _ hk
    _ ≤ 12 * (15 * M + 1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hL 1)
    _ ≤ 200 * (M + 1) := by omega

/-- A `pick` move, with the uniform cost bound `D * 200 * (M+1)`. -/
theorem step_pick (hK : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {KP D M : ℕ}
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => KP * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k : ℕ} (hk : k < L.length) (hL' : L.getD k .nil :: L = L')
    (hKP : KP ≤ D) (hsz : (L.map vsz).sum ≤ 15 * M) (hk12 : k + 1 ≤ 12) :
    WSpec main (pickP k) L L' (D * 200 * (M + 1)) := by
  refine wspec_pick hK hpick hk hL' ?_
  calc KP * (k + 1) * ((L.map vsz).sum + 1)
      = KP * ((k + 1) * ((L.map vsz).sum + 1)) := by ring
    _ ≤ D * ((k + 1) * ((L.map vsz).sum + 1)) := Nat.mul_le_mul_right _ hKP
    _ ≤ D * (200 * (M + 1)) := Nat.mul_le_mul_left _ (move_bound hk12 hsz)
    _ = D * 200 * (M + 1) := by ring

/-- A `roll` move, with the uniform cost bound `D * 200 * (M+1)`. -/
theorem step_roll (hK : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {KR D M : ℕ}
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k : ℕ} (hk : k < L.length)
    (hL' : L.getD k .nil :: L.eraseIdx k = L')
    (hKR : KR ≤ D) (hsz : (L.map vsz).sum ≤ 15 * M) (hk12 : k + 1 ≤ 12) :
    WSpec main (rollP k) L L' (D * 200 * (M + 1)) := by
  refine wspec_roll hK hroll hk hL' ?_
  calc KR * (k + 1) * ((L.map vsz).sum + 1)
      = KR * ((k + 1) * ((L.map vsz).sum + 1)) := by ring
    _ ≤ D * ((k + 1) * ((L.map vsz).sum + 1)) := Nat.mul_le_mul_right _ hKR
    _ ≤ D * (200 * (M + 1)) := Nat.mul_le_mul_left _ (move_bound hk12 hsz)
    _ = D * 200 * (M + 1) := by ring

/-! ## The setup word -/

/-- The program: `roll 2, roll 2, pick 2 ×4, roll 8, pick 3 ×3, roll 11, pick 3 ×3`. -/
def setupProg (pickP rollP : ℕ → Cmd) : Cmd :=
  .seq (rollP 2)
    (.seq (rollP 2)
      (.seq (pickP 2)
        (.seq (pickP 2)
          (.seq (pickP 2)
            (.seq (pickP 2)
              (.seq (rollP 8)
                (.seq (pickP 3)
                  (.seq (pickP 3)
                    (.seq (pickP 3)
                      (.seq (rollP 11)
                        (.seq (pickP 3)
                          (.seq (pickP 3)
                            (pickP 3)))))))))))))

/-- The window transformation performed by `setupProg`, for arbitrary values `A, …, W`. -/
theorem setupPhaseGen (hK : KernelLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (A B C U W : Val) (rest : List Val),
      WordR main prog
        (fun vs => vs = [A, B, C, U, W] ++ rest)
        (fun _ out => out = [A, B, C, U, A, B, C, W, A, B, C, A, B, C, A] ++ rest)
        (fun _ => K * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) := by
  obtain ⟨pickP, KP, hpick⟩ := hK.pick
  obtain ⟨rollP, KR, hroll⟩ := hK.roll
  refine ⟨setupProg pickP rollP, 14 * ((2 * (KP + KR) + 1) * 200), ?_⟩
  intro main A B C U W rest
  -- the 14 moves, each at cost `(2*(KP+KR)+1) * 200 * (M+1)`, `M` the size of the input window
  have s1 : WSpec main (rollP 2) [A, B, C, U, W] [C, A, B, U, W]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_roll hK hroll (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s2 : WSpec main (rollP 2) [C, A, B, U, W] [B, C, A, U, W]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_roll hK hroll (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s3 : WSpec main (pickP 2) [B, C, A, U, W] [A, B, C, A, U, W]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s4 : WSpec main (pickP 2) [A, B, C, A, U, W] [C, A, B, C, A, U, W]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s5 : WSpec main (pickP 2) [C, A, B, C, A, U, W] [B, C, A, B, C, A, U, W]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s6 : WSpec main (pickP 2) [B, C, A, B, C, A, U, W] [A, B, C, A, B, C, A, U, W]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s7 : WSpec main (rollP 8) [A, B, C, A, B, C, A, U, W] [W, A, B, C, A, B, C, A, U]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_roll hK hroll (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s8 : WSpec main (pickP 3) [W, A, B, C, A, B, C, A, U] [C, W, A, B, C, A, B, C, A, U]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s9 : WSpec main (pickP 3) [C, W, A, B, C, A, B, C, A, U]
      [B, C, W, A, B, C, A, B, C, A, U]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s10 : WSpec main (pickP 3) [B, C, W, A, B, C, A, B, C, A, U]
      [A, B, C, W, A, B, C, A, B, C, A, U]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s11 : WSpec main (rollP 11) [A, B, C, W, A, B, C, A, B, C, A, U]
      [U, A, B, C, W, A, B, C, A, B, C, A]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_roll hK hroll (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s12 : WSpec main (pickP 3) [U, A, B, C, W, A, B, C, A, B, C, A]
      [C, U, A, B, C, W, A, B, C, A, B, C, A]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s13 : WSpec main (pickP 3) [C, U, A, B, C, W, A, B, C, A, B, C, A]
      [B, C, U, A, B, C, W, A, B, C, A, B, C, A]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have s14 : WSpec main (pickP 3) [B, C, U, A, B, C, W, A, B, C, A, B, C, A]
      [A, B, C, U, A, B, C, W, A, B, C, A, B, C, A]
      ((2 * (KP + KR) + 1) * 200 * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    step_pick hK hpick (by simp) rfl (by omega) (by simp; omega) (by omega)
  have chain : WSpec main (setupProg pickP rollP) [A, B, C, U, W]
      [A, B, C, U, A, B, C, W, A, B, C, A, B, C, A]
      (14 * ((2 * (KP + KR) + 1) * 200) * (vsz A + vsz B + vsz C + vsz U + vsz W + 1)) :=
    WSpec.mono
      (WSpec.seq s1 (WSpec.seq s2 (WSpec.seq s3 (WSpec.seq s4 (WSpec.seq s5 (WSpec.seq s6
        (WSpec.seq s7 (WSpec.seq s8 (WSpec.seq s9 (WSpec.seq s10 (WSpec.seq s11 (WSpec.seq s12
          (WSpec.seq s13 s14)))))))))))))
      (le_of_eq (by ring))
  exact chain rest

/-- **The setup phase of the convolution pipeline** (paper Proposition 3.4, first step): from the
stack `[p, r, ts, us, ws] ++ rest` produce
`[p, r, ts, us, p, r, ts, ws, p, r, ts, p, r, ts, p] ++ rest`, at linear cost. -/
theorem setupPhase (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p r : ℕ) (ts : List ℕ)
      (us ws : List (List (ℤ × ℤ))) (rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.intList ts,
          HvdH.rarrVal us, HvdH.rarrVal ws] ++ rest)
        (fun _ out => out = [HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.intList ts,
            HvdH.rarrVal us,
            HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.intList ts,
            HvdH.rarrVal ws,
            HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.intList ts,
            HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.intList ts,
            HvdH.Val.int (p : ℤ)] ++ rest)
        (fun vs => K * (HvdH.vsz (HvdH.rarrVal ws) + HvdH.vsz (HvdH.rarrVal us) +
          HvdH.vsz (HvdH.intList ts) + HvdH.isz (r : ℤ) + p + 2)) := by
  obtain ⟨prog, K, h⟩ := setupPhaseGen hK
  refine ⟨prog, 2 * K, ?_⟩
  intro main p r ts us ws rest
  refine wordR_conseq hK
    (h main (Val.int (p : ℤ)) (Val.int (r : ℤ)) (intList ts) (rarrVal us) (rarrVal ws) rest)
    ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hq; exact hq
  · intro vs hvs
    have hiszp : isz (p : ℤ) ≤ p + 2 := by
      have h : p.size ≤ p := by rw [Nat.size_le]; exact Nat.lt_two_pow_self
      simp only [isz, Int.natAbs_natCast]
      omega
    simp only [Work.ConvR.vsz_int]
    calc K * (isz (p : ℤ) + isz (r : ℤ) + vsz (intList ts) + vsz (rarrVal us) + vsz (rarrVal ws)
          + 1)
        ≤ K * (2 * (vsz (rarrVal ws) + vsz (rarrVal us) + vsz (intList ts) + isz (r : ℤ)
            + (p + 2))) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * K * (vsz (rarrVal ws) + vsz (rarrVal us) + vsz (intList ts) + isz (r : ℤ)
            + p + 2) := by ring

end Work.ConvR
