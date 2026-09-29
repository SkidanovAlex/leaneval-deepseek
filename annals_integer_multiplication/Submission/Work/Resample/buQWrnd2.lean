import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWhs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.buQWstepKit
import Submission.Work.Resample.buQWrounds
import Submission.Work.Resample.buQWstep

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buQWrnd2`: the Neumann fold of the one-dimensional `B̃` word

`buQWrnd2` is the `Work.Resample.buQWrounds` statement: a program folding one Neumann round over
the sign list `buSignsT p α s t`, starting from the pair `(v, v)` and outputting the second
component `buJsumL ... v` of the folded state.

The round word required by `buQWrounds_of` must *keep* the static values `buColsT p α s t`,
`int s`, `int p` on the stack (every round reads them again), while the round word `buQWstep`
consumes them.  `buR2DupProg` duplicates the last three entries of the six-value round window:
three `pick`s of the value at index 5 bring the last three entries `C, s, p` to the front, and six
`roll`s at index 8 rotate the resulting nine-value window back into place, so that
`[σ, v, acc, C, s, p]` becomes `[σ, v, acc, C, s, p, C, s, p]`.  Running `buQWstep` on that
extended window consumes the first copy of `C, s, p` and leaves the second one below the outputs,
which is exactly the input shape of the next round.
-/

/-! ## 1.  the duplication word -/

/-- three `pick`s of index 5 -/
abbrev buR2Pick3 (pickP : ℕ → Cmd) : Cmd := .seq (.seq (pickP 5) (pickP 5)) (pickP 5)

/-- six `roll`s of index 8 -/
abbrev buR2Roll6 (rollP : ℕ → Cmd) : Cmd :=
  .seq (.seq (.seq (.seq (.seq (rollP 8) (rollP 8)) (rollP 8)) (rollP 8)) (rollP 8)) (rollP 8)

/-- the duplication word of the round window -/
abbrev buR2DupProg (pickP : ℕ → Cmd) (rollP : ℕ → Cmd) : Cmd :=
  .seq (buR2Pick3 pickP) (buR2Roll6 rollP)

/-- the six-value round window `[σ, v, acc, C, s, p]` -/
noncomputable abbrev buR2W0 (σ : ℤ) (v acc : List (ℤ × ℤ)) (p α s t : ℕ) : List Val :=
  [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]

/-- the duplicated window `[σ, v, acc, C, s, p, C, s, p]` -/
noncomputable abbrev buR2W9 (σ : ℤ) (v acc : List (ℤ × ℤ)) (p α s t : ℕ) : List Val :=
  [Val.int σ, cvecVal v, cvecVal acc, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ),
    buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]

/-- cost of a window operation on a window of `9` values of size `≤ SB` -/
theorem buR2_op_le {K KS SB : ℕ} (hK : K ≤ KS) (hSB : 1 ≤ SB) {k Z : ℕ} (hk : k + 1 ≤ 9)
    (hZ : Z ≤ 9 * SB + 1) : K * (k + 1) * Z ≤ KS * 100 * SB := by
  have h1 : K * (k + 1) * Z ≤ KS * 9 * (9 * SB + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK hk) hZ
  have h2 : 9 * (9 * SB + 1) ≤ 100 * SB := by omega
  have h3 : KS * (9 * (9 * SB + 1)) ≤ KS * (100 * SB) := Nat.mul_le_mul_left KS h2
  have h4 : KS * 9 * (9 * SB + 1) = KS * (9 * (9 * SB + 1)) := by ring
  have h5 : KS * (100 * SB) = KS * 100 * SB := by ring
  linarith [h1, h3]

/-- a bound of the shape `30 * S * P` implies the window bound at `G ≥ 1` -/
theorem buR2_small_le {a G S P : ℕ} (ha : a ≤ 30 * (S * P)) (hG : 1 ≤ G) :
    a ≤ 1000 * (G * S * P) := by
  have h1 : 30 * (S * P) ≤ 1000 * (S * P) := Nat.mul_le_mul_right (S * P) (by norm_num)
  have h2 : 1000 * (S * P) ≤ 1000 * (G * S * P) := by
    apply Nat.mul_le_mul_left 1000
    calc S * P = 1 * (S * P) := by ring
      _ ≤ G * (S * P) := Nat.mul_le_mul_right (S * P) hG
      _ = G * S * P := by ring
  linarith

/-- `List.getD` of a list of values is either an entry of the list or the default `nil` -/
theorem buR2_getD_mem_or : ∀ (l : List Val) (k : ℕ),
    l.getD k .nil ∈ l ∨ l.getD k .nil = .nil := by
  intro l
  induction l with
  | nil => intro k; right; rfl
  | cons a t ih =>
    intro k
    cases k with
    | zero => left; exact List.mem_cons_self ..
    | succ j =>
      rw [List.getD_cons_succ]
      rcases ih j with h | h
      · exact Or.inl (List.mem_cons_of_mem a h)
      · exact Or.inr h

/-- the size of `Val.nil` -/
theorem buR2_vsz_nil : vsz (Val.nil : Val) = 1 := rfl

/-- the `k`-th entry of a window of values of size `≤ SB` has size `≤ SB` -/
theorem buR2_getD_vsz_le {l : List Val} {SB : ℕ} (hSB : 1 ≤ SB) (h : ∀ x ∈ l, vsz x ≤ SB) (k : ℕ) :
    vsz (l.getD k .nil) ≤ SB := by
  rcases buR2_getD_mem_or l k with hmem | hnil
  · exact h _ hmem
  · rw [hnil, buR2_vsz_nil]; exact hSB

/-- a sublist (`eraseIdx`) inherits the size bound -/
theorem buR2_eraseIdx_vsz_le {l : List Val} {SB : ℕ} (h : ∀ x ∈ l, vsz x ≤ SB) (k : ℕ) :
    ∀ x ∈ l.eraseIdx k, vsz x ≤ SB := by
  intro x hx
  exact h x (List.Sublist.subset (List.eraseIdx_sublist l k) hx)

/-- **The duplication word.**  On the six-value window `[σ, v, acc, C, s, p]` it produces
`[σ, v, acc, C, s, p, C, s, p]` at a constant-per-step cost, provided all window entries have size
`≤ SB`. -/
theorem buR2DupPipe {pickP : ℕ → Cmd} {rollP : ℕ → Cmd} {KP KR KS SB : ℕ}
    (hpick : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => KP * (k + 1) * (Work.Fx.szl (vs.take (k + 1)) + 1)))
    (hroll : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (Work.Fx.szl (vs.take (k + 1)) + 1)))
    (hKP : KP ≤ KS) (hKR : KR ≤ KS) (hSB : 1 ≤ SB)
    (σ : ℤ) (v acc : List (ℤ × ℤ)) (p α s t : ℕ) {main : Cmd}
    (hN : ∀ x ∈ buR2W0 σ v acc p α s t, vsz x ≤ SB) :
    Pipe main (buR2DupProg pickP rollP) (buR2W0 σ v acc p α s t) (buR2W9 σ v acc p α s t)
      (9 * (KS * 100 * SB)) := by
  let W0 : List Val := buR2W0 σ v acc p α s t
  let W1 : List Val := W0.getD 5 .nil :: W0
  let W2 : List Val := W1.getD 5 .nil :: W1
  let W3 : List Val := W2.getD 5 .nil :: W2
  let W4 : List Val := W3.getD 8 .nil :: W3.eraseIdx 8
  let W5 : List Val := W4.getD 8 .nil :: W4.eraseIdx 8
  let W6 : List Val := W5.getD 8 .nil :: W5.eraseIdx 8
  let W7 : List Val := W6.getD 8 .nil :: W6.eraseIdx 8
  let W8 : List Val := W7.getD 8 .nil :: W7.eraseIdx 8
  let W9 : List Val := W8.getD 8 .nil :: W8.eraseIdx 8
  let cb : ℕ := KS * 100 * SB
  have hS0 : ∀ x ∈ W0, vsz x ≤ SB := hN
  have hS1 : ∀ x ∈ W1, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W0.getD 5 .nil ∨ x ∈ W0 := by simpa only [W1, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS0 5
    · exact hS0 x h
  have hS2 : ∀ x ∈ W2, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W1.getD 5 .nil ∨ x ∈ W1 := by simpa only [W2, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS1 5
    · exact hS1 x h
  have hS3 : ∀ x ∈ W3, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W2.getD 5 .nil ∨ x ∈ W2 := by simpa only [W3, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS2 5
    · exact hS2 x h
  have hS4 : ∀ x ∈ W4, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W3.getD 8 .nil ∨ x ∈ W3.eraseIdx 8 := by simpa only [W4, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS3 8
    · exact buR2_eraseIdx_vsz_le hS3 8 x h
  have hS5 : ∀ x ∈ W5, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W4.getD 8 .nil ∨ x ∈ W4.eraseIdx 8 := by simpa only [W5, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS4 8
    · exact buR2_eraseIdx_vsz_le hS4 8 x h
  have hS6 : ∀ x ∈ W6, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W5.getD 8 .nil ∨ x ∈ W5.eraseIdx 8 := by simpa only [W6, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS5 8
    · exact buR2_eraseIdx_vsz_le hS5 8 x h
  have hS7 : ∀ x ∈ W7, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W6.getD 8 .nil ∨ x ∈ W6.eraseIdx 8 := by simpa only [W7, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS6 8
    · exact buR2_eraseIdx_vsz_le hS6 8 x h
  have hS8 : ∀ x ∈ W8, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W7.getD 8 .nil ∨ x ∈ W7.eraseIdx 8 := by simpa only [W8, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS7 8
    · exact buR2_eraseIdx_vsz_le hS7 8 x h
  have hS9 : ∀ x ∈ W9, vsz x ≤ SB := by
    intro x hx
    have hx' : x = W8.getD 8 .nil ∨ x ∈ W8.eraseIdx 8 := by simpa only [W9, List.mem_cons] using hx
    rcases hx' with h | h
    · rw [h]; exact buR2_getD_vsz_le hSB hS8 8
    · exact buR2_eraseIdx_vsz_le hS8 8 x h
  -- lengths of the intermediate windows
  have hl0 : W0.length = 6 := by
    show (buR2W0 σ v acc p α s t).length = 6
    simp [buR2W0]
  have hl1 : W1.length = 7 := by
    show (W0.getD 5 .nil :: W0).length = 7
    rw [List.length_cons, hl0]
  have hl2 : W2.length = 8 := by
    show (W1.getD 5 .nil :: W1).length = 8
    rw [List.length_cons, hl1]
  have hl3 : W3.length = 9 := by
    show (W2.getD 5 .nil :: W2).length = 9
    rw [List.length_cons, hl2]
  have hl4 : W4.length = 9 := by
    show (W3.getD 8 .nil :: W3.eraseIdx 8).length = 9
    rw [List.length_cons, List.length_eraseIdx_of_lt (by omega), hl3]
  have hl5 : W5.length = 9 := by
    show (W4.getD 8 .nil :: W4.eraseIdx 8).length = 9
    rw [List.length_cons, List.length_eraseIdx_of_lt (by omega), hl4]
  have hl6 : W6.length = 9 := by
    show (W5.getD 8 .nil :: W5.eraseIdx 8).length = 9
    rw [List.length_cons, List.length_eraseIdx_of_lt (by omega), hl5]
  have hl7 : W7.length = 9 := by
    show (W6.getD 8 .nil :: W6.eraseIdx 8).length = 9
    rw [List.length_cons, List.length_eraseIdx_of_lt (by omega), hl6]
  have hl8 : W8.length = 9 := by
    show (W7.getD 8 .nil :: W7.eraseIdx 8).length = 9
    rw [List.length_cons, List.length_eraseIdx_of_lt (by omega), hl7]
  -- the single window steps
  have pick5 : ∀ {A B : List Val}, A.getD 5 .nil :: A = B → 5 < A.length →
      (∀ x ∈ A, vsz x ≤ SB) → Pipe main (pickP 5) A B cb := by
    intro A B hAB hlen hA
    have hpk : Pipe main (pickP 5) A (A.getD 5 .nil :: A)
        (KP * (5 + 1) * (Work.Fx.szl (A.take (5 + 1)) + 1)) :=
      Pipe.pick main hpick (A := A) (k := 5) hlen
    rw [hAB] at hpk
    refine Pipe.le hpk ?_
    have h := buQW_szl_le_of SB hA (k := 5)
    exact buR2_op_le hKP hSB (k := 5) (by omega) (by omega)
  have roll8 : ∀ {A B : List Val}, A.getD 8 .nil :: A.eraseIdx 8 = B → 8 < A.length →
      (∀ x ∈ A, vsz x ≤ SB) → Pipe main (rollP 8) A B cb := by
    intro A B hAB hlen hA
    have hrl : Pipe main (rollP 8) A (A.getD 8 .nil :: A.eraseIdx 8)
        (KR * (8 + 1) * (Work.Fx.szl (A.take (8 + 1)) + 1)) :=
      Pipe.roll main hroll (A := A) (k := 8) hlen
    rw [hAB] at hrl
    refine Pipe.le hrl ?_
    have h := buQW_szl_le_of SB hA (k := 8)
    exact buR2_op_le hKR hSB (k := 8) (by omega) (by omega)
  have h1 : Pipe main (pickP 5) W0 W1 cb := pick5 rfl (by omega) hS0
  have h2 : Pipe main (pickP 5) W1 W2 cb := pick5 rfl (by omega) hS1
  have h3 : Pipe main (pickP 5) W2 W3 cb := pick5 rfl (by omega) hS2
  have h4 : Pipe main (rollP 8) W3 W4 cb := roll8 rfl (by omega) hS3
  have h5 : Pipe main (rollP 8) W4 W5 cb := roll8 rfl (by omega) hS4
  have h6 : Pipe main (rollP 8) W5 W6 cb := roll8 rfl (by omega) hS5
  have h7 : Pipe main (rollP 8) W6 W7 cb := roll8 rfl (by omega) hS6
  have h8 : Pipe main (rollP 8) W7 W8 cb := roll8 rfl (by omega) hS7
  have h9 : Pipe main (rollP 8) W8 W9 cb := roll8 rfl (by omega) hS8
  have c12 : Pipe main (.seq (pickP 5) (pickP 5)) W0 W2 (2 * cb) :=
    Pipe.le (Pipe.comp h1 h2) (by omega)
  have c123 : Pipe main (buR2Pick3 pickP) W0 W3 (3 * cb) :=
    Pipe.le (Pipe.comp c12 h3) (by omega)
  have d12 : Pipe main (.seq (rollP 8) (rollP 8)) W3 W5 (2 * cb) :=
    Pipe.le (Pipe.comp h4 h5) (by omega)
  have d123 : Pipe main (.seq (.seq (rollP 8) (rollP 8)) (rollP 8)) W3 W6 (3 * cb) :=
    Pipe.le (Pipe.comp d12 h6) (by omega)
  have d1234 : Pipe main (.seq (.seq (.seq (rollP 8) (rollP 8)) (rollP 8)) (rollP 8)) W3 W7 (4 * cb) :=
    Pipe.le (Pipe.comp d123 h7) (by omega)
  have d12345 : Pipe main (.seq (.seq (.seq (.seq (rollP 8) (rollP 8)) (rollP 8)) (rollP 8)) (rollP 8))
      W3 W8 (5 * cb) := Pipe.le (Pipe.comp d1234 h8) (by omega)
  have d123456 : Pipe main (buR2Roll6 rollP) W3 W9 (6 * cb) :=
    Pipe.le (Pipe.comp d12345 h9) (by omega)
  have hchain : Pipe main (buR2DupProg pickP rollP) W0 W9 (9 * cb) :=
    Pipe.le (Pipe.comp c123 d123456) (by omega)
  exact hchain

/-- the cost arithmetic of one round: the duplication plus the round word fit in the round budget -/
theorem buR2_cost_le {k₀ KS Kc G Sq Pq Z Z0 : ℕ}
    (hKc : 900000 * KS + k₀ ≤ Kc) (hZ : Pq ≤ Z) (hZ0 : Z0 ≤ Z) :
    9 * (KS * 100 * (1000 * (G * Sq * Pq))) + k₀ * (G * Sq * Z0) ≤ Kc * G * Sq * Z := by
  have h1 : 9 * (KS * 100 * (1000 * (G * Sq * Pq))) = 900000 * (KS * (G * Sq * Pq)) := by ring
  rw [h1]
  have h2 : KS * (G * Sq * Pq) ≤ KS * (G * Sq * Z) :=
    Nat.mul_le_mul_left KS (Nat.mul_le_mul_left _ hZ)
  have h3 : k₀ * (G * Sq * Z0) ≤ k₀ * (G * Sq * Z) :=
    Nat.mul_le_mul_left k₀ (Nat.mul_le_mul_left _ hZ0)
  calc 900000 * (KS * (G * Sq * Pq)) + k₀ * (G * Sq * Z0)
      ≤ 900000 * (KS * (G * Sq * Z)) + k₀ * (G * Sq * Z) :=
        add_le_add (Nat.mul_le_mul_left 900000 h2) h3
    _ = (900000 * KS + k₀) * (G * Sq * Z) := by ring
    _ ≤ Kc * (G * Sq * Z) := Nat.mul_le_mul_right _ (by omega)
    _ = Kc * G * Sq * Z := by ring


/-! ## 2.  the round word: duplication followed by the round word -/

/-- **The single-round word keeping the static table entries.**  It is
`buR2DupProg` (which copies `[C, s, p]` to the top of the round window) followed by the round word
`q₀` of the step statement, applied to the extended window `[σ, v, acc, C, s, p, C, s, p]`; the step
consumes the first copy of `C, s, p` and leaves the second one below its outputs. -/
theorem buR2Round_of_step
    (hstep : ∀ (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib),
      ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
        (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
        (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
          |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
        (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
      HvdH.WordR main q
        (fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val), (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc)
        (fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val) (v' acc' : List (ℤ × ℤ)),
          (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          out = cvecVal v' :: cvecVal acc' :: rest ∧
          v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
          acc' = buAddV acc (buSMulV σ v') ∧ v'.length = s ∧ acc'.length = s ∧
          buInV (B / 2 + 34 * egM p α + 4) v' ∧
          buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
        (fun _ => Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)))
    (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
      (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
        |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val), (σ = 1 ∨ σ = -1) ∧
        vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
          Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
        v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc)
      (fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val) (v' acc' : List (ℤ × ℤ)),
        (σ = 1 ∨ σ = -1) ∧
        vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
          Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
        out = cvecVal v' :: cvecVal acc' :: buColsT p α s t ::
          Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
        v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
        acc' = buAddV acc (buSMulV σ v') ∧ v'.length = s ∧ acc'.length = s ∧
        buInV (B / 2 + 34 * egM p α + 4) v' ∧
        buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
      (fun _ => Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨q₀, k₀, hq₀⟩ := hstep KL IL LL FL
  obtain ⟨pickP, KP, hpick⟩ := KL.pick
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  refine ⟨.seq (buR2DupProg pickP rollP) q₀, k₀ + 900000 * (KP + KR + 1) + 1, ?_⟩
  intro p α s t hs hst hα hp B B2 hB hB2 hrow main N Cm hmon hmb hN
  have hKc1 : 900000 * (KP + KR + 1) ≤ k₀ + 900000 * (KP + KR + 1) + 1 := by omega
  have hNk : k₀ * p < N := by
    have h : k₀ * p ≤ (k₀ + 900000 * (KP + KR + 1) + 1) * p :=
      Nat.mul_le_mul_right p (by omega)
    omega
  -- sizes of the six window entries
  have hG1 : 1 ≤ egM p α + 1 := by omega
  have hS1 : 1 ≤ s + 1 := by omega
  have hP1 : 1 ≤ p + 1 := by omega
  have hprod1 : 1 ≤ (egM p α + 1) * (s + 1) * (p + 1) := by
    calc (1 : ℕ) = 1 * 1 * 1 := by ring
      _ ≤ (egM p α + 1) * (s + 1) * (p + 1) := Nat.mul_le_mul (Nat.mul_le_mul hG1 hS1) hP1
  have hSB1 : 1 ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
    calc (1 : ℕ) ≤ (egM p α + 1) * (s + 1) * (p + 1) := hprod1
      _ = 1 * ((egM p α + 1) * (s + 1) * (p + 1)) := by ring
      _ ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := Nat.mul_le_mul_right _ (by norm_num)
  have hSB3 : 3 ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
    calc (3 : ℕ) = 3 * 1 := by ring
      _ ≤ 3 * ((egM p α + 1) * (s + 1) * (p + 1)) := Nat.mul_le_mul_left 3 hprod1
      _ ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := Nat.mul_le_mul_right _ (by norm_num)
  have hszC : vsz (buColsT p α s t) ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
    have h := buQW_colsT_vsz_le p α s t hs hα hp hrow
    calc vsz (buColsT p α s t) ≤ 1000 * (egM p α + 1) * (s + 1) * (p + 1) := h
      _ = 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by ring
  -- the size facts of the six window values of a fixed round
  have key : ∀ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val), (σ = 1 ∨ σ = -1) →
      v.length = s → acc.length = s → buInV B v → buInV B2 acc →
      WordR main (.seq (buR2DupProg pickP rollP) q₀)
        (fun vs => vs = buR2W0 σ v acc p α s t ++ rest)
        (fun _ out => ∃ (v' acc' : List (ℤ × ℤ)),
          out = cvecVal v' :: cvecVal acc' :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
          acc' = buAddV acc (buSMulV σ v') ∧ v'.length = s ∧ acc'.length = s ∧
          buInV (B / 2 + 34 * egM p α + 4) v' ∧
          buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
        (fun _ => (k₀ + 900000 * (KP + KR + 1) + 1) * (egM p α + 1) * (s + 1) *
          (Cm ((k₀ + 900000 * (KP + KR + 1) + 1) * p) + p + 1)) := by
    intro σ v acc rest hσ hvlen hacclen hvin haccin
    have hszσ : vsz (Val.int σ) ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
      rw [Work.Fx.vsz_int]
      have h3 : isz σ ≤ 3 := by rcases hσ with h | h <;> rw [h] <;> decide
      omega
    have hszs : vsz (Val.int (s : ℤ)) ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
      rw [Work.Fx.vsz_int]
      have h2 : isz (s : ℤ) ≤ s + 2 := by
        simp only [isz, Int.natAbs_natCast]
        have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := s))
        omega
      have h3 : s + 2 ≤ 30 * ((s + 1) * (p + 1)) := by
        nlinarith [Nat.zero_le s, Nat.zero_le p]
      exact buR2_small_le (by omega) hG1
    have hszp : vsz (Val.int (p : ℤ)) ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
      rw [Work.Fx.vsz_int]
      have h2 : isz (p : ℤ) ≤ p + 2 := by
        simp only [isz, Int.natAbs_natCast]
        have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
        omega
      have h3 : p + 2 ≤ 30 * ((s + 1) * (p + 1)) := by
        nlinarith [Nat.zero_le s, Nat.zero_le p]
      exact buR2_small_le (by omega) hG1
    have hszvec : ∀ (C : ℕ) (u : List (ℤ × ℤ)), C ≤ 2 ^ (p + 2) → u.length = s → buInV C u →
        vsz (cvecVal u) ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
      intro C u hC hu huin
      have h := buQT_vsz_cvecVal (u := u) (M := p + 5) (buQW_isz_of_buInV hC huin)
      rw [hu] at h
      have h2 : 3 * s * (p + 5 + 1) + 1 ≤ 30 * ((s + 1) * (p + 1)) := by
        nlinarith [Nat.zero_le s, Nat.zero_le p]
      exact buR2_small_le (by omega) hG1
    have hN6 : ∀ x ∈ buR2W0 σ v acc p α s t,
        vsz x ≤ 1000 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
      intro x hx
      simp only [buR2W0, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h
      · rw [h]; exact hszσ
      · rw [h]; exact hszvec B v hB hvlen hvin
      · rw [h]; exact hszvec B2 acc hB2 hacclen haccin
      · rw [h]; exact hszC
      · rw [h]; exact hszs
      · rw [h]; exact hszp
    have hdup : WordR main (buR2DupProg pickP rollP)
        (fun vs => vs = buR2W0 σ v acc p α s t ++ rest)
        (fun _ out => out = buR2W9 σ v acc p α s t ++ rest)
        (fun _ => 9 * ((KP + KR + 1) * 100 * (1000 * ((egM p α + 1) * (s + 1) * (p + 1))))) :=
      buR2DupPipe hpick hroll (by omega) (by omega) hSB1 σ v acc p α s t hN6 rest
    have hstp : WordR main q₀ (fun vs => vs = buR2W9 σ v acc p α s t ++ rest)
        (fun _ out => ∃ (v' acc' : List (ℤ × ℤ)),
          out = cvecVal v' :: cvecVal acc' :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
          acc' = buAddV acc (buSMulV σ v') ∧ v'.length = s ∧ acc'.length = s ∧
          buInV (B / 2 + 34 * egM p α + 4) v' ∧
          buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
        (fun _ => k₀ * (egM p α + 1) * (s + 1) * (Cm (k₀ * p) + p + 1)) := by
      intro vs' hvs' s2 R2 hR2
      have hpre' : (fun vs => ∃ (σ' : ℤ) (v' acc' : List (ℤ × ℤ)) (rest' : List Val),
          (σ' = 1 ∨ σ' = -1) ∧
          vs = Val.int σ' :: cvecVal v' :: cvecVal acc' :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest' ∧
          v'.length = s ∧ acc'.length = s ∧ buInV B v' ∧ buInV B2 acc') vs' :=
        ⟨σ, v, acc, buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest, hσ,
          by rw [hvs']; rfl, hvlen, hacclen, hvin, haccin⟩
      obtain ⟨out, s', n, hQ, hev, hn, hstk, hoth⟩ :=
        hq₀ p α s t hs hst hα hp B B2 hB hB2 hrow main N Cm hmon hmb hNk vs' hpre' s2 R2 hR2
      obtain ⟨σ', v'', acc'', rest'', v', acc', hσ', hvs'', hout, hv', hacc', hvl, hal, hb1, hb2⟩ := hQ
      have heq : Val.int σ' :: cvecVal v'' :: cvecVal acc'' :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest'' =
          Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) ::
            (buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest) :=
        hvs''.symm.trans (by rw [hvs']; rfl)
      have h1 := List.cons.inj heq
      have h2 := List.cons.inj h1.2
      have h3 := List.cons.inj h2.2
      have h4 := List.cons.inj h3.2
      have h5 := List.cons.inj h4.2
      have h6 := List.cons.inj h5.2
      have hr : rest'' = buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest := h6.2
      have hv'' : v'' = v := buQT_cvecVal_inj h2.1
      have ha'' : acc'' = acc := buQT_cvecVal_inj h3.1
      have hs'' : σ' = σ := Val.int.inj h1.1
      refine ⟨out, s', n, ⟨v', acc', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hev, hn, hstk, hoth⟩
      · rw [hout, hr]
      · rw [hv', hv'']
      · rw [hacc', ha'', hs'']
      · exact hvl
      · exact hal
      · exact hb1
      · exact hb2
    -- compose the duplication with the round word
    intro vs hvs s0 R hR
    obtain ⟨mid, s1, n1, hmid, hev1, hn1, hstk1, hoth1⟩ := hdup vs hvs s0 R hR
    obtain ⟨out, s2, n2, hout, hev2, hn2, hstk2, hoth2⟩ := hstp mid hmid s1 R hstk1
    obtain ⟨v', acc', hout', hv', hacc', hvl, hal, hb1, hb2⟩ := hout
    refine ⟨out, s2, n1 + n2, ⟨v', acc', hout', hv', hacc', hvl, hal, hb1, hb2⟩,
      HvdH.Eval.seq hev1 hev2, ?_, hstk2, fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩
    have hn2' : n2 ≤ k₀ * ((egM p α + 1) * (s + 1) * (Cm (k₀ * p) + p + 1)) := by
      have he : k₀ * (egM p α + 1) * (s + 1) * (Cm (k₀ * p) + p + 1) =
          k₀ * ((egM p α + 1) * (s + 1) * (Cm (k₀ * p) + p + 1)) := by ring
      rw [he] at hn2
      exact hn2
    have hZ0 : Cm (k₀ * p) + p + 1 ≤
        Cm ((k₀ + 900000 * (KP + KR + 1) + 1) * p) + p + 1 := by
      have hm : Cm (k₀ * p) ≤ Cm ((k₀ + 900000 * (KP + KR + 1) + 1) * p) :=
        hmon (Nat.mul_le_mul_right p (by omega))
      omega
    exact le_trans (add_le_add hn1 hn2')
      (buR2_cost_le (k₀ := k₀) (KS := KP + KR + 1) (Kc := k₀ + 900000 * (KP + KR + 1) + 1)
        (G := egM p α + 1) (Sq := s + 1) (Pq := p + 1)
        (Z := Cm ((k₀ + 900000 * (KP + KR + 1) + 1) * p) + p + 1)
        (Z0 := Cm (k₀ * p) + p + 1) (by omega) (by omega) hZ0)
  -- the round's own pre/post against the fixed window
  intro vs hpre s0 R hR
  obtain ⟨σ, v, acc, rest, hσ, hvs, hvlen, hacclen, hvin, haccin⟩ := hpre
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    key σ v acc rest hσ hvlen hacclen hvin haccin vs hvs s0 R hR
  obtain ⟨v', acc', hout', hv', hacc', hvl, hal, hb1, hb2⟩ := hout
  exact ⟨out, s', n, ⟨σ, v, acc, rest, v', acc', hσ, hvs, hout', hv', hacc', hvl, hal, hb1, hb2⟩,
    hev, hn, hstk, hoth⟩

/-- **The target statement from the single-round step.** -/
theorem buQWrnd2_of_step
    (hstep : ∀ (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib),
      ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
        (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
        (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
          |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
        (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
      HvdH.WordR main q
        (fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val), (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc)
        (fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val) (v' acc' : List (ℤ × ℤ)),
          (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          out = cvecVal v' :: cvecVal acc' :: rest ∧
          v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
          acc' = buAddV acc (buSMulV σ v') ∧ v'.length = s ∧ acc'.length = s ∧
          buInV (B / 2 + 34 * egM p α + 4) v' ∧
          buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
        (fun _ => Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)))
    (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
        |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (Work.Resample.egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        v.length = s ∧ Work.Resample.buInV (2 ^ (p - 1) + 2) v)
      (fun vs out => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val) (u : List (ℤ × ℤ)),
        vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        out = HvdH.cvecVal u :: rest ∧
        u = Work.Resample.buJsumL (Work.Resample.buWt p α s t) p s (Work.Resample.egM p α)
          (Work.Resample.egN p α s t) v ∧
        u.length = s ∧ Work.Resample.buInV (2 ^ (p + 1)) u)
      (fun _ => Kc * (Work.Resample.egN p α s t + 1) * (Work.Resample.egM p α + 1) * (s + 1) *
          (Cm (Kc * p) + p + 1)) :=
  buQWrounds_of (buR2Round_of_step hstep) KL IL LL FL

theorem buQWrnd2 (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
        |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (Work.Resample.egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        v.length = s ∧ Work.Resample.buInV (2 ^ (p - 1) + 2) v)
      (fun vs out => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val) (u : List (ℤ × ℤ)),
        vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        out = HvdH.cvecVal u :: rest ∧
        u = Work.Resample.buJsumL (Work.Resample.buWt p α s t) p s (Work.Resample.egM p α)
          (Work.Resample.egN p α s t) v ∧
        u.length = s ∧ Work.Resample.buInV (2 ^ (p + 1)) u)
      (fun _ => Kc * (Work.Resample.egN p α s t + 1) * (Work.Resample.egM p α + 1) * (s + 1) *
          (Cm (Kc * p) + p + 1)) :=
  buQWrnd2_of_step buQWstep KL IL LL FL

end Work.Resample
