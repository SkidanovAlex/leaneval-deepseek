import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# `axisParamsUp`: the value permutation `X k sgn r p a b c -> X a c b k sgn r p`

The `SynFFT` axis word keeps a fixed block of eight parameters below the working data and has
to present them in a different order for the *up*-pass word.  This file provides that move as a
single `Cmd` built out of eight `KLib.roll` steps (a roll brings the `j`-th value to the top,
preserving the relative order of all others):

    4, 4, 4, 4,  6, 6, 6, 7

Bringing the elements to the front in the reverse order of the target gives
`X a c b k sgn r p` after eight rolls; each roll only ever inspects the top eight values, so
the intermediate stacks are permutations of the same eight values and the cost is bounded by
`64 * K_roll * (sum vsz + 1)` -- independent of `rest`, as required.

The helpers below are the `KLib` counterparts of `Submission/Work/Params/steps.lean`
(`seqC`, `rollStep`, ...); `KLib` is `KernelLib` without the refuted `loop` field, so the same
proofs go through verbatim.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## Composing exact-state steps -/

/-- Compose two steps whose intermediate stack is *exactly* `M`. -/
theorem seqC (hK : KLib) {main : Cmd} {p q : Cmd} {L M N : List Val} {c c' : Nat}
    (hp : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c))
    (hq : WordR main q (fun vs => vs = M) (fun _ out => out = N) (fun _ => c')) :
    WordR main (.seq p q) (fun vs => vs = L) (fun _ out => out = N) (fun _ => c + c') := by
  have h := hK.seq main p q (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)
    (fun vs => vs = M) (fun _ out => out = N) (fun _ => c') (fun _ => c') hp hq
    (fun vs mid _ hM => ⟨hM, le_refl _⟩)
  refine hK.conseq main (.seq p q) (fun vs => vs = L) (fun vs => vs = L)
    (fun vs out => ∃ mid, mid = M ∧ out = N) (fun _ out => out = N)
    (fun _ => c + c') (fun _ => c + c')
    h (fun _ hh => hh) ?_ (fun _ _ => le_refl _)
  intro vs out _ hq
  obtain ⟨mid, -, hout⟩ := hq
  exact hout

/-- Rewrite the resulting stack of a step with an explicit equation. -/
theorem post_eq (hK : KLib) {main : Cmd} {p : Cmd} {L M N : List Val} {c : Nat}
    (h : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)) (hMN : M = N) :
    WordR main p (fun vs => vs = L) (fun _ out => out = N) (fun _ => c) := by
  refine hK.conseq main p (fun vs => vs = L) (fun vs => vs = L) (fun _ out => out = M)
    (fun _ out => out = N) (fun _ => c) (fun _ => c) h (fun _ hh => hh) ?_
    (fun _ _ => le_refl _)
  intro vs out _ hq
  rw [hq, hMN]

/-! ## One roll, from an exact stack to an exact stack -/

/-- `KLib.roll` as an exact-state step: rolling the `k`-th value of `L` to the top. -/
theorem rollStep (hK : KLib) {main : Cmd} {prog : Nat → Cmd} {K0 : Nat}
    (h : ∀ k : Nat, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : Nat) (L : List Val) (hk : k < L.length) (c : Nat)
    (hc : K0 * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L.eraseIdx k)
      (fun _ => c) := by
  refine hK.conseq main (prog k) (fun vs => k < vs.length) (fun vs => vs = L)
    (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
    (fun _ out => out = L.getD k .nil :: L.eraseIdx k)
    (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)) (fun _ => c) (h k)
    ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hk
  · intro vs out hvs hq
    rw [hvs] at hq
    exact hq
  · intro vs hvs; rw [hvs]; exact hc

/-- `rollStep` with the resulting stack named in advance. -/
theorem rollTo (hK : KLib) {main : Cmd} {prog : Nat → Cmd} {K0 : Nat}
    (h : ∀ k : Nat, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : Nat) (L M : List Val) (hM : L.getD k .nil :: L.eraseIdx k = M) (hk : k < L.length)
    (c : Nat) (hc : K0 * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L) (fun _ out => out = M) (fun _ => c) :=
  post_eq hK (rollStep hK h k L hk c hc) hM

/-! ## Cost arithmetic -/

/-- The size of the eight values this word permutes. -/
def psSum (X a b c k sgn r p : Val) : Nat :=
  vsz X + vsz a + vsz b + vsz c + vsz k + vsz sgn + vsz r + vsz p + 1

/-- Eight consecutive rolls each cost at most `8 * K0 * psSum`: the rolled prefix is a set of
at most eight of the values and `k + 1 ≤ 8`. -/
theorem rollCost_le {K0 k P S : Nat} (hk : k + 1 ≤ 8) (hP : P + 1 ≤ S) :
    K0 * (k + 1) * (P + 1) ≤ 8 * K0 * S := by
  calc K0 * (k + 1) * (P + 1) ≤ K0 * 8 * (P + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
    _ ≤ K0 * 8 * S := Nat.mul_le_mul_left _ hP
    _ = 8 * K0 * S := by ring

/-! ## The permutation -/

theorem axisParamsUp (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X a b c k sgn r p : HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = X :: k :: sgn :: r :: p :: a :: b :: c :: rest)
        (fun _ out => out = X :: a :: c :: b :: k :: sgn :: r :: p :: rest)
        (fun vs => K * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + HvdH.vsz k +
          HvdH.vsz sgn + HvdH.vsz r + HvdH.vsz p + 1)) := by
  obtain ⟨rollP, K0, hroll⟩ := hk.roll
  refine ⟨Cmd.seq (rollP 4) (Cmd.seq (rollP 4) (Cmd.seq (rollP 4) (Cmd.seq (rollP 4)
    (Cmd.seq (rollP 6) (Cmd.seq (rollP 7) (Cmd.seq (rollP 7) (rollP 7))))))), 64 * K0, ?_⟩
  intro main X a b c k sgn r p rest
  -- bring p, r, sgn, k to the front one by one (each is 4th), giving the prefix `k sgn r p`
  have s1 : WordR main (rollP 4)
      (fun vs => vs = X :: k :: sgn :: r :: p :: a :: b :: c :: rest)
      (fun _ out => out = p :: X :: k :: sgn :: r :: a :: b :: c :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 4 (X :: k :: sgn :: r :: p :: a :: b :: c :: rest)
      (p :: X :: k :: sgn :: r :: a :: b :: c :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  have s2 : WordR main (rollP 4)
      (fun vs => vs = p :: X :: k :: sgn :: r :: a :: b :: c :: rest)
      (fun _ out => out = r :: p :: X :: k :: sgn :: a :: b :: c :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 4 (p :: X :: k :: sgn :: r :: a :: b :: c :: rest)
      (r :: p :: X :: k :: sgn :: a :: b :: c :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  have s3 : WordR main (rollP 4)
      (fun vs => vs = r :: p :: X :: k :: sgn :: a :: b :: c :: rest)
      (fun _ out => out = sgn :: r :: p :: X :: k :: a :: b :: c :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 4 (r :: p :: X :: k :: sgn :: a :: b :: c :: rest)
      (sgn :: r :: p :: X :: k :: a :: b :: c :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  have s4 : WordR main (rollP 4)
      (fun vs => vs = sgn :: r :: p :: X :: k :: a :: b :: c :: rest)
      (fun _ out => out = k :: sgn :: r :: p :: X :: a :: b :: c :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 4 (sgn :: r :: p :: X :: k :: a :: b :: c :: rest)
      (k :: sgn :: r :: p :: X :: a :: b :: c :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  -- now b (6th), then c, a and X (each 7th)
  have s5 : WordR main (rollP 6)
      (fun vs => vs = k :: sgn :: r :: p :: X :: a :: b :: c :: rest)
      (fun _ out => out = b :: k :: sgn :: r :: p :: X :: a :: c :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 6 (k :: sgn :: r :: p :: X :: a :: b :: c :: rest)
      (b :: k :: sgn :: r :: p :: X :: a :: c :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  have s6 : WordR main (rollP 7)
      (fun vs => vs = b :: k :: sgn :: r :: p :: X :: a :: c :: rest)
      (fun _ out => out = c :: b :: k :: sgn :: r :: p :: X :: a :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 7 (b :: k :: sgn :: r :: p :: X :: a :: c :: rest)
      (c :: b :: k :: sgn :: r :: p :: X :: a :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  have s7 : WordR main (rollP 7)
      (fun vs => vs = c :: b :: k :: sgn :: r :: p :: X :: a :: rest)
      (fun _ out => out = a :: c :: b :: k :: sgn :: r :: p :: X :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 7 (c :: b :: k :: sgn :: r :: p :: X :: a :: rest)
      (a :: c :: b :: k :: sgn :: r :: p :: X :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  have s8 : WordR main (rollP 7)
      (fun vs => vs = a :: c :: b :: k :: sgn :: r :: p :: X :: rest)
      (fun _ out => out = X :: a :: c :: b :: k :: sgn :: r :: p :: rest)
      (fun _ => 8 * K0 * psSum X a b c k sgn r p) :=
    rollTo hk (hroll main) 7 (a :: c :: b :: k :: sgn :: r :: p :: X :: rest)
      (X :: a :: c :: b :: k :: sgn :: r :: p :: rest) (by simp) (by simp) _
      (rollCost_le (by norm_num) (by unfold psSum; simp; omega))
  have chain := seqC hk s1 (seqC hk s2 (seqC hk s3 (seqC hk s4
    (seqC hk s5 (seqC hk s6 (seqC hk s7 s8))))))
  exact hk.conseq main _ _ _ _ _ _ _ chain (fun _ h => h) (fun _ _ _ h => h)
    (fun _ _ => by
      beta_reduce
      unfold psSum
      exact le_of_eq (by ring))

end Work.SynFFT
