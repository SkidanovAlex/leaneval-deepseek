import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.ifZeroDefs
import Submission.Work.Kernel.encodeNatBits
import Submission.Work.Kernel.ifZeroDrain

/-!
# Kernel: the `ifZero` word

`Work.Kernel.ifZero` inspects the integer value on top of the value stack: the program consumes
`Val.enc (.int z)` entirely (sign, then the bits of `|z|`, then `iend`) and then runs `q₁` if
`z = 0` and `q₂` otherwise.  The zero test is the paper's: since `encodeNat 0 = []`, the integer is
`0` exactly when the glyph following the sign is `iend`.

The work is split as follows (all in `namespace Work.Kernel`):

* `ifZero_tPop`/`ifZero_eval_pop`: `Cmd.pop` on a stack with a known head, with a canonical result
  state `(s.updStk 0 l).updReg r g`;
* `ifZero_enc_int_zero`, `ifZero_encs_int_zero`, `ifZero_encs_int_split`: the shape of `encs`
  under `Val.int z`;
* `ifZero_eval_zero` / `ifZero_eval_nonzero`: the whole prelude of `ifZero_comb`, from the value
  stack to the entrance of the chosen continuation, with exact costs;
* `ifZero`: the `WordR` spec, obtained by composing the prelude with the given `WordR`s for `q₁`,
  `q₂`.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-! ## `pop` with known head -/

/-- `State.tPop s k r` is `(s.updStk k l).updReg r g` when stack `k` starts with `g :: l`. -/
theorem ifZero_tPop (s : State) (k : Stk) (r : Reg) (g : Glyph) (l : List Glyph)
    (h : s.stk k = g :: l) : State.tPop s k r = (s.updStk k l).updReg r g := by
  have h1 : (s.stk k).headD Glyph.eos = g := by rw [h]; rfl
  have h2 : (s.stk k).tail = l := by rw [h]; rfl
  simp only [State.tPop, State.updStk, State.updReg]
  rw [h1, h2]

/-- `Cmd.pop k r` on a stack `k` starting with `g :: l`, in canonical form. -/
theorem ifZero_eval_pop (main : Cmd) (k : Stk) (r : Reg) (g : Glyph) (l : List Glyph)
    (s : State) (h : s.stk k = g :: l) :
    Eval main (Cmd.pop k r) s ((s.updStk k l).updReg r g) 1 := by
  rw [← ifZero_tPop s k r g l h]
  exact Eval.pop k r s

/-! ## The shape of `encs` under `Val.int z` -/

/-- The encoding of `Val.int 0`: sign `pos` followed immediately by `iend` (`encodeNat 0 = []`). -/
theorem ifZero_enc_int_zero : (Val.int 0).enc = [Glyph.pos, Glyph.iend] := by
  simp [Val.enc, Computability.encodeNat, Computability.encodeNum]

/-- The content of stack 0 under a top value `Val.int 0`. -/
theorem ifZero_encs_int_zero (rest : List Val) (R : List Glyph) :
    encs (Val.int 0 :: rest) ++ R = Glyph.pos :: (Glyph.iend :: (encs rest ++ R)) := by
  simp [Val.enc, Computability.encodeNat, Computability.encodeNum, encs_cons]

/-- The content of stack 0 under a top value `Val.int z` with `encodeNat z.natAbs = b :: ms`:
sign, first bit, remaining bits, `iend`, then the rest of the values. -/
theorem ifZero_encs_int_split (z : ℤ) (b : Bool) (ms : List Bool) (rest : List Val) (R : List Glyph)
    (hb : Computability.encodeNat z.natAbs = b :: ms) :
    encs (Val.int z :: rest) ++ R =
      (if z < 0 then Glyph.neg else Glyph.pos) ::
        (Glyph.bit b :: (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))) := by
  rw [encs_cons, Val.enc, hb, List.map_cons]
  simp [List.append_assoc]

/-! ## The prelude of the combinator -/

/-- The prelude of `ifZero_comb q₁ q₂` on a top value `Val.int 0`: consume the sign and the `iend`
and hand over to `q₁`, at cost `3 + n₁` if `q₁` runs at cost `n₁`. -/
theorem ifZero_eval_zero (main : Cmd) (q₁ q₂ : Cmd) (rest : List Val) (R : List Glyph)
    (s s' : State) (n₁ : ℕ) (hstk : s.stk 0 = Glyph.pos :: (Glyph.iend :: (encs rest ++ R)))
    (hq : Eval main q₁ (ifZero_afterPrelude rest R s) s' n₁) :
    Eval main (ifZero_comb q₁ q₂) s s' (3 + n₁) := by
  have e1 : Eval main (Cmd.pop 0 0) s
      ((s.updStk 0 (Glyph.iend :: (encs rest ++ R))).updReg 0 Glyph.pos) 1 :=
    ifZero_eval_pop main 0 0 Glyph.pos (Glyph.iend :: (encs rest ++ R)) s hstk
  have e2 : Eval main (Cmd.pop 0 0)
      ((s.updStk 0 (Glyph.iend :: (encs rest ++ R))).updReg 0 Glyph.pos)
      (ifZero_afterPrelude rest R s) 1 := by
    have h := ifZero_eval_pop main 0 0 Glyph.iend (encs rest ++ R)
      ((s.updStk 0 (Glyph.iend :: (encs rest ++ R))).updReg 0 Glyph.pos)
      (by simp [State.updStk, State.updReg])
    simpa [ifZero_afterPrelude, State.updStk, State.updReg, Function.update_idem] using h
  have e3 : Eval main (Cmd.ite 0 Glyph.iend q₁ (Cmd.seq (ifZero_drain 0) q₂))
      (ifZero_afterPrelude rest R s) s' (n₁ + 1) :=
    Eval.iteT (r := 0) (c := Glyph.iend) (c₁ := q₁) (c₂ := Cmd.seq (ifZero_drain 0) q₂)
      (by simp [ifZero_afterPrelude, State.updStk, State.updReg]) hq
  have e := eval_seq e1 (eval_seq e2 e3)
  rw [show 1 + (1 + (n₁ + 1)) = 3 + n₁ by omega] at e
  exact e

/-- The prelude of `ifZero_comb q₁ q₂` on a top value `Val.int z` with `z ≠ 0`: consume the sign,
the first bit and the remaining bits up to `iend`, then hand over to `q₂`.  Cost `4 * ms.length + 9`
plus the cost `n₂` of `q₂`, where `ms` is everything after the first bit of `encodeNat z.natAbs`. -/
theorem ifZero_eval_nonzero (main : Cmd) (q₁ q₂ : Cmd) (sg : Glyph) (b : Bool) (ms : List Bool)
    (rest : List Val) (R : List Glyph) (s s' : State) (n₂ : ℕ)
    (hstk : s.stk 0 = sg :: (Glyph.bit b :: (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))))
    (hq : Eval main q₂ (ifZero_afterPrelude rest R s) s' n₂) :
    Eval main (ifZero_comb q₁ q₂) s s' (4 * ms.length + 9 + n₂) := by
  have e1 : Eval main (Cmd.pop 0 0) s
      ((s.updStk 0 (Glyph.bit b :: (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R)))).updReg 0 sg) 1 :=
    ifZero_eval_pop main 0 0 sg (Glyph.bit b :: (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R)))
      s hstk
  have e2 : Eval main (Cmd.pop 0 0)
      ((s.updStk 0 (Glyph.bit b :: (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R)))).updReg 0 sg)
      ((s.updStk 0 (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))).updReg 0 (Glyph.bit b)) 1 := by
    have h := ifZero_eval_pop main 0 0 (Glyph.bit b) (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))
      ((s.updStk 0 (Glyph.bit b :: (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R)))).updReg 0 sg)
      (by simp [State.updStk, State.updReg])
    simpa [State.updStk, State.updReg, Function.update_idem] using h
  have hd : Eval main (ifZero_drain 0)
      ((s.updStk 0 (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))).updReg 0 (Glyph.bit b))
      (ifZero_afterPrelude rest R s) (4 * (ms.length + 1) + 2) := by
    have h := ifZeroDrain main 0 ms (encs rest ++ R)
      ((s.updStk 0 (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))).updReg 0 (Glyph.bit b))
      (by simp [State.updStk, State.updReg])
    rwa [show ifZero_drainState 0 (encs rest ++ R)
        ((s.updStk 0 (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))).updReg 0 (Glyph.bit b))
        = ifZero_afterPrelude rest R s by
      simp [ifZero_drainState, ifZero_afterPrelude, State.updStk, State.updReg,
        Function.update_idem]] at h
  have hne : ((s.updStk 0 (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))).updReg 0
      (Glyph.bit b)).reg 0 ≠ Glyph.iend := by
    simp [State.updReg]
  have e3 : Eval main (Cmd.ite 0 Glyph.iend q₁ (Cmd.seq (ifZero_drain 0) q₂))
      ((s.updStk 0 (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))).updReg 0 (Glyph.bit b)) s'
      (((4 * (ms.length + 1) + 2) + n₂) + 1) :=
    Eval.iteF (r := 0) (c := Glyph.iend) (c₁ := q₁) (c₂ := Cmd.seq (ifZero_drain 0) q₂) hne
      (eval_seq hd hq)
  have e := eval_seq e1 (eval_seq e2 e3)
  rw [show 1 + (1 + (((4 * (ms.length + 1) + 2) + n₂) + 1)) = 4 * ms.length + 9 + n₂ by omega] at e
  exact e

/-! ## The `ifZero` word -/

/-- `import Submission.Work.Kernel.Raw`, work in `namespace Work.Kernel`.  `HvdH.Val.enc (.int z)` is `pos`/`neg`, then the bits of `|z|` least significant first, then `iend`; `encodeNat 0 = []`, so `z = 0` iff the glyph after the sign is `iend`.  Helpers in this file must be named with the prefix `ifZero_`. -/
theorem ifZero : ∃ (comb : HvdH.Cmd → HvdH.Cmd → HvdH.Cmd) (K : ℕ), ∀ (main q₁ q₂ : HvdH.Cmd) (z : ℤ) (rest : List HvdH.Val)
    (Q₁ Q₂ : List HvdH.Val → Prop) (c₁ c₂ : ℕ),
    (z = 0 → HvdH.WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
    (z ≠ 0 → HvdH.WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
    HvdH.WordR main (comb q₁ q₂) (fun vs => vs = HvdH.Val.int z :: rest)
      (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => K * (HvdH.isz z + 1) + max c₁ c₂) := by
  refine ⟨ifZero_comb, 4, ?_⟩
  intro main q₁ q₂ z rest Q₁ Q₂ c₁ c₂ h₁ h₂ vs hvs s R hR
  subst hvs
  by_cases hz : z = 0
  · -- the top integer is `0`
    subst hz
    have hstk : s.stk 0 = Glyph.pos :: (Glyph.iend :: (encs rest ++ R)) := by
      rw [hR, ifZero_encs_int_zero]
    obtain ⟨out, s', n₁, hQ₁, he₁, hn₁, hstk₁, hoth₁⟩ :=
      h₁ rfl rest rfl (ifZero_afterPrelude rest R s) R
        (by simp [ifZero_afterPrelude, State.updStk, State.updReg])
    refine ⟨out, s', 3 + n₁, ⟨fun _ => hQ₁, fun hz0 => absurd rfl hz0⟩,
      ifZero_eval_zero main q₁ q₂ rest R s s' n₁ hstk he₁, ?_, hstk₁, ?_⟩
    · have hiz : isz (0 : ℤ) + 1 = 3 := by simp [isz]
      have hn₁' : n₁ ≤ c₁ := hn₁
      have hmax : c₁ ≤ max c₁ c₂ := le_max_left c₁ c₂
      show 3 + n₁ ≤ 4 * (isz (0 : ℤ) + 1) + max c₁ c₂
      omega
    · intro k hk
      rw [hoth₁ k hk]
      simp [ifZero_afterPrelude, hk]
  · -- the top integer is nonzero
    have hbits_ne : Computability.encodeNat z.natAbs ≠ [] := by
      intro h0
      have hlen : (Computability.encodeNat z.natAbs).length = z.natAbs.size := by
        rw [encodeNatBits]; exact Nat.size_eq_bits_len z.natAbs
      rw [h0] at hlen
      simp only [List.length_nil] at hlen
      exact hz (Int.natAbs_eq_zero.mp (Nat.size_eq_zero.mp hlen.symm))
    obtain ⟨b, ms, hb⟩ := List.exists_cons_of_ne_nil hbits_ne
    have hstk : s.stk 0 = (if z < 0 then Glyph.neg else Glyph.pos) ::
        (Glyph.bit b :: (ms.map Glyph.bit ++ Glyph.iend :: (encs rest ++ R))) := by
      rw [hR, ifZero_encs_int_split z b ms rest R hb]
    obtain ⟨out, s', n₂, hQ₂, he₂, hn₂, hstk₂, hoth₂⟩ :=
      h₂ hz rest rfl (ifZero_afterPrelude rest R s) R
        (by simp [ifZero_afterPrelude, State.updStk, State.updReg])
    refine ⟨out, s', 4 * ms.length + 9 + n₂,
      ⟨fun hz0 => absurd hz0 hz, fun _ => hQ₂⟩,
      ifZero_eval_nonzero main q₁ q₂ (if z < 0 then Glyph.neg else Glyph.pos) b ms rest R s s' n₂
        hstk he₂, ?_, hstk₂, ?_⟩
    · have hlen : ms.length + 1 = z.natAbs.size := by
        have h1 : (Computability.encodeNat z.natAbs).length = z.natAbs.size := by
          rw [encodeNatBits]; exact Nat.size_eq_bits_len z.natAbs
        rw [hb] at h1
        simpa using h1
      have hiz : isz z + 1 = z.natAbs.size + 3 := by simp [isz]
      have hn₂' : n₂ ≤ c₂ := hn₂
      have hmax : c₂ ≤ max c₁ c₂ := le_max_right c₁ c₂
      show 4 * ms.length + 9 + n₂ ≤ 4 * (isz z + 1) + max c₁ c₂
      omega
    · intro k hk
      rw [hoth₂ k hk]
      simp [ifZero_afterPrelude, hk]

end Work.Kernel
