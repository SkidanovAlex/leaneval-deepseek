import Mathlib
import Submission.Work.Resample.interfacesShim
import Submission.Work.IntLib.encodeNatBridge

/-!
# `buQWmagWord`: replace the top two integer values by their absolute values

The word takes `int a :: int b :: R` to `int |a| :: int |b| :: R` at cost
`O(isz a + isz b)`, uniformly in the ambient program `main` (no `self`).

The observation is purely syntactic: the encoding of `Val.int z` is
`(if z < 0 then neg else pos) :: bits of |z| ++ [iend]`, so `Val.enc (.int |z|)`
is obtained from `Val.enc (.int z)` by replacing the *leading* glyph `neg` by
`pos` (and is identical when `z ≥ 0`). Hence a constant-cost word (`pop` the
leading glyph of stack 0, overwrite it by `pos` if it was `neg`, push it back)
does the job on the head value; two swaps (from `KernelLib`) bring the second
value to the head in turn.

The composition and the cost bookkeeping are done with `WordR` combinators;
`magWordComp` is the constant-cost instance of `KernelLib.seq` used throughout.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-! ## Flipping the sign glyph of the top value -/

/-- `magHead l` replaces the first glyph of `l` by `pos` when it is `neg`. -/
def magHead (l : List HvdH.Glyph) : List HvdH.Glyph :=
  (if l.headD .eos = .neg then .pos else l.headD .eos) :: l.tail

/-- Constant-cost program: flip the leading `neg` glyph of stack 0 to `pos`
(leaving every other stack and the rest of stack 0 untouched). -/
def magProg : HvdH.Cmd :=
  .seq (.pop 0 0) (.seq (.ite 0 .neg (.set 0 .pos) .skip) (.push 0 0))

/-- Size of an integer value is `isz`. -/
theorem magVszInt (z : ℤ) : HvdH.vsz (HvdH.Val.int z) = HvdH.isz z := by
  simpa [HvdH.vsz] using Work.IntLib.vsz_int z

theorem magHead_append (A B : List HvdH.Glyph) (ha : A ≠ []) :
    magHead (A ++ B) = magHead A ++ B := by
  cases A with
  | nil => exact absurd rfl ha
  | cons c t => rfl

/-- The leading-glyph flip turns the encoding of `int z` into that of `int |z|`. -/
theorem magHead_enc_int (z : ℤ) :
    magHead (HvdH.Val.enc (.int z)) = HvdH.Val.enc (.int (z.natAbs : ℤ)) := by
  by_cases hz : z < 0
  · simp [HvdH.Val.enc, magHead, hz, Int.natAbs_abs]
  · simp [HvdH.Val.enc, magHead, hz, Int.natAbs_abs]

/-- `magProg` runs in 4 steps and only flips the leading glyph of stack 0. -/
theorem magProg_eval (main : HvdH.Cmd) (s : HvdH.State) :
    ∃ s' : HvdH.State, HvdH.Eval main magProg s s' 4 ∧ s'.stk 0 = magHead (s.stk 0) ∧
      ∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = s.stk k := by
  by_cases hb : (s.stk 0).headD Glyph.eos = Glyph.neg
  · rw [List.headD_eq_head?_getD] at hb
    have hreg : (HvdH.State.tPop s 0 0).reg 0 = Glyph.neg := by
      simp [HvdH.State.tPop, hb]
    have h1 : HvdH.Eval main (HvdH.Cmd.pop 0 0) s (HvdH.State.tPop s 0 0) 1 := HvdH.Eval.pop 0 0 s
    have h2 : HvdH.Eval main (HvdH.Cmd.ite 0 Glyph.neg (HvdH.Cmd.set 0 Glyph.pos) HvdH.Cmd.skip)
        (HvdH.State.tPop s 0 0) (HvdH.State.tSet (HvdH.State.tPop s 0 0) 0 Glyph.pos) 2 :=
      HvdH.Eval.iteT hreg (HvdH.Eval.set 0 Glyph.pos _)
    have h3 : HvdH.Eval main (HvdH.Cmd.push 0 0)
        (HvdH.State.tSet (HvdH.State.tPop s 0 0) 0 Glyph.pos)
        (HvdH.State.tPush (HvdH.State.tSet (HvdH.State.tPop s 0 0) 0 Glyph.pos) 0 0) 1 :=
      HvdH.Eval.push 0 0 _
    refine ⟨HvdH.State.tPush (HvdH.State.tSet (HvdH.State.tPop s 0 0) 0 Glyph.pos) 0 0,
      HvdH.Eval.seq h1 (HvdH.Eval.seq h2 h3), ?_, ?_⟩
    · simp [HvdH.State.tPush, HvdH.State.tSet, HvdH.State.tPop, magHead, hb]
    · intro k hk
      simp [HvdH.State.tPush, HvdH.State.tSet, HvdH.State.tPop, hk]
  · rw [List.headD_eq_head?_getD] at hb
    have hreg : (HvdH.State.tPop s 0 0).reg 0 ≠ Glyph.neg := by
      simp [HvdH.State.tPop, hb]
    have h1 : HvdH.Eval main (HvdH.Cmd.pop 0 0) s (HvdH.State.tPop s 0 0) 1 := HvdH.Eval.pop 0 0 s
    have h2 : HvdH.Eval main (HvdH.Cmd.ite 0 Glyph.neg (HvdH.Cmd.set 0 Glyph.pos) HvdH.Cmd.skip)
        (HvdH.State.tPop s 0 0) (HvdH.State.tPop s 0 0) 2 :=
      HvdH.Eval.iteF hreg (HvdH.Eval.skip _)
    have h3 : HvdH.Eval main (HvdH.Cmd.push 0 0)
        (HvdH.State.tPop s 0 0) (HvdH.State.tPush (HvdH.State.tPop s 0 0) 0 0) 1 :=
      HvdH.Eval.push 0 0 _
    refine ⟨HvdH.State.tPush (HvdH.State.tPop s 0 0) 0 0,
      HvdH.Eval.seq h1 (HvdH.Eval.seq h2 h3), ?_, ?_⟩
    · simp [HvdH.State.tPush, HvdH.State.tPop, magHead, hb]
    · intro k hk
      simp [HvdH.State.tPush, HvdH.State.tPop, hk]

/-- Hoare triple of `magProg`: it replaces the top integer value `int z` by `int |z|`. -/
theorem magFlipWord (main : HvdH.Cmd) :
    HvdH.WordR main magProg
      (fun vs => ∃ (z : ℤ) (rest : List HvdH.Val), vs = HvdH.Val.int z :: rest)
      (fun vs out => ∃ (z : ℤ) (rest : List HvdH.Val),
        vs = HvdH.Val.int z :: rest ∧ out = HvdH.Val.int (z.natAbs : ℤ) :: rest)
      (fun _ => 4) := by
  intro vs ⟨z, rest, hvs⟩ s R hR
  obtain ⟨s', hev, hstk0, hoth⟩ := magProg_eval main s
  refine ⟨HvdH.Val.int (z.natAbs : ℤ) :: rest, s', 4, ⟨z, rest, hvs, rfl⟩, hev, le_rfl, ?_, hoth⟩
  rw [hstk0, hR, hvs]
  simp only [Work.Kernel.encs_cons, List.append_assoc]
  rw [magHead_append _ _ (by simp [HvdH.Val.enc]), magHead_enc_int]

/-! ## Constant-cost composition and the swap step -/

/-- `KernelLib.seq`, specialised to constant cost functions and functional posts. -/
theorem magWordComp {main p q : HvdH.Cmd} {P : List HvdH.Val → Prop}
    {Q Q' : List HvdH.Val → Prop} {C B : ℕ}
    (hp : HvdH.WordR main p P (fun _ out => Q out) (fun _ => C))
    (hq : HvdH.WordR main q Q (fun _ out => Q' out) (fun _ => B)) :
    HvdH.WordR main (HvdH.Cmd.seq p q) P (fun _ out => Q' out) (fun _ => C + B) := by
  intro vs hP s R hR
  obtain ⟨mid, s1, n1, hQ, he1, hn1, hs1, ho1⟩ := hp vs hP s R hR
  obtain ⟨out, s2, n2, hQ', he2, hn2, hs2, ho2⟩ := hq mid hQ s1 R hs1
  exact ⟨out, s2, n1 + n2, hQ', HvdH.Eval.seq he1 he2, Nat.add_le_add hn1 hn2, hs2,
    fun k hk => by rw [ho2 k hk, ho1 k hk]⟩

/-- The `KernelLib` swap word, with the two top values named explicitly. -/
theorem magSwapStep {main sw : HvdH.Cmd} {Ksw : ℕ}
    (hsw : ∀ m : HvdH.Cmd, HvdH.WordR m sw (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (HvdH.vsz (vs.getD 0 .nil) + HvdH.vsz (vs.getD 1 .nil) + 1)))
    (u v : HvdH.Val) (rest : List HvdH.Val) :
    HvdH.WordR main sw (fun vs => vs = u :: v :: rest) (fun _ out => out = v :: u :: rest)
      (fun _ => Ksw * (HvdH.vsz u + HvdH.vsz v + 1)) := by
  refine Work.Kernel.WordR_conseq (hsw main) ?_ ?_ ?_
  · intro vs hv; rw [hv]; simp only [List.length_cons]; omega
  · rintro vs out hv ⟨x, y, rst, hxy, hout⟩
    rw [hv] at hxy
    simp only [List.cons.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    subst h1; subst h2; subst h3
    exact hout
  · intro vs hv
    rw [hv]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact le_rfl

/-! ## The word -/

theorem buQWmagWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (a b : ℤ) (R : List HvdH.Val),
      HvdH.WordR main q
        (fun vs => vs = HvdH.Val.int a :: HvdH.Val.int b :: R)
        (fun _ out => out = HvdH.Val.int (a.natAbs : ℤ) :: HvdH.Val.int (b.natAbs : ℤ) :: R)
        (fun _ => K * (a.natAbs.size + b.natAbs.size + 1)) := by
  obtain ⟨sw, Ksw, hsw⟩ := KL.swap
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq sw magProg) (HvdH.Cmd.seq sw magProg), 500 * Ksw + 500, ?_⟩
  intro main a b R
  -- swap: the second value comes to the head
  have hstep1 : HvdH.WordR main sw
      (fun vs => vs = HvdH.Val.int a :: HvdH.Val.int b :: R)
      (fun _ out => out = HvdH.Val.int b :: HvdH.Val.int a :: R)
      (fun _ => Ksw * (HvdH.isz a + HvdH.isz b + 1)) := by
    refine Work.Kernel.WordR_conseq
      (magSwapStep (main := main) (sw := sw) (Ksw := Ksw) hsw (HvdH.Val.int a) (HvdH.Val.int b) R)
      (fun vs h => h) (fun vs out _ h => h) ?_
    intro vs _
    simp only [magVszInt]
    exact le_rfl
  -- flip the (head) second value
  have hstep2 : HvdH.WordR main magProg
      (fun vs => vs = HvdH.Val.int b :: HvdH.Val.int a :: R)
      (fun _ out => out = HvdH.Val.int (b.natAbs : ℤ) :: HvdH.Val.int a :: R)
      (fun _ => 4) := by
    refine Work.Kernel.WordR_conseq (magFlipWord main)
      (fun vs hv => ⟨b, HvdH.Val.int a :: R, hv⟩) ?_ (fun _ _ => le_rfl)
    rintro vs out hv ⟨z, rest, hz, hout⟩
    rw [hv] at hz
    simp only [List.cons.injEq, HvdH.Val.int.injEq] at hz
    obtain ⟨h1, h2⟩ := hz
    subst h1
    rw [← h2] at hout
    exact hout
  -- swap back: the first value is at the head again
  have hstep3 : HvdH.WordR main sw
      (fun vs => vs = HvdH.Val.int (b.natAbs : ℤ) :: HvdH.Val.int a :: R)
      (fun _ out => out = HvdH.Val.int a :: HvdH.Val.int (b.natAbs : ℤ) :: R)
      (fun _ => Ksw * (HvdH.isz b + HvdH.isz a + 1)) := by
    refine Work.Kernel.WordR_conseq
      (magSwapStep (main := main) (sw := sw) (Ksw := Ksw) hsw (HvdH.Val.int (b.natAbs : ℤ))
        (HvdH.Val.int a) R)
      (fun vs h => h) (fun vs out _ h => h) ?_
    intro vs _
    simp only [magVszInt, HvdH.isz]
    exact le_rfl
  -- flip the first value
  have hstep4 : HvdH.WordR main magProg
      (fun vs => vs = HvdH.Val.int a :: HvdH.Val.int (b.natAbs : ℤ) :: R)
      (fun _ out => out = HvdH.Val.int (a.natAbs : ℤ) :: HvdH.Val.int (b.natAbs : ℤ) :: R)
      (fun _ => 4) := by
    refine Work.Kernel.WordR_conseq (magFlipWord main)
      (fun vs hv => ⟨a, HvdH.Val.int (b.natAbs : ℤ) :: R, hv⟩) ?_ (fun _ _ => le_rfl)
    rintro vs out hv ⟨z, rest, hz, hout⟩
    rw [hv] at hz
    simp only [List.cons.injEq, HvdH.Val.int.injEq] at hz
    obtain ⟨h1, h2⟩ := hz
    subst h1
    rw [← h2] at hout
    exact hout
  have hall := magWordComp (magWordComp hstep1 hstep2) (magWordComp hstep3 hstep4)
  refine Work.Kernel.WordR_conseq hall (fun vs h => h) (fun vs out _ h => h) ?_
  intro vs _
  have hcost : (Ksw * (HvdH.isz a + HvdH.isz b + 1) + 4) + (Ksw * (HvdH.isz b + HvdH.isz a + 1) + 4)
      = 2 * Ksw * (a.natAbs.size + b.natAbs.size + 5) + 8 := by
    simp only [HvdH.isz]; ring
  rw [hcost]
  have hsp : a.natAbs.size + b.natAbs.size + 5 ≤ 5 * (a.natAbs.size + b.natAbs.size + 1) := by omega
  have h8 : 8 ≤ 8 * (a.natAbs.size + b.natAbs.size + 5) := by omega
  calc 2 * Ksw * (a.natAbs.size + b.natAbs.size + 5) + 8
      ≤ 2 * Ksw * (a.natAbs.size + b.natAbs.size + 5) +
          8 * (a.natAbs.size + b.natAbs.size + 5) := Nat.add_le_add_left h8 _
    _ = (2 * Ksw + 8) * (a.natAbs.size + b.natAbs.size + 5) := by ring
    _ ≤ (2 * Ksw + 8) * (5 * (a.natAbs.size + b.natAbs.size + 1)) :=
        Nat.mul_le_mul_left _ hsp
    _ = (5 * (2 * Ksw + 8)) * (a.natAbs.size + b.natAbs.size + 1) := by ring
    _ ≤ (500 * Ksw + 500) * (a.natAbs.size + b.natAbs.size + 1) := by
        apply Nat.mul_le_mul_right
        omega

end Work.Resample
