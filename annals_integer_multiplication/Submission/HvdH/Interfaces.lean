import Mathlib
import ChallengeDeps

/-!
# Harvey–van der Hoeven `M(n) = O(n log n)` in Mathlib's TM2 model — lead-owned interfaces

DO NOT EDIT (lead-owned). Definitions and `Prop`s only. Every area proves ONE of the `Prop`s below,
possibly assuming other areas' `Prop`s as hypotheses; `Submission/HvdH/Wiring.lean` composes them
into `theorem_1_1`.

## Layers
* **L0** Mathlib `FinTM2`.
* **L1 StackLang** (`Cmd`, `Eval`): 16 stacks over one finite alphabet `Glyph`, 16 registers, structured
  control, ONE recursive procedure (`Cmd.self` = call the whole program `main` again). Cost = number of
  primitive steps. `CompilerThm` turns a StackLang program into a `TM2ComputableInTime`.
* **L2 value stacks** (`Val`, `WordR`): stack 0 holds a stack of self-delimiting values (`Val.enc`),
  top value first. `WordR main p Pre Post C` = Hoare triple with cost; FRAME built in: raw content `R`
  below the values and all other stacks are unchanged. Everything above L2 is stated with `WordR`.
* **Libraries** `KernelLib`, `IntLib`, `LayoutLib`, `FxLib`: shared words with exact specs and costs.
* **Chapters** (paper arXiv 1903.07227 / HAL hal-02070778): `SynFFTProp` (Prop 3.3), `ConvRProp`
  (Prop 3.4), `TransformProp` (Thm 3.1), `ResMath1DProp` (Prop 4.7(i) + Lemmas 4.5, 4.6),
  `ResampleProp` (Thm 4.1), `ParamsProp` (§5.1), `MainStepProp` (Props 5.2–5.4), `RecursionProp`
  (Cor 5.5 / proof of Thm 1.1), `DFTMathProp` (§2.4 facts), `AssemblyProp` (top-level program).

## Recursion discipline
Programs that need fast multiplication of sub-products call `Cmd.self`. Their specs hold for every
`main` satisfying `MulBelow main N Cm` ("`self` multiplies naturals of bit-size `< N` in cost `Cm`").
The final program is built once, in `AssemblyProp`, and correctness follows by strong induction on `N`.
-/

set_option autoImplicit false

namespace HvdH

open Computability Turing

/-- The dimension parameter of the paper (§5): `d = 1729`. -/
def D : ℕ := 1729

/-! ## L1: StackLang -/

/-- Input symbols of the challenge encoding `encodeProd encodeNat encodeNat`. -/
abbrev InSym := Option Bool × Option Bool

/-- The single finite work alphabet (all 16 stacks). `eos` is what a read of an EMPTY stack returns;
`inp` = raw input symbols; `bit/pos/neg/iend/nil/cons` are used by `Val.enc`; `mk i` are free
markers for library programs (never part of a `Val` encoding). -/
inductive Glyph where
  | eos
  | inp (a b : Option Bool)
  | bit (b : Bool)
  | pos
  | neg
  | iend
  | nil
  | cons
  | mk (i : Fin 16)
  deriving DecidableEq, Fintype, Inhabited

abbrev Stk := Fin 16
abbrev Reg := Fin 16

/-- StackLang commands. `pop k r`/`peek k r` read the top of stack `k` into register `r`
(`eos` if the stack is empty; `pop` then removes it, a no-op on an empty stack); `push k r` pushes the
content of register `r`; `ite r c p q` = if `reg r = c` then `p` else `q`; `loop r c body` = while
`reg r = c` do `body`; `self` = run the whole program `main` (recursion). -/
inductive Cmd where
  | skip
  | pop (k : Stk) (r : Reg)
  | peek (k : Stk) (r : Reg)
  | push (k : Stk) (r : Reg)
  | set (r : Reg) (c : Glyph)
  | mov (dst src : Reg)
  | seq (c₁ c₂ : Cmd)
  | ite (r : Reg) (c : Glyph) (c₁ c₂ : Cmd)
  | loop (r : Reg) (c : Glyph) (body : Cmd)
  | self
  deriving Inhabited

/-- Machine state: registers and stacks (head of the list = top of the stack). -/
structure State where
  reg : Reg → Glyph
  stk : Stk → List Glyph

/-- Big-step semantics with cost. `Eval main c s s' n`: running `c` from `s` ends in `s'` after
cost `n` (1 per primitive, per `ite` test, per `loop` test, per `self` call; `seq` is free). -/
inductive Eval (main : Cmd) : Cmd → State → State → ℕ → Prop
  | skip (s : State) : Eval main .skip s s 1
  | pop (k : Stk) (r : Reg) (s : State) :
      Eval main (.pop k r) s
        ⟨Function.update s.reg r ((s.stk k).headD .eos), Function.update s.stk k (s.stk k).tail⟩ 1
  | peek (k : Stk) (r : Reg) (s : State) :
      Eval main (.peek k r) s ⟨Function.update s.reg r ((s.stk k).headD .eos), s.stk⟩ 1
  | push (k : Stk) (r : Reg) (s : State) :
      Eval main (.push k r) s ⟨s.reg, Function.update s.stk k (s.reg r :: s.stk k)⟩ 1
  | set (r : Reg) (c : Glyph) (s : State) :
      Eval main (.set r c) s ⟨Function.update s.reg r c, s.stk⟩ 1
  | mov (dst src : Reg) (s : State) :
      Eval main (.mov dst src) s ⟨Function.update s.reg dst (s.reg src), s.stk⟩ 1
  | seq {c₁ c₂ : Cmd} {s₁ s₂ s₃ : State} {n₁ n₂ : ℕ} :
      Eval main c₁ s₁ s₂ n₁ → Eval main c₂ s₂ s₃ n₂ → Eval main (.seq c₁ c₂) s₁ s₃ (n₁ + n₂)
  | iteT {r : Reg} {c : Glyph} {c₁ c₂ : Cmd} {s s' : State} {n : ℕ} :
      s.reg r = c → Eval main c₁ s s' n → Eval main (.ite r c c₁ c₂) s s' (n + 1)
  | iteF {r : Reg} {c : Glyph} {c₁ c₂ : Cmd} {s s' : State} {n : ℕ} :
      s.reg r ≠ c → Eval main c₂ s s' n → Eval main (.ite r c c₁ c₂) s s' (n + 1)
  | loopF {r : Reg} {c : Glyph} {body : Cmd} {s : State} :
      s.reg r ≠ c → Eval main (.loop r c body) s s 1
  | loopT {r : Reg} {c : Glyph} {body : Cmd} {s s' s'' : State} {n m : ℕ} :
      s.reg r = c → Eval main body s s' n → Eval main (.loop r c body) s' s'' m →
      Eval main (.loop r c body) s s'' (n + m + 1)
  | self {s s' : State} {n : ℕ} : Eval main main s s' n → Eval main .self s s' (n + 1)

/-- Glyph of an input symbol. -/
def inpGlyph (a : InSym) : Glyph := .inp a.1 a.2

/-- Initial state for input word `w`: stack 0 = `w` (first letter on top), all else empty,
registers `eos`. -/
def initState (w : List InSym) : State :=
  ⟨fun _ => .eos, fun k => if k = 0 then w.map inpGlyph else []⟩

/-- `P` (run as its own `main`) maps input `w` to output `out` within `bound`: at the end stack 1 is
`out` (first bit on top) and every other stack is empty (registers arbitrary). -/
def RunsWithin (P : Cmd) (w : List InSym) (out : List Bool) (bound : ℕ) : Prop :=
  ∃ (s' : State) (n : ℕ), Eval P P (initState w) s' n ∧ n ≤ bound ∧
    ∀ k : Stk, s'.stk k = if k = 1 then out.map Glyph.bit else []

/-- **Area Compiler.** StackLang compiles to `FinTM2` with linear overhead. -/
def CompilerThm : Prop :=
  ∀ {α : Type} (ea : α → List InSym) (f : α → List Bool) (P : Cmd) (cost : ℕ → ℕ),
    (∀ a, RunsWithin P (ea a) (f a) (cost (ea a).length)) →
    ∃ T : TM2ComputableInTime ea id f, ∃ c : ℕ, ∀ n, T.time n ≤ c * (cost n + n + 1)

/-! ## L2: values on stack 0 -/

/-- Self-delimiting values. Lists are `cons`-chains ending in `nil` (see `ofList`). -/
inductive Val where
  | int (z : ℤ)
  | nil
  | cons (a b : Val)
  deriving DecidableEq, Inhabited

/-- Encoding (first symbol = top of stack): an integer is its sign glyph, the bits of `|z|`
least significant first (`encodeNat`, no leading zeros), then `iend`. -/
def Val.enc : Val → List Glyph
  | .int z => (if z < 0 then Glyph.neg else Glyph.pos) :: ((encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend])
  | .nil => [Glyph.nil]
  | .cons a b => Glyph.cons :: (a.enc ++ b.enc)

/-- Size of a value = length of its encoding. -/
def vsz (v : Val) : ℕ := v.enc.length

/-- Size of an integer value: `vsz (.int z) = isz z`. -/
def isz (z : ℤ) : ℕ := z.natAbs.size + 2

/-- Encoding of a stack of values (head = top). -/
def encs (vs : List Val) : List Glyph := (vs.map Val.enc).flatten

def ofList (l : List Val) : Val := l.foldr Val.cons Val.nil

def intList (l : List ℕ) : Val := ofList (l.map fun n => Val.int n)

/-- Hoare triple with cost on the value stack. For every value stack `vs` with `Pre vs`, every
state whose stack 0 is `encs vs ++ R`: `p` terminates with cost `≤ C vs`, stack 0 becomes
`encs out ++ R` for some `out` with `Post vs out`, and all other stacks are restored.
Registers are unconstrained before and after. -/
def WordR (main p : Cmd) (Pre : List Val → Prop) (Post : List Val → List Val → Prop)
    (C : List Val → ℕ) : Prop :=
  ∀ vs, Pre vs → ∀ (s : State) (R : List Glyph), s.stk 0 = encs vs ++ R →
    ∃ (out : List Val) (s' : State) (n : ℕ), Post vs out ∧ Eval main p s s' n ∧ n ≤ C vs ∧
      s'.stk 0 = encs out ++ R ∧ ∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k

/-! ## Self-multiplication hypothesis -/

def mulPre (N : ℕ) (vs : List Val) : Prop :=
  ∃ (x y : ℕ) (rest : List Val), vs = .int x :: .int y :: rest ∧ x.size < N ∧ y.size < N

def mulPost (vs out : List Val) : Prop :=
  ∃ (x y : ℕ) (rest : List Val), vs = .int x :: .int y :: rest ∧ out = .int (x * y : ℕ) :: rest

/-- The paper's `n` for a multiplication call: max bit-size of the two operands. -/
def mulSize : List Val → ℕ
  | .int x :: .int y :: _ => max x.natAbs.size y.natAbs.size
  | _ => 0

/-- `self` multiplies two naturals on top of the value stack (replacing them by the product), when
both have bit-size `< N`, at cost `≤ Cm (max bit-size)`. -/
def MulBelow (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ) : Prop :=
  WordR main .self (mulPre N) mulPost (fun vs => Cm (mulSize vs))

/-! ## KernelLib: generic value-stack words (area Kernel) -/

/-- Generic words and laws. Costs: `K` is a uniform constant (independent of `main`, the values
and the static parameters). -/
structure KernelLib : Prop where
  seq : ∀ (main p q : Cmd) (P : List Val → Prop) (Q : List Val → List Val → Prop) (C : List Val → ℕ)
      (P' : List Val → Prop) (Q' : List Val → List Val → Prop) (C' B : List Val → ℕ),
      WordR main p P Q C → WordR main q P' Q' C' →
      (∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ B vs) →
      WordR main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out) (fun vs => C vs + B vs)
  conseq : ∀ (main p : Cmd) (P P' : List Val → Prop) (Q Q' : List Val → List Val → Prop)
      (C C' : List Val → ℕ),
      WordR main p P Q C → (∀ vs, P' vs → P vs) → (∀ vs out, P' vs → Q vs out → Q' vs out) →
      (∀ vs, P' vs → C vs ≤ C' vs) → WordR main p P' Q' C'
  skip : ∀ main : Cmd, WordR main .skip (fun _ => True) (fun vs out => out = vs) (fun _ => 1)
  selfLaw : ∀ (main : Cmd) (P : List Val → Prop) (Q : List Val → List Val → Prop) (C : List Val → ℕ),
      WordR main main P Q C → WordR main .self P Q (fun vs => C vs + 1)
  dup : ∃ (prog : Cmd) (K : ℕ), ∀ main : Cmd, WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))
  drop : ∃ (prog : Cmd) (K : ℕ), ∀ main : Cmd, WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))
  swap : ∃ (prog : Cmd) (K : ℕ), ∀ main : Cmd, WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
  /-- copy the `k`-th value (0 = top) to the top -/
  pick : ∃ (prog : ℕ → Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ), WordR main (prog k)
      (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))
  /-- move the `k`-th value (0 = top) to the top -/
  roll : ∃ (prog : ℕ → Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ), WordR main (prog k)
      (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))
  /-- push a constant value -/
  pushVal : ∃ (prog : Val → Cmd) (K : ℕ), ∀ (main : Cmd) (v : Val), WordR main (prog v)
      (fun _ => True) (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))
  consV : ∃ (prog : Cmd) (K : ℕ), ∀ main : Cmd, WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K)
  unconsV : ∃ (prog : Cmd) (K : ℕ), ∀ main : Cmd, WordR main prog
      (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K)
  /-- consume `int z`; run `q₁` if `z = 0`, else `q₂` -/
  ifZero : ∃ (comb : Cmd → Cmd → Cmd) (K : ℕ), ∀ (main q₁ q₂ : Cmd) (z : ℤ) (rest : List Val)
      (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ),
      (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
      (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
      WordR main (comb q₁ q₂) (fun vs => vs = .int z :: rest)
        (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => K * (isz z + 1) + max c₁ c₂)
  /-- if the top value is `nil`, drop it and run `q₁`; otherwise run `q₂` (top value kept) -/
  ifNil : ∃ (comb : Cmd → Cmd → Cmd) (K : ℕ), ∀ (main q₁ q₂ : Cmd) (v : Val) (rest : List Val)
      (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ),
      (v = .nil → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
      (v ≠ .nil → WordR main q₂ (fun vs => vs = v :: rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
      WordR main (comb q₁ q₂) (fun vs => vs = v :: rest)
        (fun _ out => (v = .nil → Q₁ out) ∧ (v ≠ .nil → Q₂ out)) (fun _ => K + max c₁ c₂)
  /-- map `q` over a list; `q` sees `x :: rest` (so it can read parameters in `rest`) -/
  mapList : ∃ (comb : Cmd → Cmd) (K : ℕ), ∀ (main q : Cmd) (rest : List Val) (P : Val → Prop)
      (Q : Val → Val → Prop) (c L : ℕ),
      (∀ x, P x → WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) →
      ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) →
      WordR main (comb q) (fun vs => vs = ofList xs :: rest)
        (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys)
        (fun _ => xs.length * (c + K * (L + 1)) + K)
  /-- zip two lists of equal length with `q`; `q` sees `x :: y :: rest` -/
  zipWith : ∃ (comb : Cmd → Cmd) (K : ℕ), ∀ (main q : Cmd) (rest : List Val) (P : Val → Val → Prop)
      (Q : Val → Val → Val → Prop) (c L : ℕ),
      (∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest)
        (fun _ out => ∃ z, out = z :: rest ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c)) →
      ∀ xs ys : List Val, xs.length = ys.length →
      (∀ i < xs.length, P (xs.getD i .nil) (ys.getD i .nil)) → (∀ x ∈ xs ++ ys, vsz x ≤ L) →
      WordR main (comb q) (fun vs => vs = ofList xs :: ofList ys :: rest)
        (fun _ out => ∃ zs, out = ofList zs :: rest ∧ zs.length = xs.length ∧
          ∀ i < xs.length, Q (xs.getD i .nil) (ys.getD i .nil) (zs.getD i .nil))
        (fun _ => xs.length * (c + K * (L + 1)) + K)
  /-- left fold: `q` sees `xᵢ :: acc` and leaves the new accumulator stack -/
  foldList : ∃ (comb : Cmd → Cmd) (K : ℕ), ∀ (main q : Cmd) (xs : List Val)
      (I : ℕ → List Val → Prop) (c L : ℕ),
      (∀ x ∈ xs, vsz x ≤ L) →
      (∀ i acc, i < xs.length → I i acc → WordR main q (fun vs => vs = xs.getD i .nil :: acc)
        (fun _ out => I (i + 1) out) (fun _ => c)) →
      WordR main (comb q) (fun vs => ∃ acc, vs = ofList xs :: acc ∧ I 0 acc)
        (fun _ out => I xs.length out) (fun _ => xs.length * (c + K * (L + 1)) + K)
  /-- do-while: run `q`, which pushes a flag `int 0` (stop) or `int 1` (continue); round `i` may only
  continue if `i + 1 < m`, so at most `max m 1` rounds (bound `(m+1)(c+K)+K`, true also at `m = 0`;
  v1 had `m*(c+K)+K`, refuted at `m = 0` by `Work.Kernel.loopField_false`) -/
  loop : ∃ (comb : Cmd → Cmd) (K : ℕ), ∀ (main q : Cmd) (I : ℕ → List Val → Prop)
      (F : List Val → Prop) (c m : ℕ),
      (∀ i vs, I i vs → WordR main q (fun w => w = vs)
        (fun _ out => ∃ vs', (out = .int 0 :: vs' ∧ F vs') ∨
          (out = .int 1 :: vs' ∧ I (i + 1) vs' ∧ i + 1 < m)) (fun _ => c)) →
      WordR main (comb q) (I 0) (fun _ out => F out) (fun _ => (m + 1) * (c + K) + K)

/-! ## IntLib: integer arithmetic words (area IntLib) -/

def binCost (C : ℤ → ℤ → ℕ) : List Val → ℕ
  | .int a :: .int b :: _ => C a b
  | _ => 0

def unCost (C : ℤ → ℕ) : List Val → ℕ
  | .int a :: _ => C a
  | _ => 0

/-- `int a :: int b :: rest ↦ int (f a b) :: rest` (top = `a`) when `P a b`, cost `≤ C a b`. -/
def BinOp (main p : Cmd) (P : ℤ → ℤ → Prop) (f : ℤ → ℤ → ℤ) (C : ℤ → ℤ → ℕ) : Prop :=
  WordR main p (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ P a b)
    (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (f a b) :: rest) (binCost C)

/-- `int a :: rest ↦ int (f a) :: rest` when `P a`, cost `≤ C a`. -/
def UnOp (main p : Cmd) (P : ℤ → Prop) (f : ℤ → ℤ) (C : ℤ → ℕ) : Prop :=
  WordR main p (fun vs => ∃ a rest, vs = .int a :: rest ∧ P a)
    (fun vs out => ∃ a rest, vs = .int a :: rest ∧ out = .int (f a) :: rest) (unCost C)

/-- `chunks x b N` = the `N` base-`2^b` digits of `x`, least significant first. -/
def chunks (x b N : ℕ) : List ℕ := (List.range N).map fun j => x / 2 ^ (b * j) % 2 ^ b

/-- `Σ_j hs[j]·2^{b j}` (overlap-add evaluation). -/
def evalChunks (hs : List ℕ) (b : ℕ) : ℕ :=
  ((List.range hs.length).map fun j => hs.getD j 0 * 2 ^ (b * j)).sum

structure IntLib : Prop where
  add : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True) (· + ·) (fun a b => K * (isz a + isz b))
  sub : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True) (· - ·) (fun a b => K * (isz a + isz b))
  neg : ∃ (p : Cmd) (K : ℕ), ∀ main, UnOp main p (fun _ => True) (fun a => -a) (fun a => K * isz a)
  max : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True) max (fun a b => K * (isz a + isz b))
  /-- `1` if `a < b` else `0` -/
  lt : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True) (fun a b => if a < b then 1 else 0)
    (fun a b => K * (isz a + isz b))
  eq : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True) (fun a b => if a = b then 1 else 0)
    (fun a b => K * (isz a + isz b))
  /-- schoolbook product -/
  mulS : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True) (· * ·) (fun a b => K * isz a * isz b)
  tdiv : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ b => b ≠ 0) Int.tdiv (fun a b => K * isz a * isz b)
  tmod : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ b => b ≠ 0) Int.tmod (fun a b => K * isz a * isz b)
  /-- floor division / nonnegative remainder by a positive divisor -/
  fdiv : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ b => 0 < b) Int.fdiv (fun a b => K * isz a * isz b)
  fmod : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ b => 0 < b) Int.fmod (fun a b => K * isz a * isz b)
  /-- `a · 2^k` -/
  shl : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ k => 0 ≤ k) (fun a k => a * 2 ^ k.toNat)
    (fun a k => K * (isz a + k.toNat + isz k))
  /-- `a / 2^k` rounded toward zero -/
  shrT : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ k => 0 ≤ k)
    (fun a k => Int.tdiv a (2 ^ k.toNat)) (fun a k => K * (isz a + isz k))
  /-- `a / 2^k` rounded toward `-∞` -/
  shrF : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ k => 0 ≤ k)
    (fun a k => Int.fdiv a (2 ^ k.toNat)) (fun a k => K * (isz a + isz k))
  /-- bit-size of `|a|` -/
  size : ∃ (p : Cmd) (K : ℕ), ∀ main, UnOp main p (fun _ => True) (fun a => (a.natAbs.size : ℤ))
    (fun a => K * isz a)
  sqrt : ∃ (p : Cmd) (K : ℕ), ∀ main, UnOp main p (fun a => 0 ≤ a) (fun a => (Nat.sqrt a.toNat : ℤ))
    (fun a => K * isz a ^ 2)
  clog2 : ∃ (p : Cmd) (K : ℕ), ∀ main, UnOp main p (fun a => 0 ≤ a) (fun a => (Nat.clog 2 a.toNat : ℤ))
    (fun a => K * isz a)
  pow2 : ∃ (p : Cmd) (K : ℕ), ∀ main, UnOp main p (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat)
    (fun k => K * (k.toNat + isz k))
  gcd : ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True) (fun a b => (Int.gcd a b : ℤ))
    (fun a b => K * (isz a + isz b) ^ 2)
  /-- split `x < 2^{bN}` into `N` chunks of `b` bits -/
  chunk : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (x b N : ℕ), 1 ≤ b → x < 2 ^ (b * N) →
    WordR main p (fun vs => ∃ rest, vs = .int x :: .int b :: .int N :: rest)
      (fun vs out => ∃ rest, vs = .int x :: .int b :: .int N :: rest ∧ out = intList (chunks x b N) :: rest)
      (fun _ => K * (isz x + N * (b + 1) + isz b + isz N))
  /-- overlap-add: `intList hs :: int b :: rest ↦ int (Σ hs[j] 2^{bj}) :: rest` -/
  evalPoly : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (hs : List ℕ) (b : ℕ), 1 ≤ b → (∀ h ∈ hs, h < 2 ^ (3 * b)) →
    WordR main p (fun vs => ∃ rest, vs = intList hs :: .int b :: rest)
      (fun vs out => ∃ rest, vs = intList hs :: .int b :: rest ∧ out = .int (evalChunks hs b) :: rest)
      (fun _ => K * ((hs.map fun h => isz h).sum + hs.length * (b + 1) + isz b + 1))
  /-- top level: raw input (and nothing below it) to `int x :: int y` -/
  parse : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (x y : ℕ) (s : State),
    s.stk 0 = (IntegerMultiplication.encodeProd encodeNat encodeNat (x, y)).map inpGlyph →
    ∃ (s' : State) (n : ℕ), Eval main prog s s' n ∧
      n ≤ K * ((IntegerMultiplication.encodeProd encodeNat encodeNat (x, y)).length + 1) ∧
      s'.stk 0 = encs [.int x, .int y] ∧ ∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k
  /-- top level: `int z` (alone on stack 0, stack 1 empty) to the output bits on stack 1 -/
  emit : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (z : ℕ) (s : State),
    s.stk 0 = (Val.int z).enc → s.stk 1 = [] →
    ∃ (s' : State) (n : ℕ), Eval main prog s s' n ∧ n ≤ K * (z.size + 1) ∧ s'.stk 0 = [] ∧
      s'.stk 1 = (encodeNat z).map Glyph.bit ∧ ∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k

/-! ## LayoutLib: list / array words (area Layout) -/

/-- The `i`-slices of a flat array of shape `A × m × B` (lexicographic, last index fastest):
slice `s = a*B + b` is `j ↦ es[(a*m + j)*B + b]`, `j < m`. -/
def slices {α : Type} [Inhabited α] (A m B : ℕ) (es : List α) : List (List α) :=
  (List.range (A * B)).map fun s => (List.range m).map fun j => es.getD ((s / B * m + j) * B + s % B) default

/-- Inverse of `slices` for output slices of length `n`: shape `A × n × B`. -/
def unslices {α : Type} [Inhabited α] (A n B : ℕ) (outs : List (List α)) : List α :=
  (List.range (A * n * B)).map fun idx =>
    (outs.getD (idx / (n * B) * B + idx % B) []).getD (idx / B % n) default

def pairKey : Val → ℤ
  | .cons (.int k) _ => k
  | _ => 0

structure LayoutLib : Prop where
  length : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = .int xs.length :: ofList xs :: rest)
    (fun _ => K * (vsz (ofList xs) + 1))
  reverse : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
    (fun _ => K * (vsz (ofList xs) + 1))
  append : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs ys : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: ofList ys :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: ofList ys :: rest ∧ out = ofList (xs ++ ys) :: rest)
    (fun _ => K * (vsz (ofList xs) + 1))
  take : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
    (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.take k) :: rest)
    (fun _ => K * (vsz (ofList xs) + isz k + 1))
  drop : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
    (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.drop k) :: rest)
    (fun _ => K * (vsz (ofList xs) + isz k + 1))
  replicate : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ) (v : Val), WordR main p
    (fun vs => ∃ rest, vs = .int k :: v :: rest)
    (fun vs out => ∃ rest, vs = .int k :: v :: rest ∧ out = ofList (List.replicate k v) :: rest)
    (fun _ => K * ((k + 1) * (vsz v + 1) + isz k + 1))
  flatten : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xss : List (List Val)), WordR main p
    (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
    (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧ out = ofList xss.flatten :: rest)
    (fun _ => K * (vsz (ofList (xss.map ofList)) + 1))
  /-- cut a list into consecutive chunks of length `m ≥ 1` (`m ∣ length`) -/
  chunksOf : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (m : ℕ) (xs : List Val), 1 ≤ m → m ∣ xs.length →
    WordR main p (fun vs => ∃ rest, vs = .int m :: ofList xs :: rest)
    (fun vs out => ∃ rest, vs = .int m :: ofList xs :: rest ∧
      out = ofList ((List.range (xs.length / m)).map fun i => ofList ((xs.drop (i * m)).take m)) :: rest)
    (fun _ => K * (vsz (ofList xs) + (xs.length / m + 1) * isz m + 1))
  /-- label every element with its index: `xs[i] ↦ cons (int i) xs[i]` -/
  enumerate : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
      out = ofList ((List.range xs.length).map fun i : ℕ => Val.cons (.int (i : ℤ)) (xs.getD i .nil)) :: rest)
    (fun _ => K * (vsz (ofList xs) + xs.length * (xs.length.size + 1) + 1))
  /-- stable-free sort of `cons (int key) payload` records with distinct natural keys -/
  sortByKey : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val),
    (∀ x ∈ xs, ∃ (k : ℕ) (v : Val), x = .cons (.int k) v) → (xs.map pairKey).Nodup →
    WordR main p (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest ys, vs = ofList xs :: rest ∧ out = ofList ys :: rest ∧ ys.Perm xs ∧
        ys.Pairwise fun a b => pairKey a < pairKey b)
      (fun _ => K * (vsz (ofList xs) + 1) * (xs.length.size + 1))
  /-- apply the 1-D word `q` (lists of length `m` ↦ lists of length `n`) to every `i`-slice of a
  flat `A × m × B` array (paper Lemma 2.11). `q` sees `ofList slice :: rest`. -/
  applyAlong : ∃ (comb : Cmd → Cmd) (K : ℕ), ∀ (main q : Cmd) (rest : List Val) (m n : ℕ)
      (P : List Val → Prop) (Q : List Val → List Val → Prop) (c L : ℕ),
      (∀ sl : List Val, sl.length = m → P sl → WordR main q (fun vs => vs = ofList sl :: rest)
        (fun _ out => ∃ ol, out = ofList ol :: rest ∧ ol.length = n ∧ Q sl ol ∧ ∀ y ∈ ol, vsz y ≤ L)
        (fun _ => c)) →
      ∀ (A B : ℕ) (es : List Val), es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      (∀ s < A * B, P ((slices A m B es).getD s [])) →
      WordR main (comb q) (fun vs => vs = .int A :: .int m :: .int n :: .int B :: ofList es :: rest)
        (fun _ out => ∃ outs : List (List Val), out = ofList (unslices A n B outs) :: rest ∧
          outs.length = A * B ∧ ∀ s < A * B, (outs.getD s []).length = n ∧
            Q ((slices A m B es).getD s []) (outs.getD s []))
        (fun _ => A * B * c +
          K * (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1) *
            ((A * B * (m + n + 1)).size + 1) + K * (isz A + isz m + isz n + isz B))

/-! ## Fixed-point complex numbers (paper §2.2) -/

/-- The complex number `2^{-p} (x + i y)` represented by `z = (x, y)`. -/
noncomputable def fxC (p : ℕ) (z : ℤ × ℤ) : ℂ := ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / (2 : ℂ) ^ p

/-- `z ∈ C̃◦`: `x² + y² ≤ 2^{2p}`. -/
def inDisc (p : ℕ) (z : ℤ × ℤ) : Prop := z.1 ^ 2 + z.2 ^ 2 ≤ 4 ^ p

def cfxVal (z : ℤ × ℤ) : Val := .cons (.int z.1) (.int z.2)

/-- A vector of fixed-point complex numbers (flat lexicographic layout for arrays). -/
def cvecVal (zs : List (ℤ × ℤ)) : Val := ofList (zs.map cfxVal)

/-- An array of elements of `ℝ = ℂ[y]/(y^r+1)`, each a coefficient vector of length `r`. -/
def rarrVal (ws : List (List (ℤ × ℤ))) : Val := ofList (ws.map cvecVal)

noncomputable def fxVec (p n : ℕ) (zs : List (ℤ × ℤ)) : Fin n → ℂ := fun i => fxC p (zs.getD i (0, 0))

noncomputable def fxArr (p M r : ℕ) (ws : List (List (ℤ × ℤ))) : Fin M → Fin r → ℂ :=
  fun i j => fxC p ((ws.getD i []).getD j (0, 0))

/-- `zs` is a fixed-point vector in `C̃◦ⁿ`. -/
def InDiscVec (p n : ℕ) (zs : List (ℤ × ℤ)) : Prop := zs.length = n ∧ ∀ z ∈ zs, inDisc p z

def InDiscArr (p M r : ℕ) (ws : List (List (ℤ × ℤ))) : Prop :=
  ws.length = M ∧ ∀ w ∈ ws, InDiscVec p r w

/-- `zs ∈ C̃◦ⁿ` approximates `v` with error `ε < e` (paper: `ε(ṽ) = 2^p ‖ṽ - v‖ < e`). -/
def Approx (p : ℕ) {n : ℕ} (zs : List (ℤ × ℤ)) (v : Fin n → ℂ) (e : ℝ) : Prop :=
  InDiscVec p n zs ∧ ∀ i : Fin n, (2 : ℝ) ^ p * ‖fxC p (zs.getD i (0, 0)) - v i‖ < e

def ApproxR (p : ℕ) {M r : ℕ} (ws : List (List (ℤ × ℤ))) (v : Fin M → Fin r → ℂ) (e : ℝ) : Prop :=
  InDiscArr p M r ws ∧ ∀ (i : Fin M) (j : Fin r),
    (2 : ℝ) ^ p * ‖fxC p ((ws.getD i []).getD j (0, 0)) - v i j‖ < e

/-! ## FxLib: fixed-point complex words (area Fx; paper Lemmas 2.1, 2.2, 2.4, 2.12–2.14) -/

structure FxLib : Prop where
  /-- Lemma 2.1: `(u+v)/2` with error `< 1` -/
  addHalf : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), WordR main prog
    (fun vs => ∃ u v rest, vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (fun vs out => ∃ u v rest w, vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - (fxC p u + fxC p v) / 2‖ < 1)
    (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil)))
  /-- Lemma 2.1: `(u-v)/2` (top minus second) with error `< 1` -/
  subHalf : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), WordR main prog
    (fun vs => ∃ u v rest, vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (fun vs out => ∃ u v rest w, vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - (fxC p u - fxC p v) / 2‖ < 1)
    (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil)))
  /-- Lemma 2.4 with schoolbook products -/
  mulS : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), WordR main prog
    (fun vs => ∃ u v rest, vs = .int p :: cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (fun vs out => ∃ u v rest w, vs = .int p :: cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - fxC p u * fxC p v‖ < 2)
    (fun _ => K * (p + 1) ^ 2)
  /-- Lemma 2.4 with the four real products done by `self` -/
  mulF : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p : ℕ), Monotone Cm →
    MulBelow main N Cm → p + 2 < N → WordR main prog
    (fun vs => ∃ u v rest, vs = .int p :: cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (fun vs out => ∃ u v rest w, vs = .int p :: cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - fxC p u * fxC p v‖ < 2)
    (fun _ => 4 * Cm (p + 2) + K * (p + 1))
  /-- Lemma 2.2 (scaling by an integer `1 ≤ c ≤ 2^p`), stated for every true value `x` with
  `c‖x‖ ≤ 1` -/
  scale : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p c : ℕ), 1 ≤ c → c ≤ 2 ^ p → WordR main prog
    (fun vs => ∃ u rest, vs = .int p :: .int c :: cfxVal u :: rest ∧ inDisc p u)
    (fun vs out => ∃ u rest v, vs = .int p :: .int c :: cfxVal u :: rest ∧ out = cfxVal v :: rest ∧
      inDisc p v ∧ ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
        (2 : ℝ) ^ p * ‖fxC p v - (c : ℂ) * x‖ < 2 * c * ((2 : ℝ) ^ p * ‖fxC p u - x‖) + 3)
    (fun _ => K * (p + 1) ^ 2)
  /-- Lemma 2.12: `e^{2πi j/k}` with error `< 2`; cost polynomial -/
  cis : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ) (j : ℤ) (k : ℕ), 100 ≤ p → 1 ≤ k →
    WordR main prog (fun vs => ∃ rest, vs = .int p :: .int j :: .int k :: rest)
    (fun vs out => ∃ rest w, vs = .int p :: .int j :: .int k :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - Complex.exp (2 * Real.pi * Complex.I * j / k)‖ < 2)
    (fun _ => K * (p + isz j + isz k) ^ K)
  /-- Lemma 2.13: `e^{-π j/k}` (`j ≥ 0`) with error `< 2` -/
  expNeg : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p j k : ℕ), 100 ≤ p → 1 ≤ k →
    WordR main prog (fun vs => ∃ rest, vs = .int p :: .int j :: .int k :: rest)
    (fun vs out => ∃ rest w, vs = .int p :: .int j :: .int k :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2)
    (fun _ => K * (p + isz j + isz k) ^ K)
  /-- Lemma 2.14: `2^{-σ} e^{π j/k}` when `e^{πj/k} ≤ 2^σ`, `σ ≤ 2p`, with error `< 2` -/
  expPos : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p j k σ : ℕ), 100 ≤ p → 1 ≤ k →
    Real.exp (Real.pi * j / k) ≤ 2 ^ σ → σ ≤ 2 * p →
    WordR main prog (fun vs => ∃ rest, vs = .int p :: .int j :: .int k :: .int σ :: rest)
    (fun vs out => ∃ rest w, vs = .int p :: .int j :: .int k :: .int σ :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧
      (2 : ℝ) ^ p * ‖fxC p w - (((2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * j / k) : ℝ) : ℂ)‖ < 2)
    (fun _ => K * (p + isz j + isz k + isz σ) ^ K)

/-! ## DFTs (paper §2.4) on flat lexicographic arrays -/

/-- Mixed-radix digits `(j₁,…,j_d)` of a flat lexicographic index (last index fastest). -/
def digits : List ℕ → ℕ → List ℕ
  | [], _ => []
  | t :: ts, m => (m / ts.prod) % t :: digits ts (m % ts.prod)

def undigits : List ℕ → List ℕ → ℕ
  | _ :: ts, j :: js => j * ts.prod + undigits ts js
  | _, _ => 0

/-- `Σ_i jᵢ kᵢ / tᵢ` -/
noncomputable def phase : List ℕ → List ℕ → List ℕ → ℝ
  | t :: ts, j :: js, k :: ks => ((j * k : ℕ) : ℝ) / t + phase ts js ks
  | _, _, _ => 0

/-- Normalised multidimensional DFT: `(F u)_j = (1/T) Σ_k exp(sgn·2πi Σ jᵢkᵢ/tᵢ) u_k`.
`sgn = -1` is the paper's `F_{t₁,…,t_d}`; `sgn = 1` is `F*`. -/
noncomputable def dftMulti (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → ℂ) : Fin ts.prod → ℂ :=
  fun j => (1 / (ts.prod : ℂ)) * ∑ k : Fin ts.prod,
    Complex.exp ((sgn : ℂ) * 2 * Real.pi * Complex.I * (phase ts (digits ts j) (digits ts k) : ℂ)) * u k

/-- 1-D normalised DFT matrix `(F_n)_{jk} = (1/n) e^{-2πi jk/n}`. -/
noncomputable def dftMat (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => (1 / (n : ℂ)) * Complex.exp (-2 * Real.pi * Complex.I * ((j * k : ℕ) : ℂ) / n)

/-- read a vector at a natural index (0 outside) -/
def vget {n : ℕ} (u : Fin n → ℂ) (i : ℕ) : ℂ := if h : i < n then u ⟨i, h⟩ else 0

def subDigits : List ℕ → List ℕ → List ℕ → List ℕ
  | t :: ts, j :: js, k :: ks => (j + t - k) % t :: subDigits ts js ks
  | _, _, _ => []

/-- flat index of the multi-index `j - k` (componentwise mod `tᵢ`) -/
def subIdx (ts : List ℕ) (j k : ℕ) : ℕ := undigits ts (subDigits ts (digits ts j) (digits ts k))

/-- Normalised multidimensional cyclic convolution `(1/T) u ∗ v` over `ℂ`. -/
noncomputable def convC (ts : List ℕ) (u v : Fin ts.prod → ℂ) : Fin ts.prod → ℂ :=
  fun j => (1 / (ts.prod : ℂ)) * ∑ k : Fin ts.prod, u k * vget v (subIdx ts j k)

/-- **Area DFTMath.** Basic facts (paper §2.4, (2.1), Example 2.6). -/
def DFTMathProp : Prop :=
  ∀ ts : List ℕ, (∀ t ∈ ts, 0 < t) →
    (∀ (sgn : ℤ) (u : Fin ts.prod → ℂ), ‖dftMulti ts sgn u‖ ≤ ‖u‖) ∧
    (∀ (sgn : ℤ) (a : ℂ) (u v : Fin ts.prod → ℂ),
      dftMulti ts sgn (a • u + v) = a • dftMulti ts sgn u + dftMulti ts sgn v) ∧
    (∀ u : Fin ts.prod → ℂ, dftMulti ts 1 (dftMulti ts (-1) u) = (1 / (ts.prod : ℂ)) • u) ∧
    (∀ u v : Fin ts.prod → ℂ,
      convC ts u v = (ts.prod : ℂ) • dftMulti ts 1 (dftMulti ts (-1) u * dftMulti ts (-1) v))

/-! ## The synthetic ring `ℝ = ℂ[y]/(y^r+1)` (paper §2.3, §3) -/

/-- multiplication by `y^e` on coefficient vectors (uses `y^r = -1`) -/
noncomputable def yMul (r : ℕ) (e : ℤ) (a : Fin r → ℂ) : Fin r → ℂ := fun k =>
  let i : ℤ := ((k : ℤ) - e) % (r : ℤ)
  let q : ℤ := (i + e - (k : ℤ)) / (r : ℤ)
  (if Even q then (1 : ℂ) else -1) * vget a i.toNat

/-- product in `ℂ[y]/(y^r+1)` -/
noncomputable def negaMul (r : ℕ) (a b : Fin r → ℂ) : Fin r → ℂ := fun k =>
  ∑ i : Fin r, ∑ j : Fin r,
    if (i : ℕ) + j = k then a i * b j else if (i : ℕ) + j = k + r then -(a i * b j) else 0

def synExp (r : ℕ) : List ℕ → List ℕ → List ℕ → ℤ
  | t :: ts, j :: js, k :: ks => ((2 * r / t * j * k : ℕ) : ℤ) + synExp r ts js ks
  | _, _, _ => 0

/-- Synthetic multidimensional DFT `G_{t₁,…}` (`sgn = -1`) / `G*` (`sgn = 1`) over `ℝ`, with
`ωᵢ = y^{2r/tᵢ}`: `(G u)_j = (1/M) Σ_k y^{sgn Σ (2r/tᵢ) jᵢ kᵢ} u_k`, `M = ∏ tᵢ`. -/
noncomputable def synDFT (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → Fin r → ℂ) :
    Fin ts.prod → Fin r → ℂ :=
  fun j c => (1 / (ts.prod : ℂ)) *
    ∑ k : Fin ts.prod, yMul r (sgn * synExp r ts (digits ts j) (digits ts k)) (u k) c

/-- Normalised convolution over `ℝ`: `(1/(M r)) u ∗ v` (paper `M_ℝ`). -/
noncomputable def convR (r : ℕ) (ts : List ℕ) (u v : Fin ts.prod → Fin r → ℂ) :
    Fin ts.prod → Fin r → ℂ :=
  fun j c => (1 / ((ts.prod * r : ℕ) : ℂ)) * ∑ k : Fin ts.prod,
    negaMul r (u k) (fun c' => if h : subIdx ts j k < ts.prod then v ⟨_, h⟩ c' else 0) c

def IsPow2 (t : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ t = 2 ^ k

/-- Parameters of the synthetic transforms: `D-1` dimensions `tᵢ ∣ 2r`, all powers of two. -/
def SynParams (p r : ℕ) (ts : List ℕ) : Prop :=
  ts.length = D - 1 ∧ IsPow2 r ∧ (∀ t ∈ ts, IsPow2 t ∧ t ∣ 2 * r) ∧ ts.prod * r < 2 ^ p ∧ 100 ≤ p

/-- **Area SynFFT** (paper Lemma 3.2 + Prop 3.3): `G̃` with error `< log₂(M r)`,
cost `O(T p log T)`, `T = M r`. -/
def SynFFTProp : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r : ℕ) (ts : List ℕ) (sgn : ℤ), SynParams p r ts →
    (sgn = 1 ∨ sgn = -1) →
    WordR main prog
      (fun vs => ∃ us rest, vs = .int p :: .int r :: intList ts :: .int sgn :: rarrVal us :: rest ∧
        InDiscArr p ts.prod r us)
      (fun vs out => ∃ us rest ws, vs = .int p :: .int r :: intList ts :: .int sgn :: rarrVal us :: rest ∧
        out = rarrVal ws :: rest ∧
        ApproxR p ws (synDFT r ts sgn (fxArr p ts.prod r us)) (Nat.log 2 (ts.prod * r) : ℝ))
      (fun _ => K * (ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1) + K)

/-- **Area ConvR** (paper Lemma 2.5 + Prop 3.4): `M̃_ℝ` with error `< 3T log₂T + 2T + 3`,
`T = M r`; the `M` pointwise products in `ℝ` use 4 calls of `self` each on `≤ 3rp`-bit integers. -/
def ConvRProp : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm →
    ∀ (p r : ℕ) (ts : List ℕ), SynParams p r ts → 3 * r * p < N →
    WordR main prog
      (fun vs => ∃ us ws rest, vs = .int p :: .int r :: intList ts :: rarrVal us :: rarrVal ws :: rest ∧
        InDiscArr p ts.prod r us ∧ InDiscArr p ts.prod r ws)
      (fun vs out => ∃ us ws rest zs,
        vs = .int p :: .int r :: intList ts :: rarrVal us :: rarrVal ws :: rest ∧ out = rarrVal zs :: rest ∧
        ApproxR p zs (convR r ts (fxArr p ts.prod r us) (fxArr p ts.prod r ws))
          (3 * (ts.prod * r) * Nat.log 2 (ts.prod * r) + 2 * (ts.prod * r) + 3 : ℕ))
      (fun _ => 4 * ts.prod * Cm (3 * r * p) + K * (ts.prod * r) * p ^ 2 + K)

/-- largest entry -/
def lmax (ts : List ℕ) : ℕ := ts.foldr max 0

/-- Parameters of Theorem 3.1: `D` powers of two `2 ≤ t₁ ≤ … ≤ t_D`, `T = ∏ tᵢ < 2^p`. -/
def PowTwoParams (p : ℕ) (ts : List ℕ) : Prop :=
  ts.length = D ∧ (∀ t ∈ ts, IsPow2 t) ∧ ts.Pairwise (· ≤ ·) ∧ ts.prod < 2 ^ p ∧ 100 ≤ p

/-- **Area Transform** (paper Theorem 3.1, with Prop 3.5 and Bluestein): `F̃_{t₁,…,t_D}` with error
`< 8 T log₂ T`, cost `(4T/r) M(3rp) + O(T p²) + O(Σtᵢ · poly p)` (the last term: per-dimension tables). -/
def TransformProp : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm →
    ∀ (p : ℕ) (ts : List ℕ), PowTwoParams p ts → 3 * lmax ts * p < N →
    WordR main prog
      (fun vs => ∃ zs rest, vs = .int p :: intList ts :: cvecVal zs :: rest ∧ InDiscVec p ts.prod zs)
      (fun vs out => ∃ zs rest ws, vs = .int p :: intList ts :: cvecVal zs :: rest ∧
        out = cvecVal ws :: rest ∧
        Approx p ws (dftMulti ts (-1) (fxVec p ts.prod zs)) (8 * ts.prod * Nat.log 2 ts.prod : ℕ))
      (fun _ => 4 * (ts.prod / lmax ts) * Cm (3 * lmax ts * p) + K * ts.prod * p ^ 2 +
        K * ts.sum * (p + 1) ^ K)

/-! ## Gaussian resampling (paper §4) -/

/-- nearest integer, ties up: `[x] = ⌊x + 1/2⌋` -/
noncomputable def rnd (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

/-- `β_ℓ = tℓ/s - [tℓ/s]` -/
noncomputable def betaR (s t ℓ : ℕ) : ℝ := (t * ℓ : ℝ) / s - rnd ((t * ℓ : ℝ) / s)

/-- `S : ℂ^s → ℂ^t`, `(Su)_k = α⁻¹ Σ_{j∈ℤ} e^{-π α⁻² s² (k/t - j/s)²} u_{j mod s}` -/
noncomputable def resSmat (s t α : ℕ) : Matrix (Fin t) (Fin s) ℂ := fun k j =>
  ((1 / (α : ℝ)) * ∑' q : ℤ,
    Real.exp (-Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2 * ((k : ℝ) / t - (j : ℝ) / s - q) ^ 2) : ℝ)

/-- `T : ℂ^s → ℂ^t`, `(Tu)_k = Σ_{j∈ℤ} e^{-π α² t² (k/t - j/s)²} u_{j mod s}` -/
noncomputable def resTmat (s t α : ℕ) : Matrix (Fin t) (Fin s) ℂ := fun k j =>
  ((∑' q : ℤ,
    Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((k : ℝ) / t - (j : ℝ) / s - q) ^ 2)) : ℝ)

/-- `(P_s u)_j = u_{tj mod s}` -/
noncomputable def permS (s t : ℕ) : Matrix (Fin s) (Fin s) ℂ := fun j i => if (i : ℕ) = t * j % s then 1 else 0

/-- `(P_t u)_k = u_{-sk mod t}` -/
noncomputable def permT (s t : ℕ) : Matrix (Fin t) (Fin t) ℂ := fun k i =>
  if (i : ℕ) = (t - s * k % t) % t then 1 else 0

/-- `(C u)_ℓ = u_{[tℓ/s]}` -/
noncomputable def rowSel (s t : ℕ) : Matrix (Fin s) (Fin t) ℂ := fun ℓ i =>
  if (i : ℤ) = rnd ((t * ℓ : ℝ) / s) then 1 else 0

/-- `D = diag(e^{π α² β_ℓ²})` -/
noncomputable def diagD (s t α : ℕ) : Matrix (Fin s) (Fin s) ℂ :=
  Matrix.diagonal fun ℓ => ((Real.exp (Real.pi * (α : ℝ) ^ 2 * betaR s t ℓ ^ 2) : ℝ) : ℂ)

noncomputable def Nmat (s t α : ℕ) : Matrix (Fin s) (Fin s) ℂ := rowSel s t * resTmat s t α * diagD s t α

noncomputable def Emat (s t α : ℕ) : Matrix (Fin s) (Fin s) ℂ := Nmat s t α - 1

noncomputable def Jmat (s t α : ℕ) : Matrix (Fin s) (Fin s) ℂ := (Nmat s t α)⁻¹

/-- `A = S' = S/2` -/
noncomputable def resA (s t α : ℕ) : Matrix (Fin t) (Fin s) ℂ := (1 / 2 : ℂ) • resSmat s t α

/-- `D' = D / 2^{2α²-2}` -/
noncomputable def diagD' (s t α : ℕ) : Matrix (Fin s) (Fin s) ℂ := (1 / (2 : ℂ) ^ (2 * α ^ 2 - 2)) • diagD s t α

/-- `B = P_s⁻¹ D' J' C P_t` with `J' = J/2` (`P_s⁻¹ = P_sᵀ`) -/
noncomputable def resB (s t α : ℕ) : Matrix (Fin s) (Fin t) ℂ :=
  (permS s t).transpose * diagD' s t α * ((1 / 2 : ℂ) • Jmat s t α) * rowSel s t * permT s t

/-- **Area ResMath** (paper Thm 4.2, Lemmas 4.5, 4.6, Prop 4.7(i) and the norm facts used by
Lemmas 4.8–4.12). Norms are sup norms on `Fin _ → ℂ`. -/
def ResMath1DProp : Prop :=
  ∀ (s t α p : ℕ), 2 ≤ s → s < t → Nat.Coprime s t → 2 ≤ α → α ^ 2 < p →
    (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1 →
    dftMat s = (2 : ℂ) ^ (2 * α ^ 2) • (resB s t α * dftMat t * resA s t α) ∧
    (∀ u : Fin s → ℂ, ‖(resA s t α).mulVec u‖ ≤ 3 / 4 * ‖u‖) ∧
    (∀ u : Fin s → ℂ, ‖(Emat s t α).mulVec u‖ ≤ 21 / 50 * ‖u‖) ∧
    (∀ u : Fin s → ℂ, ‖(Emat s t α).mulVec u‖ ≤
      (2 : ℝ) ^ (-((α : ℝ) ^ 2 * ((t : ℝ) / s - 1))) * ‖u‖) ∧
    (∀ u : Fin s → ℂ, HasSum (fun m : ℕ => ((-Emat s t α) ^ m).mulVec u) ((Jmat s t α).mulVec u)) ∧
    (∀ u : Fin s → ℂ, ‖((1 / 2 : ℂ) • Jmat s t α).mulVec u‖ ≤ 7 / 8 * ‖u‖) ∧
    (∀ ℓ : Fin s, ‖diagD' s t α ℓ ℓ‖ ≤ 1) ∧
    (∀ v : Fin t → ℂ, ‖(resB s t α).mulVec v‖ ≤ ‖v‖)

/-- Parameters of Theorem 4.1 (`d = D`). -/
def ResParams (p α : ℕ) (ss ts : List ℕ) : Prop :=
  ss.length = D ∧ ts.length = D ∧ 100 ≤ p ∧ 2 ≤ α ∧ α ^ 2 < p ∧
  ∀ i < D, 2 ≤ ss.getD i 0 ∧ ss.getD i 0 < ts.getD i 0 ∧ ts.getD i 0 < 2 ^ p ∧
    Nat.Coprime (ss.getD i 0) (ts.getD i 0) ∧
    (p : ℝ) / (α : ℝ) ^ 4 ≤ (ts.getD i 0 : ℝ) / (ss.getD i 0) - 1

/-- cost of `Ã`, `B̃` in Theorem 4.1 (products by `self`; the last term = per-dimension tables) -/
def resCost (K : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ts : List ℕ) : ℕ :=
  K * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K * p) + p) + K * ts.prod * p ^ 2 + K * ts.sum * (p + 1) ^ K

/-- **Area Resample** (paper Theorem 4.1): `F_s = 2^γ B F_t A` with `‖A‖, ‖B‖ ≤ 1`, `γ = 2Dα²`,
and words computing `Ã`, `B̃` with error `< D p²`. -/
def ResampleProp : Prop :=
  ∃ (progA progB : Cmd) (K : ℕ), ∀ (p α : ℕ) (ss ts : List ℕ), ResParams p α ss ts →
    ∃ (A : (Fin ss.prod → ℂ) →ₗ[ℂ] (Fin ts.prod → ℂ)) (B : (Fin ts.prod → ℂ) →ₗ[ℂ] (Fin ss.prod → ℂ)),
      (∀ u, ‖A u‖ ≤ ‖u‖) ∧ (∀ v, ‖B v‖ ≤ ‖v‖) ∧
      (∀ u, dftMulti ss (-1) u = (2 : ℂ) ^ (2 * D * α ^ 2) • B (dftMulti ts (-1) (A u))) ∧
      ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
        WordR main progA
          (fun vs => ∃ zs rest, vs = .int p :: .int α :: intList ss :: intList ts :: cvecVal zs :: rest ∧
            InDiscVec p ss.prod zs)
          (fun vs out => ∃ zs rest ws,
            vs = .int p :: .int α :: intList ss :: intList ts :: cvecVal zs :: rest ∧
            out = cvecVal ws :: rest ∧ Approx p ws (A (fxVec p ss.prod zs)) (D * p ^ 2 : ℕ))
          (fun _ => resCost K Cm p α ts) ∧
        WordR main progB
          (fun vs => ∃ zs rest, vs = .int p :: .int α :: intList ss :: intList ts :: cvecVal zs :: rest ∧
            InDiscVec p ts.prod zs)
          (fun vs out => ∃ zs rest ws,
            vs = .int p :: .int α :: intList ss :: intList ts :: cvecVal zs :: rest ∧
            out = cvecVal ws :: rest ∧ Approx p ws (B (fxVec p ts.prod zs)) (D * p ^ 2 : ℕ))
          (fun _ => resCost K Cm p α ts)

/-! ## Parameters of the main step (paper §5.1) -/

/-- chunk size `b = ⌈log₂ n⌉` -/
def bpar (n : ℕ) : ℕ := Nat.clog 2 n
/-- precision `p = 6b` -/
def ppar (n : ℕ) : ℕ := 6 * bpar n
/-- `α = ⌈(12 d² b)^{1/4}⌉` -/
def apar (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (12 * D ^ 2 * bpar n - 1)) + 1
/-- `T = 2^{kT}` is the power of two in `[4n/b, 8n/b)` -/
def kTpar (n : ℕ) : ℕ := Nat.clog 2 ((4 * n + bpar n - 1) / bpar n)
def Tpar (n : ℕ) : ℕ := 2 ^ kTpar n
/-- `r = 2^{⌈kT/d⌉}` is the power of two in `[T^{1/d}, 2T^{1/d})` -/
def rpar (n : ℕ) : ℕ := 2 ^ ((kTpar n + D - 1) / D)

/-- Valid transform sizes for input size `n` (paper (5.11) with pairwise coprime odd `sᵢ` in place
of primes): `tᵢ ∈ {r/2, r}` ascending with `∏ tᵢ = T`, and `(1-2η)tᵢ < sᵢ ≤ (1-η)tᵢ`, `η = 1/(4d)`. -/
def ParamOK (n : ℕ) (ts ss : List ℕ) : Prop :=
  ts.length = D ∧ ss.length = D ∧ ts.Pairwise (· ≤ ·) ∧ ts.prod = Tpar n ∧
  (∀ t ∈ ts, t = rpar n ∨ 2 * t = rpar n) ∧
  (∀ i < D, (1 - 2 / (4 * D : ℝ)) * (ts.getD i 0 : ℝ) < (ss.getD i 0 : ℝ) ∧
    (ss.getD i 0 : ℝ) ≤ (1 - 1 / (4 * D : ℝ)) * (ts.getD i 0 : ℝ)) ∧
  ss.Pairwise Nat.Coprime ∧ ∀ s ∈ ss, Odd s

/-- **Area Params**: compute all parameters from `n` (cost polylog). -/
def ParamsProp : Prop :=
  ∃ (prog : Cmd) (K n₁ : ℕ), ∀ (main : Cmd) (n : ℕ), n₁ ≤ n →
    WordR main prog (fun vs => ∃ rest, vs = .int n :: rest)
      (fun vs out => ∃ rest ts ss, vs = .int n :: rest ∧ ParamOK n ts ss ∧
        out = .int (bpar n) :: .int (ppar n) :: .int (apar n) :: .int (Tpar n) :: .int (rpar n) ::
          intList ts :: intList ss :: rest)
      (fun _ => K * (n.size + 1) ^ K)

/-! ## Main step and recursion (paper §5.2–5.3, Cor 5.5) -/

/-- The cost the main step must meet: three transforms' pointwise products (`12T/r` calls of size
`3rp`), the resampling products (by `self`, size `≤ Kp`), and `O(n log n)` for everything else. -/
def mainCost (K : ℕ) (Cm : ℕ → ℕ) (n : ℕ) : ℕ :=
  12 * (Tpar n / rpar n) * Cm (3 * rpar n * ppar n) +
    K * Tpar n * (Nat.sqrt (ppar n) + 1) * apar n * Cm (K * ppar n) + K * n * n.size

/-- **Area Main** (paper Prop 5.4 with Props 5.2, 5.3): one recursive step for `n ≥ n₁`. -/
def MainStepProp : Prop :=
  ∃ (step : Cmd) (K n₁ : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm →
    WordR main step
      (fun vs => ∃ (x y : ℕ) (rest : List Val), vs = .int x :: .int y :: rest ∧
        n₁ ≤ max x.size y.size ∧ max x.size y.size ≤ N)
      mulPost (fun vs => mainCost K Cm (mulSize vs))

/-! ### Main split (v3, 2026-09-26): chapter-level pieces of the main step, dispatched in parallel.
Area Main (`MainStepProp`) may import the proved pieces (paths `Work.MainP.*`). -/

/-- **Area MainParams**: the parameter inequalities of §5.1–5.3 for all large `n` (pure arithmetic). -/
def MainParamsProp : Prop :=
  ∀ K : ℕ, ∃ n₂ : ℕ, ∀ (n : ℕ) (ts ss : List ℕ), n₂ ≤ n → ParamOK n ts ss →
    PowTwoParams (ppar n) ts ∧ ResParams (ppar n) (apar n) ss ts ∧ lmax ts = rpar n ∧
    3 * rpar n * ppar n < n ∧ K * ppar n < n ∧ 3 * D * ppar n ^ 2 < Tpar n ∧
    2 * D * apar n ^ 2 + 13 < bpar n ∧ Tpar n < 2 * ss.prod ∧ ss.prod ≤ Tpar n ∧
    2 * ((n + bpar n - 1) / bpar n) ≤ ss.prod + 1 ∧ Tpar n * bpar n < 8 * n ∧ n ≤ 2 ^ bpar n ∧
    1 ≤ bpar n ∧ 100 ≤ ppar n

/-- cost of one `F̃_s` (Prop 5.2): a transform, `Ã` and `B̃`, scaling, tables -/
def fsCost (K : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ts : List ℕ) : ℕ :=
  4 * (ts.prod / lmax ts) * Cm (3 * lmax ts * p) + 2 * resCost K Cm p α ts + K * ts.prod * p ^ 2 +
    K * ts.sum * (p + 1) ^ K

/-- Hypotheses shared by Props 5.2/5.3 (`γ = 2Dα²`). -/
def FsParams (p α : ℕ) (ss ts : List ℕ) : Prop :=
  PowTwoParams p ts ∧ ResParams p α ss ts ∧ 2 * D * α ^ 2 ≤ p ∧ 3 * D * p ^ 2 < ts.prod ∧
  ss.prod ≤ ts.prod

/-- **Area Prop52** (paper Prop 5.2): `F̃_s` (sgn = -1) and `F̃*_s` (sgn = 1, e.g. by conjugation) with
error `< 2^{γ+5} T log₂ T`. -/
def Prop52Prop : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm →
    ∀ (p α : ℕ) (ss ts : List ℕ) (sgn : ℤ), (sgn = 1 ∨ sgn = -1) → FsParams p α ss ts →
    3 * lmax ts * p < N → K * p < N →
    WordR main prog
      (fun vs => ∃ zs rest, vs = .int p :: .int α :: intList ss :: intList ts :: .int sgn :: cvecVal zs :: rest ∧
        InDiscVec p ss.prod zs)
      (fun vs out => ∃ zs rest ws,
        vs = .int p :: .int α :: intList ss :: intList ts :: .int sgn :: cvecVal zs :: rest ∧
        out = cvecVal ws :: rest ∧
        Approx p ws (dftMulti ss sgn (fxVec p ss.prod zs))
          (2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ))
      (fun _ => fsCost K Cm p α ts)

/-- **Area Prop53** (paper Prop 5.3): `M̃(u, v) ≈ convC ss u v = (1/S) u ∗ v` with error
`< 2^{γ+8} T² log₂ T`, cost three `F̃_s` plus `O(T p²)`. -/
def Prop53Prop : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm →
    ∀ (p α : ℕ) (ss ts : List ℕ), FsParams p α ss ts → 3 * lmax ts * p < N → K * p < N →
    WordR main prog
      (fun vs => ∃ us ws rest,
        vs = .int p :: .int α :: intList ss :: intList ts :: cvecVal us :: cvecVal ws :: rest ∧
        InDiscVec p ss.prod us ∧ InDiscVec p ss.prod ws)
      (fun vs out => ∃ us ws rest zs,
        vs = .int p :: .int α :: intList ss :: intList ts :: cvecVal us :: cvecVal ws :: rest ∧
        out = cvecVal zs :: rest ∧
        Approx p zs (convC ss (fxVec p ss.prod us) (fxVec p ss.prod ws))
          (2 ^ (2 * D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ))
      (fun _ => 3 * fsCost K Cm p α ts + K)

/-- Agarwal–Cooley index: position `m` of `ℤ[x]/(x^S - 1)` ↦ flat lexicographic index of
`(m mod s₁, …, m mod s_d)`. -/
def crtIdx : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: ss, m => (m % s) * ss.prod + crtIdx ss m

/-- **Area CrtWord** (paper Prop 5.4 step (2)): the reindexing and its inverse on any list of
`S = ∏ sᵢ` values, for pairwise coprime `sᵢ ≥ 1`, by label-and-sort. `dir = 0`: forward
(`ys[crtIdx m] = xs[m]`), `dir = 1`: inverse (`ys[m] = xs[crtIdx m]`). -/
def CrtWordProp : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (ss : List ℕ) (dir : ℕ) (xs : List Val),
    (∀ s ∈ ss, 1 ≤ s) → ss.Pairwise Nat.Coprime → xs.length = ss.prod → dir ≤ 1 →
    WordR main prog (fun vs => ∃ rest, vs = .int dir :: intList ss :: ofList xs :: rest)
      (fun vs out => ∃ rest ys, vs = .int dir :: intList ss :: ofList xs :: rest ∧
        out = ofList ys :: rest ∧ ys.length = ss.prod ∧
        ∀ m < ss.prod, (dir = 0 → ys.getD (crtIdx ss m) .nil = xs.getD m .nil) ∧
          (dir = 1 → ys.getD m .nil = xs.getD (crtIdx ss m) .nil))
      (fun _ => K * (vsz (ofList xs) + ss.prod * (vsz (intList ss) + 1) + 1) * (ss.prod.size + 1))

/-- the target cost shape `C (m log m + 1)` -/
def CmOf (C m : ℕ) : ℕ := C * (m * m.size + 1)

/-- **Area Recursion** (paper Cor 5.5 and the proof of Thm 1.1, pure arithmetic): for any constants
of the main step, a threshold `n₀` and a constant `C` close the induction. -/
def RecursionProp : Prop :=
  ∀ K n₁ Kb : ℕ, ∃ n₀ C : ℕ, n₁ ≤ n₀ ∧ ∀ n : ℕ,
    (n₀ ≤ n → mainCost K (CmOf C) n + Kb * (n + 1) ≤ CmOf C n) ∧
    (n < n₀ → Kb * ((n + 1) ^ 2 + n₀.size) ≤ CmOf C n)

/-! ## Assembly and final wiring -/

/-- The multiplication program with an `O(n log n)`-shaped cost. -/
def MulProgramC : Prop :=
  ∃ (P : Cmd) (C : ℕ), ∀ x y : ℕ,
    RunsWithin P (IntegerMultiplication.encodeProd encodeNat encodeNat (x, y)) (encodeNat (x * y))
      (C * ((IntegerMultiplication.encodeProd encodeNat encodeNat (x, y)).length *
        (IntegerMultiplication.encodeProd encodeNat encodeNat (x, y)).length.size + 1))

/-- **Area Assembly**: the top-level program (dispatch, parse, threshold test, base case, main step,
emit) and the strong induction on `N` establishing `MulBelow`. -/
def AssemblyProp : Prop := KernelLib → IntLib → MainStepProp → RecursionProp → MulProgramC

end HvdH
