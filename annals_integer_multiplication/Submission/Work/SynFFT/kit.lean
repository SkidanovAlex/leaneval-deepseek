import Mathlib
import Submission.Work.SynFFT.defs

/-!
# SynFFT: program-facing interface ("kit")

The FFT program is assembled from library words.  This module fixes the *interface* of each
piece as a `Prop` (`HasYMul`, `HasBF`, ...) together with the concrete predicates the pieces
must meet.  Each piece is delegated as a lemma proving one of these `Prop`s, assuming the
previously built ones.  The final assembly extracts the programs with `Classical.choose`.

Layout conventions (stack 0, head = top of stack):

* `cvecVal w` — an element of `R` as a list of `r` fixed-point coefficient pairs;
* `annV A w = cons (int A) (cvecVal w)` — an annotated element; the annotation is the single
  integer `A = q * 2^p + acc` where `q` is the flat position (`annPos`) and `acc` the running
  bit-reversal key of the axis being processed (`annAcc`).
-/

/-
NOTE (for provers of the `Has*` lemmas below): build the *real* words with the library
combinators.  `HvdH.KernelLib` is currently refuted as stated (its `loop` field is false, see
`Submission/Work/Kernel/loopRefute.lean`); do NOT discharge these lemmas by way of that
inconsistency -- the intended content is the concrete program with the stated spec, which is
what the whole area needs once `Interfaces.lean` is repaired.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- Annotated element. -/
def annV (A : ℤ) (w : List (ℤ × ℤ)) : Val := Val.cons (.int A) (cvecVal w)

/-- Position part of an annotation (`q`, the high bits). -/
def annPos (p : ℕ) (A : ℤ) : ℕ := (A / (2 : ℤ) ^ p).toNat

/-- Key part of an annotation (the low bits). -/
def annAcc (p : ℕ) (A : ℤ) : ℕ := (A % (2 : ℤ) ^ p).toNat

/-- The coefficient-list version of `yMul` (`yMulSplit` says it represents `yMul`). -/
def yMulList (r : ℕ) (e : ℤ) (w : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  let f := (-e).fmod (r : ℤ)
  let s := f.toNat
  let sg : ℤ := if e + f = 0 then 1 else -1
  (w.drop s).map (fun z => (sg * z.1, sg * z.2)) ++ (w.take s).map (fun z => (-sg * z.1, -sg * z.2))

/-- `annV`-shaped list of length `M` with positions equal to the indices and key function `acc`,
approximating `v` with error `≤ e`. -/
def AnnArrP (p r M : ℕ) (acc : ℕ → ℕ) (xs : List Val) (v : Arr r) (e : ℝ) : Prop :=
  xs.length = M ∧
    ∀ i < M, ∃ w : List (ℤ × ℤ),
      xs.getD i .nil = annV ((i : ℤ) * (2 : ℤ) ^ p + (acc i : ℤ)) w ∧ w.length = r ∧
      (∀ z ∈ w, inDisc p z) ∧
      ∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p (w.getD (j : ℕ) (0, 0)) - v i j‖ ≤ e

/-- Pure math fact: `yMulList` represents `yMul` at the level of fixed-point values. -/
def YMulListOK : Prop :=
  ∀ (p r : ℕ) (e : ℤ) (w : List (ℤ × ℤ)), w.length = r → |e| ≤ (r : ℤ) →
    ∀ j : Fin r, fxC p ((yMulList r e w).getD (j : ℕ) (0, 0)) =
      yMul r e (fun c => fxC p (w.getD (c : ℕ) (0, 0))) j

/-- **Piece 1**: the word applying `yMul r e` to one element. -/
def HasYMul (hk : KernelLib) (hi : IntLib) (hl : LayoutLib) : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r : ℕ) (e : ℤ) (w : List (ℤ × ℤ)) (rest : List Val),
    w.length = r → |e| ≤ (r : ℤ) → (∀ z ∈ w, inDisc p z) →
    WordR main prog (fun vs => vs = cvecVal w :: .int e :: .int r :: rest)
      (fun vs out => out = cvecVal (yMulList r e w) :: .int e :: .int r :: rest)
      (fun _ => K * (r + 1) * (p + 1) ^ 2)

/-- **Piece 2**: the butterfly word on a two-element slice of the level-`m` stage of an axis of
stride `B`: it replaces `(a, b)` by `((a+b)/2, y^{tw}·(a-b)/2)` (both entries keeping their
annotation, the second one increased by the level's key constant `c`). -/
def HasBF (hk : KernelLib) (hi : IntLib) (hl : LayoutLib) (hf : FxLib) : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r B m : ℕ) (sgn : ℤ) (c : ℤ)
      (A₁ A₂ : ℤ) (w₁ w₂ : List (ℤ × ℤ)) (rest : List Val) (u : Fin 2 → Fin r → ℂ) (e₀ : ℝ),
    0 < r → 0 < B → 0 < m → 2 * (m / 2) = m → 0 ≤ c → 0 ≤ A₁ → 0 ≤ A₂ →
    B < 2 ^ p → m < 2 ^ p → (sgn = 1 ∨ sgn = -1) →
    A₁ < (2 : ℤ) ^ (2 * p) → A₂ < (2 : ℤ) ^ (2 * p) → c < (2 : ℤ) ^ (2 * p) →
    A₂ + c < (2 : ℤ) ^ (2 * p) →
    w₁.length = r → w₂.length = r →
    (∀ u' ∈ w₁, inDisc p u') → (∀ u' ∈ w₂, inDisc p u') →
    (∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p (w₁.getD (j : ℕ) (0, 0)) - u 0 j‖ ≤ e₀) →
    (∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p (w₂.getD (j : ℕ) (0, 0)) - u 1 j‖ ≤ e₀) →
    WordR main prog
      (fun vs => vs = annV A₁ w₁ :: annV A₂ w₂ ::
        .int (p : ℤ) :: .int (r : ℤ) :: .int (B : ℤ) :: .int (m : ℤ) :: .int sgn :: .int c :: rest)
      (fun vs out => ∃ v₁ v₂ : List (ℤ × ℤ),
        out = annV A₁ v₁ :: annV (A₂ + c) v₂ ::
          .int (p : ℤ) :: .int (r : ℤ) :: .int (B : ℤ) :: .int (m : ℤ) :: .int sgn :: .int c :: rest ∧
        v₁.length = r ∧ v₂.length = r ∧
        (∀ z ∈ v₁, inDisc p z) ∧ (∀ z ∈ v₂, inDisc p z) ∧
        (∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p (v₁.getD (j : ℕ) (0, 0)) - (u 0 j + u 1 j) / 2‖ ≤ e₀ + 1) ∧
        (∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p (v₂.getD (j : ℕ) (0, 0)) -
            yMul r (twExp r sgn B m (annPos p A₁)) (fun c' => (u 0 c' - u 1 c') / 2) j‖ ≤ e₀ + 1))
      (fun _ => K * (r + 1) * (p + 1) ^ 2)

/-- **Piece 3**: one global level pass of one axis stage — every butterfly pair `(q, q+(m/2)B)`
is replaced by `((a_q+a_{q+m/2B})/2, y^{tw}·(a_q-a_{q+m/2B})/2)`, the second element's key
accumulator being increased by `c`.  The slices are the `(Ap, 2, Bp)`-decomposition of the array,
with `Bp = m/2·B` and `2·Ap·Bp = M`. -/
def HasLevel (hk : KernelLib) (hi : IntLib) (hl : LayoutLib) (hf : FxLib) : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r B m M Ap Bp : ℕ) (sgn c : ℤ)
      (acc : ℕ → ℕ) (xs : List Val) (v : Arr r) (e : ℝ) (rest : List Val),
    0 < r → 0 < B → 0 < m → 2 * (m / 2) = m → 0 ≤ c → 0 < M → 2 * (Ap * Bp) = M →
    Bp = m / 2 * B → Ap < 2 ^ p → Bp < 2 ^ p → (∀ i < M, acc i < 2 ^ p) →
    AnnArrP p r M acc xs v e →
    WordR main prog
      (fun vs => vs = ofList xs :: .int (p : ℤ) :: .int (r : ℤ) :: .int (B : ℤ) :: .int (m : ℤ) ::
        .int sgn :: .int c :: .int (Ap : ℤ) :: .int (Bp : ℤ) :: rest)
      (fun vs out => ∃ ys : List Val,
        out = ofList ys :: .int (p : ℤ) :: .int (r : ℤ) :: .int (B : ℤ) :: .int (m : ℤ) ::
          .int sgn :: .int c :: .int (Ap : ℤ) :: .int (Bp : ℤ) :: rest ∧
        AnnArrP p r M (fun i => if m / 2 ≤ i / B % m then acc i + c.toNat else acc i) ys
          (lvlAx r B m sgn v) (e + 1))
      (fun _ => K * M * (r + 1) * (p + 1) ^ 3)

/-- **Piece 4**: finish one axis.  Relabel each element with `tgt i = i + acc i - (i/B % t)·B`
(the flat index obtained by bit-reversing the coordinate along the axis) and re-sort, so that the
DFS-ordered output of the level passes is put back into natural order. -/
def HasKeySort (hk : KernelLib) (hi : IntLib) (hl : LayoutLib) : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r M B t : ℕ) (acc : ℕ → ℕ) (xs : List Val)
      (v : Arr r) (e : ℝ) (σ : Equiv.Perm (Fin M)) (rest : List Val),
    0 < r → 0 < B → 0 < t → 0 < M → B < 2 ^ p → t < 2 ^ p → (∀ i < M, acc i < 2 ^ p) →
    (∀ i : Fin M, ((σ i : ℕ) = (i : ℕ) + acc i - ((i : ℕ) / B % t) * B)) →
    AnnArrP p r M acc xs v e →
    WordR main prog
      (fun vs => vs = ofList xs :: .int (p : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: rest)
      (fun vs out => ∃ ys : List Val,
        out = ofList ys :: .int (p : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: rest ∧
        AnnArrP p r M (fun _ => 0) ys (fun ℓ => if h : ℓ < M then v (σ.symm ⟨ℓ, h⟩) else 0) e)
      (fun _ => K * (M + 1) * (r + 1) * (p + 1) ^ 2 * (M.size + 1))

end Work.SynFFT
