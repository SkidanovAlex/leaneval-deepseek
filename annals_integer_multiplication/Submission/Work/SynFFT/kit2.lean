import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.kit
import Submission.Work.SynFFT.yMulListOK
import Submission.Work.SynFFT.dft1Math

/-!
# SynFFT, second interface ("kit2"): a consistent kernel interface and a slice-local FFT word

## Why `KLib`

`HvdH.KernelLib` is **false** as stated in `Submission/HvdH/Interfaces.lean`: its `loop` field
bounds a do-while by `m * (c + K) + K` for *every* `m`, which degenerates at `m = 0`; see
`Submission/Work/Kernel/loopRefute.lean` (`Work.Kernel.loopField_false`) and
`Submission/Work/Kernel/STATUS.md`.  Consequently every area lemma of the form
`KernelLib → …` is vacuously provable, and a prover handed `hk : KernelLib` can close *any*
goal in one line -- which has already happened once in this area
(`Submission/Work/SynFFT/hasKeySort.lean`).

`KLib` below is a verbatim copy of all `KernelLib` fields **except** `loop`: none of the SynFFT
words uses `loop` (the FFT loop is a `foldList` over an explicit list).  `KLib` is therefore
inhabited (as soon as the Layout/Fx/Int libraries are), and every lemma stated over `KLib` has
real content.  `kLibOf : KernelLib → KLib` is the trivial projection used once, at the very top,
in `synFFT.lean` -- it does not touch `loop`.  If `Interfaces.lean` is ever repaired, everything
below keeps working unchanged.

## The algorithm (paper Lemma 3.2 + Prop 3.3)

`ts` has `D - 1` axes, `M = ∏ tᵢ`, `T = M r`, `R = ℂ[y]/(y^r+1)`.  The program is a single
`foldList` over the axes (innermost first, i.e. `ts.reverse`), each step being ONE
`LayoutLib.applyAlong` that applies a *slice-local* 1-D synthetic FFT word to every `i`-slice of
the `Aᵢ × tᵢ × Bᵢ` decomposition of the flat array (`Aᵢ = ∏_{k<i} t_k`, `Bᵢ = ∏_{k>i} t_k`).
No annotations, no key sort, no bit-reversal bookkeeping at the outer level: the slice word
produces the 1-D transform *in natural order*, because it interleaves the blocks after each
radix-two level ("Stockham"), so the well-known bit-reversal of the in-place DIF scheme is
undone inside the word (see `mrgAll`/`mrgIter` and the math lemma `mrgIter_bitrev`).

The slice word itself is built out of

* `HasPair` — the butterfly on two coefficient vectors, with the twiddle `y^{sgn·j·2^sh}`
  computed as an *exact signed cyclic shift* (`HasYMulShift`, cost `O(r p)`, **not** the
  `O(p²)` `HasYMul` of `kit.lean`, whose `Int.fmod` of two `p`-bit numbers is too expensive here);
* `HasBlkLvl`/`HasLvlPass` — one level pass on a block / on the whole slice
  (`chunksOf` + `mapList` + `flatten`);
* `HasMrgBlk`/`HasMrgPass` — the interleave ("merge") pass;
* `HasFFT1` — the whole slice word, a `foldList` over `replicate`d driver lists (§`HasFFT1`).

The error grows by `1` per level, so a slice of length `t = 2^k` gets error `≤ e + k`; over the
axes this accumulates to `Σᵢ kᵢ = log₂ M < Nat.log 2 (M r)` by `logBound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-! ## `KLib`: the consistent part of `KernelLib` -/

/-- All fields of `HvdH.KernelLib` except the refuted `loop`. -/
structure KLib : Prop where
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

/-- Projection from the (inconsistent) `KernelLib` to the consistent `KLib`. -/
def kLibOf (h : KernelLib) : KLib where
  seq := h.seq
  conseq := h.conseq
  skip := h.skip
  selfLaw := h.selfLaw
  dup := h.dup
  drop := h.drop
  swap := h.swap
  pick := h.pick
  roll := h.roll
  pushVal := h.pushVal
  consV := h.consV
  unconsV := h.unconsV
  ifZero := h.ifZero
  ifNil := h.ifNil
  mapList := h.mapList
  zipWith := h.zipWith
  foldList := h.foldList

/-! ## `yMulS`: the signed cyclic shift ("y-multiplication") in shift form -/

/-- `yMulS r s sg w`: drop the first `s` coefficients (multiplied by `sg`) and move them after the
remaining `r - s` coefficients, which get the sign `-sg`.  This is `yMulList` with the residue
`s = (-e) fmod r` and the sign computed *outside* the word, so the word costs `O(r p)` instead of
`O(r p) + O(p²)` (the `Int.fmod` of two `p`-bit numbers). -/
def yMulS (r s : ℕ) (sg : ℤ) (w : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (w.drop s).map (fun z => (sg * z.1, sg * z.2)) ++ (w.take s).map (fun z => (-sg * z.1, -sg * z.2))

/-- `yMulS` is `yMulList`'s body, with the `let`s exposed. -/
lemma yMulList_eq_yMulS (r : ℕ) (e : ℤ) (w : List (ℤ × ℤ)) :
    yMulList r e w = yMulS r ((-e).fmod (r : ℤ)).toNat
      (if e + (-e).fmod (r : ℤ) = 0 then 1 else -1) w := rfl

lemma yMulS_length {r s : ℕ} (sg : ℤ) {w : List (ℤ × ℤ)} (hw : w.length = r) :
    (yMulS r s sg w).length = r := by
  simp only [yMulS, List.length_append, List.length_map, List.length_drop, List.length_take]
  omega

lemma neg_sq (sg a : ℤ) (hsg : sg = 1 ∨ sg = -1) : (sg * a) ^ 2 = a ^ 2 := by
  rcases hsg with h | h <;> simp [h]

lemma yMulS_inDisc {p r s : ℕ} {sg : ℤ} (hsg : sg = 1 ∨ sg = -1) {w : List (ℤ × ℤ)}
    (h : ∀ z ∈ w, inDisc p z) : ∀ z ∈ yMulS r s sg w, inDisc p z := by
  intro z hz
  simp only [yMulS, List.mem_append, List.mem_map] at hz
  have hneg : (-sg) = 1 ∨ (-sg) = -1 := by rcases hsg with h | h <;> simp [h]
  rcases hz with ⟨z', hz', rfl⟩ | ⟨z', hz', rfl⟩
  · have hz'' := h z' (List.mem_of_mem_drop hz')
    simp only [inDisc] at hz'' ⊢
    rw [neg_sq sg _ hsg, neg_sq sg _ hsg]; exact hz''
  · have hz'' := h z' (List.mem_of_mem_take hz')
    simp only [inDisc] at hz'' ⊢
    rw [neg_sq (-sg) _ hneg, neg_sq (-sg) _ hneg]; exact hz''

/-- The program-facing meaning of `yMulS`: at the level of fixed-point values it *is*
`yMul r e`, by `yMulListOK`. -/
lemma yMulS_fxC (p r s : ℕ) (sg : ℤ) (e : ℤ) (w : List (ℤ × ℤ)) (hw : w.length = r)
    (hs : yMulS r s sg w = yMulList r e w) (he : |e| ≤ (r : ℤ)) (j : Fin r) :
    fxC p ((yMulS r s sg w).getD (j : ℕ) (0, 0)) =
      yMul r e (fun c => fxC p (w.getD (c : ℕ) (0, 0))) j := by
  rw [hs]
  exact yMulListOK p r e w hw he j

/-! ## The list-level radixtwo algorithm (the program's specification) -/

/-- One level-`m` butterfly stage applied to a *list* of `R`-elements (elements are coefficient
vectors `Fin r → ℂ`): the list-level form of `lvlN`.  `blkLvl r m sgn l` only makes sense when
`l.length` is a multiple of `m`. -/
noncomputable def blkLvl (r m : ℕ) (sgn : ℤ) (l : List (Fin r → ℂ)) : List (Fin r → ℂ) :=
  (List.range l.length).map fun p =>
    if p % m < m / 2 then fun c => ((l.getD p 0) c + (l.getD (p + m / 2) 0) c) / 2
    else yMul r (sgn * (((2 * r / m) * (p % m - m / 2) : ℕ) : ℤ))
      (fun c' => ((l.getD (p - m / 2) 0) c' - (l.getD p 0) c') / 2)

/-- The level-`m` pass on a whole slice of length `t` (`m ∣ t`): `blkLvl` on every block. -/
noncomputable def lvlAll (r t m : ℕ) (sgn : ℤ) (l : List (Fin r → ℂ)) : List (Fin r → ℂ) :=
  ((List.range (t / m)).map fun b =>
    blkLvl r m sgn ((List.range m).map fun j => l.getD (b * m + j) 0)).flatten

/-- The interleave of scale `s`: inside every block of size `2s`, position `2j + ε` receives what
was at `j + ε*s`. -/
noncomputable def mrgN (r s : ℕ) (u : Arr r) : Arr r :=
  fun p c => u (p / (2 * s) * (2 * s) + (p / 2 % s) + (p % 2) * s) c

/-- The list-level form of `mrgN` on a slice of length `t`. -/
noncomputable def mrgL (r t s : ℕ) (l : List (Fin r → ℂ)) : List (Fin r → ℂ) :=
  (List.range t).map fun p => l.getD (p / (2 * s) * (2 * s) + (p / 2 % s) + (p % 2) * s) 0

/-- The interleave passes of scales `1, 2, …, 2^{k-1}` (function level). -/
noncomputable def mrgIterN (r : ℕ) : ℕ → Arr r → Arr r
  | 0, u => u
  | (k + 1), u => mrgN r (2 ^ k) (mrgIterN r k u)

/-- The algorithm of the slice word: `k` level passes (block sizes `t, t/2, …, 2`) followed by
`k` interleave passes (scales `1, 2, …, 2^{k-1}`, the first of which is the identity), which undo
the bit reversal of the in-place DIF scheme.  (Verified numerically for `t ≤ 8`: for a generic
input, `fftN r t k sgn u p = dftN r t sgn u p` for all `p < t`.) -/
noncomputable def fftN (r t k : ℕ) (sgn : ℤ) (u : Arr r) : Arr r :=
  mrgIterN r k (levels r sgn t k u)

/-! ### The four pure facts the word pieces need (delegated as separate lemmas) -/

/-- The twiddle index `t = (2r/m)·j = j·2^sh` (with `t < r`) determines the shift and the sign of
`yMulS` so that `yMulS` computes `yMul r (sgn·t)` -- `|sgn·t| < r`, so `yMulList`'s residue is
`(-sgn·t) fmod r` and the sign is the one below. -/
def YMulTwiddleProp : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (sgn : ℤ), (sgn = 1 ∨ sgn = -1) → ∀ (t : ℕ), t < r →
    ∀ (w : List (ℤ × ℤ)),
      yMulS r (if sgn = 1 then (if t = 0 then 0 else r - t) else t)
          (if sgn = 1 ∧ t ≠ 0 then -1 else 1) w = yMulList r (sgn * (t : ℤ)) w

/-- The interleave passes (scales `1, …, 2^{k-1}`) compose to the bit-reversal permutation of the
low `k` bits. -/
def MrgBitrevProp : Prop :=
  ∀ (r k : ℕ) (u : Arr r) (p : ℕ), p < 2 ^ k → mrgIterN r k u p = u (bitrev k p)

/-- The level pass on a slice, read at a position, is `lvlN` (block-local, so the block
decomposition of `lvlAll` does not change it). -/
def LvlAllGetDProp : Prop :=
  ∀ (r t m : ℕ) (sgn : ℤ) (l : List (Fin r → ℂ)), m ∣ t → 0 < m → ∀ p, p < t →
    (lvlAll r t m sgn l).getD p 0 = lvlN r m sgn (fun q => l.getD q 0) p

/-- `axisT` at a flat position is the `dftN` of the slice through that position. -/
def AxisTSlicesProp : Prop :=
  ∀ (r A t B : ℕ) (sgn : ℤ) (a : Arr r) (idx : ℕ), idx < A * t * B → 0 < t → 0 < B →
    axisT r t B sgn a idx = dftN r t sgn (fun u => a ((idx / (t * B) * t + u) * B + idx % B))
      (idx / B % t)

/-- `ws` (a list of coefficient vectors, i.e. of values `cvecVal _`) approximates the array `u`
with error `≤ e` in the `2^p`-scaled sense. -/
def ApproxSL (p r t : ℕ) (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ) : Prop :=
  ws.length = t ∧ ∀ q, q < t → ∀ c : Fin r,
    (2 : ℝ) ^ p * ‖fxC p ((ws.getD q []).getD (c : ℕ) (0, 0)) - u q c‖ ≤ e

/-! ## The word pieces -/

/-- Negate one fixed-point complex number (`cfxVal (a,b) ↦ cfxVal (-a,-b)`). -/
def HasNegPair : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ) (z : ℤ × ℤ) (rest : List Val),
    inDisc p z →
    WordR main prog (fun vs => vs = cfxVal z :: rest)
      (fun vs out => out = cfxVal (-z.1, -z.2) :: rest ∧ inDisc p (-z.1, -z.2))
      (fun _ => K * (p + 1))

/-- **The y-multiplication word** (shift form): `cvecVal w ↦ cvecVal (yMulS r s sg w)`. -/
def HasYMulShift : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r s : ℕ) (sg : ℤ) (w : List (ℤ × ℤ))
      (rest : List Val),
    w.length = r → s ≤ r → (sg = 1 ∨ sg = -1) → (∀ z ∈ w, inDisc p z) →
    WordR main prog
      (fun vs => vs = cvecVal w :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun vs out => ∃ w' : List (ℤ × ℤ),
        out = cvecVal w' :: .int (s : ℤ) :: .int sg :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        w' = yMulS r s sg w ∧ w'.length = r ∧ (∀ z ∈ w', inDisc p z))
      (fun _ => K * (r + 1) * (p + 1))

/-- **The butterfly word**: `(u₁,u₂) ↦ ((u₁+u₂)/2, y^{sgn·j·2^sh}·(u₁-u₂)/2)`, with
`j·2^sh = (2r/m)·j < r` the level's twiddle exponent. -/
def HasPair : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r j sh : ℕ) (sgn : ℤ) (w₁ w₂ : List (ℤ × ℤ))
      (rest : List Val) (u₁ u₂ : Fin r → ℂ) (e : ℝ),
    0 < r → (sgn = 1 ∨ sgn = -1) → j * 2 ^ sh < r → 2 ^ sh ≤ 2 * r → 2 * r < 2 ^ p →
    w₁.length = r → w₂.length = r → (∀ z ∈ w₁, inDisc p z) → (∀ z ∈ w₂, inDisc p z) →
    (∀ c : Fin r, (2 : ℝ) ^ p * ‖fxC p (w₁.getD (c : ℕ) (0, 0)) - u₁ c‖ ≤ e) →
    (∀ c : Fin r, (2 : ℝ) ^ p * ‖fxC p (w₂.getD (c : ℕ) (0, 0)) - u₂ c‖ ≤ e) →
    WordR main prog
      (fun vs => vs = cvecVal w₁ :: cvecVal w₂ :: .int (j : ℤ) :: .int (sh : ℤ) :: .int sgn ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun vs out => ∃ v₁ v₂ : List (ℤ × ℤ),
        out = cvecVal v₁ :: cvecVal v₂ :: .int (j : ℤ) :: .int (sh : ℤ) :: .int sgn ::
          .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        v₁.length = r ∧ v₂.length = r ∧ (∀ z ∈ v₁, inDisc p z) ∧ (∀ z ∈ v₂, inDisc p z) ∧
        (∀ c : Fin r, (2 : ℝ) ^ p * ‖fxC p (v₁.getD (c : ℕ) (0, 0)) - (u₁ c + u₂ c) / 2‖ ≤ e + 1) ∧
        (∀ c : Fin r, (2 : ℝ) ^ p * ‖fxC p (v₂.getD (c : ℕ) (0, 0)) -
          yMul r (sgn * ((j * 2 ^ sh : ℕ) : ℤ)) (fun c' => (u₁ c' - u₂ c') / 2) c‖ ≤ e + 1))
      (fun _ => K * (r + 1) * (p + 1) + K)

/-- **One level pass on a block** of `m` elements (the inner loop of `HasLvlPass`). -/
def HasBlkLvl : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r m sh : ℕ) (sgn : ℤ) (ws : List (List (ℤ × ℤ)))
      (u : Arr r) (e : ℝ) (rest : List Val),
    2 ≤ m → m * 2 ^ sh = 2 * r → (sgn = 1 ∨ sgn = -1) → 2 * r < 2 ^ p →
    ws.length = m → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r m ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun vs out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn ::
          .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = m ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r m ws' (lvlN r m sgn u) (e + 1))
      (fun _ => K * m * (r + 1) * (p + 1) + K)

/-- **One level pass on the whole slice**: `chunksOf m` + `mapList` (block word) + `flatten`. -/
def HasLvlPass : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r t m sh : ℕ) (sgn : ℤ) (ws : List (List (ℤ × ℤ)))
      (u : Arr r) (e : ℝ) (rest : List Val),
    2 ≤ m → m ∣ t → m * 2 ^ sh = 2 * r → (sgn = 1 ∨ sgn = -1) → 2 * r < 2 ^ p →
    ws.length = t → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r t ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun vs out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn ::
          .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = t ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r t ws' (lvlN r m sgn u) (e + 1))
      (fun _ => K * t * (r + 1) * (p + 1) + K)

/-- **One interleave pass on a block** of `2s` elements. -/
def HasMrgBlk : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r s : ℕ) (ws : List (List (ℤ × ℤ))) (u : Arr r)
      (e : ℝ) (rest : List Val),
    0 < s → ws.length = 2 * s → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r (2 * s) ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun vs out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = 2 * s ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r (2 * s) ws' (mrgN r s u) e)
      (fun _ => K * s * (r + 1) * (p + 1) + K)

/-- **One interleave pass on the whole slice**. -/
def HasMrgPass : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r t s : ℕ) (ws : List (List (ℤ × ℤ))) (u : Arr r)
      (e : ℝ) (rest : List Val),
    0 < s → 2 * s ∣ t → ws.length = t → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r t ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun vs out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = t ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r t ws' (mrgN r s u) e)
      (fun _ => K * t * (r + 1) * (p + 1) + K)

/-- **The slice word** (paper Lemma 3.2).  A list of `t = 2^k` coefficient vectors, approximating
`u` with error `≤ e`, is mapped to a list approximating the length-`t` synthetic transform
`dftN r t sgn u` with error `≤ e + k`.  Cost `O(t r p k)`. -/
def HasFFT1 : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r t k : ℕ) (sgn : ℤ) (ws : List (List (ℤ × ℤ)))
      (u : Arr r) (e : ℝ) (rest : List Val),
    IsPow2 r → t = 2 ^ k → t ∣ 2 * r → 2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) →
    ws.length = t → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r t ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: rest)
      (fun vs out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: rest ∧
        ws'.length = t ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r t ws' (fun q => dftN r t sgn u q) (e + k))
      (fun _ => K * t * (r + 1) * (p + 1) * (k + 1) + K)

/-- **One axis pass**: `applyAlong` of the slice word over the `A × t × B` decomposition,
i.e. `axisT r t B sgn` on the flat array.  Cost `O(T p (k+1))` with `T` the flat length. -/
def HasAxis : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r A t B k : ℕ) (sgn : ℤ)
      (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ) (rest : List Val),
    IsPow2 r → t = 2 ^ k → t ∣ 2 * r → 2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) →
    0 < A → 0 < B →
    ws.length = A * t * B → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r (A * t * B) ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) ::
        .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun vs out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) ::
          .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = A * t * B ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r (A * t * B) ws' (axisT r t B sgn u) (e + k))
      (fun _ => K * (A * t * B) * (r + 1) * (p + 1) * (k + 1) +
        K * (A * t * B) * (r + 1) * (p + 1) * ((A * t * B).size + 2) + K)

/-! ## The axis loop (paper Prop 3.3, outer level) -/

/-- The axis passes for the axes `t :: ts`, innermost first: the transform for the tail `ts` is
applied first, then `axisT` for `t` with stride `ts.prod` (the paper's tensor factorisation,
`multiCons` iterated). -/
noncomputable def axisIterN (r : ℕ) (sgn : ℤ) : List ℕ → Arr r → Arr r
  | [], u => u
  | (t :: ts), u => axisT r t ts.prod sgn (axisIterN r sgn ts u)

/-- The iterated tensor factorisation: the axis passes compute the full synthetic transform. -/
def AxisIterProp : Prop :=
  ∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Arr r), (∀ t ∈ ts, 0 < t) → ∀ p, p < ts.prod →
    axisIterN r sgn ts u p = dftMultiN r ts sgn u p

/-- `synDFT` (`Fin`-indexed) is `dftMultiN` (natural-number indexed, with the trivial extension to
`ℕ`). -/
def SynDFTProp : Prop :=
  ∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → Fin r → ℂ) (j : Fin ts.prod) (c : Fin r),
    synDFT r ts sgn u j c =
      dftMultiN r ts sgn (fun i => if h : i < ts.prod then u ⟨i, h⟩ else 0) j c

/-- **The axis loop**: run the `HasAxis` word once for every axis of `ts`, innermost first
(i.e. in the order `ts.reverse`), keeping track of the suffix product `B` and recomputing the
prefix product `A = M/(t·B)`.  The error grows by `log₂ t` per axis, the cost is `(D-1)` times the
uniform per-axis bound `M(r+1)(p+1)(M.size+2)`. -/
def HasAxesFold : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r : ℕ) (ts : List ℕ) (sgn : ℤ)
      (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ) (rest : List Val),
    IsPow2 r → (∀ t ∈ ts, IsPow2 t) → (∀ t ∈ ts, t ∣ 2 * r) → (∀ t ∈ ts, 2 ≤ t) →
    2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) → ws.length = ts.prod →
    (∀ w ∈ ws, InDiscVec p r w) →
    ApproxSL p r ts.prod ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: intList ts :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: rest)
      (fun vs out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: intList ts :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: rest ∧
        ws'.length = ts.prod ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r ts.prod ws' (axisIterN r sgn ts u)
          (e + (ts.map (fun t => (Nat.log 2 t : ℝ))).sum))
      (fun _ => K * (ts.length + 1) * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + K)

/-! ## The two parameter-shuffling words of the top level -/

/-- Four `KLib.roll`s move the five top values `int p, int r, intList ts, int sgn, rarrVal us`
into the order `rarrVal us, intList ts, int sgn, int r, int p` that the axis loop expects. -/
def ReorderProp : Prop :=
  ∃ (pr : Cmd) (K : ℕ), ∀ (main : Cmd) (p r : ℕ) (ts : List ℕ) (sgn : ℤ)
      (us : List (List (ℤ × ℤ))) (rest : List Val),
      WordR main pr
        (fun vs => vs = .int (p : ℤ) :: .int (r : ℤ) :: intList ts :: .int sgn ::
          rarrVal us :: rest)
        (fun _ out => out = rarrVal us :: intList ts :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: rest)
        (fun _ => K * (D + 1) * (vsz (rarrVal us) + vsz (intList ts) + isz (p : ℤ) +
          isz (r : ℤ) + isz sgn + 3))

/-- Drop the four parameters `intList ts, int sgn, int r, int p` left behind by the axis loop. -/
def DropParamsProp : Prop :=
  ∃ (pr : Cmd) (K : ℕ), ∀ (main : Cmd) (w : Val) (ts : List ℕ) (sgn : ℤ) (r p : ℕ)
      (rest : List Val),
      WordR main pr
        (fun vs => vs = w :: intList ts :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ out => out = w :: rest)
        (fun _ => K * (vsz w + vsz (intList ts) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 5))

/-- Elementary size bounds for the encoded values: an in-disc coefficient vector and an in-disc
array cost `O(r p)` resp. `O(M r p)` glyphs, and a list of `p`-bit naturals costs `O(D p)`. -/
def ArrSizeProp : Prop :=
  (∀ (p r : ℕ), 0 < p → ∀ (w : List (ℤ × ℤ)), InDiscVec p r w →
    vsz (cvecVal w) ≤ r * (2 * p + 6) + 1) ∧
  (∀ (p r M : ℕ), 0 < p → ∀ (ws : List (List (ℤ × ℤ))), InDiscArr p M r ws →
    vsz (rarrVal ws) ≤ M * (r * (2 * p + 6) + 2) + 1) ∧
  (∀ (ts : List ℕ) (p : ℕ), (∀ t ∈ ts, t < 2 ^ p) → vsz (intList ts) ≤ ts.length * (p + 3) + 1)

/-- The cost arithmetic of the top level: the three word costs plus the size bounds dominate the
target `K * (M r) * p * (log₂(M r) + 1) + K` (delegated as `SynFFT/costArith`). -/
def CostArithProp : Prop :=
  ∀ (Kr Kd Kf : ℕ) (p r : ℕ) (ts : List ℕ) (sgn : ℤ) (us ws' : List (List (ℤ × ℤ)))
    (n1 n2 n3 : ℕ),
    ts.length = D - 1 → 2 ≤ r → 2 ≤ ts.prod →
    n1 ≤ Kr * (D + 1) * (vsz (rarrVal us) + vsz (intList ts) + isz (p : ℤ) + isz (r : ℤ)
        + isz sgn + 3) →
    n2 ≤ Kf * (ts.length + 1) * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Kf →
    n3 ≤ Kd * (vsz (rarrVal ws') + vsz (intList ts) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 5) →
    vsz (rarrVal us) ≤ ts.prod * (r * (2 * p + 6) + 2) + 1 →
    vsz (rarrVal ws') ≤ ts.prod * (r * (2 * p + 6) + 2) + 1 →
    vsz (intList ts) ≤ ts.length * (p + 3) + 1 →
    ts.prod.size ≤ Nat.log 2 (ts.prod * r) + 1 →
    isz (p : ℤ) ≤ p + 3 → isz (r : ℤ) ≤ p + 3 → isz sgn ≤ 3 →
    n1 + (n2 + n3) ≤ (2000 * (Kr + Kf + Kd) * D * D + 2000) * (ts.prod * r) * p
        * (Nat.log 2 (ts.prod * r) + 1) + (2000 * (Kr + Kf + Kd) * D * D + 2000)

end Work.SynFFT
