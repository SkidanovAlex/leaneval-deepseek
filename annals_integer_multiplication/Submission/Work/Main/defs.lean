import Mathlib
import Submission.HvdH.Interfaces

/-!
# Definitions for the main step of the Harvey–van der Hoeven algorithm (paper §5.2–5.4)

Pure-data layer used by `Work.Main.mainStep`: the Agarwal–Cooley CRT reindexing, the chunk
polynomial product, the flat fixed-point vector fed to the transforms, and the final recovery
by rounding.
-/

set_option autoImplicit false

namespace Work.Main

open HvdH

/-- `Pcr ss m` is the lexicographic ("flat") index of the multi-index `(m % s₁, …, m % s_d)`:
the CRT reindexing of the Agarwal–Cooley method. It is `undigits ss (ss.map (m % ·))`. -/
def Pcr : List ℕ → ℕ → ℕ
  | [], _ => 0
  | t :: ts, m => (m % t) * ts.prod + Pcr ts m

@[simp] theorem Pcr_nil (m : ℕ) : Pcr [] m = 0 := rfl

@[simp] theorem Pcr_cons (t : ℕ) (ts : List ℕ) (m : ℕ) :
    Pcr (t :: ts) m = (m % t) * ts.prod + Pcr ts m := rfl

/-- The inverse of `Pcr ss` on `[0, ∏ss)`: the (chosen) `m < ∏ss` with `Pcr ss m = p`
(`0` if there is none). -/
noncomputable def Pinv (ss : List ℕ) (p : ℕ) : ℕ :=
  if h : ∃ m, m < ss.prod ∧ Pcr ss m = p then h.choose else 0

/-- The `m`-th base-`2^b` chunk of `x`, zero for `m ≥ N` (padding). -/
def pchunk (x b N m : ℕ) : ℕ := if m < N then x / 2 ^ (b * m) % 2 ^ b else 0

/-- Coefficient of `x^m` in the product of the chunk polynomials of `x` and `y`
(the padding `pchunk` is zero outside `[0,N)`, and the guard `i ≤ m` makes the truncated
subtraction `m - i` harmless). -/
def hcoeff (x y b N m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, if i ≤ m then pchunk x b N i * pchunk y b N (m - i) else 0

/-- The flat-ordered fixed-point vector of the scaled chunks of `x`: at flat index `q` it holds
`2^{-b}` times the chunk of `x` whose CRT index is `Pinv ss q`. -/
noncomputable def flatv (b N : ℕ) (ss : List ℕ) (x : ℕ) : Fin ss.prod → ℂ :=
  fun q => ((pchunk x b N (Pinv ss q.val) : ℕ) : ℂ) / 2 ^ b

/-- Recovery of the integer coefficient from the computed fixed-point value `z = (re, im)`:
the integer nearest to `S · re / 2^{p-2b}`, computed as `(S·re + 2^{p-2b-1}) / 2^{p-2b}`. -/
def recov (S p b : ℕ) (z : ℤ × ℤ) : ℤ :=
  (S * z.1 + 2 ^ (p - 2 * b - 1)).fdiv (2 ^ (p - 2 * b))

/-- Number of chunks of an `n`-bit integer with chunk size `b`: `⌈n/b⌉`. -/
def nchunks (n b : ℕ) : ℕ := (n + b - 1) / b

/-- The parameters of one step of the algorithm, bundled. -/
structure SP where
  S : ℕ
  N' : ℕ
  b : ℕ
  p : ℕ
  α : ℕ
  x : ℕ
  y : ℕ
  ts : List ℕ
  ss : List ℕ
  deriving Inhabited

/-- The parameter environment kept below the working data during the main step. -/
def env (sp : SP) (R : List Val) : List Val :=
  [Val.int sp.S, Val.int sp.N', Val.int sp.b, Val.int sp.p, Val.int sp.α,
    intList sp.ts, intList sp.ss, Val.int sp.x, Val.int sp.y] ++ R

/-- Total size of the parameter environment: the sum of the sizes of its nine values. -/
def envsz (sp : SP) : ℕ := ((env sp []).map vsz).sum

/-- The chunks of `x` padded with zeros to length `S`. -/
def padChunks (x b N' S : ℕ) : List ℕ := HvdH.chunks x b N' ++ List.replicate (S - N') 0

/-- the `m`-th (padded) chunk of `x`, as a natural -/
def pchunkN (x b N' _S m : ℕ) : ℕ := pchunk x b N' m

/-- the fixed-point value of the `m`-th padded chunk of `x`, scaled by `2^k` -/
def pchunkZ (x b N' S k m : ℕ) : ℤ × ℤ := (((pchunkN x b N' S m : ℕ) : ℤ) * 2 ^ k, 0)

/-- The cost accumulated by the four stages of the main step (setup, preparation, Prop 5.3 +
recovery, epilogue), as produced by the stage lemmas `step.setup`, `step.prep`, `step.finalize`
and `final.finalWord` with constants `KPar, Ksetup, Kprep, Kfin, Kepi` (and `K53` for Prop 5.3).
This is the expression compared with `mainCost K0 Cm n` by `Work.Main.cost.mainCostBound`. -/
def totalCost (KPar Ksetup Kprep Kfin Kepi K53 : ℕ) (Cm : ℕ → ℕ) (sp : SP) : ℕ :=
  KPar * ((max sp.x.size sp.y.size).size + 1) ^ KPar * Ksetup + Ksetup * (sp.x.size + sp.y.size + 1)
  + (Kprep * (sp.S + 1) * (HvdH.vsz (HvdH.intList sp.ss) + HvdH.vsz (HvdH.intList sp.ts) + sp.b + sp.p + 1)
        * (sp.S.size + 1)
      + Kprep * (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1)
      + Kprep * (sp.x.size + sp.y.size + sp.b + sp.N' + sp.S + 1)
      + Kprep * (envsz sp + 1))
  + (3 * HvdH.fsCost K53 Cm sp.p sp.α sp.ts + K53 + Kfin * (sp.S + 1) * (sp.p + 1) * (sp.p + 1)
      + Kfin * (sp.S + 1) * (HvdH.D + 1) * (sp.p + 1) * (sp.p + 1))
  + (Kepi * (sp.S + 1) * (sp.b + 1) + Kepi * (envsz sp + 1))

/-- The pre/post/cost of the Prop 5.3 pipeline (`M̃ ≈ convC`). -/
def P53 (p α : ℕ) (ss ts : List ℕ) : List Val → Prop := fun vs =>
  ∃ us ws rest, vs = [Val.int p, Val.int α, intList ss, intList ts, cvecVal us, cvecVal ws] ++ rest ∧
    InDiscVec p ss.prod us ∧ InDiscVec p ss.prod ws

def Q53 (p α : ℕ) (ss ts : List ℕ) : List Val → List Val → Prop := fun vs out =>
  ∃ us ws rest zs, vs = [Val.int p, Val.int α, intList ss, intList ts, cvecVal us, cvecVal ws] ++ rest ∧
    out = cvecVal zs :: rest ∧
    Approx p zs (convC ss (fxVec p ss.prod us) (fxVec p ss.prod ws))
      ((2 ^ (2 * D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ) : ℝ)

/-- `γ = 2dα²` of the Gaussian resampling step (§5.1): `F_s = 2^γ B F_t A`. -/
def gpar (n : ℕ) : ℕ := 2 * HvdH.D * apar n ^ 2

/-- The error bound of the whole transform pipeline: `2^{γ+8} T² (log₂ T + 1)`. -/
def errP (n : ℕ) : ℕ := 2 ^ (gpar n + 8) * Tpar n ^ 2 * (Nat.log 2 (Tpar n) + 1)

/-- Size of the encoding of a fixed-point complex value. -/
theorem encodePosNum_eq_bits (p : PosNum) : Computability.encodePosNum p = (p : ℕ).bits := by
  induction p with
  | one => simp [Computability.encodePosNum, Nat.one_bits]
  | bit0 q ih =>
      simp only [Computability.encodePosNum]
      rw [ih, PosNum.cast_bit0,
        show (↑q + ↑q : ℕ) = 2 * (↑q) by ring, Nat.bit0_bits _ (Nat.ne_of_gt (PosNum.cast_pos q))]
  | bit1 q ih =>
      rw [Computability.encodePosNum, ih, PosNum.cast_bit1,
        show (↑q + ↑q + 1 : ℕ) = 2 * (↑q) + 1 by ring, Nat.bit1_bits]

theorem encodeNum_eq_bits (m : Num) : Computability.encodeNum m = (m : ℕ).bits := by
  induction m with
  | zero => simp [Computability.encodeNum, Nat.zero_bits]
  | pos p => simpa [Computability.encodeNum] using encodePosNum_eq_bits p

theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  simp only [Computability.encodeNat, encodeNum_eq_bits, Num.to_of_nat]
  exact Nat.size_eq_bits_len n

/-- Size of an integer value: `vsz (.int z) = isz z`. -/
@[simp] theorem vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  simp only [Val.enc, vsz, List.length_cons, List.length_append, List.length_map,
    List.length_nil, isz, encodeNat_length]

theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

@[simp] theorem vsz_cfxVal (z : ℤ × ℤ) : vsz (cfxVal z) = isz z.1 + isz z.2 + 1 := by
  simp [cfxVal, vsz_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end Work.Main
