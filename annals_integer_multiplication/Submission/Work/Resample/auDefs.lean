import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Fx.piDefs

/-!
# Fixed-point data for the 1-D Gaussian resampling word (paper Lemma 4.9)

This module fixes the objects of the one-dimensional windowed Gaussian resampling word
`Work.Resample.sliceAu`.  Nothing here is a program.

* `auM p α = (⌈√p⌉)·α` is the window half-width `m` of the paper and `auL p α = 2m+1` the
  number of terms retained for each output.
* `auK s t k = ⌊(2ks+t)/(2t)⌋ = round (k s / t)` is the window centre.
* `auN p α s t k i = t·(auK s t k + i - m) - s·k` is `t` times the distance of the `i`-th retained
  term of output `k` from `s k / t`; the exact matrix entry of `resA s t α` is the coset sum
  `Σ_{n ≡ auN (mod t·?)} …`, so the ideal weight of the `(k,i)` term is
  `auWi = (1/2α)·e^{−π (auN)²/(α²t²)}`.
* `auPi p` is the fixed-point value `2^{auPrec p}·π` (from `Work.Fx.uval`), `auWt p α t N` is the
  integer `2^p·(1/2α)·e^{−πN/(α²t²)}` computed by the fixed-point Horner recursion
  (`auH`, divisors `auNstep p, …, 1`), with the guard that weights below `e^{−(p+10)}` are `0`.
* `auRec`, `auTable`, `auPvals` are the static parameter block `P` handed from the table word
  `prep` to the resampling word `q`.
* `auPhi` is the resulting map `(Fin s → ℤ×ℤ) → (Fin t → ℤ×ℤ)`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- window half-width `m = (⌈√p⌉)·α` -/
def auM (p α : ℕ) : ℕ := (Nat.sqrt p + 1) * α

/-- window length `L = 2m+1` -/
def auL (p α : ℕ) : ℕ := 2 * auM p α + 1

/-- window centre `K k = ⌊(2ks+t)/(2t)⌋` -/
def auK (s t k : ℕ) : ℕ := (2 * k * s + t) / (2 * t)

/-- `t` times the distance of the `(k,i)`-th retained term from `s k/t`: `n = t(K k+i-m) - z k` -/
def auN (p α s t k i : ℕ) : ℤ :=
  (t : ℤ) * ((auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ)) - (s : ℤ) * (k : ℤ)

/-- the integer `n²` by which the weight of the `(k,i)`-th term is determined -/
def auNsq (p α s t k i : ℕ) : ℤ := (auN p α s t k i) ^ 2

/-- the input index of the `(k,i)`-th retained term -/
def auJ (p α s t k i : ℕ) : ℕ :=
  ((((auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ)) % (s : ℤ))).toNat

/-- the ideal (real) weight `(1/2α)·e^{−π n²/(α²t²)}` -/
noncomputable def auWi (p α s t k i : ℕ) : ℝ :=
  (1 / (2 * (α : ℝ))) *
    Real.exp (-(Real.pi * (auNsq p α s t k i : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))

/-- working precision exponent `P = 3p + 100` -/
def auPrec (p : ℕ) : ℕ := 3 * p + 100

/-- number of Horner steps used to evaluate the exponential -/
def auNstep (p : ℕ) : ℕ := 2 * auPrec p

/-- the fixed-point value of `2^{auPrec p}·π` (nested-square-root evaluation of `π`) -/
def auPi (p : ℕ) : ℤ := Work.Fx.uval (auPrec p)

/-- fixed-point representative of the exponent `2^{auPrec p}·π N/(α²t²)` -/
def auZ (p α t : ℕ) (N : ℤ) : ℤ :=
  Int.tdiv (auPi p * N) ((α : ℤ) ^ 2 * (t : ℤ) ^ 2)

/-- one step of the fixed-point Horner recursion for `Σ_{k≤j} (−y)^k/k!` at scale `2^P`:
`Q ↦ 2^P + ⌊⌊Z·Q/2^P⌋/d⌋` -/
def auH (p : ℕ) (Z : ℤ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ (auPrec p)
  | j + 1 => (2 : ℤ) ^ (auPrec p) +
      Int.tdiv (Int.tdiv (Z * auH p Z j) ((2 : ℤ) ^ (auPrec p))) ((auNstep p : ℤ) - (j : ℤ))

/-- the computed weight: `2^p·(1/2α)·e^{−πN/(α²t²)}` on the fixed-point working scale, rounded;
`0` when the exponent exceeds `p+10` (where the true weight is `< e^{-10}/4`) -/
def auWt (p α t : ℕ) (N : ℤ) : ℤ :=
  if auZ p α t N ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p) then
    Int.tdiv (auH p (-(auZ p α t N)) (auNstep p))
      ((2 : ℤ) ^ (auPrec p - p) * (2 * (α : ℤ)))
  else 0

/-- the offset `o = h₀ − m` (with `h₀` the least multiple of `z` that is `≥ m`): the extended
input array starts `o` cells before `u 0` -/
def auOff (p α s : ℕ) : ℕ := s * ((auM p α + s - 1) / s) - auM p α

/-- the number of copies of the input array needed for the extended array -/
def auCop (p α s : ℕ) : ℕ := (auOff p α s + 2 * s + 2 * auM p α) / s

/-- one table record: the slide `K(k+1) − K k` followed by the `L` weights of output `k` -/
def auRec (p α s t k : ℕ) : Val :=
  .cons (.int ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ)))
    (ofList ((List.range (auL p α)).map fun i => Val.int (auWt p α t (auNsq p α s t k i))))

/-- the table of all `t` records -/
def auTable (p α s t : ℕ) : Val := ofList ((List.range t).map fun k => auRec p α s t k)

/-- the static parameter block `P` -/
def auPvals (p α s t : ℕ) : List Val :=
  [.int (auOff p α s : ℤ), .int (auCop p α s : ℤ), .int (p : ℤ), auTable p α s t]

/-- the resulting map `Φ` -/
noncomputable def auPhi (p α s t : ℕ) : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ) :=
  fun w k =>
    ( Int.tdiv
        (∑ i ∈ Finset.range (auL p α),
          auWt p α t (auNsq p α s t k i) *
            (if h : auJ p α s t k i < s then w ⟨auJ p α s t k i, h⟩ else 0).1)
        ((2 : ℤ) ^ p),
      Int.tdiv
        (∑ i ∈ Finset.range (auL p α),
          auWt p α t (auNsq p α s t k i) *
            (if h : auJ p α s t k i < s then w ⟨auJ p α s t k i, h⟩ else 0).2)
        ((2 : ℤ) ^ p) )

/-! ## Basic facts -/

theorem auJ_lt (p α s t k i : ℕ) (hs : 2 ≤ s) : auJ p α s t k i < s := by
  have h1 : 0 ≤ ((auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ)) % (s : ℤ) := Int.emod_nonneg _ (by omega)
  have h2 : ((auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ)) % (s : ℤ) < (s : ℤ) :=
    Int.emod_lt_of_pos _ (by omega)
  simp only [auJ]
  rw [Int.toNat_lt h1]
  exact h2

/-- `auJ` is the residue class of the (unwrapped) window index -/
theorem auJ_cast (p α s t k i : ℕ) (hs : 2 ≤ s) :
    ((auJ p α s t k i : ℕ) : ℤ) = ((auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ)) % (s : ℤ) := by
  have h1 : 0 ≤ ((auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ)) % (s : ℤ) := Int.emod_nonneg _ (by omega)
  simp only [auJ]
  exact Int.toNat_of_nonneg h1

theorem auL_pos (p α : ℕ) : 0 < auL p α := by simp [auL]

theorem auNsq_nonneg (p α s t k i : ℕ) : 0 ≤ auNsq p α s t k i := sq_nonneg _

theorem auNsq_eq (p α s t k i : ℕ) :
    auNsq p α s t k i = ((auN p α s t k i).natAbs : ℤ) ^ 2 := by
  have h := Int.natAbs_mul_self (a := auN p α s t k i)
  rw [auNsq, pow_two, pow_two, ← h]
  push_cast
  ring

end Work.Resample
