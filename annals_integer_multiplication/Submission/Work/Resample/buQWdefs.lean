import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.sliceB1defs

/-!
# `Work.Resample.buQWdefs`: the list-level specification of the one-dimensional `B̃` word

The target `Work.Resample.buQW` constructs a program `q` computing the map `buPhi` of `sliceBu`
(paper Lemmas 4.8--4.12) on the input vector, reading the static table `buTabList`.

This module fixes the *list-level* functions computed by the successive stages of that program, so
that each stage can be stated as a `WordR` triple whose `Post` mentions one of these functions, and
so that the corresponding `Fin`-level objects (`buPhi`, `buRound`, `buJsum`, `buDsc`) can be
related to them by pure list arithmetic (no programs).

Everything here is a definition; the lemmas live in `buQWlist`/`buQWkey`/...
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## elementary list operations on vectors of fixed-point complex numbers -/

/-- Halving of a fixed-point pair, as used by `buPhi` (`C̃` followed by the halving). -/
def buHalve (z : ℤ × ℤ) : ℤ × ℤ := (Int.tdiv z.1 2, Int.tdiv z.2 2)

/-- **Stage 1 target**: read the input vector at the indices `egNu s t ℓ` (`ℓ < s`, the fused map
`C̃ ∘ P̃_t`) and halve.  `buSelL s t u` has length `s` when `u.length = t`. -/
def buSelL (s t : ℕ) (u : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  List.ofFn (fun ℓ : Fin s => buHalve (u.getD (egNu s t (ℓ : ℕ)) (0, 0)))

/-- Rotate left by `k` (only used with `k < length`). -/
def buRot (k : ℕ) (v : List (ℤ × ℤ)) : List (ℤ × ℤ) := v.drop k ++ v.take k

/-- Pointwise multiplication of a vector by an integer column. -/
def buMulCol (col : List ℤ) (v : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (col.zip v).map (fun a => (a.1 * a.2.1, a.1 * a.2.2))

/-- Pointwise addition of two vectors (truncated at the shorter one). -/
def buAddV : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | a :: as, b :: bs => (a.1 + b.1, a.2 + b.2) :: buAddV as bs
  | _, _ => []

/-- Scalar multiplication of a vector. -/
def buSMulV (c : ℤ) (v : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  v.map (fun z => (c * z.1, c * z.2))

/-- Pointwise division by `2^p` (truncated). -/
def buTdivV (p : ℕ) (v : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  v.map (fun z => (Int.tdiv z.1 ((2 : ℤ) ^ p), Int.tdiv z.2 ((2 : ℤ) ^ p)))

/-- The vector of the weights of the shift `h` (as a `List ℤ`). -/
def buColL (Wt : ℤ → ℤ → ℤ) (s : ℕ) (h : ℤ) : List ℤ :=
  List.ofFn (fun ℓ : Fin s => Wt (ℓ : ℤ) h)

/-- The columns of the weight table, in the order of the shift list `egHs m`. -/
def buColsL (Wt : ℤ → ℤ → ℤ) (s m : ℕ) : List (ℤ × List ℤ) :=
  (egHs m).map (fun h => (h, buColL Wt s h))

/-- The shifts written with their `ℤ → ℕ` reduction `h ↦ (h % s).toNat` (for the rotation). -/
def buColsN (Wt : ℤ → ℤ → ℤ) (s m : ℕ) : List (ℕ × List ℤ) :=
  (buColsL Wt s m).map (fun hc => ((hc.1 % (s : ℤ)).toNat, hc.2))

/-- **Stage 2 target**: one Neumann round `Ẽ`, computed as the fold of the columns over the shifts
(the initial accumulator is the zero vector, the fold adds `colₕ ⊙ (v rotated by h)`, and the
result is divided by `2^p`). -/
def buRoundL (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) (v : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  buTdivV p (List.foldl (fun acc hc => buAddV acc (buMulCol hc.2 (buRot hc.1 v)))
    (List.replicate s (0, 0)) (buColsN Wt s m))

/-- The list of the signs consumed by the Neumann fold: `(-1)^{j+1}` for `j < n-1`. -/
def buSignsL (n : ℕ) : List ℤ := (List.range (n - 1)).map (fun j => (-1 : ℤ) ^ (j + 1))

/-- **Stage 3 target**: the Neumann sum, mirroring the program: start with `(v, v)`, and for each
sign `σ` compute `v ↦ round v`, `acc ↦ acc + σ • v`; the result is the second component. -/
def buJsumL (Wt : ℤ → ℤ → ℤ) (p s m n : ℕ) (v : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (List.foldl (fun st σ =>
      let v' := buRoundL Wt p s m st.1
      (v', buAddV st.2 (buSMulV σ v'))) (v, v) (buSignsL n)).2

/-- **Stage 4 target**: the diagonal scaling `D̃'`. -/
def buDscL (Wd : ℤ → ℤ) (p s : ℕ) (u : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  ((List.ofFn (fun ℓ : Fin s => Wd (ℓ : ℤ))).zip u).map
    (fun a => (Int.tdiv (a.1 * a.2.1) ((2 : ℤ) ^ p), Int.tdiv (a.1 * a.2.2) ((2 : ℤ) ^ p)))

/-- **Stage 5 target**: the final permutation `P̃_sᵀ`. -/
noncomputable def buPermL (s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (d : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  List.ofFn (fun j : Fin s => d.getD ((egGam s t hs hcop j : Fin s) : ℕ) (0, 0))

/-- The pointwise decay bound of the Gaussian weights (`Work.Resample.egW_decay`). -/
noncomputable def egWBnd (α : ℕ) (h : ℤ) : ℝ :=
  if h.natAbs = 1 then Real.exp (-2 * Real.pi)
  else Real.exp (-(Real.pi * (α : ℝ) ^ 2 * ((h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1))))

/-- **The full list-level `B̃` map.** -/
noncomputable def buPhiL (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (u : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  buPermL s t hs hcop (buDscL (buWd p α s t) p s
    (buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) (buSelL s t u)))

end Work.Resample

namespace Work.Resample

open HvdH

/-! ## the entries of the static table, as separate values -/

/-- the key list of the fused `C̃ ∘ P̃_t` step (entry 6 of `buTabList`). -/
noncomputable def buKeysT (s t : ℕ) : Val :=
  zl (List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ)))

/-- the key list of the final `P̃_sᵀ` step (entry 7 of `buTabList`). -/
def buKeysS (s t : ℕ) : Val :=
  zl (List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ)))

/-- the diagonal weights `D̃'` (entry 8 of `buTabList`). -/
noncomputable def buWdL (p α s t : ℕ) : Val :=
  zl (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ)))

/-- the columns of the shift weights (entry 9 of `buTabList`). -/
noncomputable def buColsT (p α s t : ℕ) : Val :=
  ofList ((egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h)))

/-- the sign list of the Neumann fold (entry 10 of `buTabList`). -/
def buSignsT (p α s t : ℕ) : Val :=
  zl ((List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1)))

/-- `buTabList` in terms of the named entries. -/
theorem buTabList_eq (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) :
    buTabList p α s t hs hcop =
      [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int ((egM p α : ℕ) : ℤ),
       .int ((egN p α s t : ℕ) : ℤ), buKeysT s t, buKeysS s t, buWdL p α s t, buColsT p α s t,
       buSignsT p α s t] := rfl

/-! ## the size invariant of the work vectors -/

/-- `buIn B z`: the fixed-point pair `z` lies in the disc of (integer) radius `B`. -/
def buIn (B : ℕ) (z : ℤ × ℤ) : Prop := z.1 ^ 2 + z.2 ^ 2 ≤ (B : ℤ) ^ 2

/-- every entry of the vector `v` lies in the disc of radius `B`. -/
def buInV (B : ℕ) (v : List (ℤ × ℤ)) : Prop := ∀ z ∈ v, buIn B z

theorem buIn_coord {B : ℕ} {z : ℤ × ℤ} (h : buIn B z) : z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B := by
  have h1 : z.1 ^ 2 ≤ (B : ℤ) ^ 2 := by
    have hh : z.1 ^ 2 + z.2 ^ 2 ≤ (B : ℤ) ^ 2 := h
    nlinarith [sq_nonneg z.2]
  have h2 : z.2 ^ 2 ≤ (B : ℤ) ^ 2 := by
    have hh : z.1 ^ 2 + z.2 ^ 2 ≤ (B : ℤ) ^ 2 := h
    nlinarith [sq_nonneg z.1]
  constructor
  · have hh := (Int.natAbs_le_iff_sq_le).mpr h1
    rwa [Int.natAbs_natCast] at hh
  · have hh := (Int.natAbs_le_iff_sq_le).mpr h2
    rwa [Int.natAbs_natCast] at hh

theorem buInV_coord {B : ℕ} {v : List (ℤ × ℤ)} (h : buInV B v) {z : ℤ × ℤ} (hz : z ∈ v) :
    z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B := buIn_coord (h z hz)

theorem buIn_mono {B B' : ℕ} (h : B ≤ B') {z : ℤ × ℤ} (hz : buIn B z) : buIn B' z := by
  have h1 : (B : ℤ) ≤ (B' : ℤ) := by exact_mod_cast h
  have h0 : (0 : ℤ) ≤ (B : ℤ) := by positivity
  exact le_trans hz (pow_le_pow_left₀ h0 h1 2)

theorem buCmplxSqNorm (a b : ℝ) : ‖((a : ℂ) + (b : ℂ) * Complex.I)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

theorem buIn_add {B B' : ℕ} {x y : ℤ × ℤ} (hx : buIn B x) (hy : buIn B' y) :
    buIn (B + B') (x.1 + y.1, x.2 + y.2) := by
  set X : ℂ := ((x.1 : ℝ) : ℂ) + ((x.2 : ℝ) : ℂ) * Complex.I with hX
  set Y : ℂ := ((y.1 : ℝ) : ℂ) + ((y.2 : ℝ) : ℂ) * Complex.I with hY
  have hXn : ‖X‖ ^ 2 = (x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2 := by rw [hX]; exact buCmplxSqNorm _ _
  have hYn : ‖Y‖ ^ 2 = (y.1 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 := by rw [hY]; exact buCmplxSqNorm _ _
  have hxR : (x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by
    have h := hx; push_cast at h; exact_mod_cast h
  have hyR : (y.1 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 ≤ (B' : ℝ) ^ 2 := by
    have h := hy; push_cast at h; exact_mod_cast h
  have hXle : ‖X‖ ≤ (B : ℝ) := by
    have h1 : ‖X‖ ^ 2 ≤ (B : ℝ) ^ 2 := by rw [hXn]; exact hxR
    nlinarith [norm_nonneg X, (Nat.cast_nonneg B : (0 : ℝ) ≤ (B : ℝ))]
  have hYle : ‖Y‖ ≤ (B' : ℝ) := by
    have h1 : ‖Y‖ ^ 2 ≤ (B' : ℝ) ^ 2 := by rw [hYn]; exact hyR
    nlinarith [norm_nonneg Y, (Nat.cast_nonneg B' : (0 : ℝ) ≤ (B' : ℝ))]
  have hnorm : ‖X + Y‖ ≤ (B : ℝ) + B' := by
    have h := norm_add_le X Y; linarith
  have hXY : X + Y
      = (((x.1 + y.1 : ℤ) : ℝ) : ℂ) + (((x.2 + y.2 : ℤ) : ℝ) : ℂ) * Complex.I := by
    rw [hX, hY]; push_cast; ring
  have hnormXY : ‖X + Y‖ ^ 2
      = (((x.1 + y.1 : ℤ) : ℝ)) ^ 2 + (((x.2 + y.2 : ℤ) : ℝ)) ^ 2 := by
    rw [hXY, buCmplxSqNorm]
  have hBB : ((B : ℝ) + B') ^ 2 = ((((B + B' : ℕ)) : ℝ)) ^ 2 := by push_cast; ring
  have hcalc : (((x.1 + y.1 : ℤ) : ℝ)) ^ 2 + (((x.2 + y.2 : ℤ) : ℝ)) ^ 2
      ≤ ((((B + B' : ℕ)) : ℝ)) ^ 2 := by
    rw [← hnormXY, ← hBB]
    nlinarith [norm_nonneg (X + Y), (Nat.cast_nonneg B : (0 : ℝ) ≤ (B : ℝ)),
      (Nat.cast_nonneg B' : (0 : ℝ) ≤ (B' : ℝ))]
  exact_mod_cast hcalc

theorem inDisc_iff_buIn (p : ℕ) (z : ℤ × ℤ) : HvdH.inDisc p z ↔ buIn (2 ^ p) z := by
  have h : ((2 : ℤ) ^ p) ^ 2 = (4 : ℤ) ^ p := by
    rw [← pow_mul, show p * 2 = 2 * p by ring, pow_mul]; norm_num
  constructor
  · intro hz
    show z.1 ^ 2 + z.2 ^ 2 ≤ ((2 ^ p : ℕ) : ℤ) ^ 2
    push_cast
    rw [h]; exact hz
  · intro hz
    show z.1 ^ 2 + z.2 ^ 2 ≤ (4 : ℤ) ^ p
    have hz' : z.1 ^ 2 + z.2 ^ 2 ≤ ((2 ^ p : ℕ) : ℤ) ^ 2 := hz
    push_cast at hz'
    rwa [h] at hz'

end Work.Resample
