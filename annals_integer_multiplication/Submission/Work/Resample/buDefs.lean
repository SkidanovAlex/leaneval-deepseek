import Mathlib
import Submission.Work.Resample.fx
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.auDefs

namespace Work.Resample

open HvdH

/-! ## A program-computable weight table for the one-dimensional `B̃` word

The weights `egW s t α ℓ h = exp(-π α² ((t h/s + β_ℓ)² - (β_{ℓ+h})²))` of `sliceB1defs` are real
numbers; their rounded values `egWi = rnd (2^p * egW)` are *not* computable by any program (the
rounding of a transcendental number cannot be decided).  For the word-level statement we therefore
fix a *definite integer recursion* computing these weights, in the same way as the `Ã` word of the
paper Lemma 4.9 fixes `auWt` through the Horner recursion `auH` of `auDefs.lean`. -/

/-- `β_n · s = t n - [t n/s] · s`, an integer of absolute value `≤ s/2`. -/
noncomputable def buBeta (s t : ℕ) (n : ℤ) : ℤ := (t : ℤ) * n - HvdH.rnd ((t : ℝ) * (n : ℝ) / (s : ℝ)) * (s : ℤ)

/-- `s² · ((t h/s + β_ℓ)² - (β_{ℓ+h})²)`, the integer numerator of the exponent of `W(ℓ,h)`. -/
noncomputable def buN (s t : ℕ) (ℓ h : ℤ) : ℤ := (t * h + buBeta s t ℓ) ^ 2 - (buBeta s t (ℓ + h)) ^ 2

/-- The working-scale exponent `⌊2^P · π α² N / s²⌋` (`P = auPrec p`). -/
noncomputable def buZ (p α s t : ℕ) (ℓ h : ℤ) : ℤ :=
  Int.tdiv (auPi p * ((α : ℤ) ^ 2 * buN s t ℓ h)) ((s : ℤ) ^ 2)

/-- The tabulated weight `≈ 2^p · egW s t α ℓ h`: the fixed-point Horner recursion `auH` of the
exponent, with the same guard as `auWt` — weights whose exponent exceeds `p + 10` (where the true
weight is `< e^{-10} < 4·2^{-p}`) are set to `0`, which the truncated Taylor recursion could not
compute anyway. -/
noncomputable def buWt (p α s t : ℕ) (ℓ h : ℤ) : ℤ :=
  if buZ p α s t ℓ h ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ (auPrec p) then
    Int.tdiv (auH p (-(buZ p α s t ℓ h)) (auNstep p)) ((2 : ℤ) ^ (auPrec p - p))
  else 0

/-- The working-scale exponent of `d'_ℓ = e^{π α² β_ℓ²}/2^{2α²-2}`. -/
noncomputable def buZb (p α s t : ℕ) (ℓ : ℤ) : ℤ :=
  Int.tdiv (auPi p * ((α : ℤ) ^ 2 * (buBeta s t ℓ) ^ 2)) ((s : ℤ) ^ 2)

/-- The tabulated diagonal weight `≈ 2^p · d'_ℓ = 2^p · e^{π α² β_ℓ²}/2^{2α²-2}` (note the POSITIVE
exponent, matching `HvdH.diagD'`; `auH p Z ≈ 2^{auPrec p}·e^{Z/2^{auPrec p}}`, whence the argument
`+buZb p α s t ℓ`). -/
noncomputable def buWd (p α s t : ℕ) (ℓ : ℤ) : ℤ :=
  Int.tdiv (auH p (buZb p α s t ℓ) (auNstep p))
    ((2 : ℤ) ^ (auPrec p - p + (2 * α ^ 2 - 2)))

/-! ## The one-dimensional `B̃` word, uniformly over the weight table

`buRound Wt`, `buIter Wt`, `buJsum Wt`, `buDsc Wd`, `buPhi Wt Wd` generalise `egERound`, `egIter`,
`egJsum`, `egDsc`, `egPhi` of `sliceB1defs` to an arbitrary tabulated weight function `Wt`; the
specialisations `Wt := egWi`, `Wd := egWd` recover the originals, and `Wt := buWt`, `Wd := buWd`
give the values a program can actually compute. -/

/-- One truncated Gaussian convolution with tabulated weights. -/
noncomputable def buRound (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun ℓ =>
    (Int.tdiv (∑ h ∈ egHset (egM p α), Wt (ℓ : ℤ) h * (v (egIdx s hs ((ℓ : ℤ) + h))).1)
        ((2 : ℤ) ^ p),
     Int.tdiv (∑ h ∈ egHset (egM p α), Wt (ℓ : ℤ) h * (v (egIdx s hs ((ℓ : ℤ) + h))).2)
        ((2 : ℤ) ^ p))

/-- The iterates of the Neumann round. -/
noncomputable def buIter (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) : ℕ → Fin s → ℤ × ℤ
  | 0 => v
  | (j + 1) => buRound Wt p α s t hs (buIter Wt p α s t hs v j)

/-- The alternating (Neumann) sum. -/
noncomputable def buJsum (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun ℓ =>
    ((∑ j ∈ Finset.range (egN p α s t), ((-1 : ℤ) ^ j) * (buIter Wt p α s t hs v j ℓ).1),
     (∑ j ∈ Finset.range (egN p α s t), ((-1 : ℤ) ^ j) * (buIter Wt p α s t hs v j ℓ).2))

/-- The `D̃'` scaling with tabulated diagonal weights. -/
noncomputable def buDsc (Wd : ℤ → ℤ) (p s : ℕ) (u : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun ℓ => (Int.tdiv (Wd (ℓ : ℤ) * (u ℓ).1) ((2 : ℤ) ^ p),
            Int.tdiv (Wd (ℓ : ℤ) * (u ℓ).2) ((2 : ℤ) ^ p))

/-- The map computed by the `B̃` word. -/
noncomputable def buPhi (Wt : ℤ → ℤ → ℤ) (Wd : ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) :
    (Fin t → ℤ × ℤ) → (Fin s → ℤ × ℤ) :=
  fun w =>
    (let z : Fin s → ℤ × ℤ := fun ℓ => egGet w (egNu s t (ℓ : ℕ))
     let v0 : Fin s → ℤ × ℤ := fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)
     let u := buJsum Wt p α s t hs v0
     let d := buDsc Wd p s u
     fun j : Fin s => egGet d ((egGam s t hs hcop j : Fin s) : ℕ))

/-! ## The static table produced by `prep` -/

/-- The column of tabulated weights of the shift `h`. -/
noncomputable def buCol (p α s t : ℕ) (h : ℤ) : Val :=
  zl (List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h))

/-- The static table `P` of the `B̃` word (same layout as `egTabList`, with computable weights). -/
noncomputable def buTabList (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) : List Val :=
  [ .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int ((egM p α : ℕ) : ℤ),
    .int ((egN p α s t : ℕ) : ℤ),
    zl (List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ))),
    zl (List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ))),
    zl (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))),
    ofList ((egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h))),
    zl ((List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1))) ]



end Work.Resample
