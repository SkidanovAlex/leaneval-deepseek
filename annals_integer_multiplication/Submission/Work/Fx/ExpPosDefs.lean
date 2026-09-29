import Mathlib
import Submission.HvdH.Interfaces

/-!
# Definitions for the positive exponential field (paper Lemma 2.14)

Working precision `Q = 2p + 60` (so at least 60 guard bits above `p` and enough that the
`p`-dependent guard `E = 32·(p+60)` is negligible at scale `2^Q`).

Given `P ≈ 2^Q·π`, `L ≈ 2^Q·log 2`, `X = tdiv (P·j) k` we set
`Al = σ·L - X`, `T = tdiv (Al + L - 1) L`, `τ = max T 0`, `k₀ = σ - τ`,
`Z = X - k₀·L - E`, and after calling the complex-exponential word at precision `Q` with
argument `Z/2^Q` we truncate the output by `2^s` with `s = (p+60) + τ`.
-/

set_option autoImplicit false

namespace Work.Fx
open HvdH

/-- `A = p + 60`. -/
def epA (p : ℕ) : ℤ := (p : ℤ) + 60

/-- Working precision `Q = 2p + 60`. -/
def epQ (p : ℕ) : ℤ := 2 * (p : ℤ) + 60

/-- The guard `E = 32·(p+60)`. -/
def epE (p : ℕ) : ℤ := 32 * epA p

/-- `X = tdiv (P·j) k`. -/
def epX (P : ℤ) (j k : ℕ) : ℤ := Int.tdiv (P * (j : ℤ)) (k : ℤ)

/-- `Al = σ·L - X`. -/
def epAl (σ : ℕ) (L X : ℤ) : ℤ := (σ : ℤ) * L - X

/-- `T = tdiv (Al + L - 1) L`. -/
def epT (Al L : ℤ) : ℤ := Int.tdiv (Al + L - 1) L

/-- `τ = max T 0`. -/
def epTau (Al L : ℤ) : ℤ := max (epT Al L) 0

/-- `k₀ = σ - τ`. -/
def epK0 (σ : ℕ) (Al L : ℤ) : ℤ := (σ : ℤ) - epTau Al L

/-- `Z = X - k₀·L - E`. -/
def epZ (p σ : ℕ) (X L Al : ℤ) : ℤ := X - epK0 σ Al L * L - epE p

/-- The truncation exponent `s = A + τ`. -/
def epS (p : ℕ) (Al L : ℤ) : ℤ := epA p + epTau Al L

/-- Truncation of a coordinate by `2^s`. -/
def epSh (U s : ℤ) : ℤ := Int.tdiv U (2 ^ s.toNat)

/-- The fixed-point pair produced by the word. -/
def epW (p σ : ℕ) (Al L U V : ℤ) : ℤ × ℤ :=
  (epSh U (epS p Al L), epSh V (epS p Al L))

end Work.Fx

namespace Work.Fx

/-! ## Operational forms of the derived values (matching the word step by step) -/

/-- `X = tdiv (j·P) k` (the program multiplies `j` by `P`). -/
def epXw (j k : ℕ) (P : ℤ) : ℤ := Int.tdiv ((j : ℤ) * P) (k : ℤ)

/-- `Al = σ·L - X`. -/
def epAlw (σ : ℕ) (j k : ℕ) (P L : ℤ) : ℤ := (σ : ℤ) * L - epXw j k P

/-- `T = tdiv (Al + (L-1)) L`. -/
def epTw (σ : ℕ) (j k : ℕ) (P L : ℤ) : ℤ := Int.tdiv (epAlw σ j k P L + (L - 1)) L

/-- `τ = max 0 T`. -/
def epTauw (σ : ℕ) (j k : ℕ) (P L : ℤ) : ℤ := max 0 (epTw σ j k P L)

/-- `k₀ = σ - τ`. -/
def epK0w (σ : ℕ) (j k : ℕ) (P L : ℤ) : ℤ := (σ : ℤ) - epTauw σ j k P L

/-- `s = (A + σ) - k₀` with `A = p + 60`. -/
def epSw (p σ : ℕ) (j k : ℕ) (P L : ℤ) : ℤ := ((60 + (p : ℤ)) + (σ : ℤ)) - epK0w σ j k P L

/-- `Z = (X - k₀·L) - E`. -/
def epZw (p σ : ℕ) (j k : ℕ) (P L : ℤ) : ℤ :=
  (epXw j k P - epK0w σ j k P L * L) - (32 * (60 + (p : ℤ)))

/-- Truncation of a coordinate by `2^s`. -/
def epW1w (p σ : ℕ) (j k : ℕ) (P L U : ℤ) : ℤ := Int.tdiv U (2 ^ (epSw p σ j k P L).toNat)

end Work.Fx
