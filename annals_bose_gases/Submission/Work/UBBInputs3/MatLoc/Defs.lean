import Mathlib.Analysis.Complex.Norm
import Submission.Work.UBBInputs3.MatLoc.Interval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.Defs` — the Lieb–Solovej "localization of large matrices"

FS `final_v2.tex` §7 (`sec:LocMatrices`) prove their `lem:LocMatrices` by applying the
following theorem *from the literature* (Lieb–Solovej, *Ground state energy of the
one-component charged Bose gas*, CMP **217** (2001), Appendix; stated identically as
`thm:Localizing large matrices` in LSSY and in Brietzke–Solovej):

> Let `A` be an `(N+1)×(N+1)` Hermitian matrix, `A^k` its `k`-th supra/infra-diagonal,
> `ψ` a unit vector, `d_k = ⟪ψ, A^k ψ⟫`, `λ = ⟪ψ, Aψ⟫ = Σ_k d_k`. For every `M ≤ N+1`
> there is a unit vector `φ` supported in a window of `M` consecutive indices with
> `⟪φ, Aφ⟫ ≤ λ + (C/M²)Σ_{k<M} k²|d_k| + CΣ_{k≥M}|d_k|`.

**This chapter proves that theorem** — it is pure finite-dimensional linear algebra, hence
*not* an external input of the project's proof: `MatLoc.Main.ls_localisation`, with the
universal constant `C = 100`, together with the *band ≤ 2* corollary
(`MatLoc.Main.ls_localisation_band2`) that is the form FS and Brietzke–Solovej apply, and
the transfer to `Matrix (Fin n) (Fin n) ℂ` (`MatLoc.Main.ls_localisation_matrix`).

## The proof, following Lieb–Solovej verbatim

Everything is extended to `ℤ` (the finite index set is `iRange n = [0,n-1]`, `A` vanishes
outside `iRange n × iRange n`), which is what removes the boundary problem of a naive
partition of unity.  With the **triangle profile** `tri p` (`p = (M-1)/2`, support
`[-p,p]`, values `p+1, p, …, 1`) normalised to `prof`, and the window vectors

    winVec p ψ m  =  fun j => (prof p (j - m) : ℂ) * ψ j       (m ∈ ℤ),

Lieb–Solovej's computation is, with `R(k) = Σ_s prof(s) prof(s+k)` and
`γ_k = ½Σ_s (prof(s+k) - prof(s))² = 1 - R(k)`,

    Σ_m ⟪φ_m, A φ_m⟫ = Σ_k R(k) d_k = λ - Σ_{k≥1} γ_k d_k ,

using `Σ_s prof(s)² = 1` and `Σ_s prof(s+k)² = 1`.  With `σ := -Σ_{k≥1} γ_k d_k` the
numbers `K_m = ⟪φ_m,Aφ_m⟫ - (λ+σ)⟪φ_m,φ_m⟫` satisfy `Σ_m K_m = 0`, so some `m` with
`φ_m ≠ 0` has `K_m ≤ 0`; normalising gives `⟪φ,Aφ⟫ ≤ λ + σ ≤ λ + Σ_k γ_k|d_k|`.  The
profile estimate is the pair

    γ_k ≤ ½ k² G       (telescoping: ‖T^k f - f‖ ≤ k‖Tf - f‖, G = Σ_s (prof(s+1)-prof(s))²)
    γ_k ≤ 2            (Cauchy–Schwarz / triangle inequality)

together with the *exact* computation `G = 24/(2p²+4p+3)` (from
`Σ_s tri² = (p+1)(2p²+4p+3)/3` and `Σ_s (tri(s+1)-tri(s))² = 8(p+1)`), which yields
`G ≤ 48/M²` for `p = (M-1)/2` and hence, by `min(24k²/M², 2) ≤ 100k²/(k²+M²)`, the claim
with `C = 100`.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3

/-! ## 1. The index range -/

/-- The index range `[0,n-1]` of a length-`n` vector. -/
def iRange (n : ℕ) : Finset ℤ := Finset.Icc 0 ((n : ℤ) - 1)

/-- The finite range of the translation parameter `m`: with `ψ` supported in `iRange n`
and `prof` in `[-p,p]`, `winVec p ψ m` can be nonzero only for `m ∈ [-p, n-1+p]`. -/
def mRange (p : ℕ) (n : ℕ) : Finset ℤ := Finset.Icc (-(p : ℤ)) ((n : ℤ) - 1 + (p : ℤ))

/-! ## 2. The profile -/

/-- The **triangle profile** of half-width `p`: `tri p s = max 0 (p+1-|s|)`, supported on
`[-p,p]`, with values `p+1, p, …, 1`. -/
def tri (p : ℕ) (s : ℤ) : ℝ := max 0 ((p : ℝ) + 1 - |(s : ℝ)|)

/-- The squared mass `Σ_s tri(s)²` of the triangle profile. -/
def triMass (p : ℕ) : ℝ := ∑ s ∈ Finset.Icc (-(p : ℤ)) (p : ℤ), (tri p s) ^ 2

/-- The **normalised profile** `prof p s = tri p s / √(triMass p)`, so that
`Σ_s prof(s)² = 1`. -/
def prof (p : ℕ) (s : ℤ) : ℝ := tri p s / Real.sqrt (triMass p)

/-- The **autocorrelation** `R(k) = Σ_s prof(s) prof(s+k)` of the profile. -/
def Rcorr (p : ℕ) (k : ℤ) : ℝ :=
  ∑ s ∈ Finset.Icc (-(p : ℤ)) (p : ℤ), prof p s * prof p (s + k)

/-- The Lieb–Solovej **deficit** `γ_k = ½ Σ_s (prof(s+k) - prof(s))² = 1 - R(k)`.
The summation range `[-p-|k|, p+|k|]` contains every index at which one of `s`, `s+k`
lies in the support `[-p,p]`. -/
def gamma (p : ℕ) (k : ℤ) : ℝ :=
  (1 / 2) * ∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
      (prof p (s + k) - prof p s) ^ 2

/-- The first-difference energy `G = Σ_s (prof(s+1) - prof(s))²` of the profile. -/
def profG (p : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1), (prof p (s + 1) - prof p s) ^ 2

/-! ## 3. The matrix data -/

/-- The **sesquilinear form** of `A` on `φ, χ` over the finite index set `R`:
`Σ_{i,j∈R} conj(φ i) A i j χ j`, as a real number (its real part). -/
def qform (A : ℤ → ℤ → ℂ) (R : Finset ℤ) (φ χ : ℤ → ℂ) : ℝ :=
  (∑ i ∈ R, ∑ j ∈ R, star (φ i) * A i j * χ j).re

/-- The `k`-th **supra-diagonal expectation** `Σ_i conj(ψ i) A i (i+k) ψ (i+k)`, as a real
number.  For `k = 0` this is the diagonal expectation `Σ_i |ψ_i|² A_{ii}`. -/
def dSup (A : ℤ → ℤ → ℂ) (n : ℕ) (ψ : ℤ → ℂ) (k : ℤ) : ℝ :=
  (∑ i ∈ iRange n, star (ψ i) * A i (i + k) * ψ (i + k)).re

/-- The `k`-th **diagonal expectation** `d_k = ⟪ψ, A^{(k)}ψ⟫`: for `k = 0` the diagonal
expectation (equal to `dSup 0`), and for `k ≠ 0` the sum of the supra- and infra-diagonal
parts (equal to `2 * dSup k` for Hermitian `A`, since `dSup (-k) = dSup k`).  The sum
`Σ_{k} d_k` is `λ = ⟪ψ,Aψ⟫`. -/
def dk (A : ℤ → ℤ → ℂ) (n : ℕ) (ψ : ℤ → ℂ) (k : ℤ) : ℝ :=
  if k = 0 then dSup A n ψ 0 else dSup A n ψ k + dSup A n ψ (-k)

/-- The squared norm `Σ_{j∈R} ‖φ j‖²` of a vector. -/
def normSq (R : Finset ℤ) (φ : ℤ → ℂ) : ℝ := ∑ j ∈ R, ‖φ j‖ ^ 2

/-- The **window vector** `φ_m`: `φ_m j = prof p (j - m) * ψ j`. -/
def winVec (p : ℕ) (ψ : ℤ → ℂ) (m : ℤ) : ℤ → ℂ :=
  fun j => (prof p (j - m) : ℂ) * ψ j

end Work.UBBInputs3
