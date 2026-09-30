import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the disc residue formula (`Work.BW.residue_disc`)

Let `S : Finset ℂ` be a finite set of "poles", `n : ℂ → ℕ` their multiplicities and `Y : ℂ → ℂ`.

* `rD S n z = ∏ p ∈ S, (z - p) ^ (n p)` — the global polynomial whose zero set is (contained in) `S`.
* `rDp S n p z = ∏ p' ∈ S.erase p, (z - p') ^ (n p')` — the same product with the factor of `p`
  removed.
* `rF Y S n z = Y z / rD S n z` — the meromorphic function whose poles are the points of `S`.
* `rU Y S n p w = Y (p + w) / rDp S n p (p + w)` — the local analytic function at `p`.
* `rC Y S n p i = iteratedDeriv i (rU Y S n p) 0 / i!` — the Taylor coefficients of `rU` at `0`.
* `rPrin a p N z = ∑_{i < N} a i * (z - p) ^ (i - N)` — the principal part at `p` cut at order `N`.
* `rRes a N = a (N-1)` if `0 < N` and `0` otherwise — the residue coefficient.
-/

namespace Work.BW

open Complex

/-- Global product `∏ p ∈ S, (z - p) ^ (n p)`. -/
noncomputable def rD (S : Finset ℂ) (n : ℂ → ℕ) : ℂ → ℂ :=
  fun z => ∏ p ∈ S, (z - p) ^ (n p)

/-- Product over all poles except `p`. -/
noncomputable def rDp (S : Finset ℂ) (n : ℂ → ℕ) (p : ℂ) : ℂ → ℂ :=
  fun z => ∏ p' ∈ S.erase p, (z - p') ^ (n p')

/-- The meromorphic function `Y / ∏ p ∈ S, (z-p)^(n p)`. -/
noncomputable def rF (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) : ℂ → ℂ :=
  fun z => Y z / rD S n z

/-- The function `Y / ∏_{p' ≠ p} (z - p') ^ (n p')`; analytic near `p`. -/
noncomputable def rU (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) (p : ℂ) : ℂ → ℂ :=
  fun w => Y (p + w) / rDp S n p (p + w)

/-- Taylor coefficients of `rU Y S n p` at `0`. -/
noncomputable def rC (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) (p : ℂ) (i : ℕ) : ℂ :=
  iteratedDeriv i (rU Y S n p) 0 / ((i.factorial : ℕ) : ℂ)

/-- Principal part of the pole at `p` of order `N`, with coefficients `a`. -/
noncomputable def rPrin (a : ℕ → ℂ) (p : ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => ∑ i ∈ Finset.range N, a i * (z - p) ^ ((i : ℤ) - (N : ℤ))

/-- The residue coefficient: `a (N-1)` for `0 < N`, and `0` otherwise. -/
noncomputable def rRes (a : ℕ → ℂ) (N : ℕ) : ℂ := if 0 < N then a (N - 1) else 0

end Work.BW

namespace Work.BW

open Complex

/-- `rF` with all principal parts subtracted. Analytic on the disc away from `S`. -/
noncomputable def rG (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) : ℂ → ℂ :=
  fun z => rF Y S n z - ∑ p ∈ S, rPrin (rC Y S n p) p (n p) z

/-- The "regular part" at `p`: the local analytic remainder `H p (z - p)` minus the principal
parts of the other poles (which are analytic near `p`). -/
noncomputable def rNice (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) (H : ℂ → ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  fun z => H p (z - p) - ∑ p' ∈ S.erase p, rPrin (rC Y S n p') p' (n p') z

/-- The function obtained from `rF` by subtracting all principal parts and then correcting the
values at the poles so that it becomes analytic on the disc. -/
noncomputable def rPhi (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) (H : ℂ → ℂ → ℂ) : ℂ → ℂ :=
  fun z => rG Y S n z + ∑ p ∈ S, (if z = p then rNice Y S n H p z - rG Y S n p else 0)

/-- The local expansion hypothesis at a point `p`, for a family `H` of local remainders. -/
def rIsExpansion (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) (H : ℂ → ℂ → ℂ) (p : ℂ) : Prop :=
  AnalyticAt ℂ (H p) 0 ∧
    (∀ w, rU Y S n p w = (∑ i ∈ Finset.range (n p), rC Y S n p i * w ^ i) + w ^ (n p) * H p w) ∧
    (∀ w ≠ 0, rF Y S n (p + w) = rPrin (rC Y S n p) p (n p) (p + w) + H p w)

end Work.BW
