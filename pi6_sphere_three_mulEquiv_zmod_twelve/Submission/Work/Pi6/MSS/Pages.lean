import Mathlib
import Submission.Work.Pi6.MSS.CohFilt
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The pages of the spectral sequence of a filtered cochain complex with a product

For `W : CohFilt 𝕜` we define, in the standard way (`REFS/NOTES_LEAD_PI6.md` §3.2), the
submodules

* `pZ W r s n ⊆ C^n` — the elements of `F^s C^n` whose coboundary lies in `F^{s+r} C^{n+1}`,
* `pB W r s n ⊆ C^n` — `F^s C^n ∩ d(F^{s-r+1} C^{n-1})`,
* `pDen W r s n = pZ W (r-1) (s+1) n + pB W r s n` — the denominator of `E_r^s`,

the **page** `pEraw W r s n = Z_r^s / (Z_{r-1}^{s+1} + B_r^s)` (a subquotient of `C^n`), and the
induced differential `pD W r s n : E_r^s → E_r^{s+r}` (in cohomological degree `n → n+1`).

All arithmetic is done with `ℕ`-indices `(s, n)` (filtration degree, cohomological degree), which
makes the differential cast-free; the passage to the bidegree indexing `(s,q)`, `n = s+q` used by
`Work.Pi6.CohSS` is in `Submission/Work/Pi6/MSS/Assemble.lean`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable

variable (𝕜 : Type) [CommRing 𝕜] (W : CohFilt 𝕜)

/-- `Z_r^s` in cohomological degree `n`: the elements of `F^s C^n` whose coboundary lies in
`F^{s+r} C^{n+1}`. -/
def pZ (r s n : ℕ) : Submodule 𝕜 (W.C.X n) :=
  W.F s n ⊓ (W.F (s+r) (n+1)).comap (W.d n)

/-- `B_r^s` in cohomological degree `n`: `F^s C^n ∩ d(F^{s-r+1} C^{n-1})`, where `F^k` for
`k ≤ 0` means `F^0 = C`.  In `ℕ`-arithmetic the truncated index is `s + 1 - r` (which is `0`, i.e.
`F^0`, exactly when `r > s + 1`).  (Beware: `s - r + 1` parses as `(s - r) + 1`, which is `1` when
`r ≥ s` — that is *not* the standard `B_r^s`; see `Submission/Work/Pi6/MSS/NOTES_MSS.md`.) -/
def pB (r s n : ℕ) : Submodule 𝕜 (W.C.X n) :=
  W.F s n ⊓ (W.F (s + 1 - r) (n-1)).map (W.dPrev n)

/-- The denominator `Z_{r-1}^{s+1} + B_r^s` of `E_r^s`. -/
def pDen (r s n : ℕ) : Submodule 𝕜 (W.C.X n) :=
  pZ 𝕜 W (r-1) (s+1) n ⊔ pB 𝕜 W r s n

/-- The **page** `E_r^s` in cohomological degree `n`, as the subquotient
`Z_r^s / (Z_{r-1}^{s+1} + B_r^s)` of `C^n`. -/
def pEraw (r s n : ℕ) : ModuleCat 𝕜 :=
  ModuleCat.of 𝕜 (↥(pZ 𝕜 W r s n) ⧸ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype))

/-- The restriction of the coboundary to `Z_r^s`, landing in `Z_r^{s+r}`
(this is `0` on the junk branch when the required inclusion fails — it never does, see
`Work.Pi6.MSS.pZ_leib`). -/
def pZmap (r s n : ℕ) : ↥(pZ 𝕜 W r s n) →ₗ[𝕜] ↥(pZ 𝕜 W r (s+r) (n+1)) :=
  if h : ∀ x : ↥(pZ 𝕜 W r s n), W.d n (x : W.C.X n) ∈ pZ 𝕜 W r (s+r) (n+1) then
    LinearMap.codRestrict (pZ 𝕜 W r (s+r) (n+1)) ((W.d n).comp (pZ 𝕜 W r s n).subtype) h
  else 0

/-- The **differential** `d_r : E_r^s → E_r^{s+r}` (from cohomological degree `n` to `n+1`),
the map induced by the coboundary. -/
def pD (r s n : ℕ) : pEraw 𝕜 W r s n ⟶ pEraw 𝕜 W r (s+r) (n+1) :=
  if h : (pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype ≤
      ((pDen 𝕜 W r (s+r) (n+1)).comap (pZ 𝕜 W r (s+r) (n+1)).subtype).comap
        (pZmap 𝕜 W r s n) then
    ModuleCat.ofHom (Submodule.mapQ _ _ (pZmap 𝕜 W r s n) h)
  else 0

end

end Work.Pi6.MSS
