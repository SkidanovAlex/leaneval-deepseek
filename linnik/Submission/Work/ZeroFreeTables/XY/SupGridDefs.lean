/-
# ZeroFreeTables — SupGridDefs

Certified-evaluation kernels for the sup-estimates of the order-2 `λ₁`-estimate
(`Work.ZeroFreeTables.XY.SupBoundOrderTwo`).

The two quantities are
  `xySup1 lam t = 14900·ReΦ(1,t) − 30480·ReΦ(1−lam,t)`,
  `xySup2 lam t =  1250·ReΦ(1,t) −  6000·ReΦ(1−lam,t)`,
with `ReΦ(a,t) = ∫_0^{3/2} cos(tu)·xyP u·e^{a u} du`, where `xyP` is the quintic
`64/45 − (256/81)u² + (512/243)u³ − (2048/10935)u⁵` (HB Lemma 7.2's test function with
`λ = 4/3`; on `[0,3/2]` it is `xyT.f`).

Everything is built from the *exact* closed form of the two oscillatory integrals
  `CcN a t N = ∫_0^{3/2} u^N cos(tu) e^{au} du`, `ScN a t N = ∫_0^{3/2} u^N sin(tu) e^{au} du`,
obtained by integration by parts: with `λ` for `e^{3a/2}` and `p,q` for `cos(3t/2), sin(3t/2)`,

  `C_N = (3/2)^N λ (a p + t q)/(a²+t²) − (N/(a²+t²)) (a C_{N−1} + t S_{N−1})`,
  `S_N = (3/2)^N λ (a q − t p)/(a²+t²) − (N/(a²+t²)) (a S_{N−1} − t C_{N−1})`.

`CrecI` propagates rational *intervals* for `(C_N,S_N)`, `N ≤ 3`, through this recursion, and
`cosTay`/`sinTay` give rational intervals for `cos θ`, `sin θ` via Taylor's theorem.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.xyPolyDefs

open scoped BigOperators

namespace Work.ZeroFreeTables.XY

/-- Coefficients of the quintic `xyP`: `xyP u = Σ_n coeffP n * u^n`. -/
def coeffP : ℕ → ℚ
  | 0 => 64/45
  | 2 => -256/81
  | 3 => 512/243
  | 5 => -2048/10935
  | _ => 0

/-! ## Taylor intervals for `cos` and `sin` -/

/-- `N`-th Taylor polynomial of `cos` at `θ` (`(2N+1)-term partial sum`), as a rational. -/
def cosTP (θ : ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N+1), (-1:ℚ)^k * θ^(2*k) / ((2*k).factorial)

/-- `N`-th Taylor polynomial of `sin` at `θ`. -/
def sinTP (θ : ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N+1), (-1:ℚ)^k * θ^(2*k+1) / ((2*k+1).factorial)

/-- Rational upper bound for `θ^{2N+2}/(2N+2)!` (the Taylor remainder for `cos`). -/
def remC (θ : ℚ) (N : ℕ) : ℚ := |θ|^(2*N+2) / ((2*N+2).factorial)


/-- `CcN a t N = ∫_0^{3/2} u^N cos(tu) e^{au} du`. -/
noncomputable def CcN (a t : ℝ) (N : ℕ) : ℝ :=
  ∫ u in (0:ℝ)..(3/2), u^N * Real.cos (t*u) * Real.exp (a*u)

/-- `ScN a t N = ∫_0^{3/2} u^N sin(tu) e^{au} du`. -/
noncomputable def ScN (a t : ℝ) (N : ℕ) : ℝ :=
  ∫ u in (0:ℝ)..(3/2), u^N * Real.sin (t*u) * Real.exp (a*u)

/-- `ReΦ(a,t) = ∫_0^{3/2} cos(tu) xyP(u) e^{au} du`. -/
noncomputable def RePhi (a t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (xyP u) * Real.exp (a*u)

/-! ## Interval recursion for `(CcN, ScN)`, `N ≤ 3` -/

/-- One step of the interval recursion for `(CcN, ScN)`.  Given intervals `[cl,ch]`, `[sl,sh]`
for `(C_{n},S_{n})`, `[el,eh]` for `e^{3a/2}`, `[pl,ph]` for `cos(3t/2)` and `[ql,qh]` for
`sin(3t/2)` (with `0 ≤ a`, `0 ≤ t`, `0 < el`), returns intervals for `(C_{n+1},S_{n+1})`
valid whenever the inputs bracket the true values. -/
def Cstep (a t : ℚ) (el eh pl ph ql qh : ℚ) (n : ℕ) (prev : ℚ × ℚ × ℚ × ℚ) :
    ℚ × ℚ × ℚ × ℚ :=
  let cl := prev.1; let ch := prev.2.1; let sl := prev.2.2.1; let sh := prev.2.2.2
  let K := (3/2:ℚ)^(n+1) / (a^2+t^2)
  let K2 := ((n+1 : ℕ) : ℚ) / (a^2+t^2)
  let t1lo := K * (el * (a*pl + t*ql))
  let t1hi := K * (eh * (a*ph + t*qh))
  let t2lo := K2 * (a*cl + t*sl)
  let t2hi := K2 * (a*ch + t*sh)
  let u1lo := K * (el * (a*ql - t*ph))
  let u1hi := K * (eh * (a*qh - t*pl))
  let u2lo := K2 * (a*sl - t*ch)
  let u2hi := K2 * (a*sh - t*cl)
  (t1lo - t2hi, t1hi - t2lo, u1lo - u2hi, u1hi - u2lo)

/-- Interval recursion for `(CcN, ScN)`, `N = 0,1,2,3`. -/
def CrecI (a t : ℚ) (el eh pl ph ql qh : ℚ) : ℕ → ℚ × ℚ × ℚ × ℚ
  | 0 =>
    ((el*(a*pl+t*ql) - a)/(a^2+t^2), (eh*(a*ph+t*qh) - a)/(a^2+t^2),
     (el*(a*ql-t*ph) + t)/(a^2+t^2), (eh*(a*qh-t*pl) + t)/(a^2+t^2))
  | (n+1) => Cstep a t el eh pl ph ql qh n (CrecI a t el eh pl ph ql qh n)

end Work.ZeroFreeTables.XY
