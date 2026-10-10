import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.Machinery
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.ordPlaceAPI
import Submission.Work.MotV.affLocal
import Submission.Work.MotV.infPlace_isRatPlace
import Submission.Work.MotV.invDeriv
import Submission.Work.MotV.invDerivOnA
import Submission.Work.MotV.invDerivLocalC
import Submission.Work.MotV.infLocal
import Submission.Work.MotV.supportAff
import Submission.Work.MotV.supportInf
import Submission.Work.MotV.sumA
import Submission.Work.MotV.degreeZero
import Submission.Work.MotV.fibreNorm
import Submission.Work.MotV.regularConst
import Submission.Work.MotV.mainCaseC
import Submission.Work.MotV.derivZeroPow
import Submission.Work.MotV.derivZeroConst
import Submission.Work.MotV.derivAll

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero



/-- Node H1 (Hurwitz-lite for an elliptic curve, the critical path of route V).  Over an
algebraically closed field `N` with `ringChar N ≠ 5`, an element `r` of `N(E)` whose value
`r * (r - 1)` is a fifth power at every `ℤᵐ⁰`-valued valuation trivial on `N` is constant.

Equivalently (`N` algebraically closed, so all closed points are rational and every nontrivial
valuation trivial on `N` is the order at a closed point): `5 ∣ ord_Q (r(r-1))` at every point `Q`
of `E`, and the conclusion is that `r` is constant.

Route (§3 of the design).  The point valuations and the principal-divisor facts can be taken from
`Work.MotC2.AffPlace`, `Work.MotC2.InfPlace`, `Work.MotC2.PoleOrder` once those are proved, or
built here with `IsDedekindDomain.HeightOneSpectrum.valuation` for the height-one primes of the
affine coordinate ring (Mathlib's `AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing` has the
norm/degree API `CoordinateRing.degree_norm_smul_basis`).
Let `∂` be the invariant derivation of `N(E)`: `∂x = 2y + a₁x + a₃`,
`∂y = 3x² + 2a₂x + a₄ - a₁y` (it preserves the Weierstrass relation).

1. **Local bound.**  `∂` preserves every local ring `O_Q` of a closed point, including `O_∞`
   (check on the generators `1/x`, `y/x²`), and maps a uniformiser to a unit: at an affine point
   `Q = (x₀,y₀)` use `x - x₀` if `∂x(Q) = 2y₀ + a₁x₀ + a₃ ≠ 0`, otherwise use `y - y₀` and
   `∂y(Q) = 3x₀² + 2a₂x₀ + a₄ - a₁y₀ ≠ 0` by nonsingularity; at `∞` use `x/y`, whose `∂`-image
   `(-x³ + a₄x + 2a₆ - a₃y)/y²` has order `0` in every characteristic.  Hence
   `ord_Q (∂f) ≥ ord_Q (f - f(Q)) - 1` at zeros and `≥ ord_Q f - 1` at poles.
2. **Reduce to `∂r ≠ 0`.**  In characteristic `p`, `ker ∂ = N(E)^p`; if `∂r = 0` replace `r` by
   `r^(1/p)` (the hypothesis survives because `p ≠ 5`, so `r(r-1)` is still fifth-power valued),
   and iterate.
3. **Count.**  Let `n` be the number of poles of `r` counted with multiplicity; the zeros of `r`
   and of `r - 1` also number `n` with multiplicity, and all multiplicities of the fibres over
   `0`, `1`, `∞` are `≥ 5` by the hypothesis, so each of these three fibres has at most `n/5`
   points.  Summing `ord_Q (∂r) ≥ ord_Q (r - r(Q)) - 1` over all `Q` and using
   `∑_Q ord_Q (∂r) = 0` (the degree of the divisor of a derivation on a curve is `0`) gives
   `0 ≥ (n - z₀) + (n - z₁) - (n + z_∞) ≥ 2n/5 ≥ 0`, forcing `n = 0`.  Equivalently, for
   separable `r` of degree `n`, Riemann–Hurwitz gives `2n - 2 ≥ 12n/5`, forcing `n = 0`.
`char ≠ 5` is necessary: in characteristic 5, `r = s⁵` is a counterexample. -/
theorem hurwitz_five {N : Type*} [Field N] [IsAlgClosed N] (hN : ringChar N ≠ 5)
    (E : WeierstrassCurve N) [E.IsElliptic] (r : Affine.FunctionField E)
    (hr : FifthPowerValued N (r * (r - 1))) : ∃ c : N, algebraMap N _ c = r := by
  classical
  letI : DecidableEq N := Classical.decEq N
  -- the point at infinity is a rational place
  have hInfRat : MotC2.IsRatPlace E (MotC2.infPlace E) := infPlace_isRatPlace E
  have hInfL := infLocal E hInfRat
  -- the order API at an arbitrary rational place
  have hMul : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
      (f g : MotC2.Func E), f ≠ 0 → g ≠ 0 →
      ordOfPlace E S hS (f * g) = ordOfPlace E S hS f + ordOfPlace E S hS g :=
    fun S hS => (ordPlaceAPI E S hS).1
  have hInv : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
      (f : MotC2.Func E), f ≠ 0 → ordOfPlace E S hS f⁻¹ = - ordOfPlace E S hS f :=
    fun S hS => (ordPlaceAPI E S hS).2.1
  have hNonneg : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
      (f : MotC2.Func E), 0 ≤ ordOfPlace E S hS f ↔ f ∈ S :=
    fun S hS => (ordPlaceAPI E S hS).2.2.1
  have hAdd : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
      (f g : MotC2.Func E), f + g ≠ 0 →
      min (ordOfPlace E S hS f) (ordOfPlace E S hS g) ≤ ordOfPlace E S hS (f + g) :=
    fun S hS => (ordPlaceAPI E S hS).2.2.2.1
  have hFifth : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
      (g : MotC2.Func E), FifthPowerValued N g → 5 ∣ ordOfPlace E S hS g :=
    fun S hS => (ordPlaceAPI E S hS).2.2.2.2
  -- the invariant derivation
  obtain ⟨D, hDx, hDy⟩ := invDeriv E
  have hDA := invDerivOnA E D hDx hDy
  have hAff' : ∀ (a b : N) (h : WeierstrassCurve.Affine.Nonsingular E a b),
      (2 * b + E.a₁ * a + E.a₃ ≠ 0 →
        ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
            (MotC2.genX E - algebraMap N (MotC2.Func E) a) = 1) ∧
      (2 * b + E.a₁ * a + E.a₃ = 0 →
        ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
            (MotC2.genX E - algebraMap N (MotC2.Func E) a) = 2 ∧
        ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
            (MotC2.genY E - algebraMap N (MotC2.Func E) b) = 1) :=
    fun a b h =>
      ⟨fun hw => ((affLocal E a b h).1 hw).1,
        fun hw => ⟨((affLocal E a b h).2 hw).1, ((affLocal E a b h).2 hw).2.1⟩⟩
  have hL := invDerivLocalC E hMul hAdd hNonneg hAff' hInfRat hInfL D hDx hDy
  have hb1 : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
      (f : MotC2.Func E), D f ≠ 0 → ordOfPlace E S hS f - 1 ≤ ordOfPlace E S hS (D f) :=
    fun S hS f hDf => hL.1 S hS f hDf
  have hb2 : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
      (f : MotC2.Func E), ordOfPlace E S hS f = 0 → 0 ≤ ordOfPlace E S hS (D f) :=
    fun S hS f h0 => hL.2 S hS f h0
  -- the input bundle
  let H : H1Data N E :=
    { infRat := hInfRat
      ord_mul := hMul
      ord_inv := hInv
      ord_nonneg := hNonneg
      ord_add := hAdd
      fifth := hFifth
      aff_ne := fun a b h hw => (affLocal E a b h).1 hw
      aff_eq := fun a b h hw => (affLocal E a b h).2 hw
      inf_local := hInfL
      deriv := ⟨D, hDx, hDy, hb1, hb2, hDA⟩ }
  -- the divisor degree zero
  have hSumA : ∀ (a : WeierstrassCurve.Affine.CoordinateRing E), a ≠ 0 →
      ordSum E (ptsOf E H.infRat (Algebra.norm (Polynomial N) a))
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (MotC2.Func E) a) = 0 :=
    fun a ha => sumA E H (fun a ha => supportInf E H a ha) a ha
  have hDeg : ∀ (f : MotC2.Func E), f ≠ 0 → ∀ S : Finset (Place N E),
      (∀ Q : Place N E, ordP E Q f ≠ 0 → Q ∈ S) → ordSum E S f = 0 :=
    fun f hf S hsup => degreeZero E H hSumA f hf S hsup
  have hSupAff := fun (a : WeierstrassCurve.Affine.CoordinateRing E)
      (ha : a ≠ 0) => supportAff E H a ha
  have hSupInf := fun (a : WeierstrassCurve.Affine.CoordinateRing E)
      (ha : a ≠ 0) => supportInf E H a ha
  have hFib := fun (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0)
      (c : N) => fibreNorm E H a ha c
  -- the main case `∂r ≠ 0`
  have hmain : ∀ f : MotC2.Func E, D f ≠ 0 → FifthPowerValued N (f * (f - 1)) →
      ∃ c : N, algebraMap N (MotC2.Func E) c = f :=
    fun f hDf hf => mainCaseC E H hDeg hSupAff hSupInf D hDx hDy hDA hb1 hb2 f hDf hf
  -- a function regular everywhere is constant
  have hReg : ∀ (f : MotC2.Func E), f ≠ 0 →
      (∀ Q : Place N E, 0 ≤ ordP E Q f) → ∃ c : N, algebraMap N (MotC2.Func E) c = f :=
    fun f hf hreg => regularConst E H hFib hSupInf f hf hreg
  -- a nonconstant function has a nonzero order somewhere
  have hterm : ∀ f : MotC2.Func E, (∀ c : N, algebraMap N (MotC2.Func E) c ≠ f) →
      ∃ Q : Place N E, ordP E Q f ≠ 0 := by
    intro f hf
    by_contra hcon
    push_neg at hcon
    have hf0 : f ≠ 0 := fun h0 => hf 0 (by rw [h0, map_zero])
    obtain ⟨c, hc⟩ := hReg f hf0 (fun Q => by rw [hcon Q])
    exact hf c hc
  -- the kernel of the derivation in positive characteristic
  have hkerP : ∀ (p : ℕ) [Fact p.Prime] [CharP N p], p ≠ 5 →
      ∀ f : MotC2.Func E, D f = 0 → ∃ s : MotC2.Func E, s ^ p = f :=
    fun p _ _ _ f h => derivZeroPow E D hDx hDy p f h
  -- the kernel of the derivation in characteristic zero
  have hker0 : CharZero N → ∀ f : MotC2.Func E, D f = 0 →
      ∃ c : N, algebraMap N (MotC2.Func E) c = f :=
    fun hc f h => by
      haveI := hc
      exact derivZeroConst E D hDx hDy f h
  exact derivAll E H D hmain hkerP hker0 hterm hN r hr

end Work.MotV
