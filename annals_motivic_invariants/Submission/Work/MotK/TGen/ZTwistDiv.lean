import Mathlib
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotK.TwCensus.ZTwist
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotV.Defs
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TwCensus.KummerInvariance
import Submission.Work.MotK.TGen.ZRatFuncBridge
import Submission.Work.MotK.TGen.ZPlaneModelMain
import Submission.Work.MotK.TGen.ZElim2Irreducible
import Submission.Work.MotK.TGen.ZChartPresentationMain
import Submission.Work.MotK.TGen.ChartHeightBound
import Submission.Work.MotK.TGen.KerPhiHeightBound
import Submission.Work.MotK.TGen.ZTwistDivPlaneGeom
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotK.TGen.ZTwistDiv` — node K6 for the T-twisted Crauder–Katz link

## The statement

`Work.MotK.TGen.ZTwistDiv` is the *base-curve identification* of the census of the T-twisted
Crauder–Katz link (node **K6** of `Submission/Work/MotK/GUIDE_K5K6.md`, `MOTIVIC_S45_LEAD.md`
§2.3, `MOTIVIC_LKAS_LEAD.md` §2).  With

* `R = K[x₀,x₁,x₂] ⧸ radical (Work.MotK.TwCensus.ZI D.a D.b h)`, the coordinate ring of the
  *residual curve* `Z = V(Zcub) ⊆ 𝔸³` of the `h`-twisted link, and
* `F₂ = Work.MotK.twistFieldTG K D (h²)`, the T-twist field of the Kummer class `h²`,

it asserts `Nonempty (FractionRing (Polynomial R) ≃ₐ[K] RatFunc F₂)`, i.e.
`κ(Z × 𝔸¹) ≅ F₂(t)`: the function field of the residual curve times one rational parameter is the
function field of the twisted Klein curve `C_{h²}` times one rational parameter.  It is the
paper's `C' = Jac²(C_h)` with the twist class `2T = h²`.

## Reduction carried out in this file (three pieces, all about explicit objects)

```
  Frac R  --ZPlaneModel-->  Frac K[x₁,x₂]/(ZElim2 a b h)
          --ZTwistDivPlane-->  Frac K[y₀…y₄]/(Qideal a b h² ⊔ (y₀ - 1))
          --ZChartPresentation-->  ↥(twistFieldTG K D (h²))
```

* `Work.MotK.TGen.ZPlaneModel` — the residual curve `Z` is birational to the *plane* curve
  `V(ZElim2 a b h)` (elimination of `x₀ = (a²b − ab²h x₁²x₂)/(b³h x₁ − a³h x₂²)`; needs
  `Irreducible (ZElim2 a b h)`, supplied by `Work.MotK.TGen.ZElim2Irreducible`);
* `Work.MotK.TGen.ZChartPresentation` — the chart `y₀ = 1` of the twisted Klein curve `C_H` has
  function field `twistFieldTG K D H`;
* **`ZTwistDivPlane` (below)** — the residual plane model `V(ZElim2 a b h)` and the chart
  `y₀ = 1` of `C_{h²}` are birational over `K`.  This is the remaining geometric leaf of the
  node (the `(ℤ/5)ˣ`-level statement of the ledger below).

`ZTwistDivFrac` is then the composite, and `ZTwistDiv` is `ZRatFuncBridge` applied to it.

## ⚠ Do **not** route the C-side through `Work.MotK.TwCensus.ZTwPlane` (it is not a model of `C_H`)

`Work.MotK.TwCensus.ZTwPlane` (in `TwCensus/ZTwist.lean`) was introduced as "the plane model of
the twisted Klein curve `C_H` (the eliminant of the five quadrics in the variables `(y₂,y₃,y₄)`,
CAS Gröbner)".  **That claim is false**, and the whole C-side chain
`ZPlaneChart`/`ZPlaneChartR`/`ZTwPlaneChartQuadrics`/`ZTwPlaneElim` built on it is unusable.
Decisive check (smooth models of the two plane quintics, over `𝔽_p`, with the node/branch
correction; `#C_1(𝔽_p)` computed directly from `kleinP 1 1` in `ℙ⁴`):

| `p` | `#C_1(𝔽_p)` | `#V(ZElim2 1 1 1)` | `#V(ZTwPlane 1 1 1)` |
|-----|-------------|--------------------|----------------------|
|  7  |     10      |         10         |        **11**        |
| 13  |     10      |         10         |        **12**        |
| 17  |     20      |         20         |        **22**        |
| 19  |     20      |         20         |        **22**        |

`ZElim2 1 1 1` matches the twisted Klein curve at `H = 1` in every case (as the paper's
`C' = Jac²(C_1) ≅ C_1` requires), while `ZTwPlane 1 1 1` does not — so `V(ZTwPlane)` is *not*
birational to `C_H`, and `Work.MotK.TGen.ZPlaneChart` (whose statement is exactly that
birationality at the chart `X₂ = 1`) is false as stated.  The present file therefore imports
neither `ZPlaneChart` nor `ZTwPlane`, and states its geometric leaf with `Qideal` on the C-side.
(A future stretch should recompute the elimination ideal of `kleinTwP a b H` in `(y₂,y₃,y₄)` and
repair `ZTwPlane` and its consumers.)

## Ledger: the exponent question is a `(ℤ/5)ˣ`-level statement (session 2026-10-04)

The whole remaining content of `ZTwistDivPlane` is the *Kummer class* of the residual curve: the
two curves are both `5`-nodal genus-`1` quintics with the same support shape
(`X⁵, X²YZ², XY³Z, Y⁵, Z⁵`) and the same diagonal `μ₅`-action, and the families are generated from
the base members by the **same** substitution

* `ZElim2 a b h = (ZElim2 a b 1) ∘ σ_h`,     `σ_d (x,y) = (d^{2/5}x, d^{1/5}y)`  (verified), and
* `ZTwPlane a b H = H²·(ZTwPlane a b 1) ∘ σ_H^{-1}` (the analogous statement on the C-side),

with `σ` and `σ^{-1}` respectively.  So, if the two *base* curves are `K`-isomorphic via `Ψ`,
conjugating the diagonal automorphisms `δ(x,y) = (ζ²x, ζy)` as `Ψ ∘ δ^Z ∘ Ψ^{-1} = (δ^C)^k`,
`k ∈ (ℤ/5)ˣ` (well defined up to sign), then `Z_h ≅ C_{h^m}` for the **fixed** exponent
`m ≡ -k`, and `ZTwistDivPlane` is exactly `m ≡ ±2`, equivalently `Ψ^{-1}∘δ^C∘Ψ = (δ^Z)^{3}`.

Consequences recorded for the next stretch:

* `k` is an honest geometric invariant (`±1` or `±2`); the statement is true iff `k ≡ ±2`.  The
  naive shortcut "the two diagonal actions look the same, so `k = 1`" is *not* a proof: the two
  base curves are different plane models of the same elliptic curve, and the conjugation is
  determined only up to `Aut = {±1}`.
* the reduction "base isomorphism with `k ≡ ±3` ⟹ `ZTwistDivPlane`" is *pure algebra*: with
  `a⁵ = h`, `Θ := σ_{a²} ∘ Ψ^{-1} ∘ σ_a` maps `Z_h → C_{h²}`, and
  `Θ^γ = δ_{ζ²}σ_{a²}Ψ^{-1}δ_ζσ_a` (for `γ(a) = ζa`, using `Ψ^γ = Ψ`) shows `Θ^γ = Θ` **iff**
  `δ_{ζ²}Ψ^{-1}δ_ζ = Ψ^{-1}`, i.e. `Ψ^{-1}δ^CΨ = (δ^Z)³`.  So the remaining work on the node is:
  (1) an *explicit* base isomorphism between the two base models, and (2) the check
  `Ψ^{-1}δ^CΨ = (δ^Z)³` for it; the general `h` then follows by the displayed computation.
* both base curves have exactly five ordinary nodes lying on the conic `x = y²` (for `a = b = 1`
  at `{(Y²,Y) : Y⁵ = 1}` resp. `{(Y²,Y) : Y⁵ = -1}`), and no *diagonal* (monomial) substitution
  nor any plane linear map identifies them (Gröbner, recorded in the earlier ledger), so the
  isomorphism is necessarily nonlinear.

-/

namespace Work.MotK.TGen

variable {K : Type} [Field K]

/-- The diagonal substitution `(X₀,X₁) ↦ (s²X₀, sX₁)` of `K[X₀,X₁]`, as a `K`-algebra
endomorphism (the substitution by which a fifth-power change of the parameter acts on the
plane model of the residual curve). -/
noncomputable def zScaleHom (s : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval
    ![MvPolynomial.C (s ^ 2) * MvPolynomial.X 0, MvPolynomial.C s * MvPolynomial.X 1]

/-- **Kummer invariance of the residual plane model.**  Scaling the parameter by a fifth power is
an invertible diagonal change of variables: `ZElim2 a b (h·s⁵) = zScaleHom s (ZElim2 a b h)`.
Consequently the residual curve `Z_h` depends only on the Kummer class of `h` — the analogue, on
the residual side, of `Work.MotK.TwCensus.KummerInvariance` on the twist-field side. -/
theorem ZElim2_scale (a b h s : K) :
    Work.MotK.TwCensus.ZElim2 a b (h * s ^ 5) =
      zScaleHom s (Work.MotK.TwCensus.ZElim2 a b h) := by
  simp only [zScaleHom, Work.MotK.TwCensus.ZElim2, MvPolynomial.aeval_C, map_add, map_sub,
    map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  first | refl_ring1 | ring

/-- **The remaining geometric leaf of node K6.**  The plane model `V(ZElim2 a b h)` of the
residual curve of the `h`-twisted link and the chart `y₀ = 1` of the twisted Klein curve
`C_{h²} = V(kleinTwP a b h²) ⊆ ℙ⁴` are birational over `K`.  This is the paper's
`C' = Jac²(C_h)`; the *exponent* `h²` is the `(ℤ/5)ˣ`-level statement of the ledger above (base
isomorphism with `Ψ^{-1}δ^CΨ = (δ^Z)³`).

The C-side is taken with `Work.MotK.TwCensus.Qideal` (the radical of the twisted Pfaffians) and
**not** with `Work.MotK.TwCensus.ZTwPlane`, which is not a model of `C_H` (see the warning in the
module docstring).

Hypotheses: `a ≠ 0`, `b ≠ 0`, `h ≠ 0`; `ringChar K ≠ 5` (in characteristic `5` the Pfaffians
degenerate and the statement is false); the *non-degeneracy* of the Klein family,
`a¹⁰ − 11a⁵b⁵ − b¹⁰ ≠ 0` (the locus where the twisted Klein curve degenerates; this is exactly
what `Work.MotK.TwCensus.GoodDiscNe` extracts from `D.Good`), and the irreducibility of the
residual plane model `ZElim2 a b h` (the "one component" condition, supplied in the assembly by
`Work.MotK.TGen.ZElim2Irreducible`). -/
theorem ZTwistDivPlane (K : Type) [Field K] (hk : ringChar K ≠ 5) (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hdisc : a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10 ≠ 0)
    (hirr : Irreducible (Work.MotK.TwCensus.ZElim2 a b h)) :
    Nonempty (FractionRing (MvPolynomial (Fin 2) K ⧸
        Ideal.span {Work.MotK.TwCensus.ZElim2 a b h}) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        (Work.MotK.TwCensus.Qideal a b (h ^ 2) ⊔
          Ideal.span {MvPolynomial.X (0 : Fin 5) - 1}))) :=
  Work.MotK.TGen.ZTwistDivPlaneGeom K hk a b h ha hb hh hdisc hirr

/-- **The K6 core**: the function field of the residual curve `Z = V(radical (ZI a b h))` is the
`h²`-twist field of the Klein curve.  This is the paper's `C' = Jac²(C_h)` with twist class
`2T = h²` (`Work.MotK.TwCensus.ZTwist`, `Work.MotK.TGen.ZTorsorBridge`); it is exactly the
content of `Work.MotK.TGen.ZTwistDiv` with the `Polynomial`/`RatFunc` wrapper removed.

The proof is the composite of the three pieces listed in the module docstring: the plane-model
reduction `Frac R ≅ Frac (K[x]/(ZElim2 a b h))` (`ZPlaneModel`, using `ZElim2Irreducible`), the
geometric leaf `ZTwistDivPlane`, and `ZChartPresentation`. -/
theorem ZTwistDivFrac (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) ≃ₐ[K]
      ↥(Work.MotK.twistFieldTG K D (h ^ 2))) := by
  have ha : D.a ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, zero_mul])
  have hb : D.b ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, mul_zero])
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  obtain ⟨e₁⟩ := ZPlaneModel K D.a D.b h ha hb hh
    (ZElim2Irreducible K hk D hD h hh)
  obtain ⟨e₂⟩ := ZTwistDivPlane K hk D.a D.b h ha hb hh
    (Work.MotK.TwCensus.GoodDiscNe K hk D hD)
    (ZElim2Irreducible K hk D hD h hh)
  -- The chart ideal `chartIdeal K D (h²)` is prime: the right-hand side of `e₂` is
  -- `FractionRing (K[Y] ⧸ chartIdeal K D (h²))`, while the left-hand side is the fraction ring of
  -- the *domain* `K[X₀,X₁] ⧸ (ZElim2 a b h)` (`hirr`), hence a field; `IsFractionRing.injective`
  -- then embeds the chart ring into its fraction ring.  (This avoids having to prove primeness of
  -- the general chart ideal `chartIdeal K D H`, which is a separate, harder fact.)
  have hprime : (chartIdeal K D (h ^ 2)).IsPrime := by
    have hne : Work.MotK.TwCensus.ZElim2 D.a D.b h ≠ 0 := fun h0 =>
      (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)) (by
        have hc : MvPolynomial.constantCoeff (Work.MotK.TwCensus.ZElim2 D.a D.b h) = 0 := by
          rw [h0, map_zero]
        rw [Work.MotK.TwCensus.ZElim2] at hc
        simpa using hc)
    haveI hZD : IsDomain (MvPolynomial (Fin 2) K ⧸
        Ideal.span {Work.MotK.TwCensus.ZElim2 D.a D.b h}) := by
      have hsp : (Ideal.span {Work.MotK.TwCensus.ZElim2 D.a D.b h}).IsPrime :=
        (Ideal.span_singleton_prime hne).mpr
          (UniqueFactorizationMonoid.irreducible_iff_prime.mp
            (ZElim2Irreducible K hk D hD h hh))
      exact Ideal.Quotient.isDomain _
    let A : Type := MvPolynomial (Fin 5) K ⧸
      (Work.MotK.TwCensus.Qideal D.a D.b (h ^ 2) ⊔
        Ideal.span {MvPolynomial.X (0 : Fin 5) - 1})
    haveI hF : IsDomain (FractionRing A) :=
      Function.Injective.isDomain e₂.symm.toRingEquiv (RingEquiv.injective e₂.symm.toRingEquiv)
    haveI hQ : IsDomain A :=
      Function.Injective.isDomain (algebraMap A (FractionRing A))
        (IsFractionRing.injective A (FractionRing A))
    exact (Ideal.Quotient.isDomain_iff_prime
      (I := Work.MotK.TwCensus.Qideal D.a D.b (h ^ 2) ⊔
        Ideal.span {MvPolynomial.X (0 : Fin 5) - 1})).mp hQ
  obtain ⟨e₃⟩ := ZChartPresentationMain K D hD (h ^ 2) hh2 hprime
    (ChartHeightBound K D hD (h ^ 2) hh2) (KerPhiHeightBound K D hD (h ^ 2) hh2)
  exact ⟨(e₁.trans e₂).trans e₃⟩

theorem ZTwistDiv (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Nonempty (FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h))) ≃ₐ[K]
      RatFunc ↥(Work.MotK.twistFieldTG K D (h ^ 2))) := by
  obtain ⟨e⟩ := ZTwistDivFrac K hk D hD h hh
  exact ZRatFuncBridge K _ _ ⟨e⟩

end Work.MotK.TGen
