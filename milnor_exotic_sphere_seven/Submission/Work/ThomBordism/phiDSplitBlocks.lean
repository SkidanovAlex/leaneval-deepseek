import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.range_chartIota_eq_ker_Omega

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The block structure of `phiD`: the `chartIota` layer's real content

The `Lvl` chart of a coframed level set *is*, by construction, the `chartBeta`-reading
(`Work.PTGeometric.Lvl.Setup.chartFun`: `chartFun w z = chartBeta (domChart-coordinate z - chartZ) +
chartEps • e₀`), and `Work.PTGeometric.Lvl.Setup.chartBeta_iota` /
`Setup.chartIota_beta` / `Setup.range_chartIota_eq_ker_Omega` already record that `chartBeta` and
`chartIota` are mutually inverse on the level directions `ker (aLin)`.  So the "`chartIota`
identification" `d(lvlChart) = chartIota` is **definitional**: no new pin is warranted there.

What is *not* definitional — and what the last mile's `(K1)` actually consumes (see
`Submission/Work/ThomBordism/NOTE_SESSION72_KOSZUL_SIGMA.md` §2, item 2) — is the **block structure of
the splitting map** `phiD x p = (chartBeta x, Omega x p)`:

    ModN = range (chartIota x)  ⊕  ker (chartBeta x)        (the level / normal directions),
    phiD |_{range chartIota} = (chartBeta|_, 0) : E9 ⊕ 0,    (chartBeta_iota)
    phiD |_{ker chartBeta}   = (0, Omega x p)   : 0 ⊕ Euc k,

so that in the splitting `(chartIota x, the normal-form complement)` the map `phiD x p` is
*block-(upper-triangular)* with the identity in the level block and `Omega x p` in the normal block.
This is the step that turns `sgn = sign (det (sigma ∘ phiD))` into
`sign (det sigma) * (the splitting sign)` and hence (with layer 1, `koszulSplittingInvariant`) into
`(K1)`.

**Non-vacuity.**  The statement is a pair of *equations* between concrete linear maps evaluated on
`(u, c) ∈ ℝ^9 × ℝ^k`; it is refutable if false.  The first conjunct needs `chartBeta_iota` and the
definitional blindness of `chartBeta = snd ∘ chartT` to the first factor; the second conjunct is
*exactly* the hard direction of `range_chartIota_eq_ker_Omega` (`Omega x p` kills the level directions),
which is why the hypotheses `p ∈ D.src x` and `p` interior in `M` are carried — without them the
statement is **FALSE** (found in review, session 75):
outside `x`'s chart source `ker (Omega x p)` is a generic 9-plane with no reason to contain
`range (chartIota x)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-- **The splitting map of the `Cof` datum**: the level directions `range (chartIota x)` together with
the normal-form complement `ker (chartBeta x)` (the image of the first factor of `chartT`). -/
def splitMap (D : Cof k n M) (x : D.S.Pre) : E9 × EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ModN k :=
  (D.S.chartIota x).toLinearMap.comp (LinearMap.fst ℝ E9 (EuclideanSpace ℝ (Fin k)))
    + ((D.S.chartT x).symm).toLinearMap.comp
        ((LinearMap.inl ℝ (EuclideanSpace ℝ (Fin k)) E9).comp
          (LinearMap.snd ℝ E9 (EuclideanSpace ℝ (Fin k))))

/-- **THE PINNED STATEMENT (block structure of `phiD`).**  In the splitting
`E9 × ℝ^k ≅ ℝ^{9+k}` given by `splitMap` (level directions from `chartIota`, normal directions from the
first factor of `chartT`), the map `phiD x p = (chartBeta x, Omega x p)` is block-upper-triangular with
the *identity* on the level block: the first component is the projection `(u,c) ↦ u` and the second
depends only on the normal coordinate `c`. -/
def PhiDSplitBlocks (k n : ℕ) : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (NN k)) M]
    [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Cof k n M) (x : D.S.Pre) (p : D.S.Pre) (_hp : p ∈ D.src x)
    (_hpint : (p : M) ∈ (𝓡∂ (NN k)).interior M)
    (u : E9) (c : EuclideanSpace ℝ (Fin k)),
    ((D.phiD x (p : M)) (splitMap D x (u, c))).1 = u ∧
      ((D.phiD x (p : M)) (splitMap D x (u, c))).2
        = D.Omega x (p : M) ((D.S.chartT x).symm (c, 0))

end

end Work.ThomBordism.CofAtlas
