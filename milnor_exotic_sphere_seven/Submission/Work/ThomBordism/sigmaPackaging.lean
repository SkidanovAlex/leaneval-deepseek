import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# §2 item 1 of `(K1)`: the opaque `sigma` enters `sgn` only through a constant

`Work.ThomBordism.CofAtlas.sgn` is defined as
`SignType.sign (LinearMap.det ((sigma k).toLinearMap.comp (D.phiD x p).toLinearMap))`
(`CofAtlas/Signs.lean`), where `CofAtlas.sigma k : ℝ^9 × ℝ^k ≅ ℝ^{9+k}` is an **arbitrary**
`Classical.choice` (`Signs.lean:53`).  This file pins the packaging statement which says that this
arbitrariness is *harmless*: `sigma k` is `x`- and `p`-independent, hence

    `D.sgn x p = ε • sign (det (D.phiD x p))`      with `ε := sign (det (sigma k))` a constant
                                                   depending on `k` ONLY.

This is item 1 of §2 of `Submission/Work/ThomBordism/NOTE_SESSION72_KOSZUL_SIGMA.md` — the step that
lets `(K1)` ("the coframing-induced `gamma` is the Koszul contraction up to a **global** sign") be
stated with an honest global constant even though `sigma` is opaque.

**Proof recipe** (for the prover).  `LinearMap.det_comp`:
`det ((sigma k) ∘ phiD x p) = det (sigma k) * det (phiD x p)`; then `SignType.sign_mul`:
`sign (a * b) = sign a * sign b`; the constant is `SignType.sign (LinearMap.det (sigma k).toLinearMap)`,
which is one of `{1, -1}` (`SignType.sign_eq_one_or_neg_one`).  Nothing about `x`, `p` or `D` is used.

**Non-vacuity.**  The statement is a genuine factorisation of `sgn` (it says the `x p`-dependence of
`sgn` is entirely the `x p`-dependence of `sign (det phiD)`); it is *refutable* if false, e.g. it would
fail if `sgn` had been defined with an `x`-dependent `sigma`.  The `k`-only constant is not
determinable from the statement (`sigma` is opaque), which is exactly why the statement is stated
existentially.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-- **THE PINNED STATEMENT (§2 item 1)**: replacing the arbitrary reference equivalence
`CofAtlas.sigma k` — an unmotivated `Classical.choice` — by **any** other linear equivalence
`ρ : ℝ^9 × ℝ^k ≅ ℝ^{9+k}` changes `sgn` by a constant depending on `k` only (not on the datum `D`,
the point `x`, or `p`).

This is the sharp form of "the opacity of `sigma` is harmless": it says that the whole
`x p`-dependence of `sgn` is the `x p`-dependence of the *reference-free* quantity
`sign (det (ρ ∘ phiD x p))`, for every `ρ`.

**Proof recipe** (for the prover).  Both `ρ ∘ phiD x p` and `sigma k ∘ phiD x p` are endomorphisms of
`ModN k`.  Writing `ρ ∘ phiD = (ρ ∘ (sigma k).symm) ∘ (sigma k ∘ phiD)` (`LinearEquiv`-composition),
`LinearMap.det_comp` gives
`det (ρ ∘ phiD) = det (ρ ∘ (sigma k).symm) * det (sigma k ∘ phiD)`,
and `SignType.sign_mul` turns this into
`sign (det (ρ ∘ phiD)) = sign (det (ρ ∘ (sigma k).symm)) * D.sgn x p`;
the constant is `ε := sign (det (ρ ∘ (sigma k).symm)) ∈ {1, -1}` (and `ε * ε = 1`, so the displayed
form follows).  Nothing about `D`, `x` or `p` is used.

**Non-vacuity.**  This is a genuine factorisation of the `x p`-dependence of `sgn` (it would fail if
`sgn` had been defined with an `x`-dependent reference), and it is exactly what `(K1)` needs to be
stated with an honest *global* constant despite the opacity of `sigma` (cf.
`Submission/Work/ThomBordism/NOTE_SESSION72_KOSZUL_SIGMA.md` §2 item 1 and §7). -/
def SgnPackaging (k : ℕ) : Prop :=
  ∀ (ρ : (E9 × EuclideanSpace ℝ (Fin k)) ≃L[ℝ] ModN k),
    ∃ ε : SignType, (ε = 1 ∨ ε = -1) ∧
      ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
        [ChartedSpace (EuclideanHalfSpace (NN k)) M]
        [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
        (D : Cof k n M) (x : D.S.Pre) (p : M),
        D.sgn x p
          = ε * SignType.sign (LinearMap.det (ρ.toLinearMap.comp (D.phiD x p).toLinearMap))

end

end Work.ThomBordism.CofAtlas
