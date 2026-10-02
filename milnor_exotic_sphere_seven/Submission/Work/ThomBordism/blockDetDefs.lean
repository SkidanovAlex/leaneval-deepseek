import Mathlib
import Submission.Work.ThomBordism.phiDSplitBlocks
import Submission.Work.ThomBordism.sigmaPackaging

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The endomorphic block-determinant identity of the `(K1)` chapter

`Submission/Work/ThomBordism/NOTE_SESSION72_KOSZUL_SIGMA.md` §16 records the *shape* of the
determinant step that separates `sgn = sign (det (sigma k . phiD x p))` into

* the **coframing factor** `sign (det (Omega x p . N))` (`N` = the normal factor `chartT.symm ∘ inl`,
  i.e. the frame of the coorientation in normal-form coordinates), and
* the **reference/splitting factor** `sign (det (splitMap D x . rho.symm))`, which is the
  `chartT`/`sigma`-dependent bookkeeping and cancels in the ratio of §7.

The identity has to be *endomorphic* on both sides: `phiD x p : ModN -> E9 × Euc k` and
`splitMap D x : E9 × Euc k -> ModN` are not endomorphisms, so `LinearMap.det` (and hence
`LinearMap.det_comp`) does not apply to them directly.  Composing with a reference linear equivalence
`rho` (and its inverse) makes both sides endomorphisms of `ModN`.

**Why it is true.**  `Work.CofAtlas.phiDSplitBlocks` (PROVED) gives
`phiD x p ∘ splitMap D x = prodMap id (Omega x p ∘ N)`, so
`(rho ∘ phiD) ∘ (splitMap ∘ rho.symm) = rho ∘ (phiD ∘ splitMap) ∘ rho.symm`, which is the conjugate
of `prodMap id (Omega x p ∘ N)`; `LinearMap.det_conj` removes the conjugation and
`LinearMap.det_prodMap` splits off the `id` factor.

**Non-vacuity.**  The statement is an equation between two integers computed from concrete linear
maps; it is refutable if false (e.g. it fails if `Omega` is replaced by `-Omega`, or if the second
conjunct of `phiDSplitBlocks` is dropped).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-- **The normal factor**: the second factor of `chartT.symm`, a linear map `Euc k -> ModN` whose
image is `ker (chartBeta x)` (the coorientation directions in normal-form coordinates). -/
def normFactor {k : ℕ} {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (NN k)) M]
    [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Cof k n M) (x : D.S.Pre) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ModN k :=
  ((D.S.chartT x).symm : (EuclideanSpace ℝ (Fin k) × E9) ≃L[ℝ] ModN k).toLinearMap.comp
    (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin k)) E9)

/-- **THE PINNED STATEMENT (block determinant).**  For every coframed level set `D`, every interior
point `x` of its zero set, every `p ∈ D.src x` interior in `M`, and every reference linear
equivalence `rho : E9 × Euc k ≅ ModN`,

  `det (rho ∘ phiD x p) * det (splitMap D x ∘ rho.symm) = det (Omega x p ∘ N)`.

This is the endomorphic form of the block structure of `phiD`: the product of the two determinants
is `rho`-independent and equals the determinant of the block map
`(u,c) ↦ (u, Omega x p (N c))`, whose determinant is that of the normal block `Omega x p ∘ N`. -/
def BlockDet (k : ℕ) : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (NN k)) M]
    [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Cof k n M) (x : D.S.Pre) (p : D.S.Pre) (_hp : p ∈ D.src x)
    (_hpint : (p : M) ∈ (𝓡∂ (NN k)).interior M)
    (rho : (E9 × EuclideanSpace ℝ (Fin k)) ≃ₗ[ℝ] ModN k),
    LinearMap.det (rho.toLinearMap.comp (D.phiD x (p : M)).toLinearMap)
        * LinearMap.det ((splitMap D x).comp rho.symm.toLinearMap)
      = LinearMap.det ((D.Omega x (p : M)).toLinearMap.comp (normFactor D x))

/-- **THE PINNED COROLLARY (the `sgn` factorisation).**  With the reference equivalence *being* the
opaque `CofAtlas.sigma k`, the block determinant identity reads

  `sgn = sign (det (Omega x p . N)) * sign (det (splitMap D x . (sigma k).symm))`,

i.e. the `x p`-dependence of the chart sign is the product of the **coframing factor**
`sign (det (Omega x p . N))` and the **reference/splitting factor**
`sign (det (splitMap D x . (sigma k).symm))` — with *no* further constant.  This is the exact
normalisation recorded in `NOTE_SESSION72_KOSZUL_SIGMA.md` §16. -/
def SgnBlockFactor (k : ℕ) : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (NN k)) M]
    [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Cof k n M) (x : D.S.Pre) (p : D.S.Pre) (_hp : p ∈ D.src x)
    (_hpint : (p : M) ∈ (𝓡∂ (NN k)).interior M),
    D.sgn x p
      = SignType.sign (LinearMap.det ((D.Omega x (p : M)).toLinearMap.comp (normFactor D x)))
        * SignType.sign (LinearMap.det ((splitMap D x).comp
            ((sigma k).symm : ModN k ≃ₗ[ℝ] (E9 × EuclideanSpace ℝ (Fin k))).toLinearMap))

end

end Work.ThomBordism.CofAtlas
