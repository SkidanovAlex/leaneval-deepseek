import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Whitney.Basic
import Submission.Work.Gen.Basic
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.pontryaginClass_comap
import Submission.Work.Thom.realification
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.Whitney.NowhereZeroDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Auxiliary definitions and reduction notes for `p1RatNeZero`

This module fixes the reduction vocabulary for `Work.ThomBordism.Grassmann.p1RatNeZero`.

* `equivC1R2` — the ℝ-linear identification `ℂ ≅ ℝ²`;
* `zStd` — the **standard rank-`2` real bundle over `ℂP²`** in the standard fibre `ℝ²`: the
  realification of the tautological dual line bundle `𝒪(1) = Work.Gen.tautDual 2`, transported
  along `equivC1R2`.  This is the `k = 2` universal bundle of the Grassmannian `G̃r₂(ℝ⁴) = S²×S²`,
  pulled back to `ℂP²` along the "underlying real 2-plane of a complex line" map;
* `chernReduced` — `c₂(𝒪(1) ⊕ 𝒪(-1))`, the class whose non-vanishing is the crux.

## The reduction of `p1RatNeZero` (why these definitions)

`p₁(zStd)` is the pullback of `p₁(γ_{k,m})` along the *probe* `ℂP² → G̃r_k(ℝ^{k+m})`,
`[v] ↦ ` (the real 2-plane `ℝv ⊆ ℂ³ ⊆ ℝ^{k+m}` plus a fixed oriented `(k-2)`-plane); the pullback
of `γ_{k,m}` is `zStd` stabilised by `k-2` trivial lines, so by naturality of `p₁` and stability
(`Work.Thom.pontryaginClass_comap`, `Work.Whitney.pontryagin1_whitneySumR_trivial`) it suffices
for `p₁(zStd) ≠ 0` rationally.

For the crux: `p₁(E) = - c₂(E ⊗_ℝ ℂ)` (`Work.Thom.pontryagin1_def`), and
`zStd ⊗_ℝ ℂ ≅ 𝒪(1) ⊕ 𝒪(-1)`: the transition functions of `zStd` are the real `2×2`
rotations underlying the complex scalars of `𝒪(1)`, whose complexification `cxMap` is the
`ℂ`-linear map `M(z) = [[Re z, -Im z],[Im z, Re z]]`, with eigenbasis `𝒪(1) ⊕ 𝒪(-1)`.  Finally
`c₂` of a rank-`2` complex bundle is the Euler class of its realification
(`Work.Thom.chernClass_succ_top'`), so the crux is `e(W) ≠ 0` for the rank-`4` real bundle
`W = realification (𝒪(1) ⊕ 𝒪(-1))` over `ℂP²`.

`e(W) ≠ 0` is proved *without* the Whitney formula, by the Gysin sequence
(`Work.Thom.gysin_exact_at_base`) plus the vanishing `H⁴(W∖0) = 0`: the Gysin sequence
`H⁰(ℂP²) --∪e--> H⁴(ℂP²) → H⁴(W∖0) → H¹(ℂP²) = 0` shows that `e` generates the target as soon as
`H⁴(W∖0) = 0`, and `H⁴(ℂP²) ≅ ℤ` is free, so `1 ⊗ e ≠ 0`.

`H⁴(W∖0) = 0` (Mayer–Vietoris on `W∖0 = {x ≠ 0} ∪ {y ≠ 0}`, the two coordinates of the fibre
`ℂ²` of `W`): both pieces are the total space of a vector bundle over `zeroComplement (𝒪(1)_ℝ)`
(take the other coordinate), hence homotopy equivalent to it
(`Work.Thom.bijective_CohMap_bundleProj`), and
`zeroComplement (realification (tautDual 2)) ≃ ℂ³∖0 ≃ S⁵`
(`Work.Gen.ChernGen.tautDualPunctHomeo`) has vanishing `H³`, `H⁴`
(`Work.Cohomology.cohomologyIso_of_homotopyEquiv`).  The intersection `{x ≠ 0, y ≠ 0}` is the
complement of the zero section in the pullback of `𝒪(1)_ℝ` to `zeroComplement (𝒪(1)_ℝ)`; that
pullback carries the tautological nowhere-zero section, so its Euler class vanishes
(`Work.Thom.eulerClass_eq_zero_of_nowhereZeroSection`) and its Gysin sequence
(`Work.Thom.gysin_exact_at_base`) exhibits `H³` of its zero complement as
`ker(∪ 0) = H³ ⊕ H²` of `zeroComplement (𝒪(1)_ℝ) = 0`, giving `H³ = 0`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-- The canonical ℝ-linear identification `ℂ ≅ ℝ²` (both are two-dimensional over `ℝ`). -/
def equivC1R2 : EuclideanSpace ℂ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin 1)),
      finrank_euclideanSpace_fin, Complex.finrank_real_complex]
    norm_num)

/-- **The standard rank-`2` real bundle over `ℂP²`**: the underlying real bundle of the tautological
dual line bundle `𝒪(1) = Work.Gen.tautDual 2`, transported to the standard fibre `ℝ²`. -/
def zStd : RealBundle (Work.Projective.CP 2) (EuclideanSpace ℝ (Fin 2)) (Fin 3) :=
  RealBundle.mapFibre equivC1R2 (Work.Thom.realification (Work.Gen.tautDual 2))

/-- **The reduced second Chern class**: `c₂` of the rank-`2` complex bundle
`𝒪(1) ⊕ 𝒪(-1)` over `ℂP²`. -/
def chernReduced : Work.Thom.Coh ℤ 4 (Work.Projective.CP 2) :=
  Work.Thom.chernClass 2 2
    (Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2))

end

end Work.ThomBordism.Grassmann
