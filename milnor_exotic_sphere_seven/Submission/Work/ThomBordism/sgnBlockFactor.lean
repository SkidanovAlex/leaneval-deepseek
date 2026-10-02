import Mathlib
import Submission.Work.ThomBordism.blockDetDefs
import Submission.Work.ThomBordism.blockDet

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.sgnBlockFactor`

The corollary half of the `(K1)` determinant step: instantiating the block-determinant identity
`Work.ThomBordism.CofAtlas.BlockDet` (`Submission/Work/ThomBordism/blockDet.lean`) at the opaque
reference equivalence `Work.ThomBordism.CofAtlas.sigma k` splits the chart sign `D.sgn x p`
(`= sign (det ((sigma k) ∘ phiD x p))` by definition) into the product of

* the **coframing factor** `sign (det (Omega x p ∘ normFactor D x))`, and
* the **reference/splitting factor** `sign (det (splitMap D x ∘ (sigma k).symm))`,

with *no* residual constant.  This is the exact normalisation recorded in
`NOTE_SESSION72_KOSZUL_SIGMA.md` §16.

**The one mathematical input beyond `blockDet`.**  Writing `A := det ((sigma k) ∘ phiD x p)`,
`B := det (Omega x p ∘ normFactor D x)` and `C := det (splitMap D x ∘ (sigma k).symm)`, the block
identity reads `A * C = B`, whence `sign B = sign A * sign C` (`sign_mul`).  To turn this into the
claimed `sign A = sign B * sign C` one needs `sign C * sign C = 1`, i.e. `C ≠ 0` — the "product of
two signs in `{1,-1}`" step.  For `C = 0` the two identities are *not* interchangeable, so this is
genuine content and not bookkeeping: it is the statement that the *splitting map* `splitMap D x` is
invertible (the direct-sum decomposition of `ModN k` into the level directions `range (chartIota x)`
and the normal directions `ker (chartBeta x)`).  We prove it here directly, with no determinant
theory: `chartT` turns `splitMap` into the coordinate swap `(u,c) ↦ (c,u)`
(`chartT_splitMap`), so `splitMap` is injective (`splitMap_injective`), and an injective
endomorphism of the finite free module `ModN k = ℝ^{9+k}` has nonzero determinant
(`LinearMap.det_eq_zero_iff_ker_ne_bot`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism

open Work.ThomBordism.CofAtlas

noncomputable section

/-! ## The splitting map is the coordinate swap in `chartT`-coordinates -/

theorem chartT_splitMap {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (NN k)) M]
    [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Cof k n M) (x : D.S.Pre) (u : E9) (c : EuclideanSpace ℝ (Fin k)) :
    D.S.chartT x (splitMap D x (u, c)) = (c, u) := by
  simp only [splitMap, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.inl_apply, Work.PTGeometric.Lvl.Setup.chartIota,
    ContinuousLinearMap.coe_coe]
  simp

theorem splitMap_injective {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (NN k)) M]
    [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Cof k n M) (x : D.S.Pre) : Function.Injective (splitMap D x) := by
  rintro ⟨u, c⟩ ⟨u', c'⟩ hab
  have h : (c, u) = (c', u') := by
    rw [← chartT_splitMap D x u c, ← chartT_splitMap D x u' c', hab]
  have hc : c = c' := Prod.ext_iff.mp h |>.1
  have hu : u = u' := Prod.ext_iff.mp h |>.2
  rw [hu, hc]

theorem splitMap_isUnit_det {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (NN k)) M]
    [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Cof k n M) (x : D.S.Pre) :
    LinearMap.det ((splitMap D x).comp ((sigma k).symm).toLinearMap) ≠ 0 := by
  intro h0
  have hker : LinearMap.ker ((splitMap D x).comp ((sigma k).symm).toLinearMap) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro z w hzw
    have h1 : ((sigma k).symm).toLinearMap z = ((sigma k).symm).toLinearMap w :=
      splitMap_injective D x hzw
    exact ((sigma k).symm).injective h1
  exact ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := (splitMap D x).comp
    ((sigma k).symm).toLinearMap)).mp h0) hker

/-! ## The sign algebra -/

/-- For real numbers with `a * c = b` and `c ≠ 0`, `sign a = sign b * sign c`.  (The hypothesis
`c ≠ 0` is needed: for `c = 0` both identities `sign b = sign a * sign c` and
`sign a = sign b * sign c` are *not* equivalent.) -/
theorem sign_eq_sign_mul_of_mul_eq {a b c : ℝ} (h : a * c = b) (hc : c ≠ 0) :
    SignType.sign a = SignType.sign b * SignType.sign c := by
  have hcsq : SignType.sign c * SignType.sign c = 1 := by
    rw [← sign_mul]
    exact sign_pos (mul_self_pos.mpr hc)
  have hbc : SignType.sign b = SignType.sign a * SignType.sign c := by
    rw [← h, sign_mul]
  calc SignType.sign a = SignType.sign a * 1 := (mul_one _).symm
    _ = SignType.sign a * (SignType.sign c * SignType.sign c) := by rw [hcsq]
    _ = SignType.sign b * SignType.sign c := by rw [← mul_assoc, ← hbc]

/-! ## The pinned corollary -/

theorem sgnBlockFactor (k : ℕ) : Work.ThomBordism.CofAtlas.SgnBlockFactor k := by
  intro n M _ _ _ _ _ D x p hp hpint
  have h := blockDet k n M D x p hp hpint (sigma k)
  rw [Work.ThomBordism.CofAtlas.Cof.sgn]
  exact sign_eq_sign_mul_of_mul_eq h (splitMap_isUnit_det D x)

end

end Work.ThomBordism
