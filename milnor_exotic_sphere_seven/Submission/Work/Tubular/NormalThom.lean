import Submission.Work.Tubular.nonempty_thomClass_of_bundleIso
import Submission.Work.Tubular.bundleMapEquivIso
import Submission.Work.Thom.thomClass_of_oriented_fintype
import Submission.Work.Tubular.Defs
import Submission.Work.ThomBordism.PontryaginThom.Geometry

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The integral Thom class of the normal bundle of an embedded manifold

The normal bundle `ν` of a closed oriented smooth `8`-manifold `V ⊆ ℝ^{8+k}` is **oriented** — the
orientation is the complement of the orientation of `TV` in the ambient `ℝ^{8+k}` — and this
orientation is exactly what the *Gauss map* `V → G̃r_k(ℝ^{k+m})` into the **oriented** Grassmannian
records.  In the vocabulary of the Pontryagin–Thom chapter the Gauss data are a classifying
continuous map `gauss : V.pt → G` (with `G` the oriented Grassmannian of `k`-planes), a universal
oriented bundle `γ` over `G` given by gluing data with **positive-determinant** transitions, and a
bundle isomorphism `e : gauss^*γ ≅ ν` (`Work.ThomBordism.PontryaginThom.NormalGaussData.classifies`).

This module turns that into the **Thom class of the normal bundle**: `U_ν ∈ H^k(ν, ν∖0; ℤ)`, the
object consumed by the Pontryagin–Thom pairing (`Work.Tubular.TubeThomRep`,
`Submission/Work/Tubular/PairingNotes.md` §4bis, item **M2**).

The route is two steps, both already available:

1. `Work.Thom.thomClass_of_oriented_fintype` — the Thom isomorphism theorem for a real bundle over a
   finite cover with Euclidean fibre and positive-determinant transitions.  Applied to the pullback
   `Work.Thom.bundleComap γ gauss` (whose transitions are the transitions of `γ` at `gauss x`,
   `Work.Thom.bundleComap_coordChange`, so still positive) this produces a Thom class of
   `gauss^*γ`; **no orientability of `ν` has to be proved separately**, because the orientation is
   transported *by* the isomorphism `e`.
2. `Work.Tubular.nonempty_thomClass_of_bundleIso` — isomorphism-invariance of the Thom class
   (`Work.Thom.BundleIso`), which moves it from `gauss^*γ` to `ν`.

Note that step 1 needs the *given* positive-determinant presentation of the universal bundle, and
this is precisely the reason the Grassmann chapter of this workspace had to abandon the
`OnePoint (TotalSpace γ)`-with-`fibreNorm` presentation for an orthonormal-frame one: the `IsEuclidean`
condition fixes the sign `det = ±1` but not the sign itself.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The normal bundle of an embedded manifold carries an integral Thom class.**  Given the
classifying (Gauss) data of the normal bundle — a map `gauss : V.pt → G` into the base of a
universal bundle `γ` with **positive-determinant** transitions, and a bundle isomorphism
`e : gauss^*γ ≅ ν` — the bundle `ν` has a Thom class.

No orientability hypothesis on `ν` appears: the orientation enters through `e` (the Gauss map), which
is exactly the geometric content of "the normal bundle of an oriented submanifold of an oriented
manifold is oriented (by the complement of the tangent orientation)". -/
theorem exists_normalThomClass {k : ℕ} (hk : 1 ≤ k) {G : Type} [TopologicalSpace G]
    {κ : Type} [Fintype κ] {γ : Work.TangentClasses.RealBundle G (Euc k) κ}
    (hori : ∀ (i j : κ) (x : ↥(γ.baseSet i ∩ γ.baseSet j)),
      0 < LinearMap.det ((γ.coordChange i j (x : G)).toLinearMap))
    {V : Work.ThomBordism.Man8} {ι : Type}
    {ν : Work.TangentClasses.RealBundle V.pt (Euc k) ι}
    (gauss : C(V.pt, G))
    (e : Work.Thom.BundleIso (Work.Thom.bundleComap γ gauss) ν) :
    Nonempty (Work.Thom.ThomClass ν k) := by
  obtain ⟨T⟩ := Work.Thom.thomClass_of_oriented_fintype hk (Work.Thom.bundleComap γ gauss)
    (fun i j x => by
      have hx : gauss (x : V.pt) ∈ γ.baseSet i ∩ γ.baseSet j := by
        have h := x.2
        simp only [Work.Thom.bundleComap_baseSet, Set.mem_inter_iff, Set.mem_preimage] at h
        exact h
      rw [Work.Thom.bundleComap_coordChange]
      exact hori i j ⟨gauss (x : V.pt), hx⟩)
  exact nonempty_thomClass_of_bundleIso e T


/-! ## The coordinate fibre `Fin k → ℝ`

`Work.ThomBordism.PontryaginThom.NormalGaussData` presents the normal bundle `ν` and the universal
bundle `γ` in the **coordinate fibre** `Fin k → ℝ`, while the Thom-existence theorem
`Work.Thom.thomClass_of_oriented_fintype` is stated for the euclidean fibre
`EuclideanSpace ℝ (Fin k)`.  The two presentations are related by
`Work.ThomBordism.PontryaginThom.bundleMapEquiv` along the canonical linear isometry
`EuclideanSpace.equiv (Fin k) ℝ`: `bundleMapEquiv` changes only the fibre model and the transition
functions (by conjugation, hence preserving positivity of the determinant), *not* the base or the
cover, so the Thom class can be transported there and back with
`Work.Tubular.nonempty_bundleIso_bundleMapEquiv` and
`Work.Tubular.nonempty_thomClass_of_bundleIso`. -/

/-- Conjugating a continuous linear endomorphism by a continuous linear equivalence does not change
its determinant (the continuous-linear version of `LinearMap.det_conj`). -/
theorem det_conj_clm {M N : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℝ N] [TopologicalSpace N]
    (e : M ≃L[ℝ] N) (f : M →L[ℝ] M) :
    LinearMap.det (((e : M →L[ℝ] N).comp (f.comp (e.symm : N →L[ℝ] M))).toLinearMap)
      = LinearMap.det f.toLinearMap := by
  have h : (((e : M →L[ℝ] N).comp (f.comp (e.symm : N →L[ℝ] M))).toLinearMap)
      = LinearMap.comp (e.toLinearEquiv : M →ₗ[ℝ] N)
          (LinearMap.comp f.toLinearMap (e.toLinearEquiv.symm : N →ₗ[ℝ] M)) := rfl
  rw [h, LinearMap.det_conj f.toLinearMap e.toLinearEquiv]

/-- **The normal bundle carries an integral Thom class — coordinate-fibre form.**  Same statement as
`Work.Tubular.exists_normalThomClass`, but with both bundles in the coordinate fibre `Fin k → ℝ`,
which is the convention of `Work.ThomBordism.PontryaginThom.NormalGaussData`. -/
theorem exists_normalThomClass_coord {k : ℕ} (hk : 1 ≤ k) {G : Type} [TopologicalSpace G]
    {κ : Type} [Fintype κ] {γ : Work.TangentClasses.RealBundle G (Fin k → ℝ) κ}
    (hori : ∀ (i j : κ) (x : ↥(γ.baseSet i ∩ γ.baseSet j)),
      0 < LinearMap.det ((γ.coordChange i j (x : G)).toLinearMap))
    {V : Work.ThomBordism.Man8} {ι : Type}
    {ν : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι}
    (gauss : C(V.pt, G))
    (e : Work.Thom.BundleIso (Work.Thom.bundleComap γ gauss) ν) :
    Nonempty (Work.Thom.ThomClass ν k) := by
  classical
  -- the canonical linear isometry `(Fin k → ℝ) ≃L[ℝ] Euc k`
  let e₁ : (Fin k → ℝ) ≃L[ℝ] Euc k :=
    (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearEquiv
  -- `e₁` conjugates the transition functions, hence preserves the determinant
  have hdet : ∀ (i j : κ) (x : ↥((Work.ThomBordism.PontryaginThom.bundleMapEquiv
        (Work.Thom.bundleComap γ gauss) e₁).baseSet i ∩
        (Work.ThomBordism.PontryaginThom.bundleMapEquiv
          (Work.Thom.bundleComap γ gauss) e₁).baseSet j)),
      0 < LinearMap.det (((Work.ThomBordism.PontryaginThom.bundleMapEquiv
        (Work.Thom.bundleComap γ gauss) e₁).coordChange i j (x : V.pt)).toLinearMap) := by
    intro i j x
    have hx : gauss (x : V.pt) ∈ γ.baseSet i ∩ γ.baseSet j := by
      have h := x.2
      simpa only [Work.ThomBordism.PontryaginThom.bundleMapEquiv_baseSet,
        Work.Thom.bundleComap_baseSet, Set.mem_inter_iff, Set.mem_preimage] using h
    have hdet_eq : LinearMap.det (((Work.ThomBordism.PontryaginThom.bundleMapEquiv
          (Work.Thom.bundleComap γ gauss) e₁).coordChange i j (x : V.pt)).toLinearMap)
        = LinearMap.det ((γ.coordChange i j (gauss (x : V.pt))).toLinearMap) := by
      change LinearMap.det (((e₁ : (Fin k → ℝ) →L[ℝ] Euc k).comp
          (((Work.Thom.bundleComap γ gauss).coordChange i j x).comp
            (e₁.symm : Euc k →L[ℝ] (Fin k → ℝ)))).toLinearMap)
        = LinearMap.det ((γ.coordChange i j (gauss (x : V.pt))).toLinearMap)
      rw [det_conj_clm e₁ ((Work.Thom.bundleComap γ gauss).coordChange i j x)]
      rfl
    rw [hdet_eq]
    exact hori i j ⟨gauss (x : V.pt), hx⟩
  -- the euclidean-fibre Thom class of the pullback of `γ` along `gauss`
  obtain ⟨T⟩ := Work.Thom.thomClass_of_oriented_fintype hk
    (Work.ThomBordism.PontryaginThom.bundleMapEquiv (Work.Thom.bundleComap γ gauss) e₁) hdet
  -- transport back to the coordinate fibre and then along the Gauss isomorphism
  obtain ⟨φ⟩ := nonempty_bundleIso_bundleMapEquiv (Work.Thom.bundleComap γ gauss) e₁
  obtain ⟨T'⟩ := nonempty_thomClass_of_bundleIso φ T
  exact nonempty_thomClass_of_bundleIso e T'


/-! ## The Thom class of the Gauss data of an embedding

`Work.ThomBordism.PontryaginThom.NormalGaussData` is the chapter's package of the normal bundle of
an embedding together with the Gauss map classifying it.  The hypothesis
`hori` below is the *oriented* presentation of the universal bundle: the transition functions of
`γ` have positive determinant.  For the Grassmann chapter this is the statement that the
tautological bundle is taken over the **oriented** Grassmannian `OG k m`.

The hypothesis is exactly what makes `Work.Tubular.exists_normalThomClass_coord` apply; the
geometric content ("the normal bundle of an oriented submanifold of an oriented manifold is
oriented") is then *carried* by the Gauss isomorphism `ng.classifies`, and no separate orientability
of `ν` has to be proved. -/

attribute [local instance] Work.ThomBordism.PontryaginThom.NormalGaussData.topologicalSpace

/-- **The normal bundle of the Gauss data of an embedding carries an integral Thom class.**  This is
`Work.Tubular.exists_normalThomClass_coord` in the vocabulary of
`Work.ThomBordism.PontryaginThom.NormalGaussData`: the Thom class `U_ν` of the normal bundle, the
input of the Pontryagin–Thom pairing (`Submission/Work/Tubular/PairingNotes.md` §4bis, item M2). -/
theorem NormalGaussData.exists_thomClass {V : Work.ThomBordism.Man8} {n : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V n} {k m : ℕ}
    {κ : Type} [Fintype κ] (ng : Work.ThomBordism.PontryaginThom.NormalGaussData V n E k m κ)
    (hk : 1 ≤ k)
    (hori : ∀ (i j : κ) (x : ↥(ng.γ.baseSet i ∩ ng.γ.baseSet j)),
      0 < LinearMap.det ((ng.γ.coordChange i j (x : ng.G)).toLinearMap)) :
    Nonempty (Work.Thom.ThomClass ng.ν k) := by
  obtain ⟨e⟩ := ng.classifies
  exact exists_normalThomClass_coord (G := ng.G) hk hori ng.gauss e

end

end Work.Tubular
