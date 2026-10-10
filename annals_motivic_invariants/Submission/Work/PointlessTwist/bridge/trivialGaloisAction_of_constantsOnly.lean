import Mathlib
import Submission.Work.PointlessTwist.Constants
import Submission.Work.PointlessTwist.FunctionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The bridge `ConstantsOnly ⟹ TrivialGaloisAction` at the concrete data

This file supplies the plumbing that turns the classical statement `E(𝔽(s)) = E(𝔽)`
(`Work.PointlessTwist.ConstantsOnly`) at the concrete constant Tate model into the statement that
the Galois generator acts trivially on `E(L)` (`Work.PointlessTwist.TrivialGaloisAction`).

The mathematical content of the plumbing is the compatibility of `WeierstrassCurve.Affine.Point.map`
with the two ways of presenting the same curve:

* `((Tate.tateCurve c) ⁄ 𝕜) ⁄ L` and `(Tate.tateCurve c) ⁄ L` are the same curve
  (`WeierstrassCurve.map_map` + `IsScalarTower.algebraMap_eq`);
* transporting points along that equality of curves commutes with `Point.map`
  (`map_transport_mixed`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.PointlessTwist.bridge

noncomputable section

/-! ## 1. Transport of points along an equality of curves -/

/-- Transport of points (and of their nonsingularity proofs) along an equality of Weierstrass
curves over the same base ring.  It is `Eq.rec` with the motive `fun W => W.toAffine.Point`, kept as
a definition so that it can be named in statements without `▸`-elaboration surprises. -/
def ptCast {R : Type*} [CommRing R] {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) :
    W₁.toAffine.Point → W₂.toAffine.Point := fun P => h ▸ P

theorem ptCast_zero {R : Type*} [CommRing R] {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) :
    ptCast h (0 : W₁.toAffine.Point) = (0 : W₂.toAffine.Point) := by
  dsimp [ptCast]; cases h; rfl

theorem ptCast_some {R : Type*} [CommRing R] {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) (x y : R)
    (hxy : W₁.toAffine.Nonsingular x y) :
    ptCast h (Point.some x y hxy) = Point.some x y (h ▸ hxy) := by
  dsimp [ptCast]; cases h; rfl

theorem ptCast_symm_ptCast {R : Type*} [CommRing R] {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂)
    (P : W₁.toAffine.Point) : ptCast h.symm (ptCast h P) = P := by
  dsimp [ptCast]; cases h; rfl

/-! ## 2. Naturality of `Point.map` under a change of the defining curve -/

/-- **`Point.map` commutes with the transport of points between two presentations of the same
curve.**  If `A/𝕜` and `B/𝔽` become the same curve after base change to `K`, and `f : K →ₐ[𝕜] K`,
`g : K →ₐ[𝔽] K` are the same function, then `Point.map` at `A` corresponds to `Point.map` at `B`
under that equality of curves.  (Only the underlying function of an algebra homomorphism is read by
`Point.map`; this is what lets the `𝕜`-linear generator `L.gen` be compared with its `𝔽`-linear
restriction of scalars.) -/
theorem map_transport_mixed {𝔽 𝕜 K : Type} [Field 𝔽] [Field 𝕜] [Field K]
    [Algebra 𝔽 𝕜] [Algebra 𝔽 K] [Algebra 𝕜 K] [IsScalarTower 𝔽 𝕜 K] [DecidableEq K]
    {A : WeierstrassCurve 𝕜} {B : WeierstrassCurve 𝔽} (h : A.baseChange K = B.baseChange K)
    (f : K →ₐ[𝕜] K) (g : K →ₐ[𝔽] K) (hfg : ∀ x, f x = g x)
    (P : (A.baseChange K).toAffine.Point) :
    ptCast h (Point.map (W' := A) f P) = Point.map (W' := B) g (ptCast h P) := by
  cases P with
  | zero =>
    show ptCast h (0 : (A.baseChange K).toAffine.Point) =
      Point.map (W' := B) g (ptCast h (0 : (A.baseChange K).toAffine.Point))
    rw [ptCast_zero]
    exact (Point.map_zero g).symm
  | some x y hxy =>
    rw [Point.map_some, ptCast_some]
    rw [ptCast_some, Point.map_some]
    rw [Point.some.injEq]
    exact ⟨hfg x, hfg y⟩

/-! ## 3. The bridge -/

/-- **The bridge at an abstract constant curve.**  If the curve `E/𝔽` is constant and
`E(K) = E(𝔽)` (`ConstantsOnly`), then for any `W/𝕜` that is the base change of `E` to `𝕜`, and any
`𝕜`-algebra automorphism `f` of `K`, the induced map on `W(K) = ((E⁄𝕜)⁄K)(K)` is the identity.

The curve `W` is an explicit variable so that the hypothesis `hW : W = E⁄𝕜` can be substituted,
which reduces the statement to the single curve `E⁄𝕜`; the transport `ptCast` and
`map_transport_mixed` then carry it to `E⁄K`, where `ConstantsOnly` applies. -/
theorem forall_map_eq_self_of_constantsOnly_tower {𝔽 𝕜 K : Type} [Field 𝔽] [Field 𝕜] [Field K]
    [Algebra 𝔽 𝕜] [Algebra 𝔽 K] [Algebra 𝕜 K] [IsScalarTower 𝔽 𝕜 K]
    [DecidableEq 𝔽] [DecidableEq 𝕜] [DecidableEq K]
    (E : WeierstrassCurve 𝔽) (h : ConstantsOnly 𝔽 E K) (f : K ≃ₐ[𝕜] K)
    (W : WeierstrassCurve 𝕜) (hW : W = E.baseChange 𝕜) :
    ∀ R : (W.baseChange K).toAffine.Point, Point.map (W' := W) (f : K →ₐ[𝕜] K) R = R := by
  subst hW
  intro R
  -- `((E⁄𝕜)⁄K) = (E⁄K)`, both presented as `E` mapped along a ring homomorphism.
  have hbc : (E.baseChange 𝕜).baseChange K = E.baseChange K := by
    show (E.map (algebraMap 𝔽 𝕜)).map (algebraMap 𝕜 K) = E.map (algebraMap 𝔽 K)
    rw [WeierstrassCurve.map_map]
    exact congrArg E.map (IsScalarTower.algebraMap_eq 𝔽 𝕜 K).symm
  -- the `𝕜`-linear `f` is also `𝔽`-linear, with the same underlying function
  have hgfun : ∀ x : K, (f : K →ₐ[𝕜] K) x = (AlgEquiv.restrictScalars 𝔽 f : K →ₐ[𝔽] K) x :=
    fun x => rfl
  have hself : ∀ P : (E.baseChange K).toAffine.Point,
      Point.map (W' := E) (AlgEquiv.restrictScalars 𝔽 f : K →ₐ[𝔽] K) P = P :=
    fun P => map_eq_self_of_constantsOnly E (AlgEquiv.restrictScalars 𝔽 f) h P
  have key : ptCast hbc (Point.map (W' := E.baseChange 𝕜) (f : K →ₐ[𝕜] K) R) = ptCast hbc R := by
    rw [map_transport_mixed hbc (f : K →ₐ[𝕜] K) (AlgEquiv.restrictScalars 𝔽 f : K →ₐ[𝔽] K) hgfun R]
    exact hself (ptCast hbc R)
  have h2 := congrArg (ptCast hbc.symm) key
  simpa only [ptCast_symm_ptCast] using h2

/-- **The bridge `ConstantsOnly ⟹ TrivialGaloisAction` at the concrete data.**  If the constant Tate
curve with parameter `c ∈ 𝔽` has no non-constant `L`-points (`ConstantsOnly`, the classical
`E(𝔽(s)) = E(𝔽)`), then the Galois generator of `L/𝕜` acts trivially on `E(L)`; hence the twist is
pointless (`pointlessOf_of_trivialGaloisAction`).

Pure identification plumbing: `d.E_eq` identifies the curve of `d` with the base change of the
constant Tate model, and `forall_map_eq_self_of_constantsOnly_tower` transfers the trivial action
along that identification. -/
theorem trivialGaloisAction_of_constantsOnly {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type}
    [Field 𝕜] [DecidableEq 𝕜] [Algebra 𝔽 𝕜] (c : 𝔽)
    (d : Work.PointlessTwist.ConstantTateData 𝔽 𝕜 c) (L : Work.TorsorExistence.CyclicExtension 𝕜 5)
    [DecidableEq L.L] [Algebra 𝔽 L.L] [IsScalarTower 𝔽 𝕜 L.L]
    (h : Work.PointlessTwist.ConstantsOnly 𝔽 (Work.TorsorExistence.Tate.tateCurve c) L.L) :
    Work.PointlessTwist.TrivialGaloisAction d.C₅ L := by
  intro R
  show Point.map (W' := d.C₅.E) (L.gen : L.L →ₐ[𝕜] L.L) R = R
  exact forall_map_eq_self_of_constantsOnly_tower (Work.TorsorExistence.Tate.tateCurve c) h L.gen
    d.C₅.E d.E_eq R

end

end Work.PointlessTwist.bridge
