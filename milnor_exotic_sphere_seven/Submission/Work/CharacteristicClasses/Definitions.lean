import Mathlib
import Submission.Work.CharacteristicClasses.Degree
import Submission.Work.Milnor.VBundleDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Rank-`4` real bundles over `S⁴` by their spin decomposition, and their Pontryagin class

**A rank-`4` oriented real vector bundle over `S⁴` is spin.**  Indeed `π₁(SO(4)) = ℤ/2` and
`π₂(SO(4)) = 0`, so the only obstruction to a spin structure is `w₂ ∈ H²(S⁴; ℤ/2) = 0`: *every*
oriented rank-`4` bundle over `S⁴` admits a spin structure.  The double cover
`Spin(4) ≅ Sp(1) × Sp(1) → SO(4)` sends `(u₁, u₂)` to the rotation `v ↦ u₁ v u₂⁻¹`
(`v ∈ ℍ = ℝ⁴`), so a spin structure on a rank-`4` bundle over `S⁴` is precisely a pair of
*quaternionic line bundles* `(V, W)`, and the underlying real bundle is the "tensor product"
`V ⊗_ℍ W` (`E(V,W)`, whose real dimension is `4`).

Historically the invariants of `E(V,W)` in terms of the pair `(c₂V, c₂W) ∈ ℤ²` are

* the **Euler number** `e = c₂V - c₂W`  (its evaluation on `[S⁴]`, see NOTES §9.1 for the
  conventions `e(L^aR^b) = a+b`);
* the **stable class** `s = c₂V + c₂W` in `KO~(S⁴) ≅ ℤ` (NOTES §9.1: `a - b`);
* the **first Pontryagin class** `p₁(E) = 2s = 2(c₂V + c₂W)` on a basis of `H⁴(S⁴;ℤ) ≅ ℤ`
  (NOTES §9.1: `p₁(L^aR^b) = 2(a-b)`; equivalently, in the classical normalisation in which
  `p₁ = -c₂(E ⊗_ℝ ℂ)`, the same number with the opposite global sign — the global sign is
  irrelevant for the application in `Submission/NOTES.md` §14.7/§14.8, which only uses
  `p₁(ξ) ≢ ±2 (mod 7)`).

This file fixes the *framework*: a bundle is *presented* by its spin decomposition, i.e. by a pair
of continuous maps `left right : S³ → S³` (the clutching functions of `V` and of `W`), and the
invariants above are functions of the degrees of these two maps.  Two classical facts are used,
and are the only "imported" mathematics of the chapter (everything else about them is proved):

1. **`c₂` of a quaternionic line bundle over `S⁴` is the degree of its clutching function.**  A
   quaternionic line bundle over `S⁴` with clutching `f : S³ → S³ = Sp(1)`, considered as a
   complex rank-`2` bundle via the complex structure `i`, is an `SU(2)`-bundle whose second Chern
   class `c₂ ∈ H⁴(S⁴;ℤ) ≅ ℤ` is the Bott invariant, equal to the class of `f` in `π₃(SU(2)) = ℤ`,
   i.e. to `deg f`.  (This is the standard identification; `chern2` below *is* this degree.)
2. **The Whitney sum of the underlying bundles corresponds, on the invariants, to the pointwise
   products** `(V, W) + (V', W') = (V ⊗ V', W ⊗ W')`: since `π₃(SU(2)) = ℤ` is abelian, the group
   structure induced by `⊕` and by `⊗` agree, so `c₂(V ⊕ V') = c₂V + c₂V' = deg(left · left')`.
   This is the *Hopf formula* `deg (q ↦ f q * g q) = deg f + deg g`, proved in
   `Submission/Work/CharacteristicClasses/chern2_mul.lean`.

Consequently the chapter's additivity/stability/normalisation statements (in `Invariants.lean`)
are *theorems* about the degree of maps `S³ → S³`, not assumptions.
-/

namespace Work.CharacteristicClasses

open scoped Topology

noncomputable section

/-- The `ℝ`-linear map `v ↦ a * v * b` on the quaternions `ℍ = ℝ⁴`. -/
def mulLin (a b : Quaternion ℝ) : (Quaternion ℝ) →ₗ[ℝ] (Quaternion ℝ) where
  toFun v := a * v * b
  map_add' x y := by simp [mul_add, add_mul]
  map_smul' r x := by simp [smul_mul_assoc]

@[simp] lemma mulLin_apply (a b v : Quaternion ℝ) : mulLin a b v = a * v * b := rfl

/-- **A rank-`4` oriented real bundle over `S⁴` with a spin structure, presented by its spin
decomposition**: `left` and `right` are the clutching functions of the two quaternionic line
bundles `V` and `W`, so that the clutching function of the underlying real bundle is
`q ↦ left q * v * (right q)⁻¹` (`v ∈ ℍ = ℝ⁴`).

Two presentations with homotopic `left`/`right` present the same bundle with the same spin
structure, and have the same invariants (`pontryagin1_congr`); every oriented rank-`4` real bundle
over `S⁴` admits a presentation. -/
structure SpinBundle where
  left : C(S3, S3)
  right : C(S3, S3)

namespace SpinBundle

/-- The **clutching function of the underlying rank-`4` real bundle**, at the level of the fibre
`ℍ = ℝ⁴`: `v ↦ left q * v * (right q)⁻¹`. -/
def clutchFun (b : SpinBundle) (q : S3) (v : Quaternion ℝ) : Quaternion ℝ :=
  (b.left q : Quaternion ℝ) * v * ((b.right q : Quaternion ℝ))⁻¹

/-- The clutching function of the underlying real bundle, as an `ℝ`-linear automorphism of the
fibre `ℍ = ℝ⁴`. -/
def clutchLin (b : SpinBundle) (q : S3) : (Quaternion ℝ) →ₗ[ℝ] (Quaternion ℝ) :=
  mulLin (b.left q : Quaternion ℝ) ((b.right q : Quaternion ℝ))⁻¹

@[simp] lemma clutchLin_apply (b : SpinBundle) (q : S3) (v : Quaternion ℝ) :
    b.clutchLin q v = b.clutchFun q v := rfl

/-- The second Chern class `c₂(V)` of the *left* quaternionic line bundle: the degree of its
clutching function. -/
def chern2Left (b : SpinBundle) : ℤ := chern2 b.left

/-- The second Chern class `c₂(W)` of the *right* quaternionic line bundle. -/
def chern2Right (b : SpinBundle) : ℤ := chern2 b.right

/-- The **stable class** `c₂V + c₂W ∈ ℤ ≅ KO~(S⁴)`, i.e. the class of the bundle in the reduced
stable `KO`-group of `S⁴` (NOTES §9.1: `a - b`). -/
def stableClass (b : SpinBundle) : ℤ := b.chern2Left + b.chern2Right

/-- The **first Pontryagin class** of the bundle, as an element of `H⁴(S⁴;ℤ) ≅ ℤ`: twice the
stable class.  This is the classical `p₁(E(V,W)) = 2(c₂V + c₂W)` (up to the global sign
convention discussed in the header). -/
def pontryagin1 (b : SpinBundle) : ℤ := 2 * b.stableClass

/-- The **Euler number** `e = c₂V - c₂W` of the underlying rank-`4` bundle (`⟨e, [S⁴]⟩`).
This is an invariant of the rank-`4` bundle itself (not only of its stable class), and is *not*
additive/stable; it is recorded here because it is the second classical invariant of a rank-`4`
bundle over `S⁴` (`π₃(SO(4)) = ℤ²`) and provides the cross-checks `e(TS⁴) = 2 = χ(S⁴)` and
`e(ξ) = 1` of `Submission/NOTES.md` §9.1. -/
def eulerNumber (b : SpinBundle) : ℤ := b.chern2Left - b.chern2Right

/-- **The Whitney sum** of two presentations: at the level of invariants this is the pointwise
product of the clutching functions (see the header; `c₂` is additive under both `⊕` and `⊗`). -/
def sum (b₁ b₂ : SpinBundle) : SpinBundle :=
  ⟨s3MulCm b₁.left b₂.left, s3MulCm b₁.right b₂.right⟩

/-- The **trivial bundle** (with its trivial spin structure). -/
def trivial : SpinBundle := ⟨s3OneCm, s3OneCm⟩

/-- The presentation of the **realification of a quaternionic line bundle** with clutching `f`:
the underlying real rank-`4` bundle with the spin decomposition `(V, trivial)`. -/
def ofQuaternionicLine (f : C(S3, S3)) : SpinBundle := ⟨f, s3OneCm⟩

/-- **The tangent bundle of `S⁴`**, presented by its spin decomposition.  The quaternionic
description of `TS⁴`: left translation identifies `T_q S⁴` with `ℍ`, and the clutching of `TS⁴`
is `q ↦ (v ↦ q v q)` (NOTES §9.1: `TS⁴ = LR`, i.e. `(a,b) = (1,1)`), so the spin decomposition
is `(q ↦ q, q ↦ q⁻¹)`, i.e. `(id, inv)`. -/
def tangentSphere : SpinBundle := ⟨ContinuousMap.id S3, s3InvCm⟩

/-- **Milnor's bundle `ξ = ξ_{-2}`.**  In `Submission/Work/Milnor/VBundleDefs.lean` the bundle is
defined by the clutching `vTwist 2 q v = q² v q⁻¹`, i.e. `(a,b) = (2,-1)`, whose spin
decomposition is `(q ↦ q², q ↦ q)`. -/
def xi : SpinBundle := ⟨s3Sq, ContinuousMap.id S3⟩

/-- Re-parametrising a presentation along a map of `S³` (the effect on the invariants is
multiplicativity of the degree, `chern2 g`, which is the contravariance of the characteristic
class). -/
def pullback (g : C(S3, S3)) (b : SpinBundle) : SpinBundle :=
  ⟨b.left.comp g, b.right.comp g⟩

@[simp] lemma chern2Left_mk (f g : C(S3, S3)) : (SpinBundle.mk f g).chern2Left = chern2 f := rfl
@[simp] lemma chern2Right_mk (f g : C(S3, S3)) : (SpinBundle.mk f g).chern2Right = chern2 g := rfl

@[simp] lemma sum_left (b₁ b₂ : SpinBundle) : (b₁.sum b₂).left = s3MulCm b₁.left b₂.left := rfl
@[simp] lemma sum_right (b₁ b₂ : SpinBundle) : (b₁.sum b₂).right = s3MulCm b₁.right b₂.right :=
  rfl
@[simp] lemma trivial_left : (trivial : SpinBundle).left = s3OneCm := rfl
@[simp] lemma trivial_right : (trivial : SpinBundle).right = s3OneCm := rfl
@[simp] lemma ofQuaternionicLine_left (f : C(S3, S3)) :
    (ofQuaternionicLine f).left = f := rfl
@[simp] lemma ofQuaternionicLine_right (f : C(S3, S3)) :
    (ofQuaternionicLine f).right = s3OneCm := rfl
@[simp] lemma tangentSphere_left : (tangentSphere : SpinBundle).left = ContinuousMap.id S3 := rfl
@[simp] lemma tangentSphere_right : (tangentSphere : SpinBundle).right = s3InvCm := rfl
@[simp] lemma xi_left : (xi : SpinBundle).left = s3Sq := rfl
@[simp] lemma xi_right : (xi : SpinBundle).right = ContinuousMap.id S3 := rfl
@[simp] lemma pullback_left (g : C(S3, S3)) (b : SpinBundle) :
    (b.pullback g).left = b.left.comp g := rfl
@[simp] lemma pullback_right (g : C(S3, S3)) (b : SpinBundle) :
    (b.pullback g).right = b.right.comp g := rfl

end SpinBundle

/-! ## The bridge to Milnor's bundle

The bundle `ξ = Vk (-2)` of `Submission/Work/Milnor/VBundleDefs.lean` is defined by the clutching
`vTwist 2 q v = q² * v * q⁻¹` on the fibre `ℍ = ℝ⁴`.  The two theorems below identify this
clutching function with the one of `SpinBundle.xi`, i.e. they say that `SpinBundle.xi` really is
Milnor's bundle (with the spin decomposition read off from the explicit clutching). -/

/-- The clutching function of `ξ = Vk (-2)` (as encoded in `Submission.Milnor.vTwist`) is the
clutching function of the spin presentation `SpinBundle.xi`. -/
theorem vTwist_two_eq_clutchFun (q : S3) (v : Quaternion ℝ) :
    Submission.Milnor.vTwist 2 (q : Quaternion ℝ) v = SpinBundle.xi.clutchFun q v := by
  have h2 : (q : Quaternion ℝ) ^ (2 : ℤ) = (s3Mul q q : S3) := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
    rfl
  rw [Submission.Milnor.vTwist, SpinBundle.clutchFun, SpinBundle.xi, h2]
  rfl

end

end Work.CharacteristicClasses
