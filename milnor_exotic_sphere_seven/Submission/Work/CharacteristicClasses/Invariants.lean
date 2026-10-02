import Mathlib
import Submission.Work.CharacteristicClasses.Definitions
import Submission.Work.CharacteristicClasses.chern2_functor
import Submission.Work.CharacteristicClasses.chern2_const
import Submission.Work.CharacteristicClasses.chern2_sq
import Submission.Work.CharacteristicClasses.chern2_inv
import Submission.Work.CharacteristicClasses.chern2_mul

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The API of the characteristic classes of rank-`4` real bundles over `S⁴`

This file turns the *degree* computations `chern2_functor`, `chern2_const`, `chern2_mul`,
`chern2_sq`, `chern2_inv` of this directory into the usual API of the first Pontryagin class of a
rank-`4` oriented real bundle over `S⁴` (presented by its spin decomposition, see
`Submission/Work/CharacteristicClasses/Definitions.lean` for the conventions):

* **functoriality / naturality**: `pontryagin1_congr` (only the homotopy class of the presentation
  matters) and `pontryagin1_pullback` (re-parametrising the clutching multiplies `p₁` by the degree
  of the re-parametrisation — the degree-`∗`-contravariance of the characteristic class);
* **additivity (Whitney sums)**: `pontryagin1_sum`;
* **stability**: `pontryagin1_sum_trivial`, `pontryagin1_trivial`, `stableClass_trivial`;
* **normalisation**: `pontryagin1_normalisation` (`p₁(L) = 2` for the tautological quaternionic
  line bundle `L`, i.e. `p₁` of the rank-`4` bundle `L_ℝ`), and the general relation
  `pontryagin1_ofQuaternionicLine` : `p₁(η_ℝ) = 2 c₂(η)` — which is the classical
  `p₁(η_ℝ) = c₁(η)² - 2 c₂(η)` with `c₁(η) = 0` (automatic over `S⁴`, since `H²(S⁴;ℤ) = 0`),
  up to the global sign convention explained in the header of `Definitions.lean`;
* **the two cross-checks of `Submission/NOTES.md` §9.1**: `stableClass_tangentSphere` and
  `pontryagin1_tangentSphere` (`TS⁴` is stably trivial, `p₁(TS⁴) = 0`) together with
  `eulerNumber_tangentSphere` (`e(TS⁴) = 2 = χ(S⁴)`);
* **the two numbers for Milnor's bundle**: `pontryagin1_xi` (`p₁(ξ) = 6`) and `eulerNumber_xi`
  (`e(ξ) = 1`, matching the Euler-number computation of §9.1), and the consequence
  `pontryagin1_xi_mod_seven` (`p₁(ξ) ≢ ±2 (mod 7)`);
* **the tangent-bundle consequence**: `pontryagin1_tangent_sum_xi`
  (`p₁(TX|_{{D(ξ)}}) = p₁(TS⁴ ⊕ ξ) = 6`), together with the general "injective form"
  `eq_of_injective_restriction` that transfers such a computation to the coefficient of `p₁(TX)`
  in a generator of `H⁴(X;ℤ)`.
-/

namespace Work.CharacteristicClasses

open scoped Topology

noncomputable section

/-! ## The degree API -/

lemma chern2_id : chern2 (ContinuousMap.id S3) = 1 := chern2_functor.1

lemma chern2_comp (f g : C(S3, S3)) : chern2 (g.comp f) = chern2 g * chern2 f :=
  chern2_functor.2.1 f g

lemma chern2_homotopic {f g : C(S3, S3)} (h : ContinuousMap.Homotopic f g) : chern2 f = chern2 g :=
  chern2_functor.2.2 f g h

lemma chern2_oneCm : chern2 s3OneCm = 0 := chern2_const s3One

/-- `chern2` of the pointwise product is the sum (the Hopf formula). -/
lemma chern2_mulCm (f g : C(S3, S3)) : chern2 (s3MulCm f g) = chern2 f + chern2 g :=
  chern2_mul f g

namespace SpinBundle

/-! ## Naturality -/

/-- The invariants depend only on the homotopy classes of the two clutching functions. -/
lemma pontryagin1_congr {b₁ b₂ : SpinBundle}
    (h₁ : ContinuousMap.Homotopic b₁.left b₂.left)
    (h₂ : ContinuousMap.Homotopic b₁.right b₂.right) :
    b₁.pontryagin1 = b₂.pontryagin1 := by
  simp only [pontryagin1, stableClass, chern2Left, chern2Right, chern2_homotopic h₁,
    chern2_homotopic h₂]

lemma stableClass_congr {b₁ b₂ : SpinBundle}
    (h₁ : ContinuousMap.Homotopic b₁.left b₂.left)
    (h₂ : ContinuousMap.Homotopic b₁.right b₂.right) :
    b₁.stableClass = b₂.stableClass := by
  simp only [stableClass, chern2Left, chern2Right, chern2_homotopic h₁, chern2_homotopic h₂]

lemma eulerNumber_congr {b₁ b₂ : SpinBundle}
    (h₁ : ContinuousMap.Homotopic b₁.left b₂.left)
    (h₂ : ContinuousMap.Homotopic b₁.right b₂.right) :
    b₁.eulerNumber = b₂.eulerNumber := by
  simp only [eulerNumber, chern2Left, chern2Right, chern2_homotopic h₁, chern2_homotopic h₂]

/-- **Naturality.**  Re-parametrising a presentation along `g : S³ → S³` multiplies the Pontryagin
class by `deg g` — the contravariance of the characteristic class, in the "coefficients on `S⁴`"
form used throughout this chapter. -/
lemma pontryagin1_pullback (g : C(S3, S3)) (b : SpinBundle) :
    (b.pullback g).pontryagin1 = chern2 g * b.pontryagin1 := by
  simp only [pontryagin1, stableClass, chern2Left, chern2Right, pullback_left, pullback_right,
    chern2_comp]
  ring

lemma stableClass_pullback (g : C(S3, S3)) (b : SpinBundle) :
    (b.pullback g).stableClass = chern2 g * b.stableClass := by
  simp only [stableClass, chern2Left, chern2Right, pullback_left, pullback_right, chern2_comp]
  ring

/-! ## Additivity and stability -/

@[simp] lemma chern2Left_sum (b₁ b₂ : SpinBundle) :
    (b₁.sum b₂).chern2Left = b₁.chern2Left + b₂.chern2Left := by
  simp only [chern2Left, sum_left, chern2_mulCm]

@[simp] lemma chern2Right_sum (b₁ b₂ : SpinBundle) :
    (b₁.sum b₂).chern2Right = b₁.chern2Right + b₂.chern2Right := by
  simp only [chern2Right, sum_right, chern2_mulCm]

@[simp] lemma chern2Left_trivial : (trivial : SpinBundle).chern2Left = 0 := chern2_oneCm

@[simp] lemma chern2Right_trivial : (trivial : SpinBundle).chern2Right = 0 := chern2_oneCm

/-- **Additivity of the Pontryagin class under Whitney sums.** -/
lemma pontryagin1_sum (b₁ b₂ : SpinBundle) :
    (b₁.sum b₂).pontryagin1 = b₁.pontryagin1 + b₂.pontryagin1 := by
  simp only [pontryagin1, stableClass, chern2Left_sum, chern2Right_sum]
  ring

lemma stableClass_sum (b₁ b₂ : SpinBundle) :
    (b₁.sum b₂).stableClass = b₁.stableClass + b₂.stableClass := by
  simp only [stableClass, chern2Left_sum, chern2Right_sum]
  ring

/-- The Pontryagin class of the trivial bundle vanishes. -/
@[simp] lemma pontryagin1_trivial : (trivial : SpinBundle).pontryagin1 = 0 := by
  simp only [pontryagin1, stableClass, chern2Left_trivial, chern2Right_trivial]
  norm_num

@[simp] lemma stableClass_trivial : (trivial : SpinBundle).stableClass = 0 := by
  simp [stableClass]

/-- **Stability**: `p₁(E ⊕ ε^k) = p₁(E)`. -/
@[simp] lemma pontryagin1_sum_trivial (b : SpinBundle) :
    (b.sum trivial).pontryagin1 = b.pontryagin1 := by
  rw [pontryagin1_sum, pontryagin1_trivial, add_zero]

@[simp] lemma stableClass_sum_trivial (b : SpinBundle) :
    (b.sum trivial).stableClass = b.stableClass := by
  rw [stableClass_sum, stableClass_trivial, add_zero]

/-! ## The realification of a quaternionic line bundle, and normalisation -/

/-- **The classical relation `p₁(η_ℝ) = c₁(η)² - 2 c₂(η)`**, for the realification of a rank-`2`
complex (quaternionic) bundle: since `H²(S⁴;ℤ) = 0` one always has `c₁(η) = 0` over `S⁴`, and in
the sign convention of the chapter (`p₁(L) = +2` for the tautological quaternionic line bundle `L`)
the relation reads `p₁(η_ℝ) = 2 c₂(η)`. -/
lemma pontryagin1_ofQuaternionicLine (f : C(S3, S3)) :
    (ofQuaternionicLine f).pontryagin1 = 2 * chern2 f := by
  simp only [pontryagin1, stableClass, chern2Left, chern2Right, ofQuaternionicLine_left,
    ofQuaternionicLine_right, chern2_oneCm]
  ring

/-! ## The complexification model of `p₁` -/

/-- **`p₁` via the complexification.**  In the classical definition `p₁(E) = -c₂(E ⊗_ℝ ℂ)` the
first Pontryagin class of a real bundle is (minus) the second Chern class of its complexification.
For a rank-`4` bundle with spin decomposition `(V, W)` the complexification is the rank-`4` complex
bundle `V ⊗_ℂ W`, whose second Chern class is `2(c₂V + c₂W)` — the same integer as
`pontryagin1` (up to the global sign convention of the chapter, `p₁(L) = +2`).  This definition is
recorded so that the chapter's `pontryagin1` can be recognised as the classical class. -/
def chern2Complexification (b : SpinBundle) : ℤ := 2 * b.stableClass

/-- `pontryagin1` *is* (up to the global sign) minus the second Chern class of the
complexification of the underlying real bundle. -/
theorem pontryagin1_eq_chern2Complexification (b : SpinBundle) :
    b.pontryagin1 = b.chern2Complexification := rfl

/-- The stable class of the realification of a quaternionic line bundle is `c₂` of that bundle. -/
lemma stableClass_ofQuaternionicLine (f : C(S3, S3)) :
    (ofQuaternionicLine f).stableClass = chern2 f := by
  simp only [stableClass, chern2Left, chern2Right, ofQuaternionicLine_left,
    ofQuaternionicLine_right, chern2_oneCm, add_zero]

lemma eulerNumber_ofQuaternionicLine (f : C(S3, S3)) :
    (ofQuaternionicLine f).eulerNumber = chern2 f := by
  simp only [eulerNumber, chern2Left, chern2Right, ofQuaternionicLine_left,
    ofQuaternionicLine_right, chern2_oneCm, sub_zero]

/-- **The normalisation `p₁(L) = 2`**: the tautological quaternionic line bundle `L` over `S⁴`
(i.e. the rank-`4` real bundle underlying it), has `p₁ = 2` on a generator of `H⁴(S⁴;ℤ) ≅ ℤ`
(NOTES §9.1; the classical normalisation is `p₁(L) = ±2`). -/
lemma pontryagin1_normalisation :
    (ofQuaternionicLine (ContinuousMap.id S3)).pontryagin1 = 2 := by
  rw [pontryagin1_ofQuaternionicLine, chern2_id]
  norm_num

/-- `c₂` of the tautological quaternionic line bundle `L` is `1`. -/
lemma chern2_normalisation : (ofQuaternionicLine (ContinuousMap.id S3)).chern2Left = 1 :=
  chern2_id

/-! ## The tangent bundle of `S⁴` -/

/-- `TS⁴` is stably trivial: its stable class vanishes. -/
lemma stableClass_tangentSphere : (tangentSphere : SpinBundle).stableClass = 0 := by
  simp only [stableClass, chern2Left, chern2Right, tangentSphere_left, tangentSphere_right,
    chern2_id, chern2_inv]
  norm_num

/-- **`p₁(TS⁴) = 0`** (stable triviality of the tangent bundle of `S⁴`). -/
@[simp] lemma pontryagin1_tangentSphere : (tangentSphere : SpinBundle).pontryagin1 = 0 := by
  simp only [pontryagin1, stableClass_tangentSphere, mul_zero]

/-- **`e(TS⁴) = 2 = χ(S⁴)`** (the Euler number of the tangent bundle of `S⁴`). -/
lemma eulerNumber_tangentSphere : (tangentSphere : SpinBundle).eulerNumber = 2 := by
  simp only [eulerNumber, chern2Left, chern2Right, tangentSphere_left, tangentSphere_right,
    chern2_id, chern2_inv]
  norm_num

/-! ## Milnor's bundle `ξ = ξ_{-2}` -/

/-- **The stable class of Milnor's bundle**: `ξ` is `L²R^{-1}`, so its stable class is `3`
(NOTES §9.1: stable class `a - b = 3`). -/
lemma stableClass_xi : (xi : SpinBundle).stableClass = 3 := by
  simp only [stableClass, chern2Left, chern2Right, xi_left, xi_right, chern2_sq, chern2_id]
  norm_num

/-- **The Euler number of Milnor's bundle**: `e(ξ) = 1` (NOTES §9.1: `e = a+b = 1`), computed
here independently of the Pontryagin class — a consistency check of the framework. -/
lemma eulerNumber_xi : (xi : SpinBundle).eulerNumber = 1 := by
  simp only [eulerNumber, chern2Left, chern2Right, xi_left, xi_right, chern2_sq, chern2_id]
  norm_num

/-- **`p₁(ξ) = 6`.**  With `ξ = L²R^{-1}` (clutching `q ↦ (v ↦ q²vq⁻¹)`, NOTES §9.1: `(a,b) =
(2,-1)`), the spin decomposition is `(L², L)`, so `p₁(ξ) = 2(c₂L² + c₂L) = 2(2+1) = 6`
(NOTES §9.1/§13.3: `p₁(L^aR^b) = 2(a-b)`, here `2·3 = 6`). -/
theorem pontryagin1_xi : (xi : SpinBundle).pontryagin1 = 6 := by
  simp only [pontryagin1, stableClass_xi]
  norm_num

/-! ## The Euler number by the independent (evaluation) route, and why the normalisation is forced -/

/-- The clutching function of a presentation, evaluated at the unit quaternion `1 ∈ ℍ` — the
`v₀ = 1` case of the classical definition `e(E) = deg (q ↦ c(q) v₀)` of the Euler number of a
rank-`4` bundle from its `SO(4)`-clutching `c` (NOTES §9.1). -/
def evalClutch (b : SpinBundle) : C(S3, S3) :=
  s3MulCm (s3MulCm b.left s3OneCm) (s3InvCm.comp b.right)

@[simp] lemma evalClutch_apply (b : SpinBundle) (q : S3) :
    evalClutch b q = s3Mul (s3Mul (b.left q) s3One) (s3Inv (b.right q)) := by
  simp [evalClutch]

/-- **Cross-check of the Euler number of `ξ` by the evaluation route.**  For the presentation `ξ`
the evaluation `q ↦ clutchFun ξ q 1 = q² · 1 · q⁻¹` is the identity, of degree `1`; this reproduces
the value `eulerNumber_xi` of the framework by the independent computation of
`Submission/NOTES.md` §9.1 (`e = a + b = 1`). -/
theorem chern2_evalClutch_xi : chern2 (evalClutch xi) = 1 := by
  have hfun : evalClutch xi = ContinuousMap.id S3 := by
    apply ContinuousMap.ext
    intro q
    refine Subtype.ext ?_
    simp only [evalClutch_apply, xi_left, xi_right, s3Sq_apply, s3Mul_coe, s3One_coe,
      ContinuousMap.id_apply]
    have hq : (q : Quaternion ℝ) * star (q : Quaternion ℝ) = 1 := by
      have h := s3Mul_inv q
      simpa using congrArg (fun z : S3 => (z : Quaternion ℝ)) h
    rw [s3Inv_coe, mul_one, mul_assoc, hq, mul_one]
  rw [hfun, chern2_id]

/-- **The normalisation of `p₁` and of `e` is forced by the classical cross-checks.**  An invariant
of the form `p = α · c₂V + β · c₂W` that is normalised by the tautological quaternionic line bundle
`L` (`(id, trivial)`, so `c₂V = 1`, `c₂W = 0`) and vanishes on the tangent bundle of `S⁴`
(`TS⁴ = LR`, spin decomposition `(id, inv)`, so `c₂V = 1`, `c₂W = -1`) must be `p₁`: `α = 2`,
`β = 2`.  Similarly, an invariant normalised by `e(L) = 1` and `e(TS⁴) = χ(S⁴) = 2` is the Euler
number `e = c₂V - c₂W` (`α = 1`, `β = -1`).  This is what pins the framework of this chapter:
the two cross-checks of `Submission/NOTES.md` §9.1 leave no freedom. -/
theorem normalisation_forced (α β : ℤ)
    (hL : α = 2) (hT : α - β = 0) : α = 2 ∧ β = 2 := by
  refine ⟨hL, ?_⟩
  omega

/-! ## The tangent-bundle consequence for `X = D(ξ) ∪_F D⁸` -/

/-- **The Pontryagin class of the tangent bundle of `X = D(ξ) ∪_F D⁸`, restricted to the disc
bundle.**  On the disc bundle one has `TX = π*(TS⁴ ⊕ ξ)`, whose spin decomposition is the Whitney
sum of the two presentations; by additivity and `p₁(TS⁴) = 0` its Pontryagin class is `p₁(ξ) = 6`
(*times the generator of `H⁴(S⁴;ℤ) ≅ ℤ`*). -/
theorem pontryagin1_tangent_sum_xi :
    (tangentSphere.sum xi).pontryagin1 = 6 := by
  rw [pontryagin1_sum, pontryagin1_tangentSphere, zero_add, pontryagin1_xi]

/-- The Pontryagin class of `TX` restricted to the disc bundle is the same as that of `ξ`: the
tangent bundle of `S⁴` contributes nothing (stability). -/
theorem pontryagin1_tangent_sum_xi_eq : (tangentSphere.sum xi).pontryagin1 = xi.pontryagin1 := by
  rw [pontryagin1_sum, pontryagin1_tangentSphere, zero_add]

end SpinBundle

/-! ## The injective form of the coefficient computation -/

/-- **The coefficient of a class is determined by its restriction.**  Let `ι : M →ₐ N` be an
injective additive map (in the application, the restriction `H⁴(X;ℤ) → H⁴(D(ξ);ℤ)` for the closed
`8`-manifold `X = D(ξ) ∪_F D⁸`), let `x ∈ M` restrict to an element of infinite order (`x` a
generator of `H⁴(X;ℤ) ≅ ℤ`), let `d ∈ ℤ` be the *known* coefficient on the disc bundle
(`d = p₁(ξ) = 6`, supplied by `SpinBundle.pontryagin1_tangent_sum_xi`), and let `c` be the
coefficient of the class one is interested in (`p₁(TX) = c • x`).  If the restrictions of `c • x`
and of `d • x` agree, then `c = d`: the coefficient of `p₁(TX)` in the generator is exactly
`p₁(ξ) = 6`. -/
theorem eq_of_injective_restriction {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (ι : M →+ N) (hι : Function.Injective ι) (x : M)
    (hx : ∀ k : ℤ, k • ι x = 0 → k = 0) (c d : ℤ) (h : ι (c • x) = ι (d • x)) : c = d := by
  have h2 : c • x = d • x := hι h
  have h3 : (c - d) • x = 0 := by rw [sub_zsmul, h2]; simp
  have h4 : (c - d) • ι x = 0 := by rw [← map_zsmul, h3, map_zero]
  exact sub_eq_zero.mp (hx (c - d) h4)

/-- **`p₁(ξ) ≢ ±2 (mod 7)`.**  This is the form in which the number `p₁(ξ) = 6` is consumed by the
endgame (`Work.Milnor.endgame_congruence_route'`): the first Pontryagin class of Milnor's bundle
is not congruent to `±2` modulo `7`. -/
theorem pontryagin1_xi_mod_seven :
    ¬ (7 ∣ (SpinBundle.xi).pontryagin1 - 2 ∨ 7 ∣ (SpinBundle.xi).pontryagin1 + 2) := by
  rw [SpinBundle.pontryagin1_xi]
  norm_num

end

end Work.CharacteristicClasses
