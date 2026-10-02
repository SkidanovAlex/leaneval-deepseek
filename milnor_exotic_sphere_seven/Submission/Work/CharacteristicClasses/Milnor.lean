import Mathlib
import Submission.Work.CharacteristicClasses.Invariants

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The first Pontryagin class of Milnor's bundle `ξ = ξ_{-2}`, and the tangent-bundle consequence

This is the interface file of the characteristic-class chapter: everything the endgame of
`Submission/Work/Milnor/EndgameArith.lean` needs, under the `Work.Milnor` namespace.

The conventions and the framework are in
`Submission/Work/CharacteristicClasses/Definitions.lean` (a rank-`4` oriented real bundle over `S⁴`
is spin, and is presented by its spin decomposition `(V, W)`, a pair of quaternionic line bundles,
i.e. of continuous maps `S³ → S³`); the invariants are
`p₁ = 2(c₂V + c₂W)`, stable class `c₂V + c₂W`, Euler number `c₂V - c₂W`, where `c₂` of a
quaternionic line bundle over `S⁴` is the *degree* of its clutching function.

For Milnor's bundle `ξ = L²R^{-1}` (clutching `q ↦ (v ↦ q²vq^{-1})`, i.e. spin decomposition
`(L², L) = (q ↦ q², q ↦ q)`):

* `p1_xi` : `p₁(ξ) = 6` (NOTES §9.1: `p₁(L^aR^b) = 2(a-b)` with `(a,b) = (2,-1)`);
* `p1_xi_mod_seven` : `p₁(ξ) ≢ ±2 (mod 7)` — the form consumed by
  `Work.Milnor.endgame_congruence_route'`;
* `p1_tangent_X` : the first Pontryagin class of the tangent bundle of `X = D(ξ) ∪_F D⁸`,
  restricted to the disc bundle (`TX|_{{D(ξ)}} = π*(TS⁴ ⊕ ξ)`), is `6` — the tangent bundle of `S⁴`
  contributes nothing because it is stably trivial (`p₁(TS⁴) = 0`);
* `p1_tangent_X_coefficient` : the consequent "injective form": if the restriction of the class
  `p₁(TX) = c • x` to the disc bundle agrees with `6 • x`, `x` a generator of `H⁴(X;ℤ) ≅ ℤ` of
  infinite order and the restriction injective, then the coefficient is `c = 6`;
* `p1_tangent_X_coefficient_mod_seven` : hence `7 ∤ c² - 4` for that coefficient.

**The class-level form** (the input the endgame actually consumes) is in
`Submission/Work/CharacteristicClasses/Capped.lean`: the first Pontryagin class of `TX` as a class
`Work.Milnor.cappedPontryaginClass ∈ H⁴(X;ℤ)` (the class restricting to `6 · τ` on the disc
bundle), with `Work.Milnor.cappedPontryaginClass_six : p₁(TX) = q • x` for `q ∈ {6, -6}` in every
generator `x` of `H⁴(X;ℤ) ≅ ℤ`, and the restriction `H⁴(X;ℤ) → H⁴(D(ξ);ℤ)` being an isomorphism
(`Work.Milnor.cappedRestriction_isIso`).  `Submission/Work/CharacteristicClasses/Endgame.lean`
then feeds that input to `Work.SignatureBordism.capped_obstruction_of_selfIntersection`
(`Work.Milnor.capped_obstruction_with_pontryagin`).

The two cross-checks of `Submission/NOTES.md` §9.1 are also available in the framework file
(`Work.CharacteristicClasses.SpinBundle.eulerNumber_xi` : `e(ξ) = 1`,
`...eulerNumber_tangentSphere` : `e(TS⁴) = 2 = χ(S⁴)`,
`...stableClass_tangentSphere` and `...pontryagin1_tangentSphere` : `TS⁴` is stably trivial).
-/

namespace Work.Milnor

open Work.CharacteristicClasses

/-- **The first Pontryagin class of Milnor's bundle `ξ = ξ_{-2}` is `6`.**

`ξ` is the rank-`4` real bundle over `S⁴` of `Submission/Work/Milnor/VBundleDefs.lean`
(`Vk (-2)`), with clutching `vTwist 2 q v = q² v q⁻¹` (see
`Work.CharacteristicClasses.vTwist_two_eq_clutchFun`), i.e. `L²R^{-1}` in the conventions of
`Submission/NOTES.md` §9.1.  Its spin decomposition is `(L², L)`, so
`p₁(ξ) = 2(c₂L² + c₂L) = 2(2 + 1) = 6`; this is the value quoted in NOTES §9.1/§13.3
(`p₁(L^aR^b) = 2(a-b)` with `(a,b) = (2,-1)`), up to the global sign convention. -/
theorem p1_xi : (SpinBundle.xi).pontryagin1 = 6 := SpinBundle.pontryagin1_xi

/-- **`p₁(ξ) ≢ ±2 (mod 7)`.**  The precise statement consumed by the endgame: the first
Pontryagin class of Milnor's bundle is congruent to neither `2` nor `-2` modulo `7` (it is `6`).
With `Work.Milnor.endgame_congruence_route'` this is the third input of the contradiction
(the other two being `m = ±1` and the dimension-`8` Hirzebruch congruence). -/
theorem p1_xi_mod_seven :
    ¬ (7 ∣ (SpinBundle.xi).pontryagin1 - 2 ∨ 7 ∣ (SpinBundle.xi).pontryagin1 + 2) :=
  Work.CharacteristicClasses.pontryagin1_xi_mod_seven

/-- **The Euler number of `ξ` is `1`** (NOTES §9.1: `e(L^aR^b) = a+b`, here `2 + (-1) = 1`).
This is an independent consistency check of the framework: the Euler number is the degree of the
evaluation map `q ↦ q²·1·q⁻¹ = q`, computed without any Pontryagin class. -/
theorem eulerNumber_xi : (SpinBundle.xi).eulerNumber = 1 := SpinBundle.eulerNumber_xi

/-- **The tangent-bundle consequence.**  For the closed `8`-manifold `X = D(ξ) ∪_F D⁸`
(`Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)`) one has
`TX|_{{D(ξ)}} = π*(TS⁴ ⊕ ξ)`, and the first Pontryagin class of that bundle is `6` (times a
generator of `H⁴(S⁴;ℤ) ≅ ℤ`): the tangent bundle of `S⁴` is stably trivial (`p₁(TS⁴) = 0`), so
it contributes nothing, and `p₁(ξ) = 6`. -/
theorem p1_tangent_X : (SpinBundle.tangentSphere.sum SpinBundle.xi).pontryagin1 = 6 :=
  SpinBundle.pontryagin1_tangent_sum_xi

/-- The Pontryagin class of `TX` restricted to the disc bundle equals that of `ξ`: the stably
trivial summand `TS⁴` contributes nothing. -/
theorem p1_tangent_X_eq :
    (SpinBundle.tangentSphere.sum SpinBundle.xi).pontryagin1 = (SpinBundle.xi).pontryagin1 :=
  SpinBundle.pontryagin1_tangent_sum_xi_eq

/-- **The injective form: the coefficient of `p₁(TX)` in a generator of `H⁴(X;ℤ) ≅ ℤ` is `6`.**

Let `ι` be the restriction `H⁴(X;ℤ) → H⁴(D(ξ);ℤ)` (injective, because the latter is the
`H⁴(S⁴;ℤ)` of the disc bundle and the Mayer–Vietoris sequence of the cover of `X` has vanishing
neighbouring terms), let `x` be a generator of `H⁴(X;ℤ) ≅ ℤ` (so `k • ι x = 0` only for `k = 0`),
and suppose the class `p₁(TX) = c • x` restricts to `6 • (ι x)` — which is what
`p1_tangent_X` computes on the disc bundle.  Then `c = 6`. -/
theorem p1_tangent_X_coefficient {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (ι : M →+ N) (hι : Function.Injective ι) (x : M)
    (hx : ∀ k : ℤ, k • ι x = 0 → k = 0) (c : ℤ)
    (h : ι (c • x) = ι ((6 : ℤ) • x)) : c = 6 :=
  Work.CharacteristicClasses.eq_of_injective_restriction ι hι x hx c 6 h

/-- **The congruence obtained from the coefficient.**  The coefficient `c` of `p₁(TX)` in a
generator of `H⁴(X;ℤ) ≅ ℤ` satisfies `c = ±6` (depending on the orientation chosen for `x`), and
therefore `c² ≡ 36 ≡ 1 (mod 7)`: in particular `7 ∤ c² - 4`, which is the negation of the
Hirzebruch congruence `c² ≡ 4 (mod 7)` obtained from `m = ±1`. -/
theorem p1_tangent_X_coefficient_mod_seven (c : ℤ) (hc : c = 6 ∨ c = -6) :
    ¬ (7 ∣ c ^ 2 - 4) := by
  rcases hc with rfl | rfl <;> decide

end Work.Milnor
