import Mathlib
import Submission.Work.StemsB.wangThetaTw
import Submission.Work.StemsB.wangTheta_cup
import Submission.Work.Cohomology.CupRing

/-!
# The derivation property of the *twisted* Wang transgression

`wangThetaTw.lean` defines the twisted transgression `ω_n = c_n • θ_n` with `c_n = (-1)^{b n}`,
`θ = ρ ∘ Σ ∘ λ_G^*` the geometric transgression of `wangCollarDerivDefs.lean`, and shows
(`wangTheta_cup.lean`) that the *untwisted* transgression `θ` satisfies the degree-dependent
sign rule

`θ_{n+n'}(a ⌣ b') = (-1)^{n+b} · a ⌣ θ_{n'}(b') + (-1)^{b(n'+1)} · θ_n(a) ⌣ b'`.

Here the two scalar identities of `wangThetaTw.lean` (`wangSgn_mul_neg_one`, `wangSgn_mul_neg_one'`)
turn this into the derivation property of `ω` in the Koszul form required by
`Work.StemsB.WangCohShiftDerivation`:

`ω_{n+n'+b}(a ⌣ b') = ω_n(a) ⌣ b' + (-1)^{(b-1)(n+b)} · a ⌣ ω_{n'}(b')`,

i.e. `ω` is a derivation of degree `-(b-1)`.  Concretely, with `X = a ⌣ θ_{n'}(b')`,
`Y = θ_n(a) ⌣ b'` and `A = (-1)^{n+b}`, `B = (-1)^{b(n'+1)}` the untwisted identity reads
`θ_{n+n'+b}(...) = A·X + B·Y`, so the twisted statement is the coefficient computation

`c_{n+n'+b} · A · c_{n'} = (-1)^{(b-1)(n+b)}`, `c_{n+n'+b} · B · c_n = 1`,

which is exactly the pair of identities proved in `wangThetaTw.lean`.

The only non-formal-algebra ingredients are the linearity of the degree transports
(`cohEqIso`) and of the cup product in either variable, in the `ℤ`-scalar normalisation of the
`•` notation on `H^*(X;ℤ)` used throughout this directory.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.StemsB

noncomputable section

/-! ## Scalar bookkeeping

The `•` notation on the cohomology groups `H^n(X;ℤ)` resolves to the canonical
`ZSMul.toSMul` of an additive commutative group, whereas the lemmas about linear maps produce the
`SMul` coming from the `Module ℤ` structure.  The two agree by definition but not definitionally; as
in `Work.Kunneth.PointTopValue`, every transfer between them goes through Mathlib's bridge
`int_smul_eq_zsmul`, while the *canonical* `ZSMul` lemmas (`zsmul_add`, `smul_smul`) are used for
the module algebra itself. -/

/-- The evaluation of a scalar multiple of a linear map, for the canonical `ℤ`-module structures. -/
private lemma linSmulApply {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (c : ℤ) (f : M →ₗ[ℤ] N) (x : M) : (c • f) x = c • f x := rfl

/-- The degree transport `cohEqIso` is `ℤ`-linear. -/
private lemma wangCohEqIso_smul (Fsp : TopCat) {k l : ℕ} (h : k = l) (c : ℤ)
    (z : Work.Cohomology.singularCohomology ℤ k Fsp) :
    (cohEqIso Fsp h).hom (c • z) = c • (cohEqIso Fsp h).hom z := by
  cases h; rfl

/-- The cup product is `ℤ`-linear in its first variable, in the normalisation of the `•`
notation of this file. -/
private lemma wangCupH_smul_left (Fsp : TopCat) (m m' : ℕ) (c : ℤ)
    (x : Work.Cohomology.singularCohomology ℤ m Fsp)
    (y : Work.Cohomology.singularCohomology ℤ m' Fsp) :
    Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) m m' (c • x) y
      = c • Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) m m' x y := by
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
    (Work.Cohomology.singularCohomology ℤ m Fsp)) c x]
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
    (Work.Cohomology.singularCohomology ℤ (m + m') Fsp)) c
      (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) m m' x y)]
  exact Work.Cohomology.cupH'_smul_left ℤ (TopCat.toSSet.obj Fsp) m m' c x y

/-- The cup product is `ℤ`-linear in its second variable. -/
private lemma wangCupH_smul_right (Fsp : TopCat) (m m' : ℕ) (c : ℤ)
    (x : Work.Cohomology.singularCohomology ℤ m Fsp)
    (y : Work.Cohomology.singularCohomology ℤ m' Fsp) :
    Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) m m' x (c • y)
      = c • Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) m m' x y := by
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
    (Work.Cohomology.singularCohomology ℤ m' Fsp)) c y]
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
    (Work.Cohomology.singularCohomology ℤ (m + m') Fsp)) c
      (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) m m' x y)]
  exact Work.Cohomology.cupH'_smul_right ℤ (TopCat.toSSet.obj Fsp) m m' c x y

/-- The first twist identity of `wangThetaTw.lean`, solved for the twist scalar: the product
`c_{n+n'+b} · (-1)^{b(n'+1)}` is `c_n`. -/
private lemma wangSgn_mul_neg_one_eq (b n n' : ℕ) :
    wangSgn b (n + n' + b) * (-1 : ℤ) ^ (b * (n' + 1)) = wangSgn b n := by
  have h := wangSgn_mul_neg_one b n n'
  calc wangSgn b (n + n' + b) * (-1 : ℤ) ^ (b * (n' + 1))
      = (wangSgn b (n + n' + b) * (-1 : ℤ) ^ (b * (n' + 1)) * wangSgn b n) * wangSgn b n := by
        rw [mul_assoc, wangSgn_sq, mul_one]
    _ = 1 * wangSgn b n := by rw [h]
    _ = wangSgn b n := one_mul _

/-- The second twist identity of `wangThetaTw.lean`, solved for the twist scalar: the product
`c_{n+n'+b} · (-1)^{n+b}` is `(-1)^{(b-1)(n+b)} · c_{n'}`. -/
private lemma wangSgn_mul_neg_one_eq' (b n n' : ℕ) (hb : 1 ≤ b) :
    wangSgn b (n + n' + b) * (-1 : ℤ) ^ (n + b)
      = (-1 : ℤ) ^ ((b - 1) * (n + b)) * wangSgn b n' := by
  have h := wangSgn_mul_neg_one' b n n' hb
  calc wangSgn b (n + n' + b) * (-1 : ℤ) ^ (n + b)
      = (wangSgn b (n + n' + b) * (-1 : ℤ) ^ (n + b) * wangSgn b n') * wangSgn b n' := by
        rw [mul_assoc, wangSgn_sq, mul_one]
    _ = (-1 : ℤ) ^ ((b - 1) * (n + b)) * wangSgn b n' := by rw [h]

/-! ## The derivation property -/

theorem wangThetaTw_derivation (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b)
      (Work.StemsB.dOuter b)) :
    ∀ (n n' : ℕ) (a : Work.Cohomology.singularCohomology ℤ (n + b) (Work.StemsB.wangCohFsp b p))
      (b' : Work.Cohomology.singularCohomology ℤ (n' + b) (Work.StemsB.wangCohFsp b p)),
      Work.StemsB.wangThetaTw b hb p d_G hT_G hT_O (n + n' + b)
          ((Work.StemsB.cohEqIso (Work.StemsB.wangCohFsp b p) (by omega)).hom
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (Work.StemsB.wangCohFsp b p)) (n + b) (n' + b) a b'))
        = (Work.StemsB.cohEqIso (Work.StemsB.wangCohFsp b p) (by omega)).hom
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (Work.StemsB.wangCohFsp b p)) (n + 1) (n' + b)
              (Work.StemsB.wangThetaTw b hb p d_G hT_G hT_O n a) b')
          + (-1 : ℤ) ^ ((b - 1) * (n + b)) •
              (Work.StemsB.cohEqIso (Work.StemsB.wangCohFsp b p) (by omega)).hom
                (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (Work.StemsB.wangCohFsp b p)) (n + b) (n' + 1)
                  a (Work.StemsB.wangThetaTw b hb p d_G hT_G hT_O n' b')) := by
  intro n n' a b'
  -- the untwisted derivation property, in the spelling of this file
  have hc := wangTheta_cup b hb E p d_G hT_G hT_O n n' a b'
  have hc' : wangTheta b hb p d_G hT_G hT_O (n + n' + b)
        ((cohEqIso (wangCohFsp b p) (by omega : (n + b) + (n' + b) = (n + n' + b) + b)).hom
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (wangCohFsp b p)) (n + b) (n' + b) a b'))
      = (-1 : ℤ) ^ (n + b) •
          (cohEqIso (wangCohFsp b p) (by omega : (n + b) + (n' + 1) = (n + n' + b) + 1)).hom
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (wangCohFsp b p)) (n + b) (n' + 1) a
              (wangTheta b hb p d_G hT_G hT_O n' b'))
        + (-1 : ℤ) ^ (b * (n' + 1)) •
            (cohEqIso (wangCohFsp b p) (by omega : (n + 1) + (n' + b) = (n + n' + b) + 1)).hom
              (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (wangCohFsp b p)) (n + 1) (n' + b)
                (wangTheta b hb p d_G hT_G hT_O n a) b') := hc
  -- unfold the twist `ω = c • θ` and pull the scalars out of the linear maps
  simp only [wangThetaTw]
  rw [linSmulApply, linSmulApply, linSmulApply]
  rw [hc']
  -- push the scalars out of the two cup products and the two degree transports
  rw [wangCupH_smul_left]
  rw [wangCohEqIso_smul]
  rw [wangCupH_smul_right]
  rw [wangCohEqIso_smul]
  -- now only the module algebra over `ℤ` remains
  rw [zsmul_add, smul_smul, smul_smul, smul_smul]
  rw [wangSgn_mul_neg_one_eq' b n n' (by omega), wangSgn_mul_neg_one_eq]
  exact add_comm _ _

end

end Work.StemsB
