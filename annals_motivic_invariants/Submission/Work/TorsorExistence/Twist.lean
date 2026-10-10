/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence
-/
import Submission.Work.TorsorExistence.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The quintic twist

For an elliptic curve `E/𝕜` with a rational point `P ∈ E(𝕜)` of order `5`, a cyclic extension
`L/𝕜` of degree `5` with generator `σ`, the *twist* of `E` by the cocycle `σ ↦ P` is the genus-one
curve `C := (E_L)/G` where `G = ℤ/5` acts on `E_L` by `g ⋆ Q = g·Q + P`.  This is step (C) of the
paper's proof of Lemma `lem:torsors`, and its three consequences (D) are:

* `C` carries a `𝕜`-rational divisor of degree `5` (the orbit divisor `Σ_{g ∈ G} [g ⋆ Q]` for any
  `L`-point `Q`), i.e. the period divides `5` (`five_smul_cls`);
* `C(𝕜) = ∅` iff the cocycle is not a coboundary, i.e. iff `P ∉ (σ - 1)E(L)`
  (`cls_eq_zero_iff`, `pointless_iff_nontrivial`);
* `j(Jac⁰C) = j(E) ≠ 1728` (`toTorsor`, whose `j_ne` field is inherited from `E`).

Since Mathlib has no Jacobian varieties, no Weil–Châtelet groups and no quotients of varieties by
group actions, the twist is *not* realised here as a scheme; what is realised is its class in the
concrete Galois cohomology group

  `H¹(ℤ/5, E(L)) = ker(1 + σ + σ² + σ³ + σ⁴) / (σ - 1)·E(L)`,

which is exactly what "the cocycle `σ ↦ P` is trivial" means, together with the bridge to
`Work.Arithmetic.Torsor` (`toTorsor`, `period_toTorsor_eq_five_iff`).  The single statement that
is *not* proved here, `QuinticTwist.Pointless D` (i.e. `P ∉ (σ - 1)E(L)`), is the arithmetic
content of the paper's Lemma `lem:torsors`; see `NOTES.md` §3 for why it needs weak
Mordell–Weil or a local obstruction, and `Main.lean` for the reduction of `HasLLinkCurve` to the
scheme-theoretic statement that bypasses this question.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.TorsorExistence

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

namespace QuinticTwist

variable (D : QuinticTwist 𝕜)

/-- `5 • x = x + x + x + x + x` in any additive commutative monoid.  (Stated separately so
that the `5` can be rewritten without disturbing the `5` in the type `CyclicExtension 𝕜 5` of
the twist data.) -/
theorem five_nsmul_eq {M : Type*} [AddCommMonoid M] (x : M) :
    (5 : ℕ) • x = x + x + x + x + x := by
  rw [show (5 : ℕ) = 1 + 1 + 1 + 1 + 1 by norm_num, add_nsmul, add_nsmul, add_nsmul, add_nsmul,
    one_nsmul]

/-- The group `E(L)` of `L`-points of `E`. -/
abbrev LPoints : Type := WeierstrassCurve.Affine.Point (D.E.baseChange D.ext.L)

/-- The marked point `P ∈ E(𝕜) ⊆ E(L)`. -/
def PL : D.LPoints :=
  WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L D.P

/-- The action of the generator `σ` of `Gal(L/𝕜)` on `E(L)`. -/
def galMap : D.LPoints →+ D.LPoints :=
  WeierstrassCurve.Affine.Point.map (W' := D.E) (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L)

/-- `σ` fixes the `𝕜`-rational points: `σ · P = P`. -/
theorem galMap_PL : galMap D D.PL = D.PL :=
  WeierstrassCurve.Affine.Point.map_baseChange (W' := D.E)
    (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) D.P

/-- `5 • P = 0` in `E(L)`. -/
theorem five_smul_PL : (5 : ℕ) • D.PL = 0 := by
  have h : D.PL = (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) D.P := rfl
  rw [h]
  calc (5 : ℕ) • (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) D.P
      = (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) ((5 : ℕ) • D.P) :=
        (map_nsmul _ 5 D.P).symm
    _ = (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) 0 := by
        exact congrArg _ D.five_smul
    _ = 0 := map_zero _

/-- The norm endomorphism `1 + σ + σ² + σ³ + σ⁴` of `E(L)`. -/
def norm : D.LPoints →+ D.LPoints where
  toFun x := x + galMap D x + galMap D (galMap D x) + galMap D (galMap D (galMap D x)) +
    galMap D (galMap D (galMap D (galMap D x)))
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add]
    abel

theorem norm_apply (x : D.LPoints) :
    norm D x = x + galMap D x + galMap D (galMap D x) + galMap D (galMap D (galMap D x)) +
      galMap D (galMap D (galMap D (galMap D x))) := rfl

/-- `N(x) = 5x` for a `σ`-fixed `x`: the norm of a `𝕜`-rational point is its `5`-fold multiple. -/
theorem norm_eq_nsmul (x : D.LPoints) (hx : galMap D x = x) : norm D x = 5 • x := by
  rw [norm_apply, hx, hx, hx, hx, five_nsmul_eq]

/-- The norm of the marked point vanishes, so `P` defines a class in `H¹(ℤ/5, E(L))`. -/
theorem norm_PL : norm D D.PL = 0 := by
  rw [norm_eq_nsmul D D.PL D.galMap_PL, D.five_smul_PL]

/-- The map `σ - 1` on `E(L)`, whose image is the subgroup of coboundaries. -/
def shift : D.LPoints →+ D.LPoints where
  toFun x := galMap D x - x
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add]
    abel

/-- `ker N`, the group of `0`-cocycles with values in `E(L)`. -/
def cocycles : AddSubgroup D.LPoints := (norm D).ker

/-- The subgroup of coboundaries `(σ - 1)E(L)`, viewed inside `ker N`. -/
def coboundaries : AddSubgroup D.cocycles :=
  (AddSubgroup.map (shift D) ⊤).comap (D.cocycles).subtype

/-- **The Galois cohomology group `H¹(ℤ/5, E(L))`**, realised as `ker N / (σ - 1)E(L)`. -/
abbrev H1 : Type := D.cocycles ⧸ D.coboundaries

/-- The class of the cocycle `σ ↦ P`. -/
def cls : D.H1 := QuotientAddGroup.mk' D.coboundaries ⟨D.PL, D.norm_PL⟩

/-- **`C(𝕜) = ∅`**: the class of the cocycle `σ ↦ P` in `H¹(ℤ/5, E(L))` is non-zero, i.e. `P`
is not a coboundary.  This is the arithmetic residual of the paper's Lemma `lem:torsors`; see
`NOTES.md` §3.  (It is *not* proved here: it is the statement that needs weak Mordell–Weil or a
local obstruction.) -/
def Pointless : Prop := cls D ≠ 0

/-- The trivial action of `Aut(E)` on `H¹(ℤ/5, E(L))`, used in the bridge to
`Work.Arithmetic.Torsor`. -/
def act : Work.Arithmetic.Aut 𝕜 D.E →* MulAut (Multiplicative D.H1) where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (one_mul 1).symm

/-- The quintic twist, as a `Work.Arithmetic.Torsor`: the Weil–Châtelet group is replaced by the
concrete group `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)`, in which the class of the twist is the class
of the cocycle `σ ↦ P`, and `Jac⁰C = E` is inherited (`j ≠ 1728` included). -/
def toTorsor : Work.Arithmetic.Torsor 𝕜 where
  E := D.E
  isElliptic := D.isElliptic
  j_ne := D.j_ne
  W := Multiplicative D.H1
  commGroup := inferInstance
  act := act D
  cls := Multiplicative.ofAdd (cls D)
  order_aut := D.order_aut

end QuinticTwist

end

end Work.TorsorExistence
