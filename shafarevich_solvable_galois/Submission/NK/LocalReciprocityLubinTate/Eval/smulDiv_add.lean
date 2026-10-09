/-
# The Lubin–Tate addition formula on torsion points, without the module structure

The `𝒪[F]`-action on `Λ_n` (`Eval/TorsionAction.lean`, `smulDiv`) is not obviously additive:
the missing axiom of the `𝒪[F]`-**module** structure on `Λ_n` is the distributivity law

  `(b + d) · x = b · x ⊕ d · x`

where `⊕` is the Lubin–Tate group law.  Evaluating the group law at a pair of torsion points is
what the chapter's `T_n`-based design has to make precise — and it can be done *without* any
topological completion, by using the factorisation of the group law by its second variable.

Since a formal group law satisfies `F(X,Y) = X + Y·Θ(X,Y)` with `Θ` a *unit* of the power series
ring (`FormalGroup.exists_unit_factorization`), substituting the multiplication series
`![[b],[d]]` into it and applying Milne's evaluation `evalTau` gives the addition formula

  `(b + d) · x = b · x + (d · x) · H,     H ≠ 0`,

for a fixed nonzero scalar `H ∈ F(x)`.  The factor `H ≠ 0` is what replaces the missing
module/discussion of the group law: it says that the "correction term" is *invertible*, i.e. that
`(b + d) · x = b · x` holds exactly when `d · x = 0`.

## Main results

* `NK.LocalReciprocityLubinTate.Eval.smulDiv_add_formula`;
* `NK.LocalReciprocityLubinTate.Eval.smulDiv_add_of_eq_zero`
  (the action of `d` is periodic with period the annihilator of `x`);
* `NK.LocalReciprocityLubinTate.Eval.smulDiv_one_add_eq_self_iff`
  (the stabiliser of `x` under the unit group: `(1+c)·x = x ↔ c·x = 0`).
-/
import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_ann
import Submission.NK.LocalReciprocityLubinTate.Eval.actionTau_add
import Submission.NK.LocalReciprocityLubinTate.Eval.law_factorization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped ValuativeRel
open Polynomial MvPowerSeries

namespace NK.LocalReciprocityLubinTate.Eval

set_option linter.style.haveILetI false

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **The Lubin–Tate addition formula on the torsion points `Λ_n`.**  For `x ∈ Λ_n`, a
factorisation `M.toLaw.law = X + Y·Θ` of the group law with `Θ` a unit of the power series ring,
and `b d ∈ 𝒪[F]`, there is `H ≠ 0` in `F(x)` with

  `(b + d) · x = b · x + (d · x) · H`.

The proof is presented in the module docstring: `subst` (which is algebraic, unlike `eval₂`, and
therefore available at the pair `![[b],[d]]`) turns the factorisation into
`[b+d] = [b] + [d]·(Θ ∘ ![[b],[d]])`, and the unit `Θ` stays a unit under substitution because the
substitution of a unit of the power series ring by series of zero constant term is a unit. -/
theorem smulDiv_add_formula (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q)
    (Θ : MvPowerSeries (Fin 2) (O F)) (hΘ : IsUnit Θ)
    (hlaw : (M.toLaw.law : MvPowerSeries (Fin 2) (O F)) =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 * Θ)
    {x : AlgebraicClosure F}
    (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n) (b d : O F) :
    ∃ H : AlgebraicClosure F, H ≠ 0 ∧
      smulDiv π hπ q n hq M hx (b + d)
        = smulDiv π hπ q n hq M hx b + smulDiv π hπ q n hq M hx d * H := by
  have hψb : MvPowerSeries.constantCoeff (M.action b) = 0 := constantCoeff_action π q M b
  have hψd : MvPowerSeries.constantCoeff (M.action d) = 0 := constantCoeff_action π q M d
  have hsub : MvPowerSeries.HasSubst
      (![M.action b, M.action d] : Fin 2 → MvPowerSeries (Fin 1) (O F)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> assumption)
  obtain ⟨Θ', hΘ'⟩ := hΘ
  have hsubunit : IsUnit (MvPowerSeries.subst ![M.action b, M.action d] Θ) := by
    rw [← hΘ']
    have h1 : MvPowerSeries.subst ![M.action b, M.action d]
          ((Θ' : ((MvPowerSeries (Fin 2) (O F))ˣ)) : MvPowerSeries (Fin 2) (O F)) *
        MvPowerSeries.subst ![M.action b, M.action d]
          (((Θ'⁻¹ : ((MvPowerSeries (Fin 2) (O F))ˣ)) : MvPowerSeries (Fin 2) (O F))) = 1 := by
      rw [← MvPowerSeries.subst_mul hsub, Units.mul_inv]
      show MvPowerSeries.subst ![M.action b, M.action d] (MvPowerSeries.C (1 : O F)) = 1
      rw [MvPowerSeries.subst_C, map_one]
    exact ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
  have hmain : actionTau π hπ q n hq M (b + d)
      = actionTau π hπ q n hq M b + actionTau π hπ q n hq M d *
        evalTau π hπ q n hq (MvPowerSeries.subst ![M.action b, M.action d] Θ) := by
    rw [actionTau, M.action_add b d, hlaw, MvPowerSeries.subst_add hsub,
      MvPowerSeries.subst_mul hsub, MvPowerSeries.subst_X hsub, MvPowerSeries.subst_X hsub]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      actionTau, map_add, map_mul]
  refine ⟨evMap π q n hq x hx
    (evalTau π hπ q n hq (MvPowerSeries.subst ![M.action b, M.action d] Θ)), ?_, ?_⟩
  · intro h0
    have hunit : IsUnit (evMap π q n hq x hx
        (evalTau π hπ q n hq (MvPowerSeries.subst ![M.action b, M.action d] Θ))) :=
      (hsubunit.map (evalTau π hπ q n hq)).map (evMap π q n hq x hx)
    exact hunit.ne_zero h0
  · show evMap π q n hq x hx (actionTau π hπ q n hq M (b + d)) = _
    rw [hmain, map_add, map_mul]
    rfl

/-- **The action is periodic with period the annihilator**: if `d · x = 0` then adding `d` to the
multiplier does not change the point.  This is the addition formula together with the vanishing of
`d · x`. -/
theorem smulDiv_add_of_eq_zero (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q)
    (Θ : MvPowerSeries (Fin 2) (O F)) (hΘ : IsUnit Θ)
    (hlaw : (M.toLaw.law : MvPowerSeries (Fin 2) (O F)) =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 * Θ)
    {x : AlgebraicClosure F}
    (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n) (b d : O F)
    (hd : smulDiv π hπ q n hq M hx d = 0) :
    smulDiv π hπ q n hq M hx (b + d) = smulDiv π hπ q n hq M hx b := by
  obtain ⟨H, -, hform⟩ := smulDiv_add_formula π hπ q n hq M Θ hΘ hlaw hx b d
  rw [hform, hd, zero_mul, add_zero]

/-- **The stabiliser of a torsion point under the action of the unit `1 + c`**: `(1+c) · x = x`
if and only if `c · x = 0`.  This is the addition formula plus the invertibility of the correction
factor `H ≠ 0`; it is the substitute for the missing module axioms which the fibre computation of
`Eval/smulDiv_fibre.lean` needs. -/
theorem smulDiv_one_add_eq_self_iff (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q)
    (Θ : MvPowerSeries (Fin 2) (O F)) (hΘ : IsUnit Θ)
    (hlaw : (M.toLaw.law : MvPowerSeries (Fin 2) (O F)) =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 * Θ)
    {x : AlgebraicClosure F}
    (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n) (c : O F) :
    smulDiv π hπ q n hq M hx (1 + c) = smulDiv π hπ q n hq M hx 1 ↔
      smulDiv π hπ q n hq M hx c = 0 := by
  obtain ⟨H, hH, hform⟩ := smulDiv_add_formula π hπ q n hq M Θ hΘ hlaw hx 1 c
  constructor
  · intro h
    have hzero : smulDiv π hπ q n hq M hx c * H = 0 := by
      rw [hform] at h
      exact add_left_cancel (by rw [h, add_zero])
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact h1
    · exact absurd h1 hH
  · intro h
    rw [hform, h, zero_mul, add_zero]

end NK.LocalReciprocityLubinTate.Eval
