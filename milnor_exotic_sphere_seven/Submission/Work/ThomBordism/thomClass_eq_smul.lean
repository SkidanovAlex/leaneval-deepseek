import Mathlib
import Submission.Work.ThomBordism.gaussTubeData
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.Oriented

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Thom classes of a bundle over a path connected base are unique up to sign

`Work.Thom.ThomClass Z n` is the workspace's model of "an oriented rank-`n` real bundle with its
Thom isomorphism": a class `τ ∈ H^n(E,E∖0;ℤ)` for which cupping with `τ` is an isomorphism in every
degree.  Two orientations of the same bundle differ by a sign, so the classes themselves should
differ only by a sign.  This module proves that:

* `Work.ThomBordism.thomClass_eq_smul_of_joined` — for a real bundle `Z → B` over a **path
  connected** non-empty base, any two Thom classes `U U'` of `Z` in the degree `n` satisfy
  `U.τ = s • U'.τ` with `s = ±1`;
* `Work.ThomBordism.thomClass_eq_smul` — the special case of the tautological rank-`k` bundle
  `γ_{k,10}` over `G̃r_k(ℝ^{k+10})`, whose base is path connected
  (`Work.ThomBordism.Grassmann.deg8PathConnectedOG`).  This is "step (i)" of the tie/polarity
  analysis of the Gauss data: it says that the choice of Thom class of `γ_{k,10}` affects the
  local-degree sign of the canonical Gauss candidate only by a global factor `±1`.

## The argument

Write `T_τ : H⁰(B;ℤ) → H^n(E,E∖0;ℤ)` for the degree-zero Thom map `x ↦ π^*(x) ⌣ τ`.  For a Thom
class it is bijective, and for *any* class `τ` it is computed by the unit law of the relative
cohomology: the class `1 ∈ H⁰(B;ℤ)` acts by the identity, `π^*(1) = 1`, so
`T_τ 1 = τ` (`Work.Thom.mixedCupC_oneH_zero` along `CohMap_oneH`).

Since `T_{U'}` is bijective, `U.τ = T_{U'} x` for some `x ∈ H⁰(B;ℤ)`, and since `B` is path
connected, `x` is a multiple of the unit class: `x = s • 1` with `s = ptEv p x`
(`Work.Thom.ptEv_ext` and the constancy of degree-zero evaluations along paths,
`Work.Thom.ptEv_eq_of_joined`).  Hence `U.τ = s • U'.τ`; the same argument with `U` and `U'`
interchanged gives `U'.τ = t • U.τ`, with `t = ptEv p y`.

Substituting, `U.τ = (s*t) • U.τ`.  Applying the *bijective* map `T_U` to both sides turns this
back into an equation in `H⁰(B;ℤ)`: `(s*t) • 1 = 1 • 1` (the scalar multiple of `1` is `T_U 1`
because `T_U` is `ℤ`-linear).  Evaluating at the point `p` (`Work.Thom.ptEv_smul`,
`Work.Thom.ptEv_one`) gives `s*t = 1`, so `s = ±1` by `Int.eq_one_or_neg_one_of_mul_eq_one`.

The only bookkeeping is the degree cast `OpenThom Z (0+n) = OpenThom Z n` (the Thom map in degree
zero lands in degree `0+n`), handled by `smul_eq_of_cast_eq_cast` and the hypothesis
`Work.Thom.mixedCupC_oneH_zero`, which itself carries the cast `Nat.zero_add n`.
-/

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

/-- **Cancelling the degree cast in a scalar multiple.**  If `x` transported along `h : b = a`
equals `m` times the transport of `y`, then `x = m • y` (the statement is phrased so that the
proof is `cases h`). -/
private theorem smul_eq_of_cast_eq_cast {M : ℕ → ModuleCat ℤ} {a b : ℕ} (h : b = a) (m : ℤ)
    {x y : M b} (hxy : h ▸ x = m • (h ▸ y)) : x = m • y := by
  cases h
  exact hxy

/-- **Any two Thom classes of a real bundle over a path connected base differ by a sign.**

`Z → B` a real bundle with model fibre `F`, `B` non-empty and path connected, and
`U U' : ThomClass Z n` two Thom classes in the same degree `n`.  Then `U.τ = s • U'.τ` with
`s = 1` or `s = -1`.

(The path connectedness is what makes `H⁰(B;ℤ) = ℤ·1`: on a disconnected base the statement is
false, since one may rescale the Thom class independently on each component.) -/
theorem thomClass_eq_smul_of_joined {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n : ℕ)
    [Nonempty B] (hconn : ∀ b b' : B, Joined b b') :
    ∀ U U' : Work.Thom.ThomClass Z n,
      ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ U.τ = s • U'.τ := by
  classical
  intro U U'
  obtain ⟨p⟩ := (inferInstance : Nonempty B)
  -- the unit law of the degree-zero Thom map: `T_τ 1 = τ`
  have hone : ∀ (τ : Work.Thom.OpenThom Z n),
      Work.Thom.thomMap Z n τ 0 (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)))
        = (Nat.zero_add n).symm ▸ τ := by
    intro τ
    rw [Work.Thom.thomMap_apply, Work.Thom.CohMap_oneH, Work.Thom.mixedCupC_oneH_zero]
  -- step 1: the preimage of `U.τ` under the Thom map of `U'`
  obtain ⟨x, hx⟩ := (U'.isThom 0).2 ((Nat.zero_add n).symm ▸ U.τ)
  have hxsmul : x = (Work.Thom.ptEv p x) •
      Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)) := by
    refine Work.Thom.ptEv_ext (fun q => ?_)
    rw [Work.Thom.ptEv_smul, Work.Thom.ptEv_one, mul_one]
    exact Work.Thom.ptEv_eq_of_joined (hconn q p) x
  have hW : (Nat.zero_add n).symm ▸ U.τ
      = (Work.Thom.ptEv p x) • ((Nat.zero_add n).symm ▸ U'.τ) := by
    rw [← hx]
    conv_lhs => rw [hxsmul]
    rw [map_zsmul, hone U'.τ]
  -- step 2: the same with the roles of `U` and `U'` interchanged
  obtain ⟨y, hy⟩ := (U.isThom 0).2 ((Nat.zero_add n).symm ▸ U'.τ)
  have hysmul : y = (Work.Thom.ptEv p y) •
      Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)) := by
    refine Work.Thom.ptEv_ext (fun q => ?_)
    rw [Work.Thom.ptEv_smul, Work.Thom.ptEv_one, mul_one]
    exact Work.Thom.ptEv_eq_of_joined (hconn q p) y
  have hW' : (Nat.zero_add n).symm ▸ U'.τ
      = (Work.Thom.ptEv p y) • ((Nat.zero_add n).symm ▸ U.τ) := by
    rw [← hy]
    conv_lhs => rw [hysmul]
    rw [map_zsmul, hone U.τ]
  -- hence `(s*t) • U.τ = U.τ`
  have hml : ((Work.Thom.ptEv p x) * (Work.Thom.ptEv p y)) •
      ((Nat.zero_add n).symm ▸ U.τ) = (Nat.zero_add n).symm ▸ U.τ := by
    rw [mul_smul, ← hW', hW]
  -- and, applying the bijective map `T_U`, the same equation in `H⁰(B;ℤ)`
  have hmul : ((Work.Thom.ptEv p x) * (Work.Thom.ptEv p y)) •
        (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)))
      = (1 : ℤ) • (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B))) := by
    refine (U.isThom 0).1 ?_
    rw [map_zsmul, map_zsmul, hone U.τ, one_smul]
    exact hml
  -- evaluate at the point `p`
  have hst : (Work.Thom.ptEv p x) * (Work.Thom.ptEv p y) = 1 := by
    have h1 := congrArg (Work.Thom.ptEv p) hmul
    rw [Work.Thom.ptEv_smul, Work.Thom.ptEv_one, mul_one, Work.Thom.ptEv_smul,
      Work.Thom.ptEv_one, mul_one] at h1
    exact h1
  refine ⟨Work.Thom.ptEv p x, Int.eq_one_or_neg_one_of_mul_eq_one hst, ?_⟩
  exact smul_eq_of_cast_eq_cast (M := fun i => Work.Thom.OpenThom Z i) (Nat.zero_add n).symm
    (Work.Thom.ptEv p x) hW

/-- **Thom classes of the tautological oriented bundle `γ_{k,10}` are unique up to sign.**

The oriented Grassmannian `G̃r_k(ℝ^{k+10})` is path connected
(`Work.ThomBordism.Grassmann.deg8PathConnectedOG` at `m = 10`), so
`thomClass_eq_smul_of_joined` applies to the tautological rank-`k` bundle. -/
theorem thomClass_eq_smul (k : ℕ)
    (U U' : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ U.τ = s • U'.τ := by
  haveI : PathConnectedSpace (Grassmann.OG k 10) :=
    Grassmann.deg8PathConnectedOG k 10 (by norm_num)
  exact thomClass_eq_smul_of_joined (Grassmann.tautologicalBundle k 10) k
    (fun b b' => PathConnectedSpace.joined b b') U U'

end

end Work.ThomBordism
