/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The kernel of the invariant derivation is the `p`-th powers

Let `E` be an elliptic curve over a field `N` that is algebraically closed of characteristic `p`, and
let `D` be the derivation of the function field `N(E)` attached to the invariant differential
(`D x = 2y + a₁x + a₃`, `D y = 3x² + 2a₂x + a₄ - a₁y`).  This file proves that every element of
`N(E)` killed by `D` is a `p`-th power.

The proof splits into three cases according to the characteristic and the form of `E`:

* `Work.MotV.ker_deriv_eq_pthPow`: the abstract statement — over a field of characteristic `p` in
  which `γ ^ p ∈ K ^ p` generates everything, `ker D ⊆ K ^ p`;
* `Work.MotV.genY_mem_subfield_of_two_ne_zero`: in characteristic `≠ 2`, completing the square
  exhibits `y` as a rational expression in `x` over the `p`-th powers;
* `Work.MotV.genY_mem_subfield_of_two_eq_zero`: in characteristic `2` with `a₁x + a₃ ≠ 0`, the
  Weierstrass relation solves for `y`;
* `Work.MotV.genX_mem_PthPow_of_two_eq_zero`: in characteristic `2` with `a₁ = a₃ = 0`, the
  coordinate `x` is itself a square.
-/

import Mathlib
import Submission.Work.MotV.PthPowDefs
import Submission.Work.MotV.ker_deriv_eq_pthPow
import Submission.Work.MotV.genY_mem_subfield_of_two_ne_zero
import Submission.Work.MotV.genY_mem_subfield_of_two_eq_zero
import Submission.Work.MotV.genX_mem_PthPow_of_two_eq_zero
import Submission.Work.MotV.two_mul_genY_add_ne_zero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {N : Type*} [Field N]

/-! ## Elementary consequences of transcendence of the coordinate `x` -/

/-- `x² + a₄` does not vanish: otherwise `x` would be algebraic over the constants. -/
theorem genX_sq_add_a4_ne_zero (E : WeierstrassCurve N) :
    (Work.MotC2.genX E) ^ 2 + algebraMap N (Work.MotC2.Func E) E.a₄ ≠ 0 := by
  intro h
  have h' : Polynomial.aeval (Work.MotC2.genX E)
      (Polynomial.X ^ 2 + Polynomial.C E.a₄) = 0 := by
    rw [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, h]
  have hzero := (transcendental_iff.mp (Work.MotC2.transcendental_genX E)) _ h'
  have hc : (Polynomial.X ^ 2 + Polynomial.C E.a₄ : Polynomial N).coeff 2 = 1 := by
    simp
  rw [hzero] at hc
  simp at hc

/-- If `a₁x + a₃ = 0` then `a₁ = 0`, since `x` is transcendental. -/
theorem a₁_eq_zero_of_smul_add_eq_zero (E : WeierstrassCurve N)
    (he : algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₃ = 0) : E.a₁ = 0 := by
  by_contra ha₁
  have ha1' : algebraMap N (Work.MotC2.Func E) E.a₁ ≠ 0 := fun hz =>
    ha₁ (FaithfulSMul.algebraMap_injective N (Work.MotC2.Func E) (by rw [hz, map_zero]))
  have h : algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E =
      -algebraMap N (Work.MotC2.Func E) E.a₃ := by
    rw [add_eq_zero_iff_eq_neg] at he; exact he
  have hx : Work.MotC2.genX E = algebraMap N (Work.MotC2.Func E) (-(E.a₃) / E.a₁) := by
    have hkey : algebraMap N (Work.MotC2.Func E) E.a₁ *
        algebraMap N (Work.MotC2.Func E) (-(E.a₃) / E.a₁) =
        -algebraMap N (Work.MotC2.Func E) E.a₃ := by
      rw [← map_mul, ← map_neg]
      congr 1
      field_simp
    exact (mul_left_cancel₀ ha1' (hkey.trans h.symm)).symm
  refine (Work.MotC2.transcendental_genX E) ⟨Polynomial.X - Polynomial.C (-(E.a₃) / E.a₁),
    (Polynomial.monic_X_sub_C _).ne_zero, ?_⟩
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, ← hx, sub_self]

/-- If `a₁ = 0` and `a₁x + a₃ = 0` then `a₃ = 0`. -/
theorem a₃_eq_zero_of_smul_add_eq_zero (E : WeierstrassCurve N) (h₁ : E.a₁ = 0)
    (he : algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₃ = 0) : E.a₃ = 0 := by
  rw [h₁, map_zero, zero_mul, zero_add] at he
  exact FaithfulSMul.algebraMap_injective N (Work.MotC2.Func E) (by rw [he, map_zero])

/-! ## The two explicit forms of the derivation in characteristic two -/

section CharTwo

variable (E : WeierstrassCurve N)

/-- In characteristic two the element `2` of the function field vanishes. -/
theorem two_eq_zero_funcField (h2 : (2 : N) = 0) : (2 : Work.MotC2.Func E) = 0 := by
  have h : algebraMap N (Work.MotC2.Func E) ((2 : ℕ) : N) = 0 := by
    rw [show ((2 : ℕ) : N) = (2 : N) from rfl, h2, map_zero]
  rw [map_natCast] at h
  exact h

/-- In characteristic two, `D x = a₁x + a₃`. -/
theorem deriv_genX_charTwo (h2K : (2 : Work.MotC2.Func E) = 0)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hDx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃) :
    D (Work.MotC2.genX E) = algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₃ := by
  rw [hDx, h2K, zero_mul, zero_add]

/-- In characteristic two with `a₁ = 0`, `D y = x² + a₄`. -/
theorem deriv_genY_charTwo (h2K : (2 : Work.MotC2.Func E) = 0) (h₁ : E.a₁ = 0)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hDy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) :
    D (Work.MotC2.genY E) = (Work.MotC2.genX E) ^ 2 +
      algebraMap N (Work.MotC2.Func E) E.a₄ := by
  have h3K : (3 : Work.MotC2.Func E) = 1 := by
    have h31 : (3 : Work.MotC2.Func E) = (2 : Work.MotC2.Func E) + 1 := by norm_num
    rw [h31, h2K, zero_add]
  rw [hDy, h3K, h2K, h₁, map_zero]
  first | refl_ring1 | ring

end CharTwo

/-! ## The main theorem -/

/-- The subfield `N(E)^p(γ)` has carrier `N(E)^p[γ]`, so an equality of subfields is an equality of
the corresponding subalgebras. -/
theorem adjoin_eq_top_of_KpAdjoin_eq_top {N : Type*} [Field N] (E : WeierstrassCurve N)
    (p : ℕ) [Fact p.Prime] [CharP N p] (γ : Work.MotC2.Func E)
    (h : KpAdjoin p E γ = ⊤) :
    Algebra.adjoin (PthPow (Work.MotC2.Func E) p) {γ} = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : z ∈ KpAdjoin p E γ := by rw [h]; trivial
  exact hz

theorem derivZeroPow {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N)
    [E.IsElliptic]
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hDx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hDy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E)
    (p : ℕ) [Fact p.Prime] [CharP N p] :
    ∀ f : Work.MotC2.Func E, D f = 0 → ∃ s : Work.MotC2.Func E, s ^ p = f := by
  rcases eq_or_ne (2 : N) 0 with h2 | h2
  · -- characteristic two
    have h2K : (2 : Work.MotC2.Func E) = 0 := two_eq_zero_funcField E h2
    by_cases he : algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃ = 0
    · -- supersingular shape `a₁ = a₃ = 0`: use `γ = y`
      have h1 : E.a₁ = 0 := a₁_eq_zero_of_smul_add_eq_zero E he
      have h3 : E.a₃ = 0 := a₃_eq_zero_of_smul_add_eq_zero E h1 he
      have hxmem : Work.MotC2.genX E ∈ PthPow (Work.MotC2.Func E) p :=
        genX_mem_PthPow_of_two_eq_zero E p h2 h1 h3
      have htop : Algebra.adjoin (PthPow (Work.MotC2.Func E) p)
          {Work.MotC2.genY E} = ⊤ := by
        refine adjoin_eq_top_of_KpAdjoin_eq_top E p (MotC2.genY E) ?_
        exact eq_top_of_mem_genX_genY E _
          (fun c => mem_KpAdjoin_of_mem_PthPow (p := p) (E := E) _ (algebraMap_mem_PthPow p E c))
          (mem_KpAdjoin_of_mem_PthPow (p := p) (E := E) _ hxmem) (mem_KpAdjoin_self (p := p) (E := E) _)
      have hDy' : D (Work.MotC2.genY E) ≠ 0 := by
        rw [deriv_genY_charTwo E h2K h1 D hDy]
        exact genX_sq_add_a4_ne_zero E
      exact ker_deriv_eq_pthPow (Work.MotC2.genY E) D hDy' htop
    · -- `a₁x + a₃ ≠ 0`: use `γ = x`
      have hDx' : D (Work.MotC2.genX E) ≠ 0 := by
        rw [deriv_genX_charTwo E h2K D hDx]
        exact he
      have htop : Algebra.adjoin (PthPow (Work.MotC2.Func E) p)
          {Work.MotC2.genX E} = ⊤ := by
        refine adjoin_eq_top_of_KpAdjoin_eq_top E p (MotC2.genX E) ?_
        exact eq_top_of_mem_genX_genY E _
          (fun c => mem_KpAdjoin_of_mem_PthPow (p := p) (E := E) _ (algebraMap_mem_PthPow p E c))
          (mem_KpAdjoin_self (p := p) (E := E) _)
          (genY_mem_subfield_of_two_eq_zero E p h2 he _
            (fun z hz => mem_KpAdjoin_of_mem_PthPow (p := p) (E := E) _ hz) (mem_KpAdjoin_self (p := p) (E := E) _))
      exact ker_deriv_eq_pthPow (Work.MotC2.genX E) D hDx' htop
  · -- characteristic different from two
    have hw : 2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ *
        Work.MotC2.genX E + algebraMap N (Work.MotC2.Func E) E.a₃ ≠ 0 :=
      two_mul_genY_add_ne_zero E h2
    have hDx' : D (Work.MotC2.genX E) ≠ 0 := by rw [hDx]; exact hw
    have htop : Algebra.adjoin (PthPow (Work.MotC2.Func E) p) {Work.MotC2.genX E} = ⊤ := by
      refine adjoin_eq_top_of_KpAdjoin_eq_top E p (MotC2.genX E) ?_
      exact eq_top_of_mem_genX_genY E _
        (fun c => mem_KpAdjoin_of_mem_PthPow (p := p) (E := E) _ (algebraMap_mem_PthPow p E c))
        (mem_KpAdjoin_self (p := p) (E := E) _)
        (genY_mem_subfield_of_two_ne_zero E p h2 _
          (fun z hz => mem_KpAdjoin_of_mem_PthPow (p := p) (E := E) _ hz) (mem_KpAdjoin_self (p := p) (E := E) _))
    exact ker_deriv_eq_pthPow (Work.MotC2.genX E) D hDx' htop

end Work.MotV
