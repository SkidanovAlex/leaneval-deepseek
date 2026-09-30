/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The degree bound for a nonzero Weil differential

A nonzero Weil differential `ω` vanishing on `K + A(D)` forces the degree of `D` to be at
most `2g - 2`: the classical bound `deg D ≤ 2g - 2` for divisors `D` with `i D ≠ 0`, proved
here without using the existence of a canonical divisor.

The proof is the counting argument of the blueprint (RR5, step 6).  Fix a place `Q` and put
`Δ_m := m • [Q]`.  For `f ∈ L(Δ_m)` the functional `f ω = ω(f · -)` vanishes on
`K + A(D + div f)`, hence, since `D - Δ_m ≤ D + div f`, on `K + A(D - Δ_m)`:

  `l(Δ_m) ≤ i(D - Δ_m)`   (`l_le_i_sub`).

Choose `m` large enough that `deg (D - Δ_m) < 0`, so that `L(D - Δ_m) = 0` and
Riemann–Roch at `D - Δ_m` computes `i(D - Δ_m) = -deg(D - Δ_m) - 1 + g`.  Riemann's
inequality at `Δ_m` gives `deg Δ_m + 1 - g ≤ l(Δ_m)`.  Combining cancels `deg Δ_m` and
yields `deg D ≤ 2g - 2`.
-/
import Mathlib
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.Duality.finrank_WD
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.RR.L_eq_bot_of_deg_neg
import Submission.Work.RiemannRoch.RR.smulW_mem_WD
import Submission.Work.RiemannRoch.RR.smulW_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.RiemannRoch.Duality

open Work.CurveBasics

/-! ## The counting step -/

/-- **Counting.**  If `ω ∈ WD C D` and `f ∈ L(Δ)`, then `f ω ∈ WD C (D - Δ)`: the functional
`f ω` vanishes on `K + A(D + div f)`, and `D - Δ ≤ D + div f` because `div f + Δ` is
effective. -/
theorem smulW_mem_WD_sub {k : Type*} [Field k] (C : Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)} {D : C.Div}
    (h : ω ∈ Work.RiemannRoch.Curve.WD C D) (Δ : C.Div) {f : C.functionField}
    (hf : f ∈ C.L Δ) :
    Work.RiemannRoch.Curve.smulW C f ω ∈ Work.RiemannRoch.Curve.WD C (D - Δ) := by
  by_cases h0 : f = 0
  · rw [h0, Work.RiemannRoch.Curve.smulW_zero_left]
    exact Submodule.zero_mem _
  · refine Work.RiemannRoch.Curve.WD_anti C ?_ (Work.RiemannRoch.RR.smulW_mem_WD C h0 h)
    rw [Finsupp.le_def]
    intro Q
    have hf' : (C.div f + Δ).IsEffective := by
      rcases (C.mem_L_iff.mp hf) with hh | hh
      · exact absurd hh h0
      · exact hh
    have hQ := hf' Q
    rw [Finsupp.add_apply] at hQ
    simp only [Finsupp.sub_apply, Finsupp.add_apply]
    linarith

/-- **The counting inequality.**  Multiplication `f ↦ f ω` is an injective `k`-linear map
`L(Δ) → WD (D - Δ)`, whence `l Δ ≤ i (D - Δ)`. -/
theorem l_le_i_sub {k : Type*} [Field k] (C : Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)} (hω : ω ≠ 0) {D : C.Div}
    (h : ω ∈ Work.RiemannRoch.Curve.WD C D) (Δ : C.Div) :
    C.l Δ ≤ Work.RiemannRoch.Curve.i C (D - Δ) := by
  have hmem : ∀ f : ↥(C.L Δ),
      Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω ∈
        Work.RiemannRoch.Curve.WD C (D - Δ) :=
    fun f => smulW_mem_WD_sub C h Δ f.2
  let φ : ↥(C.L Δ) →ₗ[k] ↥(Work.RiemannRoch.Curve.WD C (D - Δ)) :=
  { toFun := fun f => ⟨Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω, hmem f⟩
    map_add' := by
      intro f g
      simp only [Submodule.coe_add, Work.RiemannRoch.Curve.smulW_add]
      rfl
    map_smul' := by
      intro c f
      simp only [Submodule.coe_smul, Work.RiemannRoch.Curve.smulW_smul_k, RingHom.id_apply]
      rfl }
  have hφ : ∀ f : ↥(C.L Δ),
      ((φ f : ↥(Work.RiemannRoch.Curve.WD C (D - Δ))) :
        Module.Dual k (Work.RiemannRoch.Curve.Adeles C)) =
      Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω := fun f => rfl
  have hinj : Function.Injective φ := by
    intro f g hfg
    have h1 : Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω
        = Work.RiemannRoch.Curve.smulW C (g : C.functionField) ω := by
      rw [← hφ f, ← hφ g, hfg]
    refine Subtype.ext (sub_eq_zero.mp ?_)
    by_cases hfg0 : (f : C.functionField) - g = 0
    · exact hfg0
    · have h2 : Work.RiemannRoch.Curve.smulWLin C ω ((f : C.functionField) - g) = 0 := by
        rw [map_sub, Work.RiemannRoch.Curve.smulWLin_apply,
          Work.RiemannRoch.Curve.smulWLin_apply, h1, sub_self]
      have h3 : Work.RiemannRoch.Curve.smulW C ((f : C.functionField) - g) ω = 0 := by
        rwa [Work.RiemannRoch.Curve.smulWLin_apply] at h2
      exact absurd ((Work.RiemannRoch.RR.smulW_eq_zero_iff C hfg0 ω).mp h3) hω
  haveI : Module.Finite k ↥(Work.RiemannRoch.Curve.WD C (D - Δ)) :=
    Module.Finite.of_surjective
      (Work.RiemannRoch.Curve.WDequiv C (D - Δ)).toLinearMap
      (Work.RiemannRoch.Curve.WDequiv C (D - Δ)).surjective
  have hle : Module.finrank k ↥(C.L Δ) ≤
      Module.finrank k ↥(Work.RiemannRoch.Curve.WD C (D - Δ)) :=
    LinearMap.finrank_le_finrank_of_injective (f := φ) hinj
  rw [Work.CurveBasics.Curve.l, ← Work.RiemannRoch.Duality.finrank_WD C (D - Δ)]
  exact hle

/-! ## The degree bound -/

theorem deg_le_of_mem_WD {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)} (hω : ω ≠ 0)
    {D : C.Div} (h : ω ∈ Work.RiemannRoch.Curve.WD C D) :
    C.deg D ≤ 2 * (Work.RiemannRoch.Curve.genus C : ℤ) - 2 := by
  obtain ⟨Q⟩ := Work.RiemannRoch.Curve.nonempty_place C
  have hQpos : (1 : ℤ) ≤ (Q.degree : ℤ) := by
    have h : 0 < Q.degree := Work.CurveBasics.Place.residueDegree_pos Q
    have h1 : 1 ≤ Q.degree := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
    exact_mod_cast h1
  obtain ⟨m, hm⟩ := exists_nat_gt (C.deg D)
  set Δ : C.Div := m • Work.CurveBasics.Curve.Div.place Q with hΔ
  have hdegΔ : C.deg Δ = (m : ℤ) * (Q.degree : ℤ) := by
    rw [hΔ, Work.CurveBasics.Curve.deg_nsmul, Work.CurveBasics.Curve.deg_place]
    simp
  have hlt : C.deg (D - Δ) < 0 := by
    rw [Work.CurveBasics.Curve.deg_sub, hdegΔ]
    have hmul : (m : ℤ) ≤ (m : ℤ) * (Q.degree : ℤ) := by
      have h2 := mul_le_mul_of_nonneg_left hQpos (Int.natCast_nonneg m)
      simpa using h2
    linarith
  have hl : C.l (D - Δ) = 0 := by
    rw [Work.CurveBasics.Curve.l, Work.RiemannRoch.RR.L_eq_bot_of_deg_neg C hlt, finrank_bot]
  have hcount : (C.l Δ : ℤ) ≤ (Work.RiemannRoch.Curve.i C (D - Δ) : ℤ) := by
    exact_mod_cast l_le_i_sub C hω h Δ
  have hRI := Work.RiemannRoch.Curve.riemann_inequality C Δ
  have hRR := Work.RiemannRoch.Curve.riemannRoch C (D - Δ)
  rw [hl] at hRR
  push_cast at hRR
  have hI : (Work.RiemannRoch.Curve.i C (D - Δ) : ℤ)
      = -(C.deg (D - Δ)) - 1 + (Work.RiemannRoch.Curve.genus C : ℤ) := by linarith
  have hdegsub : C.deg (D - Δ) = C.deg D - C.deg Δ :=
    Work.CurveBasics.Curve.deg_sub C D Δ
  linarith

end Work.RiemannRoch.Duality
