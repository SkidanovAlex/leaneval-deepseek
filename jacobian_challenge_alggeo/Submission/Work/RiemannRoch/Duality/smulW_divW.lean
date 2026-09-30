/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplication of a Weil differential by a rational function

`smulW C f ω` is the Weil differential `(f ω)(a) = ω (f a)`.  This file proves that its divisor
is `div ω + div f` (`smulW_divW`), the compatibility of `divW` with the `K`-module structure of
`Ω = Omega C` (Serre, *Algebraic Groups and Class Fields*, II §8).

The proof is self-contained: it establishes, for a nonzero `ω ∈ Ω`,

* `deg_mono_aux` — the degree of divisors is monotone for the pointwise order;
* `l_le_i_aux` — `l (D - E) ≤ i E` whenever `0 ≠ ω ∈ WD C D` (the counting lemma of
  `Duality/sum_l_le_finrank_WD` for a single differential; the map `L (D - E) → WD C E`,
  `f ↦ f ω` is injective since a nonzero differential times a nonzero function is nonzero);
* `deg_le_aux` — `deg D ≤ 2 g - 2` whenever `0 ≠ ω ∈ WD C D` (with `E = D` the previous bound
  gives `l D ≤ i 0 = g`, while Riemann–Roch and `1 ≤ i D` give `l D ≥ deg D + 2 - g`);
* `exists_isDivW_aux` — the divisor of `ω` exists: the divisors carrying `ω` are nonempty, closed
  under `⊔` and bounded in degree, so an element of maximal degree is largest.

Then `divW C ω + div f` is shown to be the largest divisor carrying `f ω`, by transporting
membership in `WD` along multiplication by `f` and by `f⁻¹`.
-/
import Mathlib
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.Duality.finrank_WD
import Submission.Work.RiemannRoch.Duality.sum_l_le_finrank_WD
import Submission.Work.RiemannRoch.RR.smulW_mem_WD
import Submission.Work.RiemannRoch.RR.smulW_eq_zero_iff
import Submission.Work.RiemannRoch.RR.mem_WD_sup
import Submission.Work.CurveBasics.Order.div_inv
import Submission.Work.CurveBasics.Divisor.deg_nonneg
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.RiemannRoch.Duality

open Work.RiemannRoch.Curve

variable {k : Type*} [Field k]

/-! ## The degree is monotone for the pointwise order on divisors -/

private theorem deg_mono_aux (C : Work.CurveBasics.Curve k) {D E : C.Div} (h : D ≤ E) :
    C.deg D ≤ C.deg E := by
  have hEff : Work.CurveBasics.Curve.Div.IsEffective (E - D) := fun Q => by
    have hQ : D Q ≤ E Q := (Finsupp.le_def.mp h) Q
    rw [Finsupp.sub_apply]
    exact sub_nonneg.mpr hQ
  have h0 := Work.CurveBasics.Divisor.deg_nonneg (C := C) hEff
  rw [Work.CurveBasics.Curve.deg_sub] at h0
  linarith

/-! ## The dimension bound `l (D - E) ≤ i E`

A nonzero `ω ∈ WD C D` restricts along `L (D - E) → WD C E`, `f ↦ f ω`, which is injective
because multiplying a nonzero differential by a nonzero function keeps it nonzero.  -/

/-- For `0 ≠ ω ∈ WD C D` the multiplication map `L (D - E) → WD C E` is injective, so
`l (D - E) ≤ i E`. -/
private theorem l_le_i_aux (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Adeles C)} (hω0 : ω ≠ 0) {D : C.Div} (hD : ω ∈ WD C D)
    (E : C.Div) : C.l (D - E) ≤ i C E := by
  haveI : FiniteDimensional k ↥(WD C E) := Module.Finite.equiv (WDequiv C E)
  let φ : ↥(C.L (D - E)) →ₗ[k] ↥(WD C E) :=
    { toFun := fun f => ⟨smulW C (f : C.functionField) ω, smulW_mem_WD_of_mem_L C f.2 hD⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp only [Submodule.coe_add, smulW_add]
      map_smul' := fun c f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, smulW_smul_k, RingHom.id_apply] }
  have hφ : ∀ f : ↥(C.L (D - E)), (φ f : Module.Dual k (Adeles C))
      = smulW C (f : C.functionField) ω := fun f => rfl
  have hker : ∀ f : ↥(C.L (D - E)), φ f = 0 → f = 0 := by
    intro f hf
    have h := congrArg (fun x : ↥(WD C E) => (x : Module.Dual k (Adeles C))) hf
    simp only [hφ f, ZeroMemClass.coe_zero] at h
    by_contra hf0
    exact absurd h (smulW_ne_zero C (fun hh => hf0 (Subtype.ext hh)) hω0)
  have hinj : Function.Injective φ := by
    intro f g hfg
    have hz : φ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hker (f - g) hz)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_WD] at hle
  simpa [Work.CurveBasics.Curve.l, Work.RiemannRoch.Curve.i] using hle

/-- A divisor carrying a nonzero Weil differential has degree at most `2 g - 2`. -/
private theorem deg_le_aux (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Adeles C)} (hω0 : ω ≠ 0) {D : C.Div} (hD : ω ∈ WD C D) :
    C.deg D ≤ 2 * (genus C : ℤ) - 2 := by
  have hl : (C.l D : ℤ) ≤ (genus C : ℤ) := by
    have h1 := l_le_i_aux C hω0 hD (0 : C.Div)
    rw [sub_zero] at h1
    have h2 : (C.l D : ℤ) ≤ (i C (0 : C.Div) : ℤ) := by exact_mod_cast h1
    simpa [Work.RiemannRoch.Curve.genus] using h2
  have hiD : (1 : ℤ) ≤ (i C D : ℤ) := by
    haveI : FiniteDimensional k ↥(WD C D) := Module.Finite.equiv (WDequiv C D)
    have hne : i C D ≠ 0 := by
      intro h0
      have h0' : Module.finrank k ↥(WD C D) = 0 := by rw [finrank_WD]; exact h0
      have hsub := (finrank_zero_iff_forall_zero (K := k) (V := ↥(WD C D))).mp h0' ⟨ω, hD⟩
      exact hω0 (by simpa using congrArg Subtype.val hsub)
    have h1 : 1 ≤ i C D := Nat.one_le_iff_ne_zero.mpr hne
    exact_mod_cast h1
  have hrr := Work.RiemannRoch.Curve.riemannRoch C D
  linarith

/-- Every nonzero Weil differential has a divisor. -/
private theorem exists_isDivW_aux (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Adeles C)} (hω : ω ∈ Omega C) (hω0 : ω ≠ 0) :
    ∃ W : C.Div, IsDivW C ω W := by
  classical
  obtain ⟨D₀, hD₀⟩ := mem_Omega_iff.mp hω
  have hbdd : ∀ D : C.Div, ω ∈ WD C D → C.deg D ≤ 2 * (genus C : ℤ) - 2 :=
    fun D hD => deg_le_aux C hω0 hD
  let A : Finset ℤ := (Finset.Icc (C.deg D₀) (2 * (genus C : ℤ) - 2)).filter
    (fun n => ∃ D : C.Div, ω ∈ WD C D ∧ C.deg D = n)
  have hAne : A.Nonempty := by
    refine ⟨C.deg D₀, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hbdd D₀ hD₀⟩, ⟨D₀, hD₀, rfl⟩⟩
  have hmaxA : ∀ m ∈ A, m ≤ A.max' hAne := fun m hm => Finset.le_max' A m hm
  have hmem_max : A.max' hAne ∈ A := A.max'_mem hAne
  obtain ⟨D, hDmem, hDdeg⟩ := (Finset.mem_filter.mp hmem_max).2
  have hD₀le : C.deg D₀ ≤ C.deg D := by
    rw [hDdeg]
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem_max).1).1
  refine ⟨D, hDmem, fun E hE => ?_⟩
  have hF : ω ∈ WD C (E ⊔ D) := Work.RiemannRoch.RR.mem_WD_sup C hE hDmem
  have hDF : C.deg D ≤ C.deg (E ⊔ D) := deg_mono_aux C (le_sup_right : D ≤ E ⊔ D)
  have hFD : C.deg (E ⊔ D) ≤ C.deg D := by
    have hmem : C.deg (E ⊔ D) ∈ A := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_trans hD₀le hDF, hbdd _ hF⟩, ⟨E ⊔ D, hF, rfl⟩⟩
    calc C.deg (E ⊔ D) ≤ A.max' hAne := hmaxA _ hmem
      _ = C.deg D := hDdeg.symm
  have hsum : C.deg (E ⊔ D) + C.deg (E ⊓ D) = C.deg E + C.deg D := by
    rw [← Work.CurveBasics.Curve.deg_add, ← Work.CurveBasics.Curve.deg_add]
    congr 1
    ext Q
    simp only [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
    exact max_add_min _ _
  have hEinf : C.deg E ≤ C.deg (E ⊓ D) := by linarith
  have hEff : Work.CurveBasics.Curve.Div.IsEffective (E - (E ⊓ D)) := fun Q => by
    have hQ : (E ⊓ D) Q ≤ E Q := (Finsupp.le_def.mp inf_le_left) Q
    rw [Finsupp.sub_apply]
    exact sub_nonneg.mpr hQ
  have hdeg0 : C.deg (E - (E ⊓ D)) = 0 := by
    rw [Work.CurveBasics.Curve.deg_sub]
    have hle := deg_mono_aux C (inf_le_left : E ⊓ D ≤ E)
    linarith
  have hzero : E - (E ⊓ D) = 0 :=
    (Work.CurveBasics.Divisor.deg_eq_zero_iff hEff).mp hdeg0
  calc E = E ⊓ D := sub_eq_zero.mp hzero
    _ ≤ D := inf_le_right

/-- Multiplication of a Weil differential by a rational function multiplies its divisor by
the principal divisor of the function: `div (f ω) = div ω + div f`. -/
theorem smulW_divW {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)}
    (hω : ω ∈ Work.RiemannRoch.Curve.Omega C) (hω0 : ω ≠ 0)
    {f : C.functionField} (hf : f ≠ 0) :
    Work.RiemannRoch.Curve.divW C (Work.RiemannRoch.Curve.smulW C f ω)
      = Work.RiemannRoch.Curve.divW C ω + C.div f := by
  obtain ⟨D, hD⟩ := exists_isDivW_aux C hω hω0
  have hW : IsDivW C ω (divW C ω) := divW_spec C ⟨D, hD⟩
  have hmax : IsDivW C (smulW C f ω) (divW C ω + C.div f) := by
    refine ⟨Work.RiemannRoch.RR.smulW_mem_WD C hf hW.1, ?_⟩
    intro E hE
    have h1 := Work.RiemannRoch.RR.smulW_mem_WD C (inv_ne_zero hf) hE
    have h2 : ω ∈ WD C (E + C.div f⁻¹) := by
      rw [smulW_smul, inv_mul_cancel₀ hf, smulW_one] at h1
      exact h1
    rw [Work.CurveBasics.Order.div_inv C hf] at h2
    have h3 : E + -C.div f ≤ divW C ω := le_divW C ⟨D, hD⟩ h2
    rw [Finsupp.le_def] at h3 ⊢
    intro Q
    have hQ := h3 Q
    simp only [Finsupp.add_apply, Finsupp.neg_apply] at hQ ⊢
    linarith
  exact divW_eq_of_isDivW C ⟨_, hmax⟩ hmax

end Work.RiemannRoch.Duality


