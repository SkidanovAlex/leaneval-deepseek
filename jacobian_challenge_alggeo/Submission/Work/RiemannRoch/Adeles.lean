/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR, layer 1: the adèle space of a curve

This file sets up the adèle space `A_K` of a curve `C` over a field `k` and its basic API.
This is the ambient object of the "Riemann–Roch without cohomology" development (area `RR`
of `Submission/Work/NOTES_LEAD_jacobian_blueprint.md`, §4).

## The model of the adèle space

Classically `A_K` is the restricted product of the completions `K_P` of `K = K(C)` at the
places of `C`, with respect to the valuation rings.  For Riemann–Roch one never uses the
topology: only the *lattices* `A(D)` and the quotients `A(D')/A(D)` and `A/(K + A(D))` matter,
and these are insensitive to replacing `K_P` by `K`.  We therefore use the lighter model

  `A_K := {x : C.Place → K | x Q ∈ O_Q for all but finitely many Q}`

which is a `K`-subalgebra of the product `C.Place → K`, and contains `K` diagonally.

## Main definitions

* `Work.RiemannRoch.Curve.localIdeal C Q n` — the fractional ideal `I_Q(n) = m_Q^{-n}`;
* `Work.RiemannRoch.Curve.Adeles C` — the adèle space `A_K`;
* `Work.RiemannRoch.Curve.A C D` — the lattice `A(D)` of adèles with poles bounded by `D`;
* `Work.RiemannRoch.Curve.Asub C D` — the same, as a submodule of `A_K`;
* `Work.RiemannRoch.Curve.diag C`, `Curve.diagK C` — the diagonal embedding `K → A_K`;
* `Work.RiemannRoch.Curve.H1 C D` — the quotient `A / (K + A(D))`;
* `Work.RiemannRoch.Curve.i C D`, `Curve.genus C`, `Curve.HasFiniteGenus C`.

## Conventions

`D Q` is the coefficient of the divisor `D` at the place `Q`, and
`x ∈ A(D) ↔ ∀ Q, ord_Q (x Q) ≥ -D Q`, so that `A(D) ⊆ A(E)` for `D ≤ E` and
`A(D) ∩ K = L(D)`.  With this convention `H1 C 0 = A/(K + A(0))` is the classical
`H^1(C, O_C)` and its dimension is the genus.
-/
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.Order.ord_lem
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The local ring of a curve at a place is a discrete valuation ring, registered as an
instance. -/
instance instIsDiscreteValuationRingStalk (C : Curve k) (Q : C.Place) :
    IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
  Work.CurveBasics.Place.isDiscreteValuationRing Q

/-! ## The local lattices `I_Q(n)` -/

/-- The order of vanishing of `0` at any place is `0`. -/
theorem ordAt_zero (C : Curve k) (Q : C.Place) : C.ordAt (0 : C.functionField) Q = 0 := by
  simp [Work.CurveBasics.Curve.ordAt, AlgebraicGeometry.Scheme.ord_zero]

/-- The order of vanishing is superadditive at a place (the ultra-metric inequality). -/
theorem min_ordAt_add_le (C : Curve k) (Q : C.Place) {a b : C.functionField}
    (h : a + b ≠ 0) : min (C.ordAt a Q) (C.ordAt b Q) ≤ C.ordAt (a + b) Q :=
  Scheme.ord_add (x := Q.point) (f := a) (g := b) h


/-- The `k`-submodule `I_Q(n) = {y : K | y = 0 ∨ ord_Q y ≥ -n}` of the function field: the
`n`-th (possibly negative) power of the maximal ideal of the local ring at `Q`, realised as a
set of rational functions. -/
def localIdeal (C : Curve k) (Q : C.Place) (n : ℤ) : Submodule k C.functionField where
  carrier := {y | y = 0 ∨ -n ≤ C.ordAt y Q}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    rcases eq_or_ne (a + b) 0 with hab | hab
    · exact Or.inl hab
    refine Or.inr ?_
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [ha0, zero_add]
      rcases hb with hb0 | hb0
      · exact absurd (by rw [ha0, hb0, add_zero]) hab
      · exact hb0
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, add_zero]
      exact ha.resolve_left ha0
    · have hmin : min (C.ordAt a Q) (C.ordAt b Q) ≤ C.ordAt (a + b) Q :=
        min_ordAt_add_le C Q hab
      have h1 : -n ≤ C.ordAt a Q := ha.resolve_left ha0
      have h2 : -n ≤ C.ordAt b Q := hb.resolve_left hb0
      linarith [le_min h1 h2]
  smul_mem' := by
    intro c y hy
    rcases eq_or_ne c 0 with hc | hc
    · exact Or.inl (by rw [hc, zero_smul])
    rcases eq_or_ne y 0 with hy0 | hy0
    · exact Or.inl (by rw [hy0, smul_zero])
    refine Or.inr ?_
    rw [Algebra.smul_def]
    have h1 : algebraMap k C.functionField c ≠ 0 := by
      simpa using ((algebraMap k C.functionField).injective.ne_iff).mpr hc
    rw [Work.CurveBasics.Curve.ordAt_mul C h1 hy0 Q,
      Work.CurveBasics.Curve.ordAt_algebraMap C hc Q, zero_add]
    exact hy.resolve_left hy0

theorem mem_localIdeal {C : Curve k} {Q : C.Place} {n : ℤ} {y : C.functionField} :
    y ∈ localIdeal C Q n ↔ y = 0 ∨ -n ≤ C.ordAt y Q := Iff.rfl

theorem localIdeal_mono (C : Curve k) {Q : C.Place} {m n : ℤ} (h : m ≤ n) :
    localIdeal C Q m ≤ localIdeal C Q n := by
  intro y hy
  rw [mem_localIdeal] at hy ⊢
  rcases hy with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

theorem mem_localIdeal_zero {C : Curve k} {Q : C.Place} {y : C.functionField} :
    y ∈ localIdeal C Q 0 ↔ y ∈ Q.valuationSubring := by
  rw [mem_localIdeal, Work.CurveBasics.Place.mem_valuationSubring_iff]
  constructor
  · rintro (rfl | h)
    · simp [AlgebraicGeometry.Scheme.ord_zero]
    · simpa using h
  · intro h
    by_cases hy : y = 0
    · exact Or.inl hy
    · exact Or.inr (by simpa using h)

/-! ## The adèle space and the lattices `A(D)` -/

/-- The adèle space `A_K` of a curve: the restricted product of `K` over the places of `C`.
An adèle is a family of rational functions whose components are integral at all but finitely
many places. -/
def Adeles (C : Curve k) : Submodule k (C.Place → C.functionField) where
  carrier := {x | {Q : C.Place | C.ordAt (x Q) Q < 0}.Finite}
  zero_mem' := by
    show {Q : C.Place | C.ordAt ((0 : C.Place → C.functionField) Q) Q < 0}.Finite
    have h : {Q : C.Place | C.ordAt ((0 : C.Place → C.functionField) Q) Q < 0} = ∅ := by
      ext Q
      simp [ordAt_zero]
    rw [h]; exact Set.finite_empty
  add_mem' := by
    intro x y hx hy
    show {Q : C.Place | C.ordAt ((x + y) Q) Q < 0}.Finite
    refine Set.Finite.subset (hx.union hy) ?_
    intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    simp only [Set.mem_setOf_eq, not_lt] at hcon
    have hsum : 0 ≤ C.ordAt ((x + y) Q) Q := by
      rw [Pi.add_apply]
      by_cases h0 : x Q + y Q = 0
      · rw [h0, ordAt_zero]
      · have hmin : min (C.ordAt (x Q) Q) (C.ordAt (y Q) Q) ≤ C.ordAt (x Q + y Q) Q :=
          min_ordAt_add_le C Q h0
        have h0' : 0 ≤ min (C.ordAt (x Q) Q) (C.ordAt (y Q) Q) := le_min hcon.1 hcon.2
        linarith
    exact absurd hsum (not_le.mpr hQ)
  smul_mem' := by
    intro c x hx
    show {Q : C.Place | C.ordAt ((c • x) Q) Q < 0}.Finite
    refine Set.Finite.subset hx ?_
    intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_lt] at hcon
    have hge : 0 ≤ C.ordAt ((c • x) Q) Q := by
      rw [Pi.smul_apply]
      rcases eq_or_ne c 0 with hc | hc
      · rw [hc, zero_smul, ordAt_zero]
      rcases eq_or_ne (x Q) 0 with hx0 | hx0
      · rw [hx0, smul_zero, ordAt_zero]
      · rw [Algebra.smul_def]
        have h1 : algebraMap k C.functionField c ≠ 0 := by
          simpa using ((algebraMap k C.functionField).injective.ne_iff).mpr hc
        rw [Work.CurveBasics.Curve.ordAt_mul C h1 hx0 Q,
          Work.CurveBasics.Curve.ordAt_algebraMap C hc Q, zero_add]
        exact hcon
    exact absurd hge (not_le.mpr hQ)

/-- The lattice `A(D)` of adèles with poles bounded by the divisor `D`:
`x ∈ A(D) ↔ ∀ Q, ord_Q (x Q) ≥ -D Q`. -/
def A (C : Curve k) (D : C.Div) : Submodule k (C.Place → C.functionField) :=
  ⨅ (Q : C.Place), (localIdeal C Q (D Q)).comap (LinearMap.proj Q)

@[simp]
theorem mem_A {C : Curve k} {D : C.Div} {x : C.Place → C.functionField} :
    x ∈ A C D ↔ ∀ Q, x Q = 0 ∨ -(D Q) ≤ C.ordAt (x Q) Q := by
  simp only [A, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply,
    mem_localIdeal]

theorem A_le_adeles (C : Curve k) (D : C.Div) : A C D ≤ Adeles C := by
  intro x hx
  show {Q : C.Place | C.ordAt (x Q) Q < 0}.Finite
  refine Set.Finite.subset D.support.finite_toSet ?_
  intro Q hQ
  simp only [Set.mem_setOf_eq] at hQ
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro hDQ
  rcases (mem_A.mp hx) Q with h | h
  · rw [h] at hQ
    exact absurd hQ (not_lt_of_ge (ordAt_zero C Q).ge)
  · rw [hDQ] at h; simp only [neg_zero] at h
    exact absurd h (not_le.mpr hQ)

theorem A_mono (C : Curve k) {D E : C.Div} (h : D ≤ E) : A C D ≤ A C E := by
  intro x hx
  rw [mem_A] at hx ⊢
  intro Q
  rcases hx Q with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by have := Finsupp.le_def.mp h Q; linarith)

/-- `A(D)` as a submodule of the adèle space. -/
def Asub (C : Curve k) (D : C.Div) : Submodule k (Adeles C) :=
  (A C D).comap (Adeles C).subtype

@[simp]
theorem mem_Asub {C : Curve k} {D : C.Div} {x : Adeles C} :
    x ∈ Asub C D ↔ (x : C.Place → C.functionField) ∈ A C D := Iff.rfl

theorem Asub_mono (C : Curve k) {D E : C.Div} (h : D ≤ E) : Asub C D ≤ Asub C E := by
  intro x hx
  rw [mem_Asub, mem_A] at hx ⊢
  intro Q
  rcases hx Q with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by have := Finsupp.le_def.mp h Q; linarith)

/-- The pole divisor of an adèle: the smallest effective divisor bounding its poles. -/
def poleDiv (C : Curve k) (x : Adeles C) : C.Div :=
  Finsupp.ofSupportFinite (fun Q => max 0 (-(C.ordAt ((x : C.Place → C.functionField) Q) Q)))
    (x.2.subset (by
      intro Q hQ
      simp only [Function.mem_support, ne_eq] at hQ
      simp only [Set.mem_setOf_eq]
      by_contra hcon
      push Not at hcon
      exact hQ (max_eq_left (neg_nonpos.mpr hcon))))

@[simp]
theorem poleDiv_apply (C : Curve k) (x : Adeles C) (Q : C.Place) :
    poleDiv C x Q = max 0 (-(C.ordAt ((x : C.Place → C.functionField) Q) Q)) :=
  congrFun (Finsupp.ofSupportFinite_coe) Q

theorem mem_A_poleDiv (C : Curve k) (x : Adeles C) :
    (x : C.Place → C.functionField) ∈ A C (poleDiv C x) := by
  rw [mem_A]
  intro Q
  by_cases hQ : (x : C.Place → C.functionField) Q = 0
  · exact Or.inl hQ
  · refine Or.inr ?_
    rw [poleDiv_apply]
    by_cases h : 0 ≤ C.ordAt ((x : C.Place → C.functionField) Q) Q
    · have hmax : max 0 (-(C.ordAt ((x : C.Place → C.functionField) Q) Q)) = 0 :=
        max_eq_left (by linarith)
      rw [hmax]; linarith
    · have hmax : max 0 (-(C.ordAt ((x : C.Place → C.functionField) Q) Q))
          = -(C.ordAt ((x : C.Place → C.functionField) Q) Q) := max_eq_right (by linarith)
      rw [hmax]; linarith

/-- Every adèle has bounded poles: `A_K = ⋃_D A(D)`. -/
theorem iSup_Asub_eq_top (C : Curve k) : ⨆ D : C.Div, Asub C D = ⊤ := by
  refine top_unique fun x _ => ?_
  exact le_iSup (fun D => Asub C D) (poleDiv C x) (mem_A_poleDiv C x)

/-! ## The diagonal embedding of `K` into `A_K` -/

/-- The diagonal embedding `K ↪ A_K`, `h ↦ (h)_Q`. -/
def diag (C : Curve k) : C.functionField →ₗ[k] Adeles C where
  toFun h := ⟨fun _ => h, (C.finite_support_ordAt h).subset (by
    intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ ⊢
    exact ne_of_lt hQ)⟩
  map_add' a b := by
    ext Q; simp
  map_smul' c a := by
    ext Q; simp

@[simp]
theorem diag_apply (C : Curve k) (h : C.functionField) (Q : C.Place) :
    ((diag C h : Adeles C) : C.Place → C.functionField) Q = h := rfl

/-- The image `K ⊆ A_K` of the diagonal embedding. -/
def diagK (C : Curve k) : Submodule k (Adeles C) := (diag C).range

theorem mem_diagK {C : Curve k} {x : Adeles C} :
    x ∈ diagK C ↔ ∃ h : C.functionField, diag C h = x := Iff.rfl

/-- A curve has a place: a one-dimensional noetherian Jacobson scheme which is not a point
has a closed point. -/
theorem nonempty_place (C : Curve k) : Nonempty C.Place := by
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial C.left)
  have hne : x ≠ genericPoint C.left ∨ y ≠ genericPoint C.left := by
    by_contra h
    push_neg at h
    exact hxy (h.1.trans h.2.symm)
  rcases hne with h | h
  · rcases C.eq_genericPoint_or_isClosed x with hg | hc
    · exact absurd hg h
    · exact ⟨⟨x, hc⟩⟩
  · rcases C.eq_genericPoint_or_isClosed y with hg | hc
    · exact absurd hg h
    · exact ⟨⟨y, hc⟩⟩

instance (C : Curve k) : Nonempty C.Place := nonempty_place C

theorem diag_injective (C : Curve k) : Function.Injective (diag C) := by
  intro a b h
  have h' : (fun _ : C.Place => a) = fun _ : C.Place => b := congrArg Subtype.val h
  exact congrFun h' (Classical.choice (inferInstance : Nonempty C.Place))

theorem diag_mem_Asub_iff {C : Curve k} {D : C.Div} {h : C.functionField} :
    diag C h ∈ Asub C D ↔ h ∈ C.L D := by
  rw [mem_Asub, mem_A, Work.CurveBasics.Curve.mem_L_iff]
  constructor
  · intro hh
    by_cases h0 : h = 0
    · exact Or.inl h0
    · refine Or.inr fun Q => ?_
      have hq := hh Q
      simp only [diag_apply] at hq
      simp only [Finsupp.add_apply, Work.CurveBasics.Curve.div_apply]
      rcases hq with h' | h'
      · exact absurd h' h0
      · linarith
  · rintro (rfl | hh) Q
    · exact Or.inl rfl
    · refine Or.inr ?_
      simp only [diag_apply]
      have hq := hh Q
      simp only [Finsupp.add_apply, Work.CurveBasics.Curve.div_apply] at hq
      linarith

/-! ## The diagonal copy of `K` inside the product, and `A(D) ∩ K` -/

/-- The diagonal embedding `K ↪ (Place → K)`, `h ↦ (h)_Q`, without the adèle condition. -/
def diagFn (C : Curve k) : C.functionField →ₗ[k] (C.Place → C.functionField) where
  toFun h := fun _ => h
  map_add' a b := by ext Q; simp
  map_smul' c a := by ext Q; simp

@[simp]
theorem diagFn_apply (C : Curve k) (h : C.functionField) (Q : C.Place) :
    diagFn C h Q = h := rfl

/-- The copy of `K = K(C)` inside the product `Place → K`, as a `k`-submodule.  This is the
`K` appearing in `K + A(D)`. -/
def Kdiag (C : Curve k) : Submodule k (C.Place → C.functionField) := (diagFn C).range

theorem mem_Kdiag {C : Curve k} {x : C.Place → C.functionField} :
    x ∈ Kdiag C ↔ ∃ h : C.functionField, diagFn C h = x := Iff.rfl

/-- `A(D) ∩ K = L(D)`: the bounded principal adèles are exactly the Riemann–Roch space. -/
theorem inf_Kdiag_eq (C : Curve k) (D : C.Div) :
    A C D ⊓ Kdiag C = (C.L D).map (diagFn C) := by
  ext x
  rw [Submodule.mem_inf, mem_A, Submodule.mem_map, mem_Kdiag]
  constructor
  · rintro ⟨hx, h, rfl⟩
    refine ⟨h, ?_, rfl⟩
    rw [Work.CurveBasics.Curve.mem_L_iff]
    by_cases h0 : h = 0
    · exact Or.inl h0
    · refine Or.inr fun Q => ?_
      simp only [Finsupp.add_apply, Work.CurveBasics.Curve.div_apply]
      have hq := hx Q
      simp only [diagFn_apply] at hq
      rcases hq with h' | h'
      · exact absurd h' h0
      · linarith
  · rintro ⟨h, hh, rfl⟩
    refine ⟨fun Q => ?_, ⟨h, rfl⟩⟩
    rw [Work.CurveBasics.Curve.mem_L_iff] at hh
    rcases hh with h0 | hh
    · exact Or.inl h0
    · refine Or.inr ?_
      have hq := hh Q
      simp only [Finsupp.add_apply, Work.CurveBasics.Curve.div_apply] at hq
      simp only [diagFn_apply]
      linarith

/-! ## The quotient `A/(K + A(D))` and the genus -/

/-- The quotient `A_K/(K + A(D))`, the adelic model of `H^1(C, O(D))`. -/
abbrev H1 (C : Curve k) (D : C.Div) : Type u :=
  ↥(Adeles C) ⧸ (Asub C D ⊔ diagK C)

/-- `i(D) = dim_k A/(K + A(D))`, the index of speciality.  As always with
`Module.finrank`, this is `0` if the quotient is infinite dimensional; the theorems about `i`
carry the appropriate finiteness hypothesis (`HasFiniteGenus`). -/
noncomputable def i (C : Curve k) (D : C.Div) : ℕ := Module.finrank k (H1 C D)

/-- The genus of a curve, `g = dim_k A/(K + A(0)) = h^1(C, O_C)`. -/
noncomputable def genus (C : Curve k) : ℕ := i C 0

/-- The hypothesis that the genus is finite: `H^1(C, O_C)` is finite dimensional.  This is
Serre, *Algebraic Groups and Class Fields*, II §5. -/
def HasFiniteGenus (C : Curve k) : Prop := Module.Finite k (H1 C 0)

theorem genus_eq_finrank (C : Curve k) : genus C = Module.finrank k (H1 C 0) := rfl

theorem finite_genus_iff (C : Curve k) :
    HasFiniteGenus C ↔ Module.Finite k (H1 C 0) := Iff.rfl

end

end Curve

end Work.RiemannRoch
