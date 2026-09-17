import Submission.E8Weights
import Submission.WordSpan

set_option maxHeartbeats 4000000

noncomputable section

/-!
# Triangular spanning for `U(e₈)` (the spanning half of the triangular decomposition)

Writing `e i, h i, f i` for the images in `U = U(e₈)` of the Serre generators and
`Fw w = ∏_{i ∈ w} f i`, `Hw v = ∏_{j ∈ v} h j`, `Ew u = ∏_{k ∈ u} e k`, the *triangular monomials*
are the products `triMon w v u = Fw w * Hw v * Ew u`.  This file proves

  `Submodule.span ℂ (Set.range (fun p => triMon p.1 p.2.1 p.2.2)) = ⊤`,

i.e. **every element of `U(e₈)` is a finite ℂ-linear combination of triangular monomials.**

The proof has two halves.

* The "moving" lemmas (each a list induction) show that the span `T` of the triangular monomials
  is closed under *right* multiplication by each of the three families of generators: appending
  `e i` is trivial, and moving `h i` and `f i` leftwards through the `E`-word uses the commutators
  `commutator_H_E` / `commutator_E_F` (the `f`-case also has to push the resulting `h`'s past the
  remaining `e`'s).
* Then `{u : U | ∀ x ∈ T, x * u ∈ T}` is a subalgebra of `U` containing the Serre generators
  `e i, f i, h i`; since `e₈` is generated as a Lie algebra by the Serre generators
  (`Submission.WordSpan.eq_top_of_generators`) and `ι(e₈)` generates `U` as an algebra
  (`Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota`), it is all of `U`.  Applying it
  to `x = 1 ∈ T` gives `T = ⊤`.
-/

open UniversalEnvelopingAlgebra
open CartanMatrix

namespace Submission.TriangularSpan

open Submission.E8Weights

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- The product of the lowering generators along a word. -/
def Fw (w : List (Fin 8)) : U := (w.map f).prod

/-- The product of the Cartan generators along a word. -/
def Hw (v : List (Fin 8)) : U := (v.map h).prod

/-- The product of the raising generators along a word. -/
def Ew (u : List (Fin 8)) : U := (u.map e).prod

/-- A triangular monomial `(F-word) * (H-word) * (E-word)`. -/
def triMon (w v u : List (Fin 8)) : U := Fw w * Hw v * Ew u

@[simp] lemma Fw_nil : Fw ([] : List (Fin 8)) = 1 := by simp [Fw]
@[simp] lemma Hw_nil : Hw ([] : List (Fin 8)) = 1 := by simp [Hw]
@[simp] lemma Ew_nil : Ew ([] : List (Fin 8)) = 1 := by simp [Ew]

@[simp] lemma Fw_cons (i : Fin 8) (w : List (Fin 8)) : Fw (i :: w) = f i * Fw w := by
  simp [Fw]
@[simp] lemma Hw_cons (i : Fin 8) (v : List (Fin 8)) : Hw (i :: v) = h i * Hw v := by
  simp [Hw]
@[simp] lemma Ew_cons (i : Fin 8) (u : List (Fin 8)) : Ew (i :: u) = e i * Ew u := by
  simp [Ew]

lemma Fw_append (w w' : List (Fin 8)) : Fw (w ++ w') = Fw w * Fw w' := by
  simp [Fw, List.map_append, List.prod_append]

lemma Hw_append (v v' : List (Fin 8)) : Hw (v ++ v') = Hw v * Hw v' := by
  simp [Hw, List.map_append, List.prod_append]

lemma Ew_append (u u' : List (Fin 8)) : Ew (u ++ u') = Ew u * Ew u' := by
  simp [Ew, List.map_append, List.prod_append]

@[simp] lemma Fw_singleton (i : Fin 8) : Fw [i] = f i := by simp [Fw]
@[simp] lemma Hw_singleton (i : Fin 8) : Hw [i] = h i := by simp [Hw]
@[simp] lemma Ew_singleton (i : Fin 8) : Ew [i] = e i := by simp [Ew]

@[simp] lemma triMon_nil_nil_nil : triMon ([] : List (Fin 8)) [] [] = 1 := by
  simp [triMon]

/-- The ℂ-span of all triangular monomials. -/
def T : Submodule ℂ U :=
  Submodule.span ℂ (Set.range (fun p : List (Fin 8) × List (Fin 8) × List (Fin 8) =>
    triMon p.1 p.2.1 p.2.2))

/-- The ℂ-span of the products `(H-word) * (E-word)`. -/
def T₀ : Submodule ℂ U :=
  Submodule.span ℂ (Set.range (fun p : List (Fin 8) × List (Fin 8) => Hw p.1 * Ew p.2))

/-- The ℂ-span of the `H`-words. -/
def HwSpan : Submodule ℂ U := Submodule.span ℂ (Set.range Hw)

lemma triMon_mem_T (w v u : List (Fin 8)) : triMon w v u ∈ T :=
  Submodule.subset_span ⟨(w, v, u), rfl⟩

lemma Hw_mul_Ew_mem_T₀ (v u : List (Fin 8)) : Hw v * Ew u ∈ T₀ :=
  Submodule.subset_span ⟨(v, u), rfl⟩

lemma Hw_mem_HwSpan (v : List (Fin 8)) : Hw v ∈ HwSpan :=
  Submodule.subset_span ⟨v, rfl⟩

lemma Hw_mul_Ew_mem_T (v u : List (Fin 8)) : Hw v * Ew u ∈ T := by
  have h : Hw v * Ew u = triMon [] v u := by simp [triMon]
  rw [h]; exact triMon_mem_T _ _ _

/-- The sum of the Cartan integers `A_{ij} = CartanMatrix.E₈ i j` over the letters `j` of a word. -/
def cartSum (i : Fin 8) (w : List (Fin 8)) : ℂ :=
  (w.map (fun j => (CartanMatrix.E₈ i j : ℂ))).sum

@[simp] lemma cartSum_nil (i : Fin 8) : cartSum i [] = 0 := by simp [cartSum]

@[simp] lemma cartSum_cons (i j : Fin 8) (w : List (Fin 8)) :
    cartSum i (j :: w) = (CartanMatrix.E₈ i j : ℂ) + cartSum i w := by
  simp [cartSum]

/-- The span of the `H`-words is closed under left multiplication by an `H`-word. -/
lemma Hw_mul_HwSpan (v : List (Fin 8)) {r : U} (hr : r ∈ HwSpan) : Hw v * r ∈ HwSpan := by
  refine Submodule.span_induction (p := fun x _ => Hw v * x ∈ HwSpan) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨v', rfl⟩
    rw [← Hw_append]
    exact Hw_mem_HwSpan (v ++ v')
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of the `(H-word)*(E-word)` products is closed under left multiplication by an
`H`-word. -/
lemma Hw_mul_T₀ (v : List (Fin 8)) {r : U} (hr : r ∈ T₀) : Hw v * r ∈ T₀ := by
  refine Submodule.span_induction (p := fun x _ => Hw v * x ∈ T₀) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    show Hw v * (Hw v' * Ew u') ∈ T₀
    rw [← mul_assoc, ← Hw_append]
    exact Hw_mul_Ew_mem_T₀ (v ++ v') u'
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of `(H-word)*(E-word)` products is closed under right multiplication by an
`E`-word. -/
lemma T₀_mul_Ew (u : List (Fin 8)) {r : U} (hr : r ∈ T₀) : r * Ew u ∈ T₀ := by
  refine Submodule.span_induction (p := fun x _ => x * Ew u ∈ T₀) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    show (Hw v' * Ew u') * Ew u ∈ T₀
    rw [mul_assoc, ← Ew_append]
    exact Hw_mul_Ew_mem_T₀ v' (u' ++ u)
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- Moving a single `e i` past an `H`-word. -/
lemma throughH (v : List (Fin 8)) (i : Fin 8) : e i * Hw v ∈ T₀ := by
  induction v with
  | nil => simpa using Hw_mul_Ew_mem_T₀ ([] : List (Fin 8)) [i]
  | cons j v' ih =>
      have hce : e i * h j = h j * e i - ((CartanMatrix.E₈ j i : ℂ)) • e i := by
        have h2 := sub_eq_iff_eq_add.mp (commutator_H_E j i)
        simp only [e, h] at h2 ⊢
        rw [Int.cast_smul_eq_zsmul, h2, add_sub_cancel_left]
      have hstep : e i * Hw (j :: v') =
          h j * (e i * Hw v') - ((CartanMatrix.E₈ j i : ℂ)) • (e i * Hw v') := by
        rw [Hw_cons, ← mul_assoc, hce, sub_mul, smul_mul_assoc, mul_assoc]
      rw [hstep]
      exact Submodule.sub_mem _ (by simpa using Hw_mul_T₀ [j] ih) (Submodule.smul_mem _ _ ih)

/-- The span of `(H-word)*(E-word)` products is closed under left multiplication by a single
raising generator. -/
lemma e_mul_T₀ (i : Fin 8) {r : U} (hr : r ∈ T₀) : e i * r ∈ T₀ := by
  refine Submodule.span_induction (p := fun x _ => e i * x ∈ T₀) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    show e i * (Hw v' * Ew u') ∈ T₀
    rw [← mul_assoc]
    exact T₀_mul_Ew u' (throughH v' i)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of `(H-word)*(E-word)` products is closed under left multiplication by an
`E`-word. -/
lemma Ew_mul_T₀ (u : List (Fin 8)) {r : U} (hr : r ∈ T₀) : Ew u * r ∈ T₀ := by
  induction u with
  | nil => simpa using hr
  | cons k u' ih =>
      rw [Ew_cons, mul_assoc]
      exact e_mul_T₀ k ih

/-- Moving an `E`-word past an `H`-word. -/
lemma Ew_mul_Hw (u v : List (Fin 8)) : Ew u * Hw v ∈ T₀ :=
  Ew_mul_T₀ u (by simpa using Hw_mul_Ew_mem_T₀ v [])

/-- `e i * h j = h j * e i - A_{ji} • e i` in `U(e₈)` (Cartan index `j`, raising index `i`). -/
lemma e_mul_h (i j : Fin 8) : e i * h j = h j * e i - ((CartanMatrix.E₈ j i : ℂ)) • e i := by
  have h2 := sub_eq_iff_eq_add.mp (commutator_H_E j i)
  simp only [e, h] at h2 ⊢
  rw [Int.cast_smul_eq_zsmul, h2, add_sub_cancel_left]

/-- Moving an `E`-word past a single `H`-generator. -/
lemma Ew_mul_h (u : List (Fin 8)) (i : Fin 8) :
    Ew u * h i = h i * Ew u - (cartSum i u) • Ew u := by
  induction u with
  | nil => simp [Ew, cartSum]
  | cons j u' ih =>
      have hstep : Ew (j :: u') * h i =
          (e j * h i) * Ew u' - (cartSum i u') • (e j * Ew u') := by
        rw [Ew_cons, mul_assoc, ih, mul_sub, mul_smul_comm]
        simp only [mul_assoc]
      rw [hstep, e_mul_h j i, cartSum_cons, Ew_cons, sub_mul, smul_mul_assoc, mul_assoc,
        add_smul]
      module

/-- `h j * f i = f i * h j - A_{ji} • f i` in `U(e₈)` (Cartan index `j`, lowering index `i`). -/
lemma h_mul_f (i j : Fin 8) : h j * f i = f i * h j - ((CartanMatrix.E₈ j i : ℂ)) • f i := by
  have h2 := sub_eq_iff_eq_add.mp (commutator_H_F j i)
  simp only [f, h] at h2 ⊢
  rw [Int.cast_smul_eq_zsmul, h2, neg_smul, sub_eq_add_neg]
  abel

/-- Moving an `H`-word past a single lowering generator: the result is `f i` times an element of
the span of the `H`-words. -/
lemma Hw_mul_f (v : List (Fin 8)) (i : Fin 8) :
    ∃ R ∈ HwSpan, Hw v * f i = f i * R := by
  induction v with
  | nil => exact ⟨1, Hw_mem_HwSpan [], by simp [Hw]⟩
  | cons j v' ih =>
      obtain ⟨R', hR', hEq⟩ := ih
      refine ⟨h j * R' - ((CartanMatrix.E₈ j i : ℂ)) • R', ?_, ?_⟩
      · exact Submodule.sub_mem _ (by simpa using Hw_mul_HwSpan [j] hR')
          (Submodule.smul_mem _ _ hR')
      · calc Hw (j :: v') * f i
            = h j * (Hw v' * f i) := by rw [Hw_cons, mul_assoc]
          _ = h j * (f i * R') := by rw [hEq]
          _ = (h j * f i) * R' := by rw [mul_assoc]
          _ = (f i * h j - ((CartanMatrix.E₈ j i : ℂ)) • f i) * R' := by rw [h_mul_f i j]
          _ = f i * (h j * R') - ((CartanMatrix.E₈ j i : ℂ)) • (f i * R') := by
                rw [sub_mul, smul_mul_assoc, mul_assoc]
          _ = f i * (h j * R' - ((CartanMatrix.E₈ j i : ℂ)) • R') := by
                rw [mul_sub, mul_smul_comm]

/-- `e i * f j = f j * e i + δ_{ij} h i` in `U(e₈)`. -/
lemma e_mul_f (i j : Fin 8) :
    e i * f j = f j * e i + (if i = j then h i else 0) := by
  have h2 := commutator_E_F i j
  simp only [e, f, h] at h2 ⊢
  rw [← h2]; abel

/-- Moving an `E`-word past a single lowering generator: the result is `f i * E` plus a correction
in the span of the `(H-word)*(E-word)` products. -/
lemma Ew_mul_f (u : List (Fin 8)) (i : Fin 8) :
    ∃ R ∈ T₀, Ew u * f i = f i * Ew u + R := by
  induction u with
  | nil => exact ⟨0, Submodule.zero_mem _, by simp [Ew]⟩
  | cons k u' ih =>
      obtain ⟨R', hR', hEq⟩ := ih
      refine ⟨(if k = i then h k * Ew u' else 0) + e k * R', ?_, ?_⟩
      · refine Submodule.add_mem _ ?_ (e_mul_T₀ k hR')
        by_cases hk : k = i
        · subst hk
          rw [if_pos rfl]
          simpa using Hw_mul_Ew_mem_T₀ [k] u'
        · rw [if_neg hk]; exact Submodule.zero_mem _
      · have hA : Ew (k :: u') * f i = (e k * f i) * Ew u' + e k * R' := by
          rw [Ew_cons, mul_assoc, hEq, mul_add]
          simp only [mul_assoc]
        have hB : (e k * f i) * Ew u' + e k * R' = f i * (e k * Ew u')
            + ((if k = i then h k * Ew u' else 0) + e k * R') := by
          rw [e_mul_f k i, add_mul]
          by_cases hk : k = i
          · subst hk
            rw [if_pos rfl, if_pos rfl]
            simp only [mul_assoc]
            abel
          · rw [if_neg hk, if_neg hk]
            simp only [mul_assoc, zero_mul, zero_add]
            abel
        have step : Ew (k :: u') * f i = f i * (e k * Ew u')
            + ((if k = i then h k * Ew u' else 0) + e k * R') := hA.trans hB
        rw [step, ← Ew_cons]

/-- `Fw w * r * Ew u ∈ T` for `r` in the span of the `H`-words. -/
lemma T_mem_of_HwSpan (w u : List (Fin 8)) {r : U} (hr : r ∈ HwSpan) : Fw w * r * Ew u ∈ T := by
  refine Submodule.span_induction (p := fun x _ => Fw w * x * Ew u ∈ T) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨v', rfl⟩
    have : Fw w * Hw v' * Ew u = triMon w v' u := by simp only [triMon]
    rw [this]; exact triMon_mem_T _ _ _
  · simp
  · intro x y _ _ hx hy
    rw [mul_add, add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm, smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- `Fw w * Hw v * r ∈ T` for `r` in the span of the `(H-word)*(E-word)` products. -/
lemma T_mem_of_T₀ (w v : List (Fin 8)) {r : U} (hr : r ∈ T₀) : Fw w * Hw v * r ∈ T := by
  refine Submodule.span_induction (p := fun x _ => Fw w * Hw v * x ∈ T) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    have h : Fw w * Hw v * (Hw v' * Ew u') = triMon w (v ++ v') u' := by
      simp only [triMon, Hw_append, mul_assoc]
    rw [h]; exact triMon_mem_T _ _ _
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of the triangular monomials is closed under right multiplication by `e i`. -/
lemma T_mul_e (i : Fin 8) {t : U} (ht : t ∈ T) : t * e i ∈ T := by
  refine Submodule.span_induction (p := fun x _ => x * e i ∈ T) ?_ ?_ ?_ ?_ ht
  · rintro x ⟨⟨w, v, u⟩, rfl⟩
    have h : triMon w v u * e i = triMon w v (u ++ [i]) := by
      simp only [triMon, Ew_append, Ew_singleton, mul_assoc]
    rw [h]; exact triMon_mem_T _ _ _
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- The span of the triangular monomials is closed under right multiplication by `h i`. -/
lemma T_mul_h (i : Fin 8) {t : U} (ht : t ∈ T) : t * h i ∈ T := by
  refine Submodule.span_induction (p := fun x _ => x * h i ∈ T) ?_ ?_ ?_ ?_ ht
  · rintro x ⟨⟨w, v, u⟩, rfl⟩
    have h1 : Fw w * Hw v * (Ew u * h i) = Fw w * Hw v * (h i * Ew u)
        - (cartSum i u) • (Fw w * Hw v * Ew u) := by
      rw [Ew_mul_h u i, mul_sub, mul_smul_comm]
    have h2 : Fw w * Hw v * (h i * Ew u) = triMon w (v ++ [i]) u := by
      simp only [triMon, Hw_append, Hw_singleton, mul_assoc]
    have h3 : Fw w * Hw v * Ew u = triMon w v u := by simp only [triMon]
    have key : triMon w v u * h i = triMon w (v ++ [i]) u - (cartSum i u) • triMon w v u := by
      rw [triMon, mul_assoc, h1, h2, h3]
    rw [key]
    exact Submodule.sub_mem _ (triMon_mem_T _ _ _) (Submodule.smul_mem _ _ (triMon_mem_T _ _ _))
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- The span of the triangular monomials is closed under right multiplication by `f i`. -/
lemma T_mul_f (i : Fin 8) {t : U} (ht : t ∈ T) : t * f i ∈ T := by
  refine Submodule.span_induction (p := fun x _ => x * f i ∈ T) ?_ ?_ ?_ ?_ ht
  · rintro x ⟨⟨w, v, u⟩, rfl⟩
    obtain ⟨R, hR, hEq⟩ := Ew_mul_f u i
    obtain ⟨Rv, hRv, hEqv⟩ := Hw_mul_f v i
    have key : triMon w v u * f i = Fw (w ++ [i]) * Rv * Ew u + Fw w * Hw v * R := by
      rw [triMon]
      calc Fw w * Hw v * Ew u * f i
          = Fw w * (Hw v * (Ew u * f i)) := by simp only [mul_assoc]
        _ = Fw w * (Hw v * (f i * Ew u + R)) := by rw [hEq]
        _ = Fw w * (Hw v * (f i * Ew u)) + Fw w * (Hw v * R) := by simp only [mul_add]
        _ = Fw w * ((Hw v * f i) * Ew u) + Fw w * (Hw v * R) := by simp only [mul_assoc]
        _ = Fw w * ((f i * Rv) * Ew u) + Fw w * (Hw v * R) := by rw [hEqv]
        _ = Fw (w ++ [i]) * Rv * Ew u + Fw w * Hw v * R := by
              rw [Fw_append, Fw_singleton]
              simp only [mul_assoc]
    rw [key]
    exact Submodule.add_mem _ (T_mem_of_HwSpan (w ++ [i]) u hRv) (T_mem_of_T₀ w v hR)
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- The subalgebra of `U(e₈)` consisting of the elements that preserve `T` under right
multiplication. -/
def TRight : Subalgebra ℂ U where
  carrier := {u : U | ∀ x ∈ T, x * u ∈ T}
  zero_mem' := by intro x hx; rw [mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb x hx
    rw [mul_add]
    exact Submodule.add_mem _ (ha x hx) (hb x hx)
  mul_mem' := by
    intro a b ha hb x hx
    have h1 : x * a ∈ T := ha x hx
    have h2 : x * a * b ∈ T := hb (x * a) h1
    rwa [mul_assoc] at h2
  one_mem' := by intro x hx; simpa using hx
  algebraMap_mem' := by
    intro c x hx
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
    exact Submodule.smul_mem _ c hx

lemma mem_TRight (u : U) : u ∈ TRight ↔ ∀ x ∈ T, x * u ∈ T := Iff.rfl

/-- Every element of `ι(e₈)` lies in the subalgebra of right-preservers of `T`. -/
lemma iota_mem_TRight (x : L) : ι ℂ x ∈ TRight := by
  let N : LieSubalgebra ℂ L :=
    { carrier := {x : L | ι ℂ x ∈ TRight}
      zero_mem' := by
        change ι ℂ (0 : L) ∈ TRight
        rw [map_zero]
        exact (TRight).zero_mem
      add_mem' := by
        intro p q hp hq
        change ι ℂ (p + q) ∈ TRight
        rw [map_add]
        exact (TRight).add_mem hp hq
      smul_mem' := by
        intro c p hp
        change ι ℂ (c • p) ∈ TRight
        rw [map_smul]
        exact TRight.toSubmodule.smul_mem c hp
      lie_mem' := by
        intro p q hp hq
        change ι ℂ ⁅p, q⁆ ∈ TRight
        rw [LieHom.map_lie (ι ℂ) p q, LieRing.of_associative_ring_bracket]
        exact TRight.sub_mem (TRight.mul_mem hp hq) (TRight.mul_mem hq hp) }
  have hE : ∀ i : Fin 8, SerreE i ∈ N := fun i =>
    (mem_TRight (e i)).mpr (fun x hx => T_mul_e i hx)
  have hF : ∀ i : Fin 8, SerreF i ∈ N := fun i =>
    (mem_TRight (f i)).mpr (fun x hx => T_mul_f i hx)
  have hH : ∀ i : Fin 8, SerreH i ∈ N := fun i =>
    (mem_TRight (h i)).mpr (fun x hx => T_mul_h i hx)
  have hgen : ∀ g : Generators (Fin 8),
      LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ g) ∈ N := by
    intro g
    match g with
    | Generators.H i => exact hH i
    | Generators.E i => exact hE i
    | Generators.F i => exact hF i
  have htop : N = ⊤ := Submission.WordSpan.eq_top_of_generators N hgen
  have hx : x ∈ N := by rw [htop]; trivial
  exact hx

/-- **Triangular spanning.**  `U(e₈)` is spanned by the triangular monomials
`(F-word) * (H-word) * (E-word)`. -/
theorem T_eq_top : T = ⊤ := by
  have hle : (⊤ : Subalgebra ℂ U) ≤ TRight := by
    rw [← Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota]
    exact Algebra.adjoin_le (fun y hy => by obtain ⟨z, rfl⟩ := hy; exact iota_mem_TRight z)
  rw [eq_top_iff]
  intro u _
  have h1 : (1 : U) ∈ T := by
    have := triMon_mem_T ([] : List (Fin 8)) [] []
    simpa using this
  have hu : (1 : U) * u ∈ T := hle trivial 1 h1
  simpa using hu

/-- **Triangular spanning**, in the form used by the rest of the development: every element of
`U(e₈)` is a finite ℂ-linear combination of products `(F-word) * (H-word) * (E-word)`. -/
theorem span_triMon_eq_top :
    Submodule.span ℂ (Set.range (fun p : List (Fin 8) × List (Fin 8) × List (Fin 8) =>
      triMon p.1 p.2.1 p.2.2)) = ⊤ :=
  T_eq_top

end Submission.TriangularSpan

