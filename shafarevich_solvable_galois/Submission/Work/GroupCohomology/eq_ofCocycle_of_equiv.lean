/-
Copyright (c) 2025. All rights reserved.

# Equivalent extensions have equal classes in `H²`

This file proves that two `2`-cocycles `c`, `c'` whose associated group extensions
`Extension.ofCocycle Q A c` and `Extension.ofCocycle Q A c'` are isomorphic (as extensions of `Q`
by `A` with the prescribed action) define the same class in `H²(Q, A)`.

The mathematical content is the classical computation: an equivalence `φ` of the two extensions
is a group isomorphism `A × Q ≅ A × Q` (the twisted products) which is the identity on `A ⊂ A × Q`
and compatible with the projections to `Q`; writing `φ (a, q) = (a + F q, q)` the multiplicativity
of `φ` says precisely that `normCocycle c' - normCocycle c = -d¹ F`, hence the two (normalized)
cocycles differ by a coboundary.  Since `c - normCocycle c` and `c' - normCocycle c'` are also
coboundaries (namely `d¹ (fun q => c (q, 1))` and so on), `c - c'` is a coboundary, i.e. the
classes of `c` and `c'` in `H²` coincide.

## Main results

* `Work.GroupCohomology.sub_mem_B2_of_map` : the coordinate computation
* `Work.GroupCohomology.sub_mem_B2_of_equiv_ofNormalized` : the same for an extension equivalence
* `Work.GroupCohomology.eq_ofCocycle_of_equiv` : the statement of the file
-/
import Mathlib
import Submission.Work.GroupCohomology.Extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-! ## The quotient map `H²π` -/

/-- `H²π` is the quotient map `Z²(Q, A) → H²(Q, A)`, so two cocycles have the same image in `H²`
exactly when their difference is a coboundary. -/
theorem H2pi_eq_iff_coe (c c' : Z2 Q A) :
    H2π Q A c = H2π Q A c' ↔ ((c - c' : Z2 Q A) : Q × Q → A) ∈ B2 Q A := by
  rw [H2π, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_comap]
  rfl

/-! ## The normalization of a `2`-cocycle is cohomologous to it -/

/-- For any `2`-cochain `c`, the difference `c - normCocycle c` is a coboundary. -/
theorem sub_normCocycle_mem_B2 (c : Q × Q → A) (hc : c ∈ Z2 Q A) :
    c - normCocycle Q A c ∈ B2 Q A := by
  refine (mem_B2_iff Q A _).mpr ⟨fun q => c (q, 1), ?_⟩
  funext p
  obtain ⟨q, r⟩ := p
  rw [d1_apply, Pi.sub_apply, normCocycle_apply]
  rw [Z2.map_one_snd Q A hc (q * r), Z2.map_one_snd Q A hc q, Z2.map_one_snd Q A hc r, ← mul_smul]
  abel

/-! ## The coordinate computation -/

/-- **The coordinate computation.**  Let `c`, `c'` be `2`-cochains vanishing on `(1, ·)` and let
`Φ : A × Q → A × Q` be a multiplicative map between the corresponding twisted products, which is
the identity on `A × {1}` and compatible with the projections to `Q`.  Then `c' - c` is a
coboundary.

This is the heart of the classification of extensions by `H²`:  an equivalence of extensions is
given in coordinates by `(a, q) ↦ (a + F q, q)`, and multiplicativity forces
`c' (q, r) - c (q, r) = d¹(-F) (q, r)`. -/
theorem sub_mem_B2_of_map {c c' : Q × Q → A}
    (hc1 : ∀ q, c (1, q) = 0) (hc'1 : ∀ q, c' (1, q) = 0)
    (Φ : A × Q → A × Q) (hΦ1 : ∀ a : A, Φ (a, 1) = (a, 1))
    (hΦ2 : ∀ x : A × Q, (Φ x).2 = x.2)
    (hΦmul : ∀ x y : A × Q, Φ (twMul Q A c x y) = twMul Q A c' (Φ x) (Φ y)) :
    c' - c ∈ B2 Q A := by
  set F : Q → A := fun q => (Φ (0, q)).1 with hF
  have hform : ∀ x : A × Q, Φ x = (x.1 + F x.2, x.2) := by
    intro x
    have hx : twMul Q A c (x.1, 1) (0, x.2) = x := by
      refine Prod.ext ?_ ?_ <;> simp [twMul, hc1 x.2]
    calc Φ x = Φ (twMul Q A c (x.1, 1) (0, x.2)) := by rw [hx]
      _ = twMul Q A c' (Φ (x.1, 1)) (Φ (0, x.2)) := hΦmul _ _
      _ = twMul Q A c' (x.1, 1) (F x.2, x.2) := by
            rw [hΦ1]
            congr 1
            exact Prod.ext rfl (hΦ2 (0, x.2))
      _ = (x.1 + F x.2, x.2) := by simp [twMul, hc'1 x.2]
  refine (mem_B2_iff Q A _).mpr ⟨fun q => -F q, ?_⟩
  funext p
  obtain ⟨q, r⟩ := p
  have h2 := hΦmul (0, q) (0, r)
  rw [hform (twMul Q A c (0, q) (0, r)), hform (0, q), hform (0, r)] at h2
  simp only [twMul, zero_add, smul_zero] at h2
  have h2' : c (q, r) + F (q * r) = F q + q • F r + c' (q, r) := by
    simpa using congrArg Prod.fst h2
  have h4 : c' (q, r) = c (q, r) + F (q * r) - F q - q • F r := by
    rw [h2']; abel
  simp only [d1_apply, Pi.sub_apply]
  rw [h4, smul_neg]
  abel

/-! ## From an equivalence of extensions to a coboundary -/

/-- If the extensions attached to the normalized `2`-cocycles `c` and `c'` are equivalent, then
`c' - c` is a coboundary. -/
theorem sub_mem_B2_of_equiv_ofNormalized {c c' : Q × Q → A}
    (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0) (hc' : c' ∈ Z2 Q A) (h1' : c' (1, 1) = 0)
    (φ : Extension.Equiv (Extension.ofNormalized Q A c hc h1)
      (Extension.ofNormalized Q A c' hc' h1')) :
    c' - c ∈ B2 Q A := by
  let X : Extension Q A := Extension.ofNormalized Q A c hc h1
  let Y : Extension Q A := Extension.ofNormalized Q A c' hc' h1'
  letI : Group X.E := X.groupE
  letI : Group Y.E := Y.groupE
  have hψ : X.ext.Equiv Y.ext := φ
  let Φ : X.E → Y.E := fun x => hψ x
  have hΦ1 : ∀ a : A, Φ (a, 1) = (a, 1) := by
    intro a
    have h := GroupExtension.Equiv.map_inl hψ (Multiplicative.ofAdd a)
    rw [show X.ext.inl (Multiplicative.ofAdd a) = (a, 1) from rfl,
        show Y.ext.inl (Multiplicative.ofAdd a) = (a, 1) from rfl] at h
    exact h
  have hΦ2 : ∀ x : A × Q, (Φ x).2 = x.2 := by
    intro x
    have h := GroupExtension.Equiv.rightHom_map hψ (x : X.E)
    rw [show Y.ext.rightHom (Φ (x : X.E)) = (Φ (x : X.E)).2 from rfl,
        show X.ext.rightHom (x : X.E) = (x : X.E).2 from rfl] at h
    exact h
  have hΦmul : ∀ x y : A × Q, Φ (twMul Q A c x y) = twMul Q A c' (Φ x) (Φ y) := by
    intro x y
    have hmul := @MulEquivClass.map_mul (X.ext.Equiv Y.ext) X.E Y.E
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) hψ (x : X.E) (y : X.E)
    have key1 : @Mul.mul X.E (inferInstance) (x : X.E) (y : X.E) = twMul Q A c x y := rfl
    have key2 : @Mul.mul Y.E (inferInstance) (hψ (x : X.E)) (hψ (y : X.E))
        = twMul Q A c' (Φ x) (Φ y) := rfl
    rw [← key1, ← key2]
    exact hmul
  exact sub_mem_B2_of_map (fun q => by rw [Z2.map_one_fst Q A hc q, h1])
    (fun q => by rw [Z2.map_one_fst Q A hc' q, h1']) Φ hΦ1 hΦ2 hΦmul

/-! ## The main statement -/

theorem eq_ofCocycle_of_equiv {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c c' : Work.GroupCohomology.Z2 Q A)
    (h : Nonempty (Work.GroupCohomology.Extension.Equiv
      (Work.GroupCohomology.Extension.ofCocycle Q A c)
      (Work.GroupCohomology.Extension.ofCocycle Q A c'))) :
    Work.GroupCohomology.H2π Q A c = Work.GroupCohomology.H2π Q A c' := by
  obtain ⟨φ⟩ := h
  have hsub : normCocycle Q A (c' : Q × Q → A) - normCocycle Q A (c : Q × Q → A) ∈ B2 Q A :=
    sub_mem_B2_of_equiv_ofNormalized (normCocycle_mem Q A (c : Q × Q → A) c.2)
      (normCocycle_one Q A (c : Q × Q → A)) (normCocycle_mem Q A (c' : Q × Q → A) c'.2)
      (normCocycle_one Q A (c' : Q × Q → A)) φ
  have hA : ((c : Q × Q → A) - normCocycle Q A (c : Q × Q → A)) ∈ B2 Q A :=
    sub_normCocycle_mem_B2 (c : Q × Q → A) c.2
  have hB : ((c' : Q × Q → A) - normCocycle Q A (c' : Q × Q → A)) ∈ B2 Q A :=
    sub_normCocycle_mem_B2 (c' : Q × Q → A) c'.2
  refine (H2pi_eq_iff_coe c c').mpr ?_
  show ((c : Q × Q → A) - (c' : Q × Q → A)) ∈ B2 Q A
  have hdecomp : ((c : Q × Q → A) - (c' : Q × Q → A))
      = ((c : Q × Q → A) - normCocycle Q A (c : Q × Q → A))
        - (normCocycle Q A (c' : Q × Q → A) - normCocycle Q A (c : Q × Q → A))
        - ((c' : Q × Q → A) - normCocycle Q A (c' : Q × Q → A)) := by abel
  rw [hdecomp]
  exact sub_mem (sub_mem hA hsub) hB

end Work.GroupCohomology
