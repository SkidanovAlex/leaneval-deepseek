import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch.Aquot

open Work.CurveBasics
open Work.RiemannRoch.Curve

noncomputable section

variable {k : Type u} [Field k]

/-! ## The `Q`-component of `A(D + [Q])` -/

theorem add_place_apply_same {C : Curve k} (D : C.Div) (Q : C.Place) :
    (D + Curve.Div.place Q) Q = D Q + 1 := by
  rw [Curve.Div.place, Finsupp.add_apply, Finsupp.single_eq_same]

theorem add_place_apply_of_ne {C : Curve k} (D : C.Div) {P Q : C.Place} (h : P ≠ Q) :
    (D + Curve.Div.place Q) P = D P := by
  rw [Curve.Div.place, Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero]

/-- Membership in `A(D + [Q])` in terms of the `Q`-component and all the others. -/
theorem mem_A_add_place_iff {C : Curve k} (D : C.Div) (Q : C.Place)
    (x : C.Place → C.functionField) :
    x ∈ A C (D + Curve.Div.place Q) ↔
      x Q ∈ localIdeal C Q (D Q + 1) ∧ ∀ P, P ≠ Q → x P ∈ localIdeal C P (D P) := by
  rw [mem_A]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [mem_localIdeal]
      rcases h Q with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rwa [add_place_apply_same] at h0)
    · intro P hP
      rw [mem_localIdeal]
      rcases h P with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rwa [add_place_apply_of_ne D hP] at h0)
  · rintro ⟨hQ, hrest⟩ P
    rcases mem_localIdeal.mp hQ with h0 | h0
    · by_cases hP : P = Q
      · rw [hP, add_place_apply_same]; exact Or.inl h0
      · rw [add_place_apply_of_ne D hP]
        rcases mem_localIdeal.mp (hrest P hP) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
    · by_cases hP : P = Q
      · rw [hP, add_place_apply_same]; exact Or.inr h0
      · rw [add_place_apply_of_ne D hP]
        rcases mem_localIdeal.mp (hrest P hP) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1

/-- The projection of `A(D + [Q])` to its `Q`-component. -/
def projQ (C : Curve k) (D : C.Div) (Q : C.Place) :
    ↥(A C (D + Curve.Div.place Q)) →ₗ[k] ↥(localIdeal C Q (D Q + 1)) where
  toFun x := ⟨x.1 Q, ((mem_A_add_place_iff D Q x.1).mp x.2).1⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

theorem projQ_surjective (C : Curve k) (D : C.Div) (Q : C.Place) :
    Function.Surjective (projQ C D Q) := by
  intro y
  have hmem : (fun P => if P = Q then (y : C.functionField) else 0)
      ∈ A C (D + Curve.Div.place Q) := by
    rw [mem_A_add_place_iff D Q]
    constructor
    · simp
    · intro P hP
      simp [hP]
  refine ⟨⟨fun P => if P = Q then (y : C.functionField) else 0, hmem⟩, ?_⟩
  apply Subtype.ext
  simp [projQ]

/-- The composite of `projQ` with the quotient map. -/
def aquotProj (C : Curve k) (D : C.Div) (Q : C.Place) :
    ↥(A C (D + Curve.Div.place Q)) →ₗ[k]
      (↥(localIdeal C Q (D Q + 1)) ⧸
        (localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + 1)).subtype) :=
  (Submodule.mkQ _).comp (projQ C D Q)

theorem aquotProj_ker (C : Curve k) (D : C.Div) (Q : C.Place) :
    (aquotProj C D Q).ker = (A C D).comap (A C (D + Curve.Div.place Q)).subtype := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  have key : (aquotProj C D Q) x = 0 ↔ x.1 Q ∈ localIdeal C Q (D Q) := by
    rw [aquotProj, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    rfl
  rw [key]
  constructor
  · intro h
    rw [mem_A]
    intro P
    by_cases hP : P = Q
    · rw [hP]
      rcases mem_localIdeal.mp h with h0 | h0
      · exact Or.inl h0
      · exact Or.inr h0
    · rcases mem_localIdeal.mp (((mem_A_add_place_iff D Q x.1).mp x.2).2 P hP) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr h0
  · intro h
    rw [mem_A] at h
    rcases h Q with h0 | h0
    · rw [mem_localIdeal]; exact Or.inl h0
    · rw [mem_localIdeal]; exact Or.inr h0

/-- **Only the `Q`-component matters.**  The quotient `A(D + [Q])/A(D)` is the local quotient
`I_Q(D Q + 1)/I_Q(D Q)` of fractional ideals at `Q`. -/
theorem rank_Aquot_eq_localIdeal (C : Curve k) (D : C.Div) (Q : C.Place) :
    Module.rank k (Aquot C D (D + Curve.Div.place Q)) =
      Module.rank k (↥(localIdeal C Q (D Q + 1)) ⧸
        (localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + 1)).subtype) := by
  have hsurj : Function.Surjective (aquotProj C D Q) := by
    intro y
    obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
      ((localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + 1)).subtype) y
    obtain ⟨x, hx⟩ := projQ_surjective C D Q z
    exact ⟨x, by rw [aquotProj, LinearMap.comp_apply, hx, hz]⟩
  have hrange : (aquotProj C D Q).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h1 : Module.rank k (Aquot C D (D + Curve.Div.place Q)) =
      Module.rank k (↥(A C (D + Curve.Div.place Q)) ⧸ (aquotProj C D Q).ker) :=
    (Submodule.quotEquivOfEq _ _ (aquotProj_ker C D Q).symm).rank_eq
  calc Module.rank k (Aquot C D (D + Curve.Div.place Q))
      = Module.rank k (↥(A C (D + Curve.Div.place Q)) ⧸ (aquotProj C D Q).ker) := h1
    _ = Module.rank k ↥(aquotProj C D Q).range :=
        (LinearMap.quotKerEquivRange (aquotProj C D Q)).rank_eq
    _ = Module.rank k (↥(localIdeal C Q (D Q + 1)) ⧸
          (localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + 1)).subtype) := by
        rw [hrange]
        exact (Submodule.topEquiv
          (M := (↥(localIdeal C Q (D Q + 1)) ⧸
            (localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + 1)).subtype))).rank_eq

/-! ## The one-step local quotient `I_Q(j)/I_Q(j-1)` -/

theorem rank_localIdeal_quotient_succ (C : Curve k) (Q : C.Place) (j : ℤ) :
    Module.rank k (↥(localIdeal C Q j) ⧸
        (localIdeal C Q (j - 1)).comap (localIdeal C Q j).subtype)
      = ((Q.degree : ℕ) : Cardinal) := by
  classical
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  letI : Algebra k (C.left.presheaf.stalk Q.point) := Linear.instAlgebraStalk C Q
  haveI hST : IsScalarTower k (C.left.presheaf.stalk Q.point) C.functionField :=
    Linear.isScalarTower_stalk_field C Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (C.left.presheaf.stalk Q.point)
  have hϖ_ne : algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero ((FaithfulSMul.algebraMap_injective _ _) (by rw [h, map_zero]))
  let w : C.functionField := (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ^ j
  have hw_eq : w = (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ^ j := rfl
  have hw_ne : w ≠ 0 := by
    rw [hw_eq]; exact zpow_ne_zero j hϖ_ne
  have hordw : C.ordAt w Q = j := by
    rw [hw_eq]
    exact Linear.ord_zpow_uniformizer C Q hϖ j
  have hordFrac_w : Ring.ordFrac (C.left.presheaf.stalk Q.point) w = WithZero.exp j := by
    rw [hw_eq, map_zpow₀, Ring.ordFrac_irreducible hϖ, ← WithZero.exp_zsmul j (1 : ℤ)]
    have h : j • (1 : ℤ) = j := by simp
    rw [h]
  -- the `k`-linear isomorphism `O_{C,Q} ≃ₗ I_Q(0)`
  let ι : (C.left.presheaf.stalk Q.point) →ₗ[k] C.functionField :=
    (IsScalarTower.toAlgHom k (C.left.presheaf.stalk Q.point) C.functionField).toLinearMap
  have hι_apply (a : C.left.presheaf.stalk Q.point) :
      ι a = algebraMap (C.left.presheaf.stalk Q.point) C.functionField a := rfl
  have hι_inj : Function.Injective ι := by
    intro a b hab
    exact FaithfulSMul.algebraMap_injective _ _ (by simpa only [hι_apply] using hab)
  have hι_mem : ∀ a : C.left.presheaf.stalk Q.point, ι a ∈ localIdeal C Q 0 := by
    intro a
    rw [mem_localIdeal, hι_apply]
    by_cases ha : a = 0
    · exact Or.inl (by rw [ha, map_zero])
    · refine Or.inr ?_
      have hane : algebraMap (C.left.presheaf.stalk Q.point) C.functionField a ≠ 0 :=
        fun h => ha (FaithfulSMul.algebraMap_injective _ _ (by rw [h, map_zero]))
      have h1 : 1 ≤ Ring.ordFrac (C.left.presheaf.stalk Q.point)
          (algebraMap (C.left.presheaf.stalk Q.point) C.functionField a) :=
        Ring.ordFrac_ge_one_of_ne_zero ha
      have h2 : 0 ≤ C.ordAt (algebraMap (C.left.presheaf.stalk Q.point) C.functionField a) Q :=
        (Linear.le_ord_iff_ordFrac C Q _ hane).mpr h1
      simpa only [Curve.ordAt, neg_zero] using h2
  have hsurjι : Function.Surjective (ι.codRestrict (localIdeal C Q 0) hι_mem) := by
    intro y
    by_cases hy0 : (y : C.functionField) = 0
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [hy0]
    · have hyord : 0 ≤ Scheme.ord (y : C.functionField) Q.point := by
        rcases mem_localIdeal.mp y.2 with h | h
        · exact absurd h hy0
        · simpa using h
      obtain ⟨a, ha⟩ := Linear.exists_algebraMap_eq_of_one_le_ordFrac
        ((Linear.le_ord_iff_ordFrac C Q _ hy0).mp hyord)
      exact ⟨a, by
        apply Subtype.ext
        simpa only [LinearMap.codRestrict_apply, hι_apply] using ha⟩
  let e : (C.left.presheaf.stalk Q.point) ≃ₗ[k] ↥(localIdeal C Q 0) :=
    LinearEquiv.ofBijective (ι.codRestrict (localIdeal C Q 0) hι_mem)
      ⟨fun a b hab =>
        hι_inj (by simpa only [LinearMap.codRestrict_apply] using congrArg Subtype.val hab),
        hsurjι⟩
  have he_apply (a : C.left.presheaf.stalk Q.point) :
      ((e a : ↥(localIdeal C Q 0)) : C.functionField) =
        algebraMap (C.left.presheaf.stalk Q.point) C.functionField a := rfl
  have he_symm (y : ↥(localIdeal C Q 0)) :
      algebraMap (C.left.presheaf.stalk Q.point) C.functionField (e.symm y) =
        (y : C.functionField) := by
    have h := he_apply (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  -- the residue map as a `k`-linear map
  let ρ : (C.left.presheaf.stalk Q.point) →ₗ[k] C.left.residueField Q.point :=
    { toFun := fun a => (C.left.residue Q.point).hom a
      map_add' := fun a b => (C.left.residue Q.point).hom.map_add a b
      map_smul' := fun c a => by
        rw [Algebra.smul_def c a, (C.left.residue Q.point).hom.map_mul,
          show (C.left.residue Q.point).hom
              (algebraMap k (C.left.presheaf.stalk Q.point) c) =
            algebraMap k (C.left.residueField Q.point) c from Linear.residue_algebraMap_eq C Q c,
          Algebra.smul_def ((RingHom.id k) c) ((C.left.residue Q.point).hom a), RingHom.id_apply] }
  -- multiplication by `w`
  let θ : C.functionField →ₗ[k] C.functionField := LinearMap.mulLeft k w
  have hθ_apply (y : C.functionField) : θ y = w * y := LinearMap.mulLeft_apply k w y
  have hV' : ∀ x : ↥(localIdeal C Q j), θ (x : C.functionField) ∈ localIdeal C Q 0 := by
    intro x
    rw [mem_localIdeal, hθ_apply]
    by_cases hx0 : (x : C.functionField) = 0
    · exact Or.inl (by rw [hx0, mul_zero])
    · refine Or.inr ?_
      have hxord : -j ≤ C.ordAt (x : C.functionField) Q := by
        rcases mem_localIdeal.mp x.2 with h | h
        · exact absurd h hx0
        · exact h
      rw [C.ordAt_mul hw_ne hx0 Q, hordw]
      linarith
  let μ : ↥(localIdeal C Q j) →ₗ[k] ↥(localIdeal C Q 0) :=
    (θ.comp (localIdeal C Q j).subtype).codRestrict _ hV'
  let Φ : ↥(localIdeal C Q j) →ₗ[k] C.left.residueField Q.point :=
    ρ.comp (e.symm.toLinearMap.comp μ)
  have hΦ (x : ↥(localIdeal C Q j)) :
      Φ x = (C.left.residue Q.point).hom (e.symm (μ x)) := rfl
  have hker : Φ.ker = (localIdeal C Q (j - 1)).comap (localIdeal C Q j).subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    by_cases hx0 : (x : C.functionField) = 0
    · have hx : x = 0 := Subtype.ext hx0
      rw [hx, map_zero, mem_localIdeal]
      simp
    · have hxord : -j ≤ C.ordAt (x : C.functionField) Q := by
        rcases mem_localIdeal.mp x.2 with h | h
        · exact absurd h hx0
        · exact h
      have hwx : Ring.ordFrac (C.left.presheaf.stalk Q.point) (w * (x : C.functionField))
          = WithZero.exp (j + C.ordAt (x : C.functionField) Q) := by
        rw [map_mul, hordFrac_w, Linear.ordFrac_eq_exp_ord C Q _ hx0, ← WithZero.exp_add]
      have ha_val : algebraMap (C.left.presheaf.stalk Q.point) C.functionField (e.symm (μ x))
          = w * (x : C.functionField) := by
        rw [he_symm]
        rfl
      rw [hΦ x]
      change IsLocalRing.residue (C.left.presheaf.stalk Q.point) (e.symm (μ x)) = 0 ↔
        (x : C.functionField) ∈ localIdeal C Q (j - 1)
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
      change (¬ IsUnit (e.symm (μ x))) ↔
        (x : C.functionField) ∈ localIdeal C Q (j - 1)
      rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := C.functionField), ha_val,
        hwx, ← WithZero.exp_zero, WithZero.exp_inj, mem_localIdeal]
      constructor
      · intro h
        refine Or.inr ?_
        simp only [Curve.ordAt] at h hxord ⊢
        omega
      · rintro (h0 | h0)
        · exact absurd h0 hx0
        · simp only [Curve.ordAt] at h0 ⊢
          omega
  have hsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c
    have hmem : w⁻¹ * (e a : C.functionField) ∈ localIdeal C Q j := by
      rw [mem_localIdeal]
      by_cases hy0 : (e a : C.functionField) = 0
      · exact Or.inl (by rw [hy0, mul_zero])
      · refine Or.inr ?_
        have h1 : 0 ≤ C.ordAt (e a : C.functionField) Q := by
          rcases mem_localIdeal.mp (e a).2 with h | h
          · exact absurd h hy0
          · exact h
        have h2 : C.ordAt (w⁻¹ : C.functionField) Q = -j := by
          rw [C.ordAt_inv hw_ne Q, hordw]
        rw [C.ordAt_mul (inv_ne_zero hw_ne) hy0 Q, h2]
        linarith
    refine ⟨⟨w⁻¹ * (e a : C.functionField), hmem⟩, ?_⟩
    have hsub : μ ⟨w⁻¹ * (e a : C.functionField), hmem⟩ = e a := by
      apply Subtype.ext
      show θ (w⁻¹ * (e a : C.functionField)) = (e a : C.functionField)
      rw [hθ_apply, ← mul_assoc, mul_inv_cancel₀ hw_ne, one_mul]
    rw [hΦ, hsub, LinearEquiv.symm_apply_apply]
    exact ha
  haveI : Module.Finite k (C.left.residueField Q.point) :=
    Linear.finiteDimensional_residueField C Q
  have hrange : Φ.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  calc Module.rank k (↥(localIdeal C Q j) ⧸
        (localIdeal C Q (j - 1)).comap (localIdeal C Q j).subtype)
      = Module.rank k (↥(localIdeal C Q j) ⧸ Φ.ker) := by rw [hker]
    _ = Module.rank k ↥Φ.range := (LinearMap.quotKerEquivRange Φ).rank_eq
    _ = Module.rank k (C.left.residueField Q.point) := by
        rw [hrange]
        exact (Submodule.topEquiv (M := C.left.residueField Q.point)).rank_eq
    _ = ((Q.degree : ℕ) : Cardinal) := by
        rw [← Module.finrank_eq_rank k (C.left.residueField Q.point),
          Place.degree_eq_finrank Q]

theorem rank_Aquot_place {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (D : C.Div)
    (Q : C.Place) :
    Module.rank k (Work.RiemannRoch.Curve.Aquot C D (D + Work.CurveBasics.Curve.Div.place Q))
      = ((Q.degree : ℕ) : Cardinal) := by
  rw [rank_Aquot_eq_localIdeal C D Q]
  have h := rank_localIdeal_quotient_succ C Q (D Q + 1)
  have hidx : D Q + 1 - 1 = D Q := by ring
  rwa [hidx] at h

end

end Work.RiemannRoch.Aquot
