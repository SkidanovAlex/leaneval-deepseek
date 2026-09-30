import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Basic.Sections
import Submission.Work.CurveBasics.Divisor
import Submission.Work.CurveBasics.Place
import Submission.Work.CurveBasics.Place.isDiscreteValuationRing
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Place.residueDegree_pos
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Linear.mul_mem_L_iff
import Submission.Work.CurveBasics.Linear.div_neg_of_not_regular

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics.Linear

open Work.CurveBasics

noncomputable section

/-- The `k`-algebra structure on the local ring `O_{C,Q}` of a curve at a place, induced by the
structure morphism `C ⟶ Spec k` together with the identification `k ≅ Γ(Spec k, ⊤)`. -/
local instance instAlgebraStalk {k : Type u} [Field k] (C : Curve k) (Q : C.Place) :
    Algebra k (C.left.presheaf.stalk Q.point) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop ≫
    C.left.presheaf.germ (⊤ : C.left.Opens) Q.point trivial).hom.toAlgebra

lemma algebraMap_stalk_eq {k : Type u} [Field k] (C : Curve k) (Q : C.Place) (c : k) :
    algebraMap k (C.left.presheaf.stalk Q.point) c =
      C.left.presheaf.germ (⊤ : C.left.Opens) Q.point trivial
        (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := rfl

/-- `0 ≤ ord_Q y` is `1 ≤ ordFrac` of the local ring, for `y ≠ 0`. -/
lemma le_ord_iff_ordFrac {k : Type u} [Field k] (C : Curve k) (Q : C.Place)
    (y : C.functionField) (hy : y ≠ 0) :
    0 ≤ Scheme.ord y Q.point ↔ 1 ≤ Ring.ordFrac (C.left.presheaf.stalk Q.point) y := by
  rw [Scheme.le_ord_iff Q.eq_coheight_one hy]
  exact Iff.rfl

/-- `ordFrac` of a nonzero function is the exponential of its order of vanishing at `Q`. -/
lemma ordFrac_eq_exp_ord {k : Type u} [Field k] (C : Curve k) (Q : C.Place)
    (y : C.functionField) (hy : y ≠ 0) :
    Ring.ordFrac (C.left.presheaf.stalk Q.point) y =
      WithZero.exp (Scheme.ord y Q.point) :=
  (Scheme.ord_eq_iff Q.eq_coheight_one hy (n := Scheme.ord y Q.point)).mp rfl

lemma isScalarTower_stalk_field {k : Type u} [Field k] (C : Curve k) (Q : C.Place) :
    IsScalarTower k (C.left.presheaf.stalk Q.point) C.functionField := by
  haveI : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [algebraMap_stalk_eq C Q c,
    Scheme.algebraMap_germ_eq_germToFunctionField (X := C.left) (U := ⊤) (x := Q.point) trivial]
  simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]

/-- The image of `c : k` under `k → κ(Q)` is the residue of the germ of the corresponding
constant section of `C`. -/
lemma algebraMap_residueField_eq {k : Type u} [Field k] (C : Curve k) (Q : C.Place) (c : k) :
    algebraMap k (C.left.residueField Q.point) c =
      C.left.residue Q.point (C.left.presheaf.germ (⊤ : C.left.Opens) Q.point trivial
        (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) := by
  simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  rw [Scheme.Γevaluation_naturality_apply]
  rfl

lemma residue_algebraMap_eq {k : Type u} [Field k] (C : Curve k) (Q : C.Place) (c : k) :
    IsLocalRing.residue (C.left.presheaf.stalk Q.point)
        (algebraMap k (C.left.presheaf.stalk Q.point) c) =
      algebraMap k (C.left.residueField Q.point) c := by
  rw [algebraMap_stalk_eq C Q c, algebraMap_residueField_eq C Q c]
  rfl

/-- The residue field of a place is finite dimensional over `k`. -/
theorem finiteDimensional_residueField {k : Type u} [Field k] (C : Curve k) (Q : C.Place) :
    FiniteDimensional k (C.left.residueField Q.point) :=
  FiniteDimensional.of_finrank_pos (by
    rw [← Place.degree_eq_finrank Q]
    exact Place.residueDegree_pos Q)

/-- Constants of a curve are regular at every place. -/
lemma algebraMap_mem_valuationSubring_place {k : Type u} [Field k] (C : Curve k) (Q : C.Place)
    (c : k) : algebraMap k C.functionField c ∈ Q.valuationSubring :=
  (Place.mem_valuationSubring_iff C Q _).mpr
    (le_of_eq (Work.CurveBasics.Order.ordAt_algebraMap_eq_zero C c Q).symm)

/-- For a uniformizer `ϖ` of the local ring, `ord_Q (ϖ^m) = m`. -/
lemma ord_zpow_uniformizer {k : Type u} [Field k] (C : Curve k) (Q : C.Place)
    {ϖ : C.left.presheaf.stalk Q.point} (hϖ : Irreducible ϖ) (m : ℤ) :
    Scheme.ord ((algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ^ m) Q.point
      = m := by
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  have hu : (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ≠ 0 := by
    intro h
    exact hϖ.ne_zero ((FaithfulSMul.algebraMap_injective _ _) (by rw [h, map_zero]))
  have hw : (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ^ m ≠ 0 :=
    zpow_ne_zero m hu
  rw [Scheme.ord_eq_iff Q.eq_coheight_one hw]
  show Ring.ordFrac (C.left.presheaf.stalk Q.point)
      ((algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ^ m) = _
  rw [map_zpow₀, Ring.ordFrac_irreducible hϖ, ← WithZero.exp_zsmul m (1 : ℤ)]
  have h : m • (1 : ℤ) = m := by simp
  rw [h, WithZero.exp_eq_coe_ofAdd]


/-- **Local Riemann–Roch step.** Adding a single place to a divisor increases the dimension of
`L` by at most the degree of the place: the quotient `L (D + [Q]) / L D` is finite dimensional
over `k`, of dimension at most `[κ(Q) : k] = Q.degree`.

Proof sketch: let `ϖ` be a uniformizer of the discrete valuation ring `O_{C,Q}`
(`Place.isDiscreteValuationRing`, `IsDiscreteValuationRing.exists_irreducible`), and set
`n := D Q + 1`.  For `x ∈ L (D + [Q])` the element `ϖ ^ n * x` has order `≥ 0` at `Q`, so it lies
in `O_{C,Q}`, and `x ↦ (ϖ ^ n * x) mod 𝔪_Q ∈ κ(Q)` is `k`-linear with kernel exactly `L D`
(using `Scheme.ord`/`Ring.ordFrac`, `Curve.div_apply`, `Scheme.ord_mul` and the fact that the
order of an element of the local ring is `≥ 0`).  Hence the quotient embeds into `κ(Q)`, whose
`k`-dimension is `Q.degree` (`Work.CurveBasics.Place.degree_eq_finrank`). -/
theorem finrank_quotient_add_place {k : Type*} [Field k] (C : Curve k) (D : C.Div)
    (Q : C.Place) :
    FiniteDimensional k (C.L (D + Curve.Div.place Q)
        ⧸ Submodule.comap (C.L (D + Curve.Div.place Q)).subtype (C.L D)) ∧
      Module.finrank k (C.L (D + Curve.Div.place Q)
        ⧸ Submodule.comap (C.L (D + Curve.Div.place Q)).subtype (C.L D)) ≤ Q.degree := by
  classical
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  haveI hST : IsScalarTower k (C.left.presheaf.stalk Q.point) C.functionField :=
    isScalarTower_stalk_field C Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (C.left.presheaf.stalk Q.point)
  have hu_ne : (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ≠ 0 := by
    intro h
    exact hϖ.ne_zero ((FaithfulSMul.algebraMap_injective _ _) (by rw [h, map_zero]))
  set n : ℤ := D Q + 1 with hn
  -- the multiplier `w = ϖ^n`
  let w : C.functionField := (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ^ n
  have hw_ne : w ≠ 0 := by
    dsimp only [w]
    exact zpow_ne_zero n hu_ne
  have hordw : Scheme.ord w Q.point = n := by
    dsimp only [w]
    exact ord_zpow_uniformizer C Q hϖ n
  have hordFrac_w : Ring.ordFrac (C.left.presheaf.stalk Q.point) w = WithZero.exp n := by
    dsimp only [w]
    rw [map_zpow₀, Ring.ordFrac_irreducible hϖ, ← WithZero.exp_zsmul n (1 : ℤ)]
    have h : n • (1 : ℤ) = n := by simp
    rw [h, WithZero.exp_eq_coe_ofAdd]
  -- the linear map `ι : O_{C,Q} → K` given by `algebraMap`
  let ι : (C.left.presheaf.stalk Q.point) →ₗ[k] C.functionField :=
    (IsScalarTower.toAlgHom k (C.left.presheaf.stalk Q.point) C.functionField).toLinearMap
  have hι_apply (a : C.left.presheaf.stalk Q.point) : ι a = algebraMap _ _ a := rfl
  have hι_inj : Function.Injective ι := by
    intro a b hab
    exact FaithfulSMul.algebraMap_injective _ _ (by simpa only [hι_apply] using hab)
  -- the submodule of functions regular at `Q`
  obtain ⟨Vsub, hVsub_mem, hVsub_ord⟩ : ∃ Vsub : Submodule k C.functionField,
      (∀ y, y ∈ Vsub ↔ y ∈ Q.valuationSubring) ∧
      (∀ y, y ∈ Vsub ↔ 0 ≤ Scheme.ord y Q.point) :=
    ⟨{ carrier := ↑Q.valuationSubring.toSubring,
       zero_mem' := Subring.zero_mem _,
       add_mem' := by intro a b ha hb; exact Subring.add_mem _ ha hb,
       smul_mem' := by
         intro c a ha
         rw [Algebra.smul_def]
         exact Subring.mul_mem _
           ((ValuationSubring.mem_toSubring _ _).mpr (algebraMap_mem_valuationSubring_place C Q c)) ha },
     fun y => ValuationSubring.mem_toSubring _ y,
     fun y => (ValuationSubring.mem_toSubring _ y).trans (Place.mem_valuationSubring_iff C Q y)⟩
  have hι_mem (a : C.left.presheaf.stalk Q.point) : ι a ∈ Vsub := by
    rw [hVsub_ord, hι_apply]
    by_cases ha : a = 0
    · rw [ha, map_zero]; simp
    · have hane : (algebraMap (C.left.presheaf.stalk Q.point) C.functionField a) ≠ 0 :=
        fun h => ha ((FaithfulSMul.algebraMap_injective _ _) (by rw [h, map_zero]))
      exact (le_ord_iff_ordFrac C Q _ hane).mpr (Ring.ordFrac_ge_one_of_ne_zero ha)
  have hsurj : Function.Surjective (ι.codRestrict Vsub hι_mem) := by
    intro y
    by_cases hy0 : (y : C.functionField) = 0
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [LinearMap.codRestrict_apply, hι_apply, hy0]
    · have hyord : 0 ≤ Scheme.ord (y : C.functionField) Q.point := (hVsub_ord _).mp y.2
      have h1 : 1 ≤ Ring.ordFrac _ (y : C.functionField) :=
        (le_ord_iff_ordFrac C Q _ hy0).mp hyord
      obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_one_le_ordFrac h1
      exact ⟨a, by
        apply Subtype.ext
        simpa only [LinearMap.codRestrict_apply, hι_apply] using ha⟩
  let e : (C.left.presheaf.stalk Q.point) ≃ₗ[k] ↥Vsub :=
    LinearEquiv.ofBijective (ι.codRestrict Vsub hι_mem)
      ⟨fun a b hab => hι_inj (by simpa only [LinearMap.codRestrict_apply] using congrArg Subtype.val hab),
        hsurj⟩
  have he_apply (a : C.left.presheaf.stalk Q.point) :
      ((e a : ↥Vsub) : C.functionField) = algebraMap _ _ a := by
    dsimp only [e]
    rfl
  have he_symm (y : ↥Vsub) : algebraMap _ _ (e.symm y) = (y : C.functionField) := by
    have h := he_apply (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  -- the residue map as a `k`-linear map
  let ρ : (C.left.presheaf.stalk Q.point) →ₗ[k] C.left.residueField Q.point :=
    { toFun := fun a => (C.left.residue Q.point).hom a
      map_add' := fun a b => (C.left.residue Q.point).hom.map_add a b
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul, Algebra.smul_def,
          show (C.left.residue Q.point).hom (algebraMap k (C.left.presheaf.stalk Q.point) c)
              = algebraMap k (C.left.residueField Q.point) c from residue_algebraMap_eq C Q c] }
  -- multiplication by `w`
  let θ : C.functionField →ₗ[k] C.functionField := LinearMap.mulLeft k w
  have hθ_apply (y : C.functionField) : θ y = w * y := rfl
  have hV' : ∀ x : ↥(C.L (D + Curve.Div.place Q)),
      (θ.comp (C.L (D + Curve.Div.place Q)).subtype) x ∈ Vsub := by
    intro x
    rw [hVsub_ord]
    show 0 ≤ Scheme.ord (w * (x : C.functionField)) Q.point
    by_cases hx0 : (x : C.functionField) = 0
    · rw [hx0, mul_zero]; simp
    · rw [Scheme.ord_mul hw_ne hx0, hordw]
      have hxM : (x : C.functionField) ∈ C.L (D + Curve.Div.place Q) := x.2
      have h1 : -(((D + Curve.Div.place Q) Q)) ≤ Scheme.ord (x : C.functionField) Q.point := by
        rw [Curve.mem_L_iff] at hxM
        rcases hxM with h0 | heff
        · exact absurd h0 hx0
        · exact (C.isEffective_div_add_iff).mp heff Q
      have h2 : (D + Curve.Div.place Q) Q = D Q + 1 := by
        simp only [Curve.Div.place, Finsupp.add_apply, Finsupp.single_eq_same, add_zero]
      rw [h2] at h1
      rw [hn]
      linarith
  -- the map `Φ`
  let Φ : ↥(C.L (D + Curve.Div.place Q)) →ₗ[k] C.left.residueField Q.point :=
    (ρ.comp e.symm.toLinearMap).comp
      ((θ.comp (C.L (D + Curve.Div.place Q)).subtype).codRestrict Vsub hV')
  have hΦ_apply (x : ↥(C.L (D + Curve.Div.place Q))) :
      Φ x = (C.left.residue Q.point).hom
        (e.symm ⟨(θ.comp (C.L (D + Curve.Div.place Q)).subtype) x, hV' x⟩) := rfl
  -- for `x ∈ L (D + [Q])` with `x ≠ 0`, membership in `L D` is the condition `ord_Q x ≥ -D Q`
  have hmemL_iff : ∀ (x : ↥(C.L (D + Curve.Div.place Q))),
      (x : C.functionField) ≠ 0 →
      ((x : C.functionField) ∈ C.L D ↔ -(D Q) ≤ Scheme.ord (x : C.functionField) Q.point) := by
    intro x hx0
    constructor
    · intro hxL
      rw [Curve.mem_L_iff] at hxL
      rcases hxL with h0 | heff
      · exact absurd h0 hx0
      · exact (C.isEffective_div_add_iff).mp heff Q
    · intro hQ
      rw [Curve.mem_L_iff]
      refine Or.inr ((C.isEffective_div_add_iff).mpr fun P => ?_)
      by_cases hP : P = Q
      · subst hP; exact hQ
      · have hxM : (x : C.functionField) ∈ C.L (D + Curve.Div.place Q) := x.2
        rw [Curve.mem_L_iff] at hxM
        rcases hxM with h0 | heff
        · exact absurd h0 hx0
        · have h1 := (C.isEffective_div_add_iff).mp heff P
          have h2 : (D + Curve.Div.place Q) P = D P := by
            simp only [Curve.Div.place, Finsupp.add_apply, Finsupp.single_apply]
            rw [if_neg (Ne.symm hP), add_zero]
          rwa [h2] at h1
  -- the kernel of `Φ` is `L D`
  have hker : Φ.ker = Submodule.comap (C.L (D + Curve.Div.place Q)).subtype (C.L D) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    by_cases hx0 : (x : C.functionField) = 0
    · have hx : x = 0 := Subtype.ext hx0
      rw [hx, map_zero]
      exact ⟨fun _ => C.zero_mem_L D, fun _ => rfl⟩
    · have hwx : Ring.ordFrac (C.left.presheaf.stalk Q.point) (w * (x : C.functionField))
          = WithZero.exp (n + Scheme.ord (x : C.functionField) Q.point) := by
        rw [map_mul, hordFrac_w, ordFrac_eq_exp_ord C Q _ hx0, ← WithZero.exp_add]
      have hord_ge : -n ≤ Scheme.ord (x : C.functionField) Q.point := by
        have hxM : (x : C.functionField) ∈ C.L (D + Curve.Div.place Q) := x.2
        rw [Curve.mem_L_iff] at hxM
        rcases hxM with h0 | heff
        · exact absurd h0 hx0
        · have h1 := (C.isEffective_div_add_iff).mp heff Q
          have h2 : (D + Curve.Div.place Q) Q = D Q + 1 := by
            simp only [Curve.Div.place, Finsupp.add_apply, Finsupp.single_eq_same, add_zero]
          rw [h2, ← hn] at h1
          exact h1
      set a : C.left.presheaf.stalk Q.point :=
        e.symm ⟨(θ.comp (C.L (D + Curve.Div.place Q)).subtype) x, hV' x⟩ with ha_def
      have ha_val : algebraMap _ _ a = w * (x : C.functionField) := by
        rw [ha_def, he_symm]
        rfl
      rw [hΦ_apply x, ← ha_def]
      change IsLocalRing.residue (C.left.presheaf.stalk Q.point) a = 0 ↔
        (x : C.functionField) ∈ C.L D
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
      change (¬ IsUnit a) ↔ (x : C.functionField) ∈ C.L D
      rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := C.functionField), ha_val, hwx,
        ← WithZero.exp_zero, WithZero.exp_inj]
      constructor
      · intro h
        rw [hmemL_iff x hx0]
        have hpos : (0 : ℤ) < n + Scheme.ord (x : C.functionField) Q.point :=
          lt_of_le_of_ne' (by linarith) h
        rw [hn] at hpos
        linarith
      · intro hxL
        rw [hmemL_iff x hx0] at hxL
        rw [hn]
        intro hc
        linarith
  haveI : FiniteDimensional k (C.left.residueField Q.point) :=
    finiteDimensional_residueField C Q
  refine ⟨?_, ?_⟩
  · haveI : FiniteDimensional k ↥Φ.range :=
      FiniteDimensional.of_injective (Submodule.subtype Φ.range) (Submodule.subtype_injective _)
    have h2 : FiniteDimensional k (↥(C.L (D + Curve.Div.place Q)) ⧸ Φ.ker) :=
      LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange Φ).symm
    rw [← hker]
    exact h2
  · rw [← hker, LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange Φ), Place.degree_eq_finrank Q]
    exact Submodule.finrank_le _

end

end Work.CurveBasics.Linear
