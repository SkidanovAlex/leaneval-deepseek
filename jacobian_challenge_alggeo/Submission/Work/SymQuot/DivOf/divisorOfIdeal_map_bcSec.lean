import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff
import Submission.Work.SymQuot.DivOf.towerHom_preimage_bcOpens
import Submission.Work.SpecLin.Core.ord_germ_eq_iff_mem_pow
import Submission.Work.Curve.BCSquare.ordAt_fieldMap
import Submission.Work.CurveBasics.BaseChange.primeIdealOf_eq_bot_of_eq_genericPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped WithZero
open Work.CurveBasics

/-! ## Preliminaries: order of vanishing versus powers of the ideal of a place -/

/-- **Order of vanishing at a place, membership form, for sections of an affine open.**

For a nonzero section `b` of an affine open `V` of a curve, the order of vanishing of `b` at a
place `z ∈ V` is at least `k` if and only if `b` lies in the `k`-th power of the maximal ideal
`placeIdeal C V z hz` of `Γ(C,V)`. -/
theorem mem_placeIdeal_pow_iff_le_ordAt {F : Type u} [Field F] {C : Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V)
    {b : Γ(C.left, V)} (hb : b ≠ 0) (z : C.Place) (hz : z.point ∈ V) (k : ℕ) :
    b ∈ (placeIdeal C V z hz) ^ k ↔ (k : ℤ) ≤ C.ordAt ((C.germToFunctionField V).hom b) z := by
  haveI hDed : IsDedekindDomain Γ(C.left, V) := isDedekindDomain_sections hV
  rw [placeIdeal_eq_primeIdealOf hV z hz]
  exact (Work.SpecLin.Core.ord_germ_eq_iff_mem_pow (X := C.left) V hV z.point hz
    z.eq_coheight_one b k hb).symm

/-- **A germ at a place has nonnegative order of vanishing.** -/
theorem ordAt_algebraMap_stalk_nonneg {F : Type u} [Field F] {C : Curve F} (Q : C.Place)
    (x : C.left.presheaf.stalk Q.point) :
    0 ≤ C.ordAt (algebraMap (C.left.presheaf.stalk Q.point) (↑C.functionField) x) Q := by
  classical
  by_cases hx : x = 0
  · subst hx
    simp [Curve.ordAt]
  · have hf : (algebraMap (C.left.presheaf.stalk Q.point) (↑C.functionField)) x ≠ 0 :=
      fun h => hx (IsFractionRing.injective (C.left.presheaf.stalk Q.point) (↑C.functionField)
        (by simpa using h))
    rw [show C.ordAt ((algebraMap (C.left.presheaf.stalk Q.point) (↑C.functionField)) x) Q
        = Scheme.ord ((algebraMap (C.left.presheaf.stalk Q.point) (↑C.functionField)) x)
            Q.point from rfl]
    rw [Scheme.le_ord_iff Q.eq_coheight_one hf]
    show (1 : ℤᵐ⁰) ≤ Ring.ordFrac (C.left.presheaf.stalk Q.point)
        ((algebraMap (C.left.presheaf.stalk Q.point) (↑C.functionField)) x)
    exact Ring.ordFrac_ge_one_of_ne_zero hx

/-- **The ramification index of a place above a place is nonnegative.** -/
theorem ramIdx_nonneg {K : Type u} [Field K] {C : Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (Q' : (C.baseChange F'').Place)
    (hc : IsClosed ({(bcSquareTower (C := C) F F'').π Q'.point} : Set (C.baseChange F).left)) :
    0 ≤ (bcSquareTower (C := C) F F'').ramIdx Q' := by
  haveI hDVR : IsDiscreteValuationRing
      ((C.baseChange F).left.presheaf.stalk ((bcSquareTower (C := C) F F'').π Q'.point)) :=
    Curve.Place.instIsDiscreteValuationRing
      (⟨(bcSquareTower (C := C) F F'').π Q'.point, hc⟩ : (C.baseChange F).Place)
  rw [Curve.BCSquare.ramIdx, dite_eq_left hc]
  show 0 ≤ (C.baseChange F'').ordAt
    ((bcSquareTower (C := C) F F'').fieldMap.hom
      (algebraMap ((C.baseChange F).left.presheaf.stalk
          ((bcSquareTower (C := C) F F'').π Q'.point)) (↑(C.baseChange F).functionField)
        (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal
          ((C.baseChange F).left.presheaf.stalk
            ((bcSquareTower (C := C) F F'').π Q'.point)))))) Q'
  rw [Work.Curve.BCSquare.fieldMap_stalkMap (bcSquareTower (C := C) F F'') Q'.point]
  exact ordAt_algebraMap_stalk_nonneg Q' _

/-- **The `bcSec`-pullback commutes with passage to the function field.** -/
theorem germToFunctionField_bcSec {K : Type u} [Field K] {C : Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens) [Nonempty V]
    [Nonempty (C.bcOpens F V)] [Nonempty (C.bcOpens F'' V)]
    (b : Γ((C.baseChange F).left, C.bcOpens F V)) :
    ((C.baseChange F'').germToFunctionField (C.bcOpens F'' V)).hom (bcSec (C := C) F F'' V b)
      = (bcSquareTower (C := C) F F'').fieldMap.hom
          (((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b) := by
  have h₁ : (bcSquareTower (C := C) F F'').fieldMap.hom
      (((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b)
      = ((C.baseChange F'').germToFunctionField
          ((bcSquareTower (C := C) F F'').π ⁻¹ᵁ (C.bcOpens F V))).hom
          (((bcSquareTower (C := C) F F'').π.app (C.bcOpens F V)).hom b) := by
    have h := Work.CurveBasics.Curve.BCSquare.germ_stalkMap_germToFunctionField
      (bcSquareTower (C := C) F F'').π (bcSquareTower (C := C) F F'').π_genericPoint
      (C.bcOpens F V)
    have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) b) h
    exact h2
  have h₂ : ((C.baseChange F'').germToFunctionField (C.bcOpens F'' V)).hom
      (bcSec (C := C) F F'' V b)
      = ((C.baseChange F'').germToFunctionField
          ((bcSquareTower (C := C) F F'').π ⁻¹ᵁ (C.bcOpens F V))).hom
          (((bcSquareTower (C := C) F F'').π.app (C.bcOpens F V)).hom b) := by
    show ((C.baseChange F'').left.presheaf.germ (C.bcOpens F'' V) (genericPoint _) _)
      (((C.baseChange F'').left.presheaf.map
        (homOfLE (le_of_eq (towerHom_preimage_bcOpens (C := C) F F'' V).symm)).op).hom
          (((bcSquareTower (C := C) F F'').π.app (C.bcOpens F V)).hom b))
      = ((C.baseChange F'').left.presheaf.germ
          ((bcSquareTower (C := C) F F'').π ⁻¹ᵁ (C.bcOpens F V)) (genericPoint _) _).hom
          (((bcSquareTower (C := C) F F'').π.app (C.bcOpens F V)).hom b)
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  rw [h₂, h₁]

/-- **The ideal of a place pulls back to the ideal of the image point.** -/
theorem comap_bcSec_placeIdeal {K : Type u} [Field K] {C : Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens)
    [Nonempty (C.bcOpens F V)] [Nonempty (C.bcOpens F'' V)]
    (hW : IsAffineOpen (C.bcOpens F V))
    (hW'' : IsAffineOpen (C.bcOpens F'' V))
    (Q' : (C.baseChange F'').Place) (hQ' : Q'.point ∈ C.bcOpens F'' V)
    (hπ : (bcSquareTower (C := C) F F'').π Q'.point ∈ C.bcOpens F V) :
    (placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ').comap (bcSec (C := C) F F'' V) =
      (hW.primeIdealOf ⟨(bcSquareTower (C := C) F F'').π Q'.point, hπ⟩).asIdeal := by
  rw [placeIdeal_eq_primeIdealOf hW'' Q' hQ', ← PrimeSpectrum.comap_asIdeal]
  exact congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE (f := (bcSquareTower (C := C) F F'').π)
      (C.bcOpens F V) hW (C.bcOpens F'' V) hW''
      (le_of_eq (towerHom_preimage_bcOpens (C := C) F F'' V).symm) (x := Q'.point) (hx := hQ'))

/-- **The pullback of sections along the tower is injective.** -/
theorem bcSec_ne_zero {K : Type u} [Field K] {C : Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens) [Nonempty V]
    [Nonempty (C.bcOpens F V)] [Nonempty (C.bcOpens F'' V)]
    {b : Γ((C.baseChange F).left, C.bcOpens F V)} (hb : b ≠ 0) :
    bcSec (C := C) F F'' V b ≠ 0 := by
  intro h0
  have h1 := germToFunctionField_bcSec (C := C) F F'' V b
  rw [h0, map_zero] at h1
  have h2 : ((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b = 0 :=
    Work.CurveBasics.Curve.BCSquare.fieldMap_injective (bcSquareTower (C := C) F F'')
      (by rw [← h1, map_zero])
  exact hb (Scheme.germToFunctionField_injective (C.baseChange F).left (C.bcOpens F V)
    (by rw [h2, map_zero]))

/-! ## The order of the extended ideal at a place -/

/-- **The order of the extended ideal.**  For a nonzero ideal `J` of `Γ(C_F, V_F)` and places
`Q ∈ V_F`, `Q' ∈ V_{F''}` with `π Q' = Q`, the order of the extension `J · Γ(C_{F''}, V_{F''})`
at `Q'` is the order of `J` at `Q` multiplied by the ramification index `e(Q'/Q)`. -/
theorem placeOrder_map_bcSec {K : Type u} [Field K] {C : Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens) (hV : IsAffineOpen V) [Nonempty V]
    [Nonempty (C.bcOpens F V)] [Nonempty (C.bcOpens F'' V)]
    [IsDedekindDomain Γ((C.baseChange F).left, C.bcOpens F V)]
    [IsDedekindDomain Γ((C.baseChange F'').left, C.bcOpens F'' V)]
    (J : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) (hJ : J ≠ ⊥)
    (Q : (C.baseChange F).Place) (hQ : Q.point ∈ C.bcOpens F V)
    (Q' : (C.baseChange F'').Place) (hQ' : Q'.point ∈ C.bcOpens F'' V)
    (hpt : (Q.point : (C.baseChange F).left) = (bcSquareTower (C := C) F F'').π Q'.point) :
    (placeOrder (C.baseChange F'') (C.bcOpens F'' V)
        (J.map (bcSec (C := C) F F'' V)) Q' hQ' : ℤ) =
      (placeOrder (C.baseChange F) (C.bcOpens F V) J Q hQ : ℤ)
        * (bcSquareTower (C := C) F F'').ramIdx Q' := by
  classical
  have hW : IsAffineOpen (C.bcOpens F V) := BaseChange.isAffineOpen_bcOpens F V hV
  have hW'' : IsAffineOpen (C.bcOpens F'' V) := BaseChange.isAffineOpen_bcOpens F'' V hV
  have hc : IsClosed ({(bcSquareTower (C := C) F F'').π Q'.point} : Set (C.baseChange F).left) := by
    rw [← hpt]; exact Q.isClosed
  have hram : 0 ≤ (bcSquareTower (C := C) F F'').ramIdx Q' := ramIdx_nonneg F F'' Q' hc
  have hJ' : J.map (bcSec (C := C) F F'' V) ≠ ⊥ := by
    intro hbot
    obtain ⟨b, hbJ, hb⟩ := (Submodule.ne_bot_iff J).mp hJ
    have hle := (Ideal.map_eq_bot_iff_le_ker (I := J) (bcSec (C := C) F F'' V)).mp hbot
    exact bcSec_ne_zero F F'' V hb (RingHom.mem_ker.mp (hle hbJ))
  set p' : ℕ := placeOrder (C.baseChange F) (C.bcOpens F V) J Q hQ with hp'
  set p'' : ℕ := placeOrder (C.baseChange F'') (C.bcOpens F'' V)
    (J.map (bcSec (C := C) F F'' V)) Q' hQ' with hp''
  set e : ℕ := ((bcSquareTower (C := C) F F'').ramIdx Q').toNat with he
  have hee : (bcSquareTower (C := C) F F'').ramIdx Q' = (e : ℤ) :=
    (Int.toNat_of_nonneg hram).symm
  have hbound : ∀ b ∈ J, b ≠ 0 → (p' : ℤ) ≤ (C.baseChange F).ordAt
      (((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b) Q := by
    intro b hbJ _
    have hsub : J ≤ (placeIdeal (C.baseChange F) (C.bcOpens F V) Q hQ) ^ p' :=
      (le_placeOrder_iff hW hJ Q hQ p').mp (le_of_eq hp')
    exact (mem_placeIdeal_pow_iff_le_ordAt hW ‹b ≠ 0› Q hQ p').mp (hsub hbJ)
  have hord : ∀ b ∈ J, b ≠ 0 → (C.baseChange F'').ordAt
      (((C.baseChange F'').germToFunctionField (C.bcOpens F'' V)).hom
        (bcSec (C := C) F F'' V b)) Q'
      = (bcSquareTower (C := C) F F'').ramIdx Q' *
        (C.baseChange F).ordAt
          (((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b) Q := by
    intro b _ hb
    have hf : ((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b ≠ 0 := by
      intro h
      exact hb (Scheme.germToFunctionField_injective (C.baseChange F).left (C.bcOpens F V)
        (by rw [h, map_zero]))
    rw [germToFunctionField_bcSec (C := C) F F'' V b]
    rw [Work.Curve.BCSquare.ordAt_fieldMap (bcSquareTower (C := C) F F'') Q' hc (hf := hf)]
    rw [show (bcSquareTower (C := C) F F'').under Q' hc = Q from Subtype.ext hpt.symm]
  have hge : p' * e ≤ p'' := by
    rw [hp'']
    rw [(le_placeOrder_iff hW'' hJ' Q' hQ' (p' * e))]
    rw [Ideal.map_le_iff_le_comap]
    intro b hbJ
    rw [Ideal.mem_comap]
    by_cases hb : b = 0
    · subst hb
      rw [map_zero]
      exact Ideal.zero_mem _
    · rw [mem_placeIdeal_pow_iff_le_ordAt hW'' (bcSec_ne_zero F F'' V hb) Q' hQ' (p' * e)]
      rw [hord b hbJ hb, hee]
      have h1 := hbound b hbJ hb
      have h2 : (0 : ℤ) ≤ (e : ℤ) := Int.natCast_nonneg e
      push_cast
      nlinarith [h1, h2]
  have hle : p'' ≤ p' * e := by
    by_contra hcon
    rw [Nat.not_le, hp''] at hcon
    have h1 : p' * e + 1 ≤ placeOrder (C.baseChange F'') (C.bcOpens F'' V)
        (J.map (bcSec (C := C) F F'' V)) Q' hQ' := by omega
    have hsub : J.map (bcSec (C := C) F F'' V) ≤
        (placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ') ^ (p' * e + 1) :=
      (le_placeOrder_iff hW'' hJ' Q' hQ' (p' * e + 1)).mp h1
    have hnot : ¬ (J ≤ (placeIdeal (C.baseChange F) (C.bcOpens F V) Q hQ) ^ (p' + 1)) := by
      intro hle'
      have h2 : p' + 1 ≤ p' := (le_placeOrder_iff hW hJ Q hQ (p' + 1)).mpr hle'
      omega
    obtain ⟨b, hbJ, hbnot⟩ := Set.not_subset.mp hnot
    have hb : b ≠ 0 := fun h0 => hbnot (h0 ▸ Ideal.zero_mem _)
    have hmem : bcSec (C := C) F F'' V b ∈
        (placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ') ^ (p' * e + 1) := by
      have h3 : b ∈ ((placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ') ^
            (p' * e + 1)).comap (bcSec (C := C) F F'' V) :=
        (Ideal.map_le_iff_le_comap.mp hsub) hbJ
      exact (Ideal.mem_comap).mp h3
    rw [mem_placeIdeal_pow_iff_le_ordAt hW'' (bcSec_ne_zero F F'' V hb) Q' hQ'
      (p' * e + 1)] at hmem
    rw [hord b hbJ hb, hee] at hmem
    have h2' : (C.baseChange F).ordAt
        (((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b) Q = (p' : ℤ) := by
      refine le_antisymm ?_ (hbound b hbJ hb)
      have h4 : ¬ (((p' + 1 : ℕ) : ℤ) ≤ (C.baseChange F).ordAt
          (((C.baseChange F).germToFunctionField (C.bcOpens F V)).hom b) Q) :=
        (mem_placeIdeal_pow_iff_le_ordAt hW hb Q hQ (p' + 1)).not.mp hbnot
      push_cast at h4
      omega
    rw [h2'] at hmem
    push_cast at hmem
    nlinarith
  have hnat : p'' = p' * e := le_antisymm hle hge
  rw [hnat, hee]
  push_cast
  ring

/-! ## The divisor of an extended ideal -/

theorem divisorOfIdeal_map_bcSec {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens) (hV : IsAffineOpen V)
    [Nonempty V] [Nonempty (C.bcOpens F V)] [Nonempty (C.bcOpens F'' V)]
    [IsDedekindDomain Γ((C.baseChange F).left, C.bcOpens F V)]
    [IsDedekindDomain Γ((C.baseChange F'').left, C.bcOpens F'' V)]
    (J : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) (hJ : J ≠ ⊥) :
    divisorOfIdeal (C.baseChange F'') (C.bcOpens F'' V)
        (BaseChange.isAffineOpen_bcOpens F'' V hV) (J.map (bcSec (C := C) F F'' V)) =
      (bcSquareTower (C := C) F F'').divMap
        (divisorOfIdeal (C.baseChange F) (C.bcOpens F V)
          (BaseChange.isAffineOpen_bcOpens F V hV) J) := by
  classical
  have hW : IsAffineOpen (C.bcOpens F V) := BaseChange.isAffineOpen_bcOpens F V hV
  have hW'' : IsAffineOpen (C.bcOpens F'' V) := BaseChange.isAffineOpen_bcOpens F'' V hV
  have hJ' : J.map (bcSec (C := C) F F'' V) ≠ ⊥ := by
    intro hbot
    obtain ⟨b, hbJ, hb⟩ := (Submodule.ne_bot_iff J).mp hJ
    have hle := (Ideal.map_eq_bot_iff_le_ker (I := J) (bcSec (C := C) F F'' V)).mp hbot
    exact bcSec_ne_zero F F'' V hb (RingHom.mem_ker.mp (hle hbJ))
  ext Q'
  simp only [divisorOfIdeal_apply, Curve.BCSquare.divMap_apply, Curve.BCSquare.divMapCoeff]
  by_cases hQ' : Q'.point ∈ C.bcOpens F'' V
  · rw [dite_eq_left hQ']
    have hπ : (bcSquareTower (C := C) F F'').π Q'.point ∈ C.bcOpens F V := by
      have hmem := hQ'
      rw [← towerHom_preimage_bcOpens (C := C) F F'' V] at hmem
      exact hmem
    by_cases hc : IsClosed
        ({(bcSquareTower (C := C) F F'').π Q'.point} : Set (C.baseChange F).left)
    · rw [dite_eq_left hc]
      have hq : ((bcSquareTower (C := C) F F'').under Q' hc).point ∈ C.bcOpens F V := hπ
      rw [dite_eq_left hq]
      exact placeOrder_map_bcSec F F'' V hV J hJ ((bcSquareTower (C := C) F F'').under Q' hc)
        hq Q' hQ' rfl
    · rw [dite_eq_right hc]
      have hgen : (bcSquareTower (C := C) F F'').π Q'.point
          = genericPoint (C.baseChange F).left := by
        rcases Curve.eq_genericPoint_or_isClosed (C.baseChange F)
          ((bcSquareTower (C := C) F F'').π Q'.point) with h | h
        · exact h
        · exact absurd h hc
      have hzero : placeOrder (C.baseChange F'') (C.bcOpens F'' V)
          (J.map (bcSec (C := C) F F'' V)) Q' hQ' = 0 := by
        by_contra hne
        have hpos : 1 ≤ placeOrder (C.baseChange F'') (C.bcOpens F'' V)
            (J.map (bcSec (C := C) F F'' V)) Q' hQ' := Nat.one_le_iff_ne_zero.mpr hne
        have hsub : J.map (bcSec (C := C) F F'' V) ≤
            (placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ') ^ 1 :=
          (le_placeOrder_iff hW'' hJ' Q' hQ' 1).mp hpos
        obtain ⟨b, hbJ, hb⟩ := (Submodule.ne_bot_iff J).mp hJ
        have hmem : bcSec (C := C) F F'' V b ∈
            (placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ') ^ 1 := by
          have h3 : b ∈ ((placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ') ^
                1).comap (bcSec (C := C) F F'' V) :=
            (Ideal.map_le_iff_le_comap.mp hsub) hbJ
          exact (Ideal.mem_comap).mp h3
        rw [pow_one] at hmem
        have h4 : b ∈ (placeIdeal (C.baseChange F'') (C.bcOpens F'' V) Q' hQ').comap
            (bcSec (C := C) F F'' V) := (Ideal.mem_comap).mpr hmem
        rw [comap_bcSec_placeIdeal F F'' V hW hW'' Q' hQ' hπ] at h4
        rw [Work.CurveBasics.BaseChange.primeIdealOf_eq_bot_of_eq_genericPoint
          (C := C.baseChange F) (W := C.bcOpens F V) hW
          (xW := ⟨(bcSquareTower (C := C) F F'').π Q'.point, hπ⟩) hgen] at h4
        exact hb (Ideal.mem_bot.mp h4)
      rw [hzero]
      ring
  · rw [dite_eq_right hQ']
    by_cases hc : IsClosed
        ({(bcSquareTower (C := C) F F'').π Q'.point} : Set (C.baseChange F).left)
    · rw [dite_eq_left hc]
      have hnot : ¬ ((bcSquareTower (C := C) F F'').under Q' hc).point ∈ C.bcOpens F V := by
        intro hmem
        apply hQ'
        have hmem' : Q'.point ∈ (TopologicalSpace.Opens.map
            BCSquareBaseChange.towerHom.base).obj (C.bcOpens F V) := hmem
        rw [towerHom_preimage_bcOpens (C := C) F F'' V] at hmem'
        exact hmem'
      rw [dite_eq_right hnot]
      ring
    · rw [dite_eq_right hc]

end Work.SymQuot.DivOf
