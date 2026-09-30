import Mathlib
import Submission.Work.SpecLin.Setup.keyUnit
import Submission.Work.SpecLin.Setup.tensorProductInf
import Submission.Work.SpecLin.Setup.unitOfGenericUnit
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Core.module_free_chartTensor
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.CurveBasics.BaseChange.krullDimLE_tensor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Auxiliary development for `unitOfAllHeightOne`

The generic fibre `A_F = A ⊗[K] Frac R` of the relative chart `B = A ⊗[K] R` of a curve over a
valuation ring, and the localisation infrastructure used in the proof that a rational function
which is a unit at the special-fibre prime and at every height-one prime is a unit of `B`.
-/

namespace Work.SpecLin.Setup

universe u

open scoped TensorProduct

section LocalizationSetup

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
  {R : Type u} [CommRing R] [IsDomain R] [Algebra K R]

instance : Algebra R (TensorProduct K A R) := Algebra.TensorProduct.rightAlgebra

/-- The canonical `K`-algebra map from the relative chart `B = A ⊗[K] R` to the generic fibre
`A_F = A ⊗[K] Frac R`. -/
noncomputable def tensorToFractionRing :
    TensorProduct K A R →ₐ[K] TensorProduct K A (FractionRing R) :=
  Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R (FractionRing R))

lemma tensorToFractionRing_tmul (a : A) (r : R) :
    tensorToFractionRing (K := K) (A := A) (R := R) (a ⊗ₜ[K] r)
      = a ⊗ₜ[K] (algebraMap R (FractionRing R) r) :=
  Algebra.TensorProduct.map_tmul _ _ a r

noncomputable instance instAlgebraTensorProdFractionRing :
    Algebra (TensorProduct K A R) (TensorProduct K A (FractionRing R)) :=
  (tensorToFractionRing (K := K) (A := A) (R := R)).toRingHom.toAlgebra

lemma algebraMap_tensorToFractionRing (x : TensorProduct K A R) :
    algebraMap (TensorProduct K A R) (TensorProduct K A (FractionRing R)) x
      = tensorToFractionRing (K := K) (A := A) (R := R) x := by
  rw [RingHom.algebraMap_toAlgebra]
  rfl

lemma tensorToFractionRing_includeRight (r : R) :
    tensorToFractionRing (K := K) (A := A) (R := R)
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r)
      = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)
          (algebraMap R (FractionRing R) r) := by
  show tensorToFractionRing (K := K) (A := A) (R := R) ((1 : A) ⊗ₜ[K] r)
      = (1 : A) ⊗ₜ[K] (algebraMap R (FractionRing R) r)
  exact Algebra.TensorProduct.map_tmul _ _ 1 r

/-- **The relative chart is a localisation of the generic fibre.** -/
instance isLocalization_tensorProduct_fractionRing :
    IsLocalization
      ((nonZeroDivisors R).map
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)))
      (TensorProduct K A (FractionRing R)) := by
  haveI hST : IsScalarTower A (TensorProduct K A R) (TensorProduct K A (FractionRing R)) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      have h1 : algebraMap A (TensorProduct K A R) a = a ⊗ₜ[K] (1 : R) := rfl
      have h2 : algebraMap A (TensorProduct K A (FractionRing R)) a
          = a ⊗ₜ[K] (1 : FractionRing R) := rfl
      rw [h1, h2, algebraMap_tensorToFractionRing, tensorToFractionRing_tmul]
      simp)
  have hH : (algebraMap (TensorProduct K A R) (TensorProduct K A (FractionRing R))).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)).toRingHom
      = (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)).toRingHom.comp
          (algebraMap R (FractionRing R)) := by
    ext r
    show tensorToFractionRing (K := K) (A := A) (R := R) ((1 : A) ⊗ₜ[K] r)
      = (1 : A) ⊗ₜ[K] (algebraMap R (FractionRing R) r)
    rw [tensorToFractionRing_tmul]
  exact IsLocalization.tensorProduct_tensorProduct_right (R := K) (S := A) (A := R)
    (M := nonZeroDivisors R) (B := FractionRing R) hH

/-- `A_F = A ⊗[K] Frac R` is a domain: it is the localisation of the domain `B = A ⊗[K] R` at
the non-zero elements of `R`. -/
theorem isDomain_tensorProduct_fractionRing' [IsDomain (TensorProduct K A R)] :
    IsDomain (TensorProduct K A (FractionRing R)) := by
  haveI := isLocalization_tensorProduct_fractionRing (K := K) (A := A) (R := R)
  haveI hntB : Nontrivial (TensorProduct K A R) := inferInstance
  haveI hntA : Nontrivial A := (algebraMap A (TensorProduct K A R)).domain_nontrivial
  have hle : (nonZeroDivisors R).map
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))
      ≤ nonZeroDivisors (TensorProduct K A R) := by
    intro x hx
    rw [Submonoid.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hι : Function.Injective
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) :=
      Algebra.TensorProduct.includeRight_injective (R := K) (A := A) (B := R)
        (RingHom.injective (algebraMap K A))
    refine mem_nonZeroDivisors_iff_right.mpr fun z hz => ?_
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (fun h0 => nonZeroDivisors.ne_zero hr (hι (by rw [h0, map_zero])))
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _ hle



/-! ### Elements of the generic fibre as quotients by elements of `R` -/

lemma includeRight_algebraMap_eq (r : R) :
    Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)
        (algebraMap R (FractionRing R) r)
      = algebraMap (TensorProduct K A R) (TensorProduct K A (FractionRing R))
          (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r) := by
  rw [algebraMap_tensorToFractionRing (K := K) (A := A) (R := R)]
  exact tensorToFractionRing_includeRight r

/-- Every element of the generic fibre `A_F = A ⊗[K] Frac R` is a quotient of an element of the
relative chart `B = A ⊗[K] R` by the image of an element of `R ∖ {0}`. -/
theorem exists_mul_eq_tensorToFractionRing [IsDomain (TensorProduct K A R)]
    (x : TensorProduct K A (FractionRing R)) :
    ∃ (y : TensorProduct K A R) (r : R), r ≠ 0 ∧
      x * Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)
            (algebraMap R (FractionRing R) r)
        = tensorToFractionRing (K := K) (A := A) (R := R) y := by
  haveI := isLocalization_tensorProduct_fractionRing (K := K) (A := A) (R := R)
  obtain ⟨⟨y, m⟩, hsurj⟩ := IsLocalization.surj
    ((nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) x
  obtain ⟨r, hr, hrfl⟩ := Submonoid.mem_map.mp m.2
  have hid : (m : TensorProduct K A R)
      = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r := hrfl.symm
  rw [hid] at hsurj
  refine ⟨y, r, nonZeroDivisors.ne_zero hr, ?_⟩
  rw [includeRight_algebraMap_eq (K := K) (A := A) (R := R) r]
  rw [← algebraMap_tensorToFractionRing (K := K) (A := A) (R := R) y]
  rw [← hsurj]


/-! ### The canonical ring hom from the generic fibre to the fraction field of the chart -/

/-- The canonical ring hom `A_F = A ⊗[K] Frac R → Frac B`, obtained from the localisation
structure of `A_F` over `B = A ⊗[K] R`. -/
noncomputable def tensorToFracB [IsDomain (TensorProduct K A R)] :
    TensorProduct K A (FractionRing R) →+* FractionRing (TensorProduct K A R) :=
  IsLocalization.lift
    (M := (nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)))
    (g := algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)))
    (fun y => by
      obtain ⟨r, hr, hrfl⟩ := Submonoid.mem_map.mp y.2
      haveI hntB : Nontrivial (TensorProduct K A R) := inferInstance
      haveI hntA : Nontrivial A := (algebraMap A (TensorProduct K A R)).domain_nontrivial
      have hι : Function.Injective
          (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) :=
        Algebra.TensorProduct.includeRight_injective (R := K) (A := A) (B := R)
          (RingHom.injective (algebraMap K A))
      have hy0 : (y : TensorProduct K A R) ≠ 0 := by
        rw [← hrfl]
        intro h
        exact nonZeroDivisors.ne_zero hr (hι (by rw [h, map_zero]))
      exact isUnit_iff_ne_zero.mpr fun h => hy0 (IsFractionRing.injective (TensorProduct K A R)
        (FractionRing (TensorProduct K A R)) (h.trans (map_zero _).symm)))

noncomputable instance instAlgebraTensorToFracB [IsDomain (TensorProduct K A R)] :
    Algebra (TensorProduct K A (FractionRing R)) (FractionRing (TensorProduct K A R)) :=
  (tensorToFracB (K := K) (A := A) (R := R)).toAlgebra

lemma algebraMap_tensorToFracB [IsDomain (TensorProduct K A R)]
    (x : TensorProduct K A R) :
    algebraMap (TensorProduct K A (FractionRing R)) (FractionRing (TensorProduct K A R))
        (algebraMap (TensorProduct K A R) (TensorProduct K A (FractionRing R)) x)
      = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) x := by
  haveI := isLocalization_tensorProduct_fractionRing (K := K) (A := A) (R := R)
  rw [RingHom.algebraMap_toAlgebra]
  exact IsLocalization.lift_eq _ x

local instance isScalarTowerTensorToFracB [IsDomain (TensorProduct K A R)] :
    IsScalarTower (TensorProduct K A R) (TensorProduct K A (FractionRing R))
      (FractionRing (TensorProduct K A R)) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (algebraMap_tensorToFracB (K := K) (A := A) (R := R) x).symm


/-! ### Injectivity of the map to the generic fibre, and the "no hidden points" lemma -/

lemma tensorToFractionRing_injective :
    Function.Injective (tensorToFractionRing (K := K) (A := A) (R := R)) := by
  have hlin : (tensorToFractionRing (K := K) (A := A) (R := R)).toLinearMap
      = LinearMap.lTensor A
          (IsScalarTower.toAlgHom K R (FractionRing R)).toLinearMap := by
    refine TensorProduct.ext' ?_
    intro a r
    simp [tensorToFractionRing, LinearMap.lTensor_tmul]
  have hlinj : Function.Injective (LinearMap.lTensor A
      (IsScalarTower.toAlgHom K R (FractionRing R)).toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (IsFractionRing.injective R (FractionRing R))
  intro x y h
  exact hlinj (by simpa [← hlin] using h)

/-- **No hidden points.**  Every non-zero prime of the generic fibre `A_F = A ⊗[K] Frac R`
contracts to a non-zero ideal of the relative chart `B = A ⊗[K] R`. -/
theorem comap_tensorToFractionRing_ne_bot [IsDomain (TensorProduct K A R)]
    {𝔮 : Ideal (TensorProduct K A (FractionRing R))} (h𝔮 : 𝔮.IsPrime) (hne : 𝔮 ≠ ⊥) :
    𝔮.comap (tensorToFractionRing (K := K) (A := A) (R := R)).toRingHom ≠ ⊥ := by
  intro hbot
  haveI hdomAF := isDomain_tensorProduct_fractionRing' (K := K) (A := A) (R := R)
  haveI : Nontrivial A := (algebraMap A (TensorProduct K A R)).domain_nontrivial
  obtain ⟨x, hx𝔮, hx0⟩ := (Submodule.ne_bot_iff 𝔮).mp hne
  obtain ⟨y, r, hr, hxy⟩ := exists_mul_eq_tensorToFractionRing (K := K) (A := A) (R := R) x
  have hιF : Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)) :=
    Algebra.TensorProduct.includeRight_injective (R := K) (A := A) (B := FractionRing R)
      (RingHom.injective (algebraMap K A))
  have hψr0 : Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)
      (algebraMap R (FractionRing R) r) ≠ 0 := by
    intro h
    refine hr ?_
    exact IsFractionRing.injective R (FractionRing R)
      (hιF (by simpa using h))
  have hmem : y ∈ 𝔮.comap (tensorToFractionRing (K := K) (A := A) (R := R)).toRingHom := by
    rw [Ideal.mem_comap]
    have h : tensorToFractionRing (K := K) (A := A) (R := R) y ∈ 𝔮 := by
      rw [← hxy]
      exact Ideal.mul_mem_right _ _ hx𝔮
    simpa using h
  rw [hbot] at hmem
  have hy0 : (y : TensorProduct K A R) = 0 := by simpa using hmem
  rw [hy0, map_zero] at hxy
  exact hψr0 (by
    rcases mul_eq_zero.mp hxy with h | h
    · exact absurd h hx0
    · exact h)


/-! ### The height of the contraction of a maximal ideal of the generic fibre -/

theorem height_comap_tensorToFractionRing [IsDomain (TensorProduct K A R)]
    [Algebra.FiniteType K A] [Ring.KrullDimLE 1 A]
    {𝔮 : Ideal (TensorProduct K A (FractionRing R))} [𝔮.IsMaximal] (hne : 𝔮 ≠ ⊥) :
    (𝔮.comap (tensorToFractionRing (K := K) (A := A) (R := R)).toRingHom).height = 1 := by
  haveI hloc := isLocalization_tensorProduct_fractionRing (K := K) (A := A) (R := R)
  haveI hdomAF := isDomain_tensorProduct_fractionRing' (K := K) (A := A) (R := R)
  have hdim : Ring.KrullDimLE 1 (TensorProduct K A (FractionRing R)) :=
    Work.CurveBasics.BaseChange.krullDimLE_tensor (k := K) (F := FractionRing R) (R := A)
      inferInstance
  have h1 : (𝔮.comap (tensorToFractionRing (K := K) (A := A) (R := R)).toRingHom).height
      = 𝔮.height := by
    have h := IsLocalization.height_under
      ((nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)))
      𝔮
    have h2 : algebraMap (TensorProduct K A R) (TensorProduct K A (FractionRing R))
        = (tensorToFractionRing (K := K) (A := A) (R := R)).toRingHom :=
      RingHom.ext fun x => algebraMap_tensorToFractionRing x
    rw [Ideal.under_def, h2] at h
    exact h
  have hle : 𝔮.height ≤ 1 :=
    WithBot.coe_le_coe.mp ((Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔮)).trans
      ((Ring.krullDimLE_iff (n := 1) (R := TensorProduct K A (FractionRing R))).mp hdim))
  have hge : 1 ≤ 𝔮.height := by
    refine Order.one_le_iff_ne_zero.mpr fun h0 => hne ?_
    exact Ideal.height_eq_zero_iff_eq_bot.mp h0
  rw [h1]
  exact le_antisymm hle hge

/-- The generic fibre has the fraction field of the relative chart. -/
noncomputable instance isFractionRing_tensorToFracB [IsDomain (TensorProduct K A R)] :
    IsFractionRing (TensorProduct K A (FractionRing R)) (FractionRing (TensorProduct K A R)) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    ((nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)))
    (TensorProduct K A (FractionRing R)) (FractionRing (TensorProduct K A R))


/-! ### Step B: a rational function which is a unit at all height-one primes lies in the generic
fibre. -/

variable {u : FractionRing (TensorProduct K A R)}

/-- A unit of `B_Q` for a height-one prime `Q` coming from a maximal ideal of the generic fibre
gives an element of the localisation of the generic fibre at that maximal ideal. -/
lemma exists_localization_of_isMaximal [IsDomain (TensorProduct K A R)]
    [Algebra.FiniteType K A] [Ring.KrullDimLE 1 A]
    (hht : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 →
      Work.SpecLin.Alt.IsUnitAt u p)
    {𝔮 : Ideal (TensorProduct K A (FractionRing R))} [𝔮.IsMaximal] (hne : 𝔮 ≠ ⊥) :
    ∃ (n s : TensorProduct K A (FractionRing R)), s ∉ 𝔮 ∧
      u * algebraMap (TensorProduct K A (FractionRing R)) (FractionRing (TensorProduct K A R)) s
        = algebraMap (TensorProduct K A (FractionRing R))
            (FractionRing (TensorProduct K A R)) n := by
  haveI h𝔮p : 𝔮.IsPrime := (inferInstance : 𝔮.IsMaximal).isPrime
  have hht' := hht (𝔮.comap (tensorToFractionRing (K := K) (A := A) (R := R)).toRingHom)
    (Ideal.IsPrime.comap _)
    (height_comap_tensorToFractionRing (K := K) (A := A) (R := R) hne)
  obtain ⟨b, s, hs, hbs⟩ := hht'.1
  refine ⟨tensorToFractionRing b, tensorToFractionRing s, ?_, ?_⟩
  · intro hmem
    refine hs ?_
    rw [Ideal.mem_comap]
    exact hmem
  · rw [show (tensorToFractionRing (K := K) (A := A) (R := R) s)
        = algebraMap (TensorProduct K A R) (TensorProduct K A (FractionRing R)) s from rfl,
      show (tensorToFractionRing (K := K) (A := A) (R := R) b)
        = algebraMap (TensorProduct K A R) (TensorProduct K A (FractionRing R)) b from rfl,
      algebraMap_tensorToFracB (K := K) (A := A) (R := R) s,
      algebraMap_tensorToFracB (K := K) (A := A) (R := R) b]
    exact hbs

/-- The generic-fibre localisation condition at the zero ideal: this is where the fraction-field
structure is used. -/
lemma exists_localization_bot [IsDomain (TensorProduct K A R)]
    (u : FractionRing (TensorProduct K A R)) :
    ∃ (n s : TensorProduct K A (FractionRing R)),
      s ∉ (⊥ : Ideal (TensorProduct K A (FractionRing R))) ∧
      u * algebraMap (TensorProduct K A (FractionRing R)) (FractionRing (TensorProduct K A R)) s
        = algebraMap (TensorProduct K A (FractionRing R))
            (FractionRing (TensorProduct K A R)) n := by
  haveI hdomAF := isDomain_tensorProduct_fractionRing' (K := K) (A := A) (R := R)
  haveI hFR : IsFractionRing (TensorProduct K A (FractionRing R))
      (FractionRing (TensorProduct K A R)) :=
    isFractionRing_tensorToFracB (K := K) (A := A) (R := R)
  obtain ⟨a, b, hb, hdiv⟩ :=
    IsFractionRing.div_surjective (TensorProduct K A (FractionRing R)) u
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (TensorProduct K A (FractionRing R))
      (FractionRing (TensorProduct K A R)) b ≠ 0 := by
    intro h
    exact hb0 (IsFractionRing.injective _ _ (h.trans (map_zero _).symm))
  refine ⟨a, b, by simpa using hb0, ?_⟩
  rw [← hdiv]
  exact div_mul_cancel₀ _ hb'

/-- **Step B.**  A rational function on the relative chart which is a unit at every height-one
prime lies in the generic fibre: it is a quotient of an element of `B` by the image of an
element of `R ∖ {0}`. -/
theorem exists_mul_eq_of_forall_isUnitAt_height_one [IsDomain (TensorProduct K A R)]
    [Algebra.FiniteType K A] [Ring.KrullDimLE 1 A]
    (hu : u ≠ 0)
    (hht : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 →
      Work.SpecLin.Alt.IsUnitAt u p) :
    ∃ (β : TensorProduct K A R) (ρ : R), ρ ≠ 0 ∧
      algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) β
        = u * algebraMap (TensorProduct K A (FractionRing R))
            (FractionRing (TensorProduct K A R))
            (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)
              (algebraMap R (FractionRing R) ρ)) := by
  haveI hloc := isLocalization_tensorProduct_fractionRing (K := K) (A := A) (R := R)
  haveI hdomAF := isDomain_tensorProduct_fractionRing' (K := K) (A := A) (R := R)
  haveI hFR : IsFractionRing (TensorProduct K A (FractionRing R))
      (FractionRing (TensorProduct K A R)) :=
    isFractionRing_tensorToFracB (K := K) (A := A) (R := R)
  -- the ideal of denominators of `u` in the generic fibre
  let D : Ideal (TensorProduct K A (FractionRing R)) :=
    { carrier := {a | ∃ n : TensorProduct K A (FractionRing R),
        u * algebraMap (TensorProduct K A (FractionRing R))
              (FractionRing (TensorProduct K A R)) a
          = algebraMap (TensorProduct K A (FractionRing R))
              (FractionRing (TensorProduct K A R)) n}
      add_mem' := by
        rintro a b ⟨n, hn⟩ ⟨m, hm⟩
        exact ⟨n + m, by rw [map_add, map_add, mul_add, hn, hm]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨n, hn⟩
        refine ⟨c * n, ?_⟩
        rw [Algebra.smul_def c a,
          show algebraMap (TensorProduct K A (FractionRing R))
              (TensorProduct K A (FractionRing R)) c = c from rfl,
          map_mul, map_mul, mul_left_comm, hn] }
  have hD : D = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪max, hD𝔪⟩ := Ideal.exists_le_maximal D hne
    haveI : 𝔪.IsMaximal := h𝔪max
    rcases eq_or_ne 𝔪 ⊥ with rfl | h𝔪ne
    · obtain ⟨n, s, hs, hns⟩ := exists_localization_bot (K := K) (A := A) (R := R) u
      exact hs (hD𝔪 (show s ∈ D from ⟨n, hns⟩))
    · obtain ⟨n, s, hs, hns⟩ :=
        exists_localization_of_isMaximal (K := K) (A := A) (R := R) hht h𝔪ne
      exact hs (hD𝔪 (show s ∈ D from ⟨n, hns⟩))
  have h1 : (1 : TensorProduct K A (FractionRing R)) ∈ D := by rw [hD]; exact Submodule.mem_top
  obtain ⟨n, hn⟩ := h1
  have hu_eq : u = algebraMap (TensorProduct K A (FractionRing R))
      (FractionRing (TensorProduct K A R)) n := by simpa using hn
  obtain ⟨β, ρ, hρ, hβ⟩ := exists_mul_eq_tensorToFractionRing (K := K) (A := A) (R := R) n
  refine ⟨β, ρ, hρ, ?_⟩
  rw [← algebraMap_tensorToFracB (K := K) (A := A) (R := R) β,
    algebraMap_tensorToFractionRing (K := K) (A := A) (R := R) β, ← hβ, map_mul, ← hu_eq]


end LocalizationSetup





















end Work.SpecLin.Setup
