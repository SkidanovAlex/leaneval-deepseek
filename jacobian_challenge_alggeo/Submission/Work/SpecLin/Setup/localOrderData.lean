import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Alt.conservationNumber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Setup

universe u

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- **The chart dictionary extended to the fraction field of the relative chart.**

`chartTensorMap : B = Γ(C,W) ⊗[K] R →+* K(C_F)` exhibits `K(C_F)` as the fraction field of `B`;
this is the induced map `FractionRing B →+* K(C_F)`. -/
noncomputable def chartTensorFracMap (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    [IsDomain (Work.SpecLin.Core.chartTensor R W)] :
    FractionRing (Work.SpecLin.Core.chartTensor R W) →+*
      (C.baseChange (FractionRing R)).functionField :=
  IsLocalization.lift
    (M := nonZeroDivisors (Work.SpecLin.Core.chartTensor R W))
    (g := Work.SpecLin.Alt.chartTensorMap R W hW)
    (fun y => by
      letI : Algebra (Work.SpecLin.Core.chartTensor R W)
          (C.baseChange (FractionRing R)).functionField :=
        (Work.SpecLin.Alt.chartTensorMap R W hW).toAlgebra
      haveI : IsFractionRing (Work.SpecLin.Core.chartTensor R W)
          (C.baseChange (FractionRing R)).functionField :=
        Work.SpecLin.Alt.chartTensorMap_isFractionRing R W hW
      have hinj : Function.Injective (algebraMap (Work.SpecLin.Core.chartTensor R W)
          (C.baseChange (FractionRing R)).functionField) :=
        IsFractionRing.injective _ _
      have hne : algebraMap (Work.SpecLin.Core.chartTensor R W)
          (C.baseChange (FractionRing R)).functionField (y : Work.SpecLin.Core.chartTensor R W) ≠ 0 :=
        fun h => nonZeroDivisors.ne_zero y.2 (hinj (by rw [h, map_zero]))
      have hg : (Work.SpecLin.Alt.chartTensorMap R W hW) (y : Work.SpecLin.Core.chartTensor R W)
          = algebraMap (Work.SpecLin.Core.chartTensor R W)
              (C.baseChange (FractionRing R)).functionField
              (y : Work.SpecLin.Core.chartTensor R W) := rfl
      rw [hg]
      exact isUnit_iff_ne_zero.mpr hne)

theorem chartTensorFracMap_algebraMap (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    [IsDomain (Work.SpecLin.Core.chartTensor R W)]
    (b : Work.SpecLin.Core.chartTensor R W) :
    chartTensorFracMap R W hW
        (algebraMap (Work.SpecLin.Core.chartTensor R W)
          (FractionRing (Work.SpecLin.Core.chartTensor R W)) b)
      = Work.SpecLin.Alt.chartTensorMap R W hW b :=
  IsLocalization.lift_eq _ b

theorem chartTensorFracMap_injective (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    [IsDomain (Work.SpecLin.Core.chartTensor R W)] :
    Function.Injective (chartTensorFracMap (K := K) (C := C) R W hW) := by
  have hφinj : Function.Injective (Work.SpecLin.Alt.chartTensorMap R W hW) := by
    letI : Algebra (Work.SpecLin.Core.chartTensor R W)
        (C.baseChange (FractionRing R)).functionField :=
      (Work.SpecLin.Alt.chartTensorMap R W hW).toAlgebra
    haveI : IsFractionRing (Work.SpecLin.Core.chartTensor R W)
        (C.baseChange (FractionRing R)).functionField :=
      Work.SpecLin.Alt.chartTensorMap_isFractionRing R W hW
    exact IsFractionRing.injective _ _
  have key : ∀ x : FractionRing (Work.SpecLin.Core.chartTensor R W),
      chartTensorFracMap (K := K) (C := C) R W hW x = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective
      (Work.SpecLin.Core.chartTensor R W) x
    have hb0 : algebraMap _ (FractionRing (Work.SpecLin.Core.chartTensor R W)) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hab' : algebraMap _ (FractionRing (Work.SpecLin.Core.chartTensor R W)) a
        = x * algebraMap _ (FractionRing (Work.SpecLin.Core.chartTensor R W)) b := by
      rw [← div_mul_cancel₀
        (algebraMap _ (FractionRing (Work.SpecLin.Core.chartTensor R W)) a) hb0, hab]
    have h1 : Work.SpecLin.Alt.chartTensorMap R W hW a = 0 := by
      have h := congrArg (chartTensorFracMap (K := K) (C := C) R W hW) hab'
      rw [map_mul, chartTensorFracMap_algebraMap, chartTensorFracMap_algebraMap, hx, zero_mul] at h
      exact h
    have ha : a = 0 := hφinj (by rw [h1, map_zero])
    rw [← hab, ha, map_zero, zero_div]
  intro x y hxy
  have hz : chartTensorFracMap (K := K) (C := C) R W hW (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) hz)


section Bridge

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
variable [IsDomain (Work.SpecLin.Core.chartTensor R W)]

/-- **The order dictionary, relative to the fraction field `FractionRing B` of the chart.** -/
theorem inLocalization_iff_ordAt
    (p : Ideal (Work.SpecLin.Core.chartTensor R W)) [p.IsPrime]
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQ : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ p ∧
          x * Work.SpecLin.Alt.chartTensorMap R W hW b
            = Work.SpecLin.Alt.chartTensorMap R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q)
    (y : FractionRing (Work.SpecLin.Core.chartTensor R W)) :
    Work.SpecLin.Alt.InLocalization y p
      ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt
          (chartTensorFracMap R W hW y) Q := by
  constructor
  · rintro ⟨a, b, hb, hy⟩
    refine (hQ _).mp ⟨a, b, hb, ?_⟩
    rw [← chartTensorFracMap_algebraMap R W hW b, ← map_mul, hy,
      chartTensorFracMap_algebraMap R W hW a]
  · intro h
    obtain ⟨a, b, hb, hab⟩ := (hQ _).mpr h
    refine ⟨a, b, hb, ?_⟩
    apply chartTensorFracMap_injective R W hW
    rw [map_mul, chartTensorFracMap_algebraMap R W hW b,
      chartTensorFracMap_algebraMap R W hW a]
    exact hab

/-- **A rational function is a unit at `p` if and only if its order (at the place `Q`
corresponding to `p`) vanishes.** -/
theorem isUnitAt_iff_ordAt_eq_zero
    (p : Ideal (Work.SpecLin.Core.chartTensor R W)) [p.IsPrime]
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQ : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ p ∧
          x * Work.SpecLin.Alt.chartTensorMap R W hW b
            = Work.SpecLin.Alt.chartTensorMap R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q)
    (y : FractionRing (Work.SpecLin.Core.chartTensor R W)) (hy : y ≠ 0) :
    Work.SpecLin.Alt.IsUnitAt y p
      ↔ (C.baseChange (FractionRing R)).ordAt
          (chartTensorFracMap R W hW y) Q = 0 := by
  have hΦy : chartTensorFracMap (K := K) (C := C) R W hW y ≠ 0 :=
    fun h => hy (chartTensorFracMap_injective R W hW (by rw [h, map_zero]))
  have hΦinv : chartTensorFracMap (K := K) (C := C) R W hW y⁻¹
      = (chartTensorFracMap (K := K) (C := C) R W hW y)⁻¹ :=
    map_inv₀ _ y
  rw [Work.SpecLin.Alt.IsUnitAt,
    inLocalization_iff_ordAt R W hW p Q hQ y,
    inLocalization_iff_ordAt R W hW p Q hQ y⁻¹, hΦinv,
    Work.CurveBasics.Curve.ordAt_inv _ hΦy Q]
  constructor
  · rintro ⟨h1, h2⟩; omega
  · intro h; exact ⟨by omega, by omega⟩

end Bridge


section Tower

/-- The canonical ring map `B_N → B_p` between two localisations of `B` at primes `p ≤ N`. -/
noncomputable def locAtPrimeMap {B : Type u} [CommRing B] [IsDomain B]
    (N p : Ideal B) [N.IsPrime] [p.IsPrime] (h : p ≤ N) :
    Localization.AtPrime N →+* Localization.AtPrime p :=
  IsLocalization.lift (M := N.primeCompl)
    (g := algebraMap B (Localization.AtPrime p))
    (fun y => IsLocalization.map_units (Localization.AtPrime p)
      (⟨(y : B), fun hy => y.2 (h hy)⟩ : p.primeCompl))

theorem locAtPrimeMap_algebraMap {B : Type u} [CommRing B] [IsDomain B]
    (N p : Ideal B) [N.IsPrime] [p.IsPrime] (h : p ≤ N) (b : B) :
    locAtPrimeMap N p h (algebraMap B (Localization.AtPrime N) b)
      = algebraMap B (Localization.AtPrime p) b :=
  IsLocalization.lift_eq _ b

/-- Localising an ideal statement at `p ≤ N` from `B_N` to `B_p`. -/
theorem ideal_map_atPrime_le {B : Type u} [CommRing B] [IsDomain B]
    (N p : Ideal B) [N.IsPrime] [p.IsPrime] (h : p ≤ N)
    (I : Ideal B) (f : B)
    (hf : Ideal.map (algebraMap B (Localization.AtPrime N)) I
        = Ideal.span {algebraMap B (Localization.AtPrime N) f}) :
    Ideal.map (algebraMap B (Localization.AtPrime p)) I
      = Ideal.span {algebraMap B (Localization.AtPrime p) f} := by
  letI : Algebra (Localization.AtPrime N) (Localization.AtPrime p) :=
    (locAtPrimeMap N p h).toAlgebra
  haveI hST : IsScalarTower B (Localization.AtPrime N) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq (fun b => (locAtPrimeMap_algebraMap N p h b).symm)
  have key : (algebraMap (Localization.AtPrime N) (Localization.AtPrime p)).comp
      (algebraMap B (Localization.AtPrime N)) = algebraMap B (Localization.AtPrime p) :=
    (IsScalarTower.algebraMap_eq B (Localization.AtPrime N) (Localization.AtPrime p)).symm
  calc Ideal.map (algebraMap B (Localization.AtPrime p)) I
      = Ideal.map ((algebraMap (Localization.AtPrime N) (Localization.AtPrime p)).comp
          (algebraMap B (Localization.AtPrime N))) I := by rw [key]
    _ = Ideal.map (algebraMap (Localization.AtPrime N) (Localization.AtPrime p))
          (Ideal.map (algebraMap B (Localization.AtPrime N)) I) := (Ideal.map_map _ _).symm
    _ = Ideal.map (algebraMap (Localization.AtPrime N) (Localization.AtPrime p))
          (Ideal.span {algebraMap B (Localization.AtPrime N) f}) := by rw [hf]
    _ = Ideal.span (singleton (algebraMap (Localization.AtPrime N) (Localization.AtPrime p)
          (algebraMap B (Localization.AtPrime N) f))) := by
          rw [Ideal.map_span, Set.image_singleton]
    _ = Ideal.span {algebraMap B (Localization.AtPrime p) f} := by
          rw [← RingHom.comp_apply, key]

end Tower


section Extraction

/-- **A unit at a prime is a quotient with both terms outside the prime.**  If `u ∈ Frac B` is a
unit of the localisation `B_N` (with `N` a prime), then `u` can be written as `p / q` with
`p, q ∈ B ∖ N`. -/
theorem exists_notMem_of_isUnitAt {B : Type u} [CommRing B] [IsDomain B]
    (N : Ideal B) [N.IsPrime] (u : FractionRing B) (hu : u ≠ 0)
    (h : Work.SpecLin.Alt.IsUnitAt u N) :
    ∃ p q : B, p ∉ N ∧ q ∉ N ∧
      u * algebraMap B (FractionRing B) q = algebraMap B (FractionRing B) p := by
  obtain ⟨p, s, hs, hps⟩ := h.1
  obtain ⟨q, t, ht, hqt⟩ := h.2
  have hstpq : s * t = p * q := by
    refine IsFractionRing.injective B (FractionRing B) ?_
    have key : algebraMap B (FractionRing B) s * algebraMap B (FractionRing B) t
        = algebraMap B (FractionRing B) p * algebraMap B (FractionRing B) q := by
      calc algebraMap B (FractionRing B) s * algebraMap B (FractionRing B) t
          = (u⁻¹ * u) * (algebraMap B (FractionRing B) s
              * algebraMap B (FractionRing B) t) := by rw [inv_mul_cancel₀ hu, one_mul]
        _ = algebraMap B (FractionRing B) p * algebraMap B (FractionRing B) q := by
              rw [← hps, ← hqt]; ring
    rwa [← map_mul, ← map_mul] at key
  have hstN : s * t ∉ N := fun hc => (Ideal.IsPrime.mem_or_mem ‹N.IsPrime› hc).elim hs ht
  have hpq : p * q ∉ N := by rw [← hstpq]; exact hstN
  exact ⟨p, s, fun hc => hpq (Ideal.mul_mem_right q N hc), hs, hps⟩

end Extraction

end Work.SpecLin.Setup
