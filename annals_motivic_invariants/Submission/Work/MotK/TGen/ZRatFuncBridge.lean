import Mathlib
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotK.TGen.ZRatFuncBridge` — the bookkeeping `Frac (A[X]) ≅ RatFunc B` from `Frac A ≅ B`

The statement

`Nonempty (FractionRing A ≃ₐ[K] B) → Nonempty (FractionRing (Polynomial A) ≃ₐ[K] RatFunc B)`

is the last step of the K6 bridge (`Work.MotK.TGen.ZTorsorBridge`, §4): once the chart ring `R`
of the residual curve is known to have fraction field `F₂ = twistFieldTG K D (h²)`, the rational
parameter is adjoined on both sides, and the two statements `Frac R ≅ F₂` and
`Frac (R[X]) ≅ RatFunc F₂` carry the same information.

## The proof

Write `S := FractionRing A`, so that the hypothesis gives a `K`-isomorphism `e : S ≃ₐ[K] B`.  The
map `A → S` is injective (the localisation at the non-zero-divisors is injective for every
commutative ring), and since `S ≅ B` is a field, `A` is an integral domain; we record this as
`IsDomain A`, so that every ring in sight is a domain and `nonZeroDivisors _ = {x | x ≠ 0}`.

Both sides are "the same rational function field with a different base field": `RatFunc B` is the
fraction ring of `B[X]`, and `B` is the fraction ring of `A`.  The proof therefore exhibits
`RatFunc B` directly as **a fraction ring of `A[X]`**, through the `K`-algebra map

`Φ : A[X] →ₐ[K] RatFunc B`,  `Φ = algebraMap (B[X]) (RatFunc B) ∘ Polynomial.map j`,  `j = e ∘ algebraMap A S`,

and then compares it with the canonical fraction ring `FractionRing (A[X])` by
`IsLocalization.algEquiv`.  The three `IsLocalization` axioms are:

* *units*: `Φ` is injective (`Polynomial.map j` is injective because `j` is, and `B[X] → RatFunc B`
  is) and `RatFunc B` is a field, so a non-zero-divisor goes to a unit;
* *surjectivity* (`poly_clear` below): every element of `RatFunc B` is a quotient `p / q` with
  `p, q ∈ B[X]`, and each coefficient `c ∈ B` of `p` (resp. `q`) can be written `c = j a / j s`
  with `s ≠ 0` (`IsLocalization.surj` for `A → S`); multiplying `p` by the constant
  `C (j D)`, `D` the product of the denominators, clears all denominators, and the two cleared
  numerators/denominators give the required `z = Φ x / Φ y`;
* *equality*: `Φ` is injective, so `x = y` and the witness `1` works.

The passage from the `A[X]`-linear isomorphism to a `K`-linear one is `AlgEquiv.restrictScalars K`,
available because `Φ` is a `K`-algebra map (`hΦK`).
-/

namespace Work.MotK.TGen

open Polynomial

theorem ZRatFuncBridge (K A B : Type) [Field K] [CommRing A] [Field B] [Algebra K A] [Algebra K B] (h : Nonempty (FractionRing A ≃ₐ[K] B)) : Nonempty (FractionRing (Polynomial A) ≃ₐ[K] RatFunc B) := by
  obtain ⟨e⟩ := h
  -- `FractionRing A` is (isomorphic to) the field `B`, hence a domain, hence `A` is one too.
  haveI hFRdom : IsDomain (FractionRing A) :=
    Function.Injective.isDomain (e : FractionRing A →+* B) e.injective
  haveI hAdom : IsDomain A :=
    Function.Injective.isDomain (algebraMap A (FractionRing A))
      (IsFractionRing.injective A (FractionRing A))
  -- `j : A →ₐ[K] B` is the tautological `K`-algebra map `A → FractionRing A ≅ B`.
  let j : A →ₐ[K] B := e.toAlgHom.comp (IsScalarTower.toAlgHom K A (FractionRing A))
  have hj_inj : Function.Injective j := by
    intro x y hxy
    apply IsFractionRing.injective A (FractionRing A)
    apply e.injective
    exact hxy
  have hje : ∀ a, j a = e (algebraMap A (FractionRing A) a) := fun a => rfl
  -- Every element of `B` is `j a / j s` with `s` a non-zero-divisor of `A`.
  have coeff_clear : ∀ c : B, ∃ a : A, ∃ s : A, s ≠ 0 ∧ c * j s = j a := by
    intro c
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) (e.symm c)
    refine ⟨a, s, nonZeroDivisors.ne_zero s.2, ?_⟩
    have := congrArg e hs
    simpa [hje, map_mul] using this
  -- Clearing denominators, coefficient by coefficient, for a polynomial over `B`.
  let ψ : Polynomial A →+* Polynomial B := Polynomial.mapRingHom j.toRingHom
  have hψ_inj : Function.Injective ψ := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective j.toRingHom hj_inj
  have hψC : ∀ D : A, ψ (Polynomial.C D) = Polynomial.C (j D) := by
    intro D
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
    rfl
  have poly_clear : ∀ p : Polynomial B, ∃ P : Polynomial A, ∃ D : A,
      D ≠ 0 ∧ ψ P = p * Polynomial.C (j D) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        obtain ⟨P₁, D₁, hD₁, hP₁⟩ := hp
        obtain ⟨P₂, D₂, hD₂, hP₂⟩ := hq
        refine ⟨P₁ * Polynomial.C D₂ + P₂ * Polynomial.C D₁, D₁ * D₂,
          mul_ne_zero hD₁ hD₂, ?_⟩
        rw [map_add, map_mul, map_mul, hP₁, hP₂, hψC, hψC, map_mul j D₁ D₂, Polynomial.C_mul]
        first | refl_ring1 | ring
    | monomial n a =>
        obtain ⟨a', s, hs, ha⟩ := coeff_clear a
        refine ⟨Polynomial.monomial n a', s, hs, ?_⟩
        rw [Polynomial.coe_mapRingHom, Polynomial.map_monomial, Polynomial.monomial_mul_C, ha]
        rfl
  -- The `K`-algebra map `Φ : A[X] →ₐ[K] RatFunc B` through which `RatFunc B` is a fraction
  -- ring of `A[X]`.
  let Φ : Polynomial A →+* RatFunc B := (algebraMap (Polynomial B) (RatFunc B)).comp ψ
  have hΦK : ∀ k : K, Φ (algebraMap K (Polynomial A) k) = algebraMap K (RatFunc B) k := by
    intro k
    change ((algebraMap (Polynomial B) (RatFunc B)).comp (Polynomial.mapRingHom j.toRingHom))
        (algebraMap K (Polynomial A) k) = algebraMap K (RatFunc B) k
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom]
    rw [IsScalarTower.algebraMap_apply K A (Polynomial A), ← Polynomial.C_eq_algebraMap,
        Polynomial.map_C (f := j.toRingHom),
        show j.toRingHom ((algebraMap K A) k) = algebraMap K B k from j.commutes k,
        Polynomial.C_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply B (Polynomial B) (RatFunc B),
        ← IsScalarTower.algebraMap_apply K B (RatFunc B)]
  have hΦ_inj : Function.Injective Φ :=
    (IsFractionRing.injective (Polynomial B) (RatFunc B)).comp hψ_inj
  -- View `RatFunc B` as an `A[X]`-algebra through `Φ` and check the three `IsLocalization` axioms.
  letI : Algebra (Polynomial A) (RatFunc B) := Φ.toAlgebra
  haveI hST : IsScalarTower K (Polynomial A) (RatFunc B) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (hΦK k).symm
  have surj : ∀ z : RatFunc B, ∃ x : Polynomial A × nonZeroDivisors (Polynomial A),
      z * algebraMap (Polynomial A) (RatFunc B) x.2 = algebraMap (Polynomial A) (RatFunc B) x.1 := by
    rw [RingHom.algebraMap_toAlgebra]
    intro z
    induction z using RatFunc.induction_on with
    | _ p q hq =>
      obtain ⟨P₁, D₁, hD₁, hP₁⟩ := poly_clear p
      obtain ⟨P₂, D₂, hD₂, hP₂⟩ := poly_clear q
      have hqΦ : algebraMap (Polynomial B) (RatFunc B) q ≠ 0 :=
        fun h0 => hq ((IsFractionRing.injective (Polynomial B) (RatFunc B))
          (by rw [h0, map_zero]))
      have hjD₂ : j D₂ ≠ 0 := fun h0 => hD₂ (hj_inj (by rw [h0, map_zero]))
      have hP₂ne : P₂ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hP₂
        exact mul_ne_zero hq (Polynomial.C_ne_zero.mpr hjD₂) hP₂.symm
      have hY : P₂ * Polynomial.C D₁ ≠ 0 :=
        mul_ne_zero hP₂ne (Polynomial.C_ne_zero.mpr hD₁)
      refine ⟨⟨P₁ * Polynomial.C D₂,
        ⟨P₂ * Polynomial.C D₁, mem_nonZeroDivisors_iff_ne_zero.mpr hY⟩⟩, ?_⟩
      have hX : Φ (P₁ * Polynomial.C D₂) =
          algebraMap (Polynomial B) (RatFunc B) p
            * algebraMap (Polynomial B) (RatFunc B) (Polynomial.C (j D₁))
            * algebraMap (Polynomial B) (RatFunc B) (Polynomial.C (j D₂)) := by
        rw [map_mul]
        congr 1
        · show algebraMap (Polynomial B) (RatFunc B) (ψ P₁) = _
          rw [hP₁, map_mul]
        · show algebraMap (Polynomial B) (RatFunc B) (ψ (Polynomial.C D₂)) = _
          rw [hψC D₂]
      have hY' : Φ (P₂ * Polynomial.C D₁) =
          algebraMap (Polynomial B) (RatFunc B) q
            * algebraMap (Polynomial B) (RatFunc B) (Polynomial.C (j D₂))
            * algebraMap (Polynomial B) (RatFunc B) (Polynomial.C (j D₁)) := by
        rw [map_mul]
        congr 1
        · show algebraMap (Polynomial B) (RatFunc B) (ψ P₂) = _
          rw [hP₂, map_mul]
        · show algebraMap (Polynomial B) (RatFunc B) (ψ (Polynomial.C D₁)) = _
          rw [hψC D₁]
      rw [hX, hY', div_mul_eq_mul_div]
      field_simp
  have h1 : ∀ y : nonZeroDivisors (Polynomial A),
      IsUnit (algebraMap (Polynomial A) (RatFunc B) ↑y) := by
    intro y
    rw [RingHom.algebraMap_toAlgebra]
    exact isUnit_iff_ne_zero.mpr fun h0 =>
      nonZeroDivisors.ne_zero y.2 (hΦ_inj (by rw [h0, map_zero]))
  have h3 : ∀ {x y : Polynomial A},
      algebraMap (Polynomial A) (RatFunc B) x = algebraMap (Polynomial A) (RatFunc B) y →
        ∃ c : nonZeroDivisors (Polynomial A), ↑c * x = ↑c * y := by
    intro x y hxy
    rw [RingHom.algebraMap_toAlgebra] at hxy
    exact ⟨1, by rw [hΦ_inj hxy]⟩
  haveI : IsLocalization (nonZeroDivisors (Polynomial A)) (RatFunc B) :=
    (isLocalization_iff (nonZeroDivisors (Polynomial A)) (RatFunc B)).mpr ⟨h1, surj, h3⟩
  exact ⟨(IsLocalization.algEquiv (nonZeroDivisors (Polynomial A))
    (FractionRing (Polynomial A)) (RatFunc B)).restrictScalars K⟩

end Work.MotK.TGen
