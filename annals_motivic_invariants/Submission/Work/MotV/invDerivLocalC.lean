import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.derivBoundMem
import Submission.Work.MotV.invDerivOnA
import Submission.Work.MotC2.InfPlaceLocalization
import Submission.Work.MotC2.Classification
import Submission.Work.MotV5.affPlace_deriv_bound
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open Work.MotC2

variable {N : Type*} [Field N]

/-! ## The order calculus at a place, from the multiplicativity hypothesis

The multiplicativity `hMul` of the order at a rational place (a hypothesis of `invDerivLocalC`)
implies that the order behaves like a valuation on the multiplicative group: `ord 1 = 0`,
`ord (-x) = ord x`, `ord x⁻¹ = -ord x` and `ord (x ^ n) = n * ord x`. -/

/-- `ordOfPlace E S hS 1 = 0`. -/
private lemma ordOfPlace_one_of_mul (E : WeierstrassCurve N)
    (hMul : ∀ (S : Subalgebra N (Func E)) (hS : IsRatPlace E S)
      (f g : Func E), f ≠ 0 → g ≠ 0 →
      ordOfPlace E S hS (f * g) = ordOfPlace E S hS f + ordOfPlace E S hS g)
    (S : Subalgebra N (Func E)) (hS : IsRatPlace E S) :
    ordOfPlace E S hS (1 : Func E) = 0 := by
  have h := hMul S hS 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  linarith

/-- `ordOfPlace E S hS (-x) = ordOfPlace E S hS x` for `x ≠ 0`. -/
private lemma ordOfPlace_neg_of_mul (E : WeierstrassCurve N)
    (hMul : ∀ (S : Subalgebra N (Func E)) (hS : IsRatPlace E S)
      (f g : Func E), f ≠ 0 → g ≠ 0 →
      ordOfPlace E S hS (f * g) = ordOfPlace E S hS f + ordOfPlace E S hS g)
    {S : Subalgebra N (Func E)} (hS : IsRatPlace E S) {x : Func E} (hx : x ≠ 0) :
    ordOfPlace E S hS (-x) = ordOfPlace E S hS x := by
  have h1 := hMul S hS (-1 : Func E) (-1) (by norm_num) (by norm_num)
  have h1' : ordOfPlace E S hS (-1 : Func E) = 0 := by
    rw [show (-1 : Func E) * (-1) = 1 by ring, ordOfPlace_one_of_mul E hMul S hS] at h1
    linarith
  have h2 := hMul S hS (-1 : Func E) x (by norm_num) hx
  rw [neg_one_mul, h1', zero_add] at h2
  exact h2

/-- `ordOfPlace E S hS x⁻¹ = -ordOfPlace E S hS x` for `x ≠ 0`. -/
private lemma ordOfPlace_inv_of_mul (E : WeierstrassCurve N)
    (hMul : ∀ (S : Subalgebra N (Func E)) (hS : IsRatPlace E S)
      (f g : Func E), f ≠ 0 → g ≠ 0 →
      ordOfPlace E S hS (f * g) = ordOfPlace E S hS f + ordOfPlace E S hS g)
    {S : Subalgebra N (Func E)} (hS : IsRatPlace E S) {x : Func E} (hx : x ≠ 0) :
    ordOfPlace E S hS x⁻¹ = - ordOfPlace E S hS x := by
  have h := hMul S hS x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordOfPlace_one_of_mul E hMul S hS] at h
  linarith

/-- `ordOfPlace E S hS (x ^ n) = n * ordOfPlace E S hS x` for `x ≠ 0`. -/
private lemma ordOfPlace_pow_of_mul (E : WeierstrassCurve N)
    (hMul : ∀ (S : Subalgebra N (Func E)) (hS : IsRatPlace E S)
      (f g : Func E), f ≠ 0 → g ≠ 0 →
      ordOfPlace E S hS (f * g) = ordOfPlace E S hS f + ordOfPlace E S hS g)
    {S : Subalgebra N (Func E)} (hS : IsRatPlace E S) {x : Func E} (hx : x ≠ 0) (n : ℕ) :
    ordOfPlace E S hS (x ^ n) = n * ordOfPlace E S hS x := by
  induction n with
  | zero => rw [pow_zero, ordOfPlace_one_of_mul E hMul S hS, Nat.cast_zero, zero_mul]
  | succ k ih =>
      rw [pow_succ, hMul S hS _ x (pow_ne_zero k hx) hx, ih]
      push_cast
      first | refl_ring1 | ring

/-! ## The invariant derivation is regular at every rational place

`D` is the derivation of the function field with `D x = 2y + a₁x + a₃` and
`D y = 3x² + 2a₂x + a₄ - a₁y`, i.e. the derivation dual to the invariant differential.  Since
every rational place is the local ring of an affine rational point or the point at infinity
(`MotC2.Classification`), and `D` preserves both coordinate rings, it preserves every rational
place. -/

/-- **The invariant derivation preserves every rational place.** -/
private theorem derivMemPlaceAux (E : WeierstrassCurve N) [E.IsElliptic]
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₃)
    (hDy : D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₄ -
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E) :
    ∀ (S : Subalgebra N (MotC2.Func E)) (hS : IsRatPlace E S) (f : MotC2.Func E),
      f ∈ S → D f ∈ S := by
  -- the two chart coordinates and their images under `D`
  have hDu : D (MotC2.infU E) = -(2 * MotC2.infW E +
      algebraMap N (MotC2.Func E) E.a₁ * MotC2.infU E +
      algebraMap N (MotC2.Func E) E.a₃ * (MotC2.infU E) ^ 2) := by
    have h1 : D (MotC2.infU E) = -(MotC2.infU E) ^ 2 * D (MotC2.genX E) := by
      simpa [MotC2.infU, smul_eq_mul] using Derivation.leibniz_inv D (MotC2.genX E)
    rw [h1, hDx, MotC2.infW, MotC2.infU]
    have hx : MotC2.genX E ≠ 0 := MotC2.genX_ne_zero E
    field_simp
  have hDw : D (MotC2.infW E) = -(1 + 2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.infU E +
      3 * algebraMap N (MotC2.Func E) E.a₄ * (MotC2.infU E) ^ 2 +
      4 * algebraMap N (MotC2.Func E) E.a₆ * (MotC2.infU E) ^ 3 -
      algebraMap N (MotC2.Func E) E.a₁ * MotC2.infW E -
      2 * algebraMap N (MotC2.Func E) E.a₃ * MotC2.infU E * MotC2.infW E) := by
    have hD2 : D ((MotC2.genX E) ^ 2) = 2 * MotC2.genX E * D (MotC2.genX E) := by
      rw [Derivation.leibniz_pow]
      simp only [smul_eq_mul, Nat.reduceSub, pow_one]
      first | refl_ring1 | ring
    rw [MotC2.infW, Derivation.leibniz_div]
    simp only [smul_eq_mul]
    rw [hD2, hDx, hDy, MotC2.infU]
    have hx : MotC2.genX E ≠ 0 := MotC2.genX_ne_zero E
    field_simp
    linear_combination (norm := first | refl_ring1 | ring1) (-4 : MotC2.Func E) * MotC2.genY_sq_relation E
  -- `D` preserves the chart ring `infCoordRing E = N[1/x, y/x²]`
  have hchart : ∀ r : MotC2.Func E, r ∈ MotC2.infCoordRing E → D r ∈ MotC2.infCoordRing E := by
    intro r hr
    rw [MotC2.infCoordRing] at hr ⊢
    set A : Subalgebra N (MotC2.Func E) :=
      Algebra.adjoin N ({MotC2.infU E, MotC2.infW E} : Set (MotC2.Func E))
    have hun : MotC2.infU E ∈ A := Algebra.subset_adjoin (Set.mem_insert _ _)
    have hwn : MotC2.infW E ∈ A := Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    have hcn : ∀ c : N, algebraMap N (MotC2.Func E) c ∈ A := fun c =>
      Subalgebra.algebraMap_mem A c
    have hnn : ∀ n : ℕ, (n : MotC2.Func E) ∈ A := fun n => by
      simpa using Subalgebra.algebraMap_mem A (n : N)
    have hDumem : D (MotC2.infU E) ∈ A := by
      rw [hDu]
      exact Subalgebra.neg_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hnn 2) hwn)
          (Subalgebra.mul_mem _ (hcn E.a₁) hun))
        (Subalgebra.mul_mem _ (hcn E.a₃) (Subalgebra.pow_mem _ hun 2)))
    have hDwmem : D (MotC2.infW E) ∈ A := by
      rw [hDw]
      refine Subalgebra.neg_mem _ ?_
      have h123 : 1 + 2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.infU E +
          3 * algebraMap N (MotC2.Func E) E.a₄ * (MotC2.infU E) ^ 2 +
          4 * algebraMap N (MotC2.Func E) E.a₆ * (MotC2.infU E) ^ 3 ∈ A :=
        Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
          (Subalgebra.one_mem A)
          (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hnn 2) (hcn E.a₂)) hun))
          (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hnn 3) (hcn E.a₄)) (Subalgebra.pow_mem _ hun 2)))
          (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hnn 4) (hcn E.a₆)) (Subalgebra.pow_mem _ hun 3))
      exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ h123 (Subalgebra.mul_mem _ (hcn E.a₁) hwn))
        (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hnn 2) (hcn E.a₃)) hun) hwn)
    have hgen : ∀ s ∈ ({MotC2.infU E, MotC2.infW E} : Set (MotC2.Func E)), D s ∈ A := by
      rintro s (rfl | rfl)
      · exact hDumem
      · exact hDwmem
    exact deriv_maps_adjoin D ({MotC2.infU E, MotC2.infW E} : Set (MotC2.Func E)) hgen r hr
  -- `D` preserves `infPlace E`, the localization of the chart ring
  have hinf : ∀ f : MotC2.Func E, f ∈ MotC2.infPlace E → D f ∈ MotC2.infPlace E := by
    have key : ∀ x : MotC2.Func E, x ∈ Algebra.adjoin N
        ((MotC2.infCoordRing E : Set (MotC2.Func E)) ∪
          ((fun r : MotC2.Func E => r⁻¹) ''
            {r : MotC2.Func E | r ∈ MotC2.infCoordRing E ∧ r ∉ MotC2.infIdeal E})) →
        D x ∈ MotC2.infPlace E := by
      intro x hx'
      induction hx' using Algebra.adjoin_induction with
      | mem y hy' =>
          rcases hy' with hy' | ⟨r, ⟨hr, hrn⟩, rfl⟩
          · exact MotC2.InfAux.mem_infPlace_of_mem E ⟨D y, hchart y hy'⟩
          · have hrS : r⁻¹ ∈ MotC2.infPlace E :=
              MotC2.InfAux.inv_mem_infPlace_of_notMem E
                (fun hrel => hrn ((MotC2.InfAux.mem_infIdealR_iff E ⟨r, hr⟩).mpr hrel))
            have hDr : D r ∈ MotC2.infPlace E :=
              MotC2.InfAux.mem_infPlace_of_mem E ⟨D r, hchart r hr⟩
            rw [Derivation.leibniz_inv D r, smul_eq_mul]
            exact Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.pow_mem _ hrS 2)) hDr
      | algebraMap c =>
          rw [Derivation.map_algebraMap]
          exact Subalgebra.zero_mem _
      | add x y hx hy ihx ihy =>
          rw [map_add]
          exact Subalgebra.add_mem _ ihx ihy
      | mul x y hx hy ihx ihy =>
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
          exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx ihy) (Subalgebra.mul_mem _ hy ihx)
    intro f hf
    exact key f hf
  intro S hS f hf
  rcases MotC2.Classification N E S hS with h | ⟨a, b, hns, h⟩
  · subst h
    exact hinf f hf
  · subst h
    exact MotV5.deriv_mem_affPlaceAt E a b D hDx hDy f hf

theorem invDerivLocalC {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (hMul : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f g : Work.MotC2.Func E), f ≠ 0 → g ≠ 0 →
      Work.MotV.ordOfPlace E S hS (f * g) =
        Work.MotV.ordOfPlace E S hS f + Work.MotV.ordOfPlace E S hS g)
    (hAdd : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f g : Work.MotC2.Func E), f + g ≠ 0 →
      min (Work.MotV.ordOfPlace E S hS f) (Work.MotV.ordOfPlace E S hS g) ≤
        Work.MotV.ordOfPlace E S hS (f + g))
    (hNonneg : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E), 0 ≤ Work.MotV.ordOfPlace E S hS f ↔ f ∈ S)
    (hAff : ∀ (a b : N) (h : WeierstrassCurve.Affine.Nonsingular E a b),
      (2 * b + E.a₁ * a + E.a₃ ≠ 0 →
        Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
            (Work.MotC2.AffPlace N E a b h).1
            (Work.MotC2.genX E - algebraMap N (Work.MotC2.Func E) a) = 1) ∧
      (2 * b + E.a₁ * a + E.a₃ = 0 →
        Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
            (Work.MotC2.AffPlace N E a b h).1
            (Work.MotC2.genX E - algebraMap N (Work.MotC2.Func E) a) = 2 ∧
        Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
            (Work.MotC2.AffPlace N E a b h).1
            (Work.MotC2.genY E - algebraMap N (Work.MotC2.Func E) b) = 1))
    (hInfRat : Work.MotC2.IsRatPlace E (Work.MotC2.infPlace E))
    (hInf : Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInfRat (Work.MotC2.genX E) = -2 ∧
      Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInfRat (Work.MotC2.infU E) = 2 ∧
      Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInfRat (Work.MotC2.infW E) = 1 ∧
      Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInfRat (Work.MotC2.genY E) = -3)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hDx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hDy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) :
    (∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E), D f ≠ 0 →
      Work.MotV.ordOfPlace E S hS f - 1 ≤ Work.MotV.ordOfPlace E S hS (D f)) ∧
    (∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E),
      Work.MotV.ordOfPlace E S hS f = 0 → 0 ≤ Work.MotV.ordOfPlace E S hS (D f)) := by
  -- `D` preserves the local ring of every rational place
  have hmem : ∀ (S : Subalgebra N (Func E)) (hS : IsRatPlace E S) (f : Func E),
      f ∈ S → D f ∈ S := derivMemPlaceAux E D hDx hDy
  refine ⟨?_, ?_⟩
  · intro S hS f hDf
    by_cases hf : f ∈ S
    · -- `f` is regular at the place: the discrete valuation ring computation
      exact derivBoundMem E D hmem S hS hf hDf
    · -- `f` has a pole: apply the regular case to `f⁻¹` and invert
      have hf0 : f ≠ 0 := fun h => hf (h ▸ S.zero_mem)
      have hgS : f⁻¹ ∈ S := (mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf
      have hDg : D f⁻¹ ≠ 0 := by
        intro h0
        refine hDf ?_
        have hleib := Derivation.leibniz_inv D f⁻¹
        rw [inv_inv, h0] at hleib
        simpa using hleib
      have hb := derivBoundMem E D hmem S hS hgS hDg
      have hinv : ordOfPlace E S hS f⁻¹ = - ordOfPlace E S hS f :=
        ordOfPlace_inv_of_mul E hMul hS hf0
      have hDfeq : D f = -(f ^ 2 * D f⁻¹) := by
        have h := Derivation.leibniz_inv D f⁻¹
        rw [inv_inv] at h
        rw [h, smul_eq_mul]
        first | refl_ring1 | ring
      have hne : f ^ 2 * D f⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hf0) hDg
      have hord : ordOfPlace E S hS (D f) =
          2 * ordOfPlace E S hS f + ordOfPlace E S hS (D f⁻¹) := by
        rw [hDfeq, ordOfPlace_neg_of_mul E hMul hS hne,
          hMul S hS _ _ (pow_ne_zero 2 hf0) hDg, ordOfPlace_pow_of_mul E hMul hS hf0 2]
        first | refl_ring1 | ring
      linarith
  · intro S hS f hf0
    -- `ord f = 0` means `f` is regular at the place, and `D` preserves regularity
    have hmemf : f ∈ S := (hNonneg S hS f).mp (le_of_eq hf0.symm)
    exact (hNonneg S hS (D f)).mpr (hmem S hS f hmemf)

end Work.MotV
