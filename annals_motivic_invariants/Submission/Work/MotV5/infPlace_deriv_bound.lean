import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.InfAux
import Submission.Work.MotC2.InfPlaceLocalization
import Submission.Work.MotC2.infPlace_nonunit_eq_infW_mul
import Submission.Work.MotC2Cls.Setup
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV5.chart_deriv_aux
import Submission.Work.MotV5.deriv_pow_dvd

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

open WeierstrassCurve WeierstrassCurve.Affine

/-!
# The invariant derivation at the point at infinity

For an elliptic Weierstrass curve `E` over a field `N` of characteristic `5` and the derivation `D`
of the function field `N(E)` with `D x = 2y + a₁x + a₃`, `D y = 3x² + 2a₂x + a₄ - a₁y`:

* `D` preserves the local ring `infPlace E` of the point at infinity `O`;
* for every `f` with a pole at `O`, `ord_O(D f) ≥ ord_O(f) - 1`.

The first statement is proved by checking the two chart coordinates `u = 1/x`, `w = y/x²` (where
`D u = -(2w + a₁u + a₃u²)` and `D w = -1 - 2a₂u - 3a₄u² - 4a₆u³ + a₁w + 2a₃uw`) and closing
under the algebra generators.  The second is a general fact about a derivation preserving a discrete
valuation ring: writing `f⁻¹ = p^m·a` with `p` a uniformiser and `a` a unit, both `D f` and the
`p`-adic order of `D f` are controlled because `D p` and `D a` still lie in the ring.
-/

/-! ## `D` preserves the local ring at infinity -/

/-- **The invariant derivation preserves the local ring at the point at infinity.** -/
theorem deriv_mem_infPlace {N : Type*} [Field N] [CharP N 5] (E : WeierstrassCurve N)
    [E.IsElliptic] (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hx : D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₃)
    (hy : D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₄ -
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E) :
    ∀ f : MotC2.Func E, f ∈ MotC2.infPlace E → D f ∈ MotC2.infPlace E := by
  have hchart : ∀ r : MotC2.Func E, r ∈ MotC2.infCoordRing E → D r ∈ MotC2.infCoordRing E :=
    chart_deriv_aux E D hx hy
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
              (fun h => hrn ((MotC2.InfAux.mem_infIdealR_iff E ⟨r, hr⟩).mpr h))
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

/-! ## Reading `ordOfPlace` off `addVal` -/

/-- `ordOfPlace` at a place where `f` is regular, computed from `addVal`. -/
private lemma ordOfPlace_eq_of {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    {f : MotC2.Func E} (hf : f ∈ S) {n : ℕ}
    (h : @IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose (⟨f, hf⟩ : ↥S) = (n : ℕ∞)) :
    Work.MotV.ordOfPlace E S hS f = n := by
  rw [Work.MotV.ordOfPlace, dif_pos hf, h]
  exact congrArg (fun m : ℕ => (m : ℤ)) (WithTop.untopD_coe (0 : ℕ) n)

/-- `ordOfPlace` at a place where `f` has a pole, computed from `addVal` of `f⁻¹`. -/
private lemma ordOfPlace_eq_neg_of {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    {f : MotC2.Func E} (hf : f ∉ S) {n : ℕ}
    (h : @IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose
      (⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S) = (n : ℕ∞)) :
    Work.MotV.ordOfPlace E S hS f = -(n : ℤ) := by
  rw [Work.MotV.ordOfPlace, dif_neg hf, h]
  exact congrArg (fun m : ℤ => -m)
    (congrArg (fun m : ℕ => (m : ℤ)) (WithTop.untopD_coe (0 : ℕ) n))

/-- `ordOfPlace` is nonnegative on the local ring. -/
private lemma ordOfPlace_nonneg_of_mem {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    {f : MotC2.Func E} (hf : f ∈ S) : 0 ≤ Work.MotV.ordOfPlace E S hS f := by
  rw [Work.MotV.ordOfPlace, dif_pos hf]
  exact Int.ofNat_nonneg _

/-- At a pole, `ordOfPlace` is bounded below by `-n` as soon as `addVal (f⁻¹) ≤ n`. -/
private lemma neg_le_ordOfPlace_of_notMem {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    {f : MotC2.Func E} (hf : f ∉ S) {n : ℕ}
    (h : @IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose
        (⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S) ≤ (n : ℕ∞)) :
    -(n : ℤ) ≤ Work.MotV.ordOfPlace E S hS f := by
  rw [Work.MotV.ordOfPlace, dif_neg hf]
  have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ Subalgebra.zero_mem S)
  have hx : @IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose
      (⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S) ≠ ⊤ := by
    intro htop
    have hzero : (⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S) = 0 :=
      (@IsDiscreteValuationRing.addVal_eq_top_iff ↥S _ _ hS.1.choose _).mp htop
    have hz : f⁻¹ = 0 := by
      have := congrArg (fun y : ↥S => (y : MotC2.Func E)) hzero
      simpa using this
    rw [inv_eq_zero] at hz
    exact hf0 hz
  have hle : (@IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose
      (⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S)).untopD 0 ≤ n :=
    (WithTop.untopD_le_iff hx).mpr h
  rw [neg_le_neg_iff]
  exact_mod_cast hle

/-! ## The order bound at the point at infinity -/

theorem infPlace_deriv_bound {N : Type*} [Field N] [CharP N 5] (E : WeierstrassCurve N)
    [E.IsElliptic] (hinf : Work.MotC2.IsRatPlace E (Work.MotC2.infPlace E))
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) :
    (∀ f : Work.MotC2.Func E, f ∈ Work.MotC2.infPlace E → D f ∈ Work.MotC2.infPlace E) ∧
    (∀ f : Work.MotC2.Func E, f ∉ Work.MotC2.infPlace E →
      Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hinf f - 1 ≤
        Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hinf (D f)) := by
  have hD1 : ∀ f : MotC2.Func E, f ∈ MotC2.infPlace E → D f ∈ MotC2.infPlace E :=
    deriv_mem_infPlace E D hx hy
  refine ⟨hD1, ?_⟩
  intro f hf
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0] at hf
    exact hf (Subalgebra.zero_mem (MotC2.infPlace E))
  letI : IsDiscreteValuationRing ↥(MotC2.infPlace E) := hinf.1.choose
  have hgS : f⁻¹ ∈ MotC2.infPlace E :=
    (MotC2.mem_or_inv_mem_of_isRatPlace hinf f).resolve_left hf
  set g : ↥(MotC2.infPlace E) := ⟨f⁻¹, hgS⟩ with hg_def
  have hgK : (g : MotC2.Func E) = f⁻¹ := by rw [hg_def]
  -- `g = f⁻¹` is not a unit of the local ring
  have hgnu : ¬ IsUnit g := by
    rintro ⟨u, hu⟩
    have h1 : g * (↑u⁻¹ : ↥(MotC2.infPlace E)) = 1 := by rw [← hu, Units.mul_inv]
    have h2 : f⁻¹ * ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) = 1 := by
      have h := congrArg (fun y : ↥(MotC2.infPlace E) => (y : MotC2.Func E)) h1
      rw [Subalgebra.coe_mul, Subalgebra.coe_one, hgK] at h
      exact h
    have h3 : f = ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) := by
      calc f = f * (f⁻¹ * ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E)) := by rw [h2, mul_one]
        _ = (f * f⁻¹) * ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) := by ring
        _ = ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) := by
              rw [mul_inv_cancel₀ hf0, one_mul]
    exact hf (h3.symm ▸ (↑u⁻¹ : ↥(MotC2.infPlace E)).2)
  set m : ℕ := (IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E) g).untopD 0 with hm_def
  have hg_ne_top : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E) g ≠ ⊤ := by
    intro h
    have hg0 : g = 0 := IsDiscreteValuationRing.addVal_eq_top_iff.mp h
    have hz : f⁻¹ = 0 := by
      have h2 := congrArg (fun y : ↥(MotC2.infPlace E) => (y : MotC2.Func E)) hg0
      rw [hgK] at h2
      simpa using h2
    rw [inv_eq_zero] at hz
    exact hf0 hz
  have hgval : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E) g = (m : ℕ∞) := by
    rw [hm_def]
    exact (WithTop.coe_untop₀_of_ne_top hg_ne_top).symm
  have hm_ge : 1 ≤ m := by
    have hne : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E) g ≠ 0 := fun h =>
      hgnu (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h)
    have hm0 : m ≠ 0 := by
      intro h0
      exact hne (by rw [hgval, h0]; rfl)
    omega
  -- a uniformiser of the local ring
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible ↥(MotC2.infPlace E)
  -- the factorisation `g = u * p^n`, with `u` a unit
  have hg_ne : g ≠ 0 := fun h0 => hg_ne_top (IsDiscreteValuationRing.addVal_eq_top_iff.mpr h0)
  obtain ⟨n, u, hgu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg_ne hp
  have hnm : n = m := by
    have h1 : (m : ℕ∞) = (n : ℕ∞) := by
      rw [← hgval, hgu, IsDiscreteValuationRing.addVal_mul,
        IsDiscreteValuationRing.addVal_eq_zero_of_unit u, Irreducible.addVal_pow hp n, zero_add]
    exact (ENat.natCast_inj.mp h1).symm
  -- the derivative of `g` is divisible by `p^(m-1)`
  have hD' : ∀ x : ↥(MotC2.infPlace E), ∃ y : ↥(MotC2.infPlace E),
      D (algebraMap ↥(MotC2.infPlace E) (MotC2.Func E) x) =
        algebraMap ↥(MotC2.infPlace E) (MotC2.Func E) y :=
    fun x => ⟨⟨D (x : MotC2.Func E), hD1 (x : MotC2.Func E) x.2⟩, rfl⟩
  obtain ⟨z, hz⟩ :=
    deriv_pow_dvd (D := D) (hD := hD') (p := p) hp (m := m) hm_ge (g := g) hgval
  have hz' : D (g : MotC2.Func E) = (p : MotC2.Func E) ^ (m - 1) * (z : MotC2.Func E) := hz
  -- the algebra in the function field
  have hfac : (g : MotC2.Func E) = ((u : ↥(MotC2.infPlace E)) : MotC2.Func E) *
      (p : MotC2.Func E) ^ m := by
    rw [hnm] at hgu
    exact congrArg (fun y : ↥(MotC2.infPlace E) => (y : MotC2.Func E)) hgu
  have hfinv : f * (((u : ↥(MotC2.infPlace E)) : MotC2.Func E) *
      (p : MotC2.Func E) ^ m) = 1 := by
    rw [← hfac, hgK, mul_inv_cancel₀ hf0]
  have hu_inv : ((u : ↥(MotC2.infPlace E)) : MotC2.Func E) *
      ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have hfP : f * (p : MotC2.Func E) ^ m = ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) := by
    calc f * (p : MotC2.Func E) ^ m
        = f * (p : MotC2.Func E) ^ m * (((u : ↥(MotC2.infPlace E)) : MotC2.Func E) *
            ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E)) := by rw [hu_inv, mul_one]
      _ = f * (((u : ↥(MotC2.infPlace E)) : MotC2.Func E) * (p : MotC2.Func E) ^ m) *
            ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) := by ring
      _ = 1 * ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) := by rw [hfinv]
      _ = ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) := by rw [one_mul]
  have hsquare : f ^ 2 * (p : MotC2.Func E) ^ (2 * m) =
      ((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) ^ 2 := by
    have h := congrArg (fun y : MotC2.Func E => y ^ 2) hfP
    rw [mul_pow, ← pow_mul] at h
    rw [show m * 2 = 2 * m from by ring] at h
    exact h
  have hgK' : D (g : MotC2.Func E) = -(f⁻¹) ^ 2 * D f := by
    rw [hgK, Derivation.leibniz_inv, smul_eq_mul]
  have hDf : D f = -(f ^ 2) * D (g : MotC2.Func E) := by
    rw [hgK']
    have hff : f ^ 2 * (f⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hf0, one_pow]
    have hmain : -(f ^ 2) * (-(f⁻¹) ^ 2 * D f) = D f := by
      calc -(f ^ 2) * (-(f⁻¹) ^ 2 * D f) = (f ^ 2 * (f⁻¹) ^ 2) * D f := by ring
        _ = D f := by rw [hff, one_mul]
    exact hmain.symm
  set c : ↥(MotC2.infPlace E) := -((↑u⁻¹ : ↥(MotC2.infPlace E)) ^ 2 * z) with hc_def
  have hkey : (p : MotC2.Func E) ^ (m + 1) * D f = (c : MotC2.Func E) := by
    have hexp : (p : MotC2.Func E) ^ (m + 1) * (p : MotC2.Func E) ^ (m - 1) =
        (p : MotC2.Func E) ^ (2 * m) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hDf, hz', hc_def]
    simp only [Subalgebra.coe_neg, Subalgebra.coe_mul, Subalgebra.coe_pow]
    calc (p : MotC2.Func E) ^ (m + 1) * (-(f ^ 2) * ((p : MotC2.Func E) ^ (m - 1) *
            (z : MotC2.Func E)))
        = -((f ^ 2 * (p : MotC2.Func E) ^ (2 * m)) * (z : MotC2.Func E)) := by
          rw [← hexp]; ring
      _ = -(((↑u⁻¹ : ↥(MotC2.infPlace E)) : MotC2.Func E) ^ 2 * (z : MotC2.Func E)) := by
          rw [hsquare]
  have h2f : Work.MotV.ordOfPlace E (MotC2.infPlace E) hinf f = -(m : ℤ) := by
    refine ordOfPlace_eq_neg_of E _ hinf hf ?_
    rw [← hg_def]
    exact hgval
  by_cases hcase : D f ∈ MotC2.infPlace E
  · have h1 : 0 ≤ Work.MotV.ordOfPlace E (MotC2.infPlace E) hinf (D f) :=
      ordOfPlace_nonneg_of_mem E _ hinf hcase
    have hmnn : (0 : ℤ) ≤ (m : ℤ) := Int.ofNat_nonneg m
    linarith
  · have hDf0 : D f ≠ 0 := by
      intro h0
      rw [h0] at hcase
      exact hcase (Subalgebra.zero_mem _)
    have hTc : (⟨(D f)⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hinf (D f)).resolve_left hcase⟩ :
        ↥(MotC2.infPlace E)) * c = p ^ (m + 1) := by
      apply Subtype.ext
      show (D f)⁻¹ * (c : MotC2.Func E) =
        ((p ^ (m + 1) : ↥(MotC2.infPlace E)) : MotC2.Func E)
      rw [Subalgebra.coe_pow]
      calc (D f)⁻¹ * (c : MotC2.Func E)
          = (D f)⁻¹ * ((p : MotC2.Func E) ^ (m + 1) * D f) := by rw [hkey]
        _ = (p : MotC2.Func E) ^ (m + 1) := by
            rw [mul_comm ((p : MotC2.Func E) ^ (m + 1)) (D f), ← mul_assoc,
              inv_mul_cancel₀ hDf0, one_mul]
    have hle : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E)
        (⟨(D f)⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hinf (D f)).resolve_left hcase⟩ :
          ↥(MotC2.infPlace E)) ≤ ((m + 1 : ℕ) : ℕ∞) := by
      have hTle : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E)
          (⟨(D f)⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hinf (D f)).resolve_left hcase⟩ :
            ↥(MotC2.infPlace E)) ≤
          IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E) (p ^ (m + 1)) :=
        (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr ⟨c, hTc.symm⟩
      rwa [Irreducible.addVal_pow hp (m + 1)] at hTle
    have h3 : -(↑(m + 1) : ℤ) ≤ Work.MotV.ordOfPlace E (MotC2.infPlace E) hinf (D f) :=
      neg_le_ordOfPlace_of_notMem E _ hinf hcase hle
    have hm1 : (↑(m + 1) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    linarith

end Work.MotV5
