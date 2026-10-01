import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

open _root_.Polynomial
open scoped PowerSeries

/-! ## Auxiliary lemmas -/

/-- The geometric series `∑_n γ^n X^n` as a formal power series over `ℂ`. -/
noncomputable def powerSumsGeo (γ : ℂ) : ℂ⟦X⟧ := PowerSeries.mk fun n => γ ^ n

lemma coe_one_sub (γ : ℂ) :
    ((1 - C γ * X : ℂ[X]) : ℂ⟦X⟧) = 1 - PowerSeries.C γ * PowerSeries.X := by simp

/-- `(1 - γX) * ∑_n γ^n X^n = 1` in `ℂ⟦X⟧`. -/
lemma geo_spec (γ : ℂ) : ((1 - C γ * X : ℂ[X]) : ℂ⟦X⟧) * powerSumsGeo γ = 1 := by
  have h := congrArg (PowerSeries.rescale γ) (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h
  rw [PowerSeries.rescale_mk] at h
  simp only [Pi.one_apply, mul_one] at h
  rw [coe_one_sub γ, mul_comm]
  exact h

lemma deriv_one_sub (γ : ℂ) : Polynomial.derivative (1 - C γ * X : ℂ[X]) = -C γ := by
  simp [derivative_sub, derivative_mul]

/-- The key power series identity: for `L = ∏_{j<t} (1 - γ_j X)`,
`L * (-∑_j (∑_n γ_j^n X^n - 1)) = X * L'`. -/
lemma powerSums_key_identity (t : ℕ) (γ : Fin t → ℂ) (f : Fin t → ℂ[X])
    (hf : ∀ j, f j = 1 - C (γ j) * X) :
    ((∏ j : Fin t, f j : ℂ[X]) : ℂ⟦X⟧) * (-∑ j : Fin t, (powerSumsGeo (γ j) - 1))
      = (PowerSeries.X : ℂ⟦X⟧)
        * ((Polynomial.derivative (∏ j : Fin t, f j : ℂ[X]) : ℂ[X]) : ℂ⟦X⟧) := by
  classical
  set L : ℂ[X] := ∏ j, f j with hL
  set g : Fin t → ℂ[X] := fun j => ∏ k ∈ Finset.univ.erase j, f k with hg
  have hfg : ∀ j, f j * g j = L := by
    intro j
    rw [hL, hg]
    exact Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)
  have hderiv : Polynomial.derivative L = ∑ j, (-C (γ j)) * g j := by
    rw [hL, Polynomial.derivative_prod_finset]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg, hf j, deriv_one_sub]
    ring
  have hkey1 : ∀ j, (L : ℂ⟦X⟧) * (powerSumsGeo (γ j) - 1) = (g j : ℂ⟦X⟧) - (L : ℂ⟦X⟧) := by
    intro j
    rw [mul_sub, mul_one]
    congr 1
    rw [show (L : ℂ⟦X⟧) = (f j : ℂ⟦X⟧) * (g j : ℂ⟦X⟧) from by
      rw [← hfg j, Polynomial.coe_mul]]
    rw [mul_assoc, mul_comm (g j : ℂ⟦X⟧) (powerSumsGeo (γ j)), ← mul_assoc,
      show (f j : ℂ⟦X⟧) * powerSumsGeo (γ j) = 1 from by rw [hf j]; exact geo_spec (γ j), one_mul]
  have hkey2 : ∀ j, (PowerSeries.X : ℂ⟦X⟧) * (((-C (γ j) : ℂ[X]) : ℂ⟦X⟧) * (g j : ℂ⟦X⟧))
      = (L : ℂ⟦X⟧) - (g j : ℂ⟦X⟧) := by
    intro j
    have hCX : (C (γ j) : ℂ[X]) * X = 1 - f j := by rw [hf j]; ring
    have hCXg : (C (γ j) : ℂ[X]) * X * g j = g j - L := by rw [hCX, sub_mul, one_mul, hfg j]
    rw [show ((-C (γ j) : ℂ[X]) : ℂ⟦X⟧) = -(((C (γ j) : ℂ[X])) : ℂ⟦X⟧) from by
      simp only [Polynomial.coe_neg, Polynomial.coe_C]]
    rw [show (PowerSeries.X : ℂ⟦X⟧) * (-(((C (γ j) : ℂ[X])) : ℂ⟦X⟧) * (g j : ℂ⟦X⟧))
        = -(((C (γ j) : ℂ[X]) * X * g j : ℂ[X]) : ℂ⟦X⟧) from by
      simp only [Polynomial.coe_mul, Polynomial.coe_X]
      ring]
    rw [hCXg, Polynomial.coe_sub]
    ring
  have e1 : (L : ℂ⟦X⟧) * (-∑ j : Fin t, (powerSumsGeo (γ j) - 1))
      = ∑ j : Fin t, ((L : ℂ⟦X⟧) - (g j : ℂ⟦X⟧)) := by
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hkey1 j]
    ring
  have e2 : (PowerSeries.X : ℂ⟦X⟧)
        * (∑ j : Fin t, ((-C (γ j) : ℂ[X]) : ℂ⟦X⟧) * (g j : ℂ⟦X⟧))
      = ∑ j : Fin t, ((L : ℂ⟦X⟧) - (g j : ℂ⟦X⟧)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hkey2 j]
  rw [e1, hderiv]
  rw [show (((∑ j : Fin t, -C (γ j) * g j) : ℂ[X]) : ℂ⟦X⟧)
      = ∑ j : Fin t, ((-C (γ j) * g j : ℂ[X]) : ℂ⟦X⟧) from
    map_sum (Polynomial.coeToPowerSeries.ringHom (R:=ℂ)) (fun j => -C (γ j) * g j) Finset.univ]
  simp only [Polynomial.coe_mul]
  exact e2.symm

/-! ## Factorization of a polynomial with constant coefficient one -/

lemma sub_X_C {K : Type*} [Field K] (r : K) (hr : r ≠ 0) :
    (X - C r : K[X]) = C (-r) * (1 - C r⁻¹ * X) := by
  rw [mul_sub, mul_one, ← mul_assoc, ← map_mul]
  rw [show (-r) * r⁻¹ = (-1 : K) by field_simp]
  rw [show (C (-1 : K) : K[X]) = -1 by simp]
  rw [map_neg]
  ring

lemma prod_map_neg {K : Type*} [Field K] (m : Multiset K) :
    (m.map (fun r => -r)).prod = (-1 : K) ^ m.card * m.prod := by
  have h : (fun r : K => -r) = (fun r : K => (-1 : K) * r) := by funext r; ring
  rw [h, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
  simp

lemma prod_map_one_sub {K : Type*} [Field K] [DecidableEq K] (m : Multiset K) :
    (m.map (fun r => (1 - C r⁻¹ * X : K[X]))).prod
      = ∏ x : m.ToType, (1 - C (x.1)⁻¹ * X : K[X]) := by
  rw [← Multiset.map_univ m (fun r => (1 - C r⁻¹ * X : K[X])), Finset.prod_eq_multiset_prod]

/-- A polynomial over a field with constant coefficient `1` factors as a product of factors
`1 - C γ * X`, with as many factors as its degree. -/
theorem exists_prod_one_sub_mul_X_of_coeff_zero {K : Type*} [Field K] [IsAlgClosed K] (L : Polynomial K)
    (h0 : L.coeff 0 = 1) :
    ∃ (t : ℕ) (_ : t ≤ L.natDegree) (γ : Fin t → K),
      L = ∏ j : Fin t, (1 - Polynomial.C (γ j) * Polynomial.X) := by
  classical
  have hsp : L.Splits := IsAlgClosed.splits L
  have hL0 : L ≠ 0 := by intro h; rw [h] at h0; simp at h0
  set m : Multiset K := L.roots with hm
  have heq : L = C L.leadingCoeff * (m.map (X - C ·)).prod := by
    rw [hm]; exact hsp.eq_prod_roots
  have hroot0 : ∀ r ∈ m, r ≠ 0 := by
    intro r hr hr0
    subst hr0
    have hmem : (0 : K) ∈ L.roots := by rwa [← hm]
    have h1 : L.eval 0 = 0 := (Polynomial.mem_roots hL0).mp hmem
    rw [Polynomial.coeff_zero_eq_eval_zero] at h0
    rw [h1] at h0
    exact one_ne_zero h0.symm
  have hmcard : m.card = L.natDegree := by rw [hm]; exact hsp.natDegree_eq_card_roots.symm
  have hcz : (-1 : K) ^ m.card * L.leadingCoeff * m.prod = 1 := by
    have h := hsp.coeff_zero_eq_leadingCoeff_mul_prod_roots
    rw [← hm] at h
    rw [h0, ← hmcard] at h
    exact h.symm
  have hmap : m.map (X - C ·) = m.map (fun r => C (-r) * (1 - C r⁻¹ * X)) := by
    refine Multiset.map_congr rfl fun r hr => ?_
    exact sub_X_C r (hroot0 r hr)
  have hCneg : (m.map (fun r => C (-r))).prod = C ((m.map (fun r => -r)).prod) := by
    have h1 : (fun r : K => C (-r)) = (Polynomial.C : K →+* K[X]) ∘ (fun r : K => -r) := rfl
    rw [h1, ← Multiset.map_map]
    exact (map_multiset_prod (Polynomial.C : K →+* K[X]) (m.map fun r => -r)).symm
  have hprod : (m.map (X - C ·)).prod
      = C ((m.map (fun r => -r)).prod) * (m.map (fun r => 1 - C r⁻¹ * X)).prod := by
    rw [hmap, Multiset.prod_map_mul, hCneg]
  have hc : L.leadingCoeff * (m.map (fun r => -r)).prod = 1 := by
    rw [prod_map_neg]
    rw [show L.leadingCoeff * ((-1 : K) ^ m.card * m.prod)
        = (-1 : K) ^ m.card * L.leadingCoeff * m.prod from by ring]
    exact hcz
  have hLR : L = (m.map (fun r => 1 - C r⁻¹ * X)).prod := by
    rw [heq, hprod, ← mul_assoc, ← map_mul, hc, map_one, one_mul]
  let e₀ : Fin m.card ≃ m.ToType := (Fintype.equivFinOfCardEq (Multiset.card_coe m)).symm
  refine ⟨m.card, hmcard.le, fun j => (e₀ j).1⁻¹, ?_⟩
  rw [hLR, prod_map_one_sub]
  exact (Fintype.prod_equiv e₀ (fun j : Fin m.card => (1 - C ((e₀ j).1)⁻¹ * X))
    (fun x : m.ToType => (1 - C (x.1)⁻¹ * X)) (fun j => rfl)).symm

/-! ## Main theorem -/

lemma coeff_mul_mk (L : ℂ[X]) (a : ℕ → ℂ) (n : ℕ) :
    (PowerSeries.coeff n) ((L : ℂ⟦X⟧) * PowerSeries.mk a)
      = ∑ i ∈ Finset.range (n+1), L.coeff i * a (n - i) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (PowerSeries.coeff i ↑L) * (PowerSeries.coeff j) (PowerSeries.mk a))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

open _root_.Polynomial in
/-- If `L ∈ ℂ[X]` has constant coefficient `1`, and a sequence `a` with `a 0 = 0` satisfies the
linear recurrence `∑_{m<n} (L.coeff m) · a (n-m) = n · L.coeff n` for all `n ≥ 1`, then `a` is a
power sum of at most `L.natDegree` complex numbers: there are `t ≤ L.natDegree` and `γ : Fin t → ℂ`
with `a n = -∑_j (γ j)^n` for every `n ≥ 1`.

Proof route: let `L = ∏_{j<t} (1 - γ_j X)` over `ℂ` (`t = L.natDegree`, possible since `L` splits
over `ℂ` and `L(0) = 1`); show the formal power series identity `L * (∑_n a n · X^n) = X * L'`
coefficient-wise from the recurrence, and likewise for `b n := -∑_j γ_j^n` using
`(1 - γ X) * (-∑_{n≥1} γ^n X^n) = -γ X`; cancel `L` (a unit since `L 0 = 1`). -/
theorem exists_powerSums_of_recurrence (L : Polynomial ℂ) (h0 : L.coeff 0 = 1) (a : ℕ → ℂ)
    (ha0 : a 0 = 0)
    (hrec : ∀ n, 1 ≤ n → ∑ m ∈ Finset.range n, L.coeff m * a (n - m) = (n : ℂ) * L.coeff n) :
    ∃ (t : ℕ) (_ : t ≤ L.natDegree) (γ : Fin t → ℂ), ∀ n, 1 ≤ n → a n = -∑ j : Fin t, γ j ^ n := by
  classical
  obtain ⟨t, ht, γ, hLfac⟩ := exists_prod_one_sub_mul_X_of_coeff_zero L h0
  have hkey := powerSums_key_identity t γ (fun j => (1 - C (γ j) * X : ℂ[X])) (fun j => rfl)
  rw [← hLfac] at hkey
  -- hkey : (L : ℂ⟦X⟧) * (-∑ j, (powerSumsGeo (γ j) - 1)) = X * (L.derivative : ℂ⟦X⟧)
  have hLA : (L : ℂ⟦X⟧) * PowerSeries.mk a = (PowerSeries.X : ℂ⟦X⟧) * (L.derivative : ℂ⟦X⟧) := by
    ext n
    rcases n with _ | k
    · rw [coeff_mul_mk]
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X, zero_mul]
      rw [Finset.sum_range_one]
      simp [ha0]
    · rw [coeff_mul_mk, PowerSeries.coeff_succ_X_mul]
      rw [Polynomial.coeff_coe, Polynomial.coeff_derivative]
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, ha0, mul_zero, add_zero]
      rw [hrec (k + 1) (by omega)]
      push_cast
      ring
  have hunit : IsUnit (L : ℂ⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe, h0]
    exact isUnit_one
  have hAB : PowerSeries.mk a = -∑ j : Fin t, (powerSumsGeo (γ j) - 1) :=
    hunit.mul_left_cancel (hLA.trans hkey.symm)
  refine ⟨t, ht, γ, fun n hn => ?_⟩
  rw [show a n = (PowerSeries.mk a).coeff n from (PowerSeries.coeff_mk n a).symm, hAB]
  rw [map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sub, powerSumsGeo, PowerSeries.coeff_mk]
  rw [show ((1 : ℂ⟦X⟧).coeff n) = 0 from by
    rw [PowerSeries.coeff_one]
    exact if_neg (by omega)]
  ring

end Commons.Algebra.Polynomial