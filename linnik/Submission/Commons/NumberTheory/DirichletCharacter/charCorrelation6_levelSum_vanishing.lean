import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_levelSum_nondegenerate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.DirichletCharacter

/-- **Degenerate stationary-phase step (`r = 3`).**  When the criticality is exact to first
order (`κ` a `p`-unit, the sum difference being `p^ℓ · κ`) and the quadratic invariant
vanishes modulo `p`, the level-`ℓ` sum over `ZMod (p^M)` vanishes identically for `M ≥ 2`:
the inner digit sum is the sum of the powers of a *nontrivial* `p`-th root of unity. -/
theorem levelSum_step3_deg {p e ℓ M : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e)
    (hℓ : 1 ≤ ℓ) (hM : 2 ≤ M) (heq : e = 2 * ℓ + M)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A C : Fin 3 → ZMod (p ^ e)) (κ : ℕ)
    (hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (hκ : ¬ (p : ℕ) ∣ κ)
    (hΔ : (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val) :
    levelSum3 p e ℓ M χ A C = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p (show 1 ≤ e by omega)
  have h2ℓ : 2 * ℓ ≤ e := by omega
  have hℓ'e : ℓ + M - 1 = e - ℓ - 1 := by omega
  have h2ℓ' : e ≤ 2 * (ℓ + M - 1) := by omega
  set Δ : ZMod (p ^ e) := (∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) with hΔdef
  have hΔcast : ZMod.castHom hdiv1 (ZMod p) Δ = 0 :=
    (castHom_eq_zero_iff_dvd_val_one hdiv1 Δ).mpr hΔ
  -- ### the residual units and the derivative
  set θA : ZMod (p ^ e) → Fin 3 → ZMod (p ^ e) :=
    fun x l => A l * (1 + pPow p e ℓ * A l * x)⁻¹ with hθA
  set θC : ZMod (p ^ e) → Fin 3 → ZMod (p ^ e) :=
    fun x l => C l * (1 + pPow p e ℓ * C l * x)⁻¹ with hθC
  set Gfun : ZMod (p ^ e) → ZMod (p ^ e) :=
    fun x => (∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l) with hGfun
  set ζ : ℂ := χ (1 + pPow p e (e - 1)) with hζdef
  have hζprim : IsPrimitiveRoot ζ p := by
    rw [hζdef, pPow]
    simpa using chi_one_add_primePow_isPrimitiveRoot p e hp2 (by omega) χ hχ
  -- ### the expansion of the derivative
  have hexpand : ∀ x : ZMod (p ^ e),
      pPow p e (ℓ + M - 1) * Gfun x
        = pPow p e (e - 1) * ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x) := by
    intro x
    have h1 : ∀ l : Fin 3, pPow p e (ℓ + M - 1) * θA x l
        = pPow p e (ℓ + M - 1) * A l - pPow p e (e - 1) * A l ^ 2 * x := by
      intro l
      rw [hℓ'e]
      exact pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ (A l) x
    have h2 : ∀ l : Fin 3, pPow p e (ℓ + M - 1) * θC x l
        = pPow p e (ℓ + M - 1) * C l - pPow p e (e - 1) * C l ^ 2 * x := by
      intro l
      rw [hℓ'e]
      exact pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ (C l) x
    have hpp : pPow p e (ℓ + M - 1) * ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l))
        = pPow p e (e - 1) * ((κ : ℕ) : ZMod (p ^ e)) := by
      rw [hsum, pPow, pPow]
      push_cast
      rw [← mul_assoc, ← pow_add, show ℓ + M - 1 + ℓ = e - 1 by omega]
    have hgx : Gfun x = (∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l) := by rw [hGfun]
    rw [hgx, mul_sub, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_congr rfl (fun l _ => h2 l)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [show (∑ l : Fin 3, pPow p e (ℓ + M - 1) * A l)
        = pPow p e (ℓ + M - 1) * (∑ l : Fin 3, A l) by rw [Finset.mul_sum]]
    rw [show (∑ l : Fin 3, pPow p e (ℓ + M - 1) * C l)
        = pPow p e (ℓ + M - 1) * (∑ l : Fin 3, C l) by rw [Finset.mul_sum]]
    rw [show (∑ l : Fin 3, pPow p e (e - 1) * A l ^ 2 * x)
        = pPow p e (e - 1) * (∑ l : Fin 3, A l ^ 2) * x by
      rw [Finset.sum_congr rfl (fun l _ => show pPow p e (e - 1) * A l ^ 2 * x
        = (pPow p e (e - 1) * x) * A l ^ 2 by ring), ← Finset.mul_sum]; ring]
    rw [show (∑ l : Fin 3, pPow p e (e - 1) * C l ^ 2 * x)
        = pPow p e (e - 1) * (∑ l : Fin 3, C l ^ 2) * x by
      rw [Finset.sum_congr rfl (fun l _ => show pPow p e (e - 1) * C l ^ 2 * x
        = (pPow p e (e - 1) * x) * C l ^ 2 by ring), ← Finset.mul_sum]; ring]
    rw [hΔdef]
    rw [show pPow p e (ℓ + M - 1) * (∑ l : Fin 3, A l)
          - (pPow p e (e - 1) * (∑ l : Fin 3, A l ^ 2)) * x
          - (pPow p e (ℓ + M - 1) * (∑ l : Fin 3, C l)
              - (pPow p e (e - 1) * (∑ l : Fin 3, C l ^ 2)) * x)
        = pPow p e (ℓ + M - 1) * ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l))
          - pPow p e (e - 1) * ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2)) * x by ring]
    rw [hpp]
    ring
  -- ### the character value of the inner exponential
  have hη : ∀ x : ZMod (p ^ e),
      χ (1 + pPow p e (ℓ + M - 1) * Gfun x)
        = ζ ^ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val := by
    intro x
    rw [hexpand x, chi_top_level (p := p) (e := e) (by omega) χ]
  have hηpow : ∀ x : ZMod (p ^ e),
      (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ p = 1 := by
    intro x
    rw [hη x, ← pow_mul, mul_comm, pow_mul, hζprim.pow_eq_one, one_pow]
  -- ### the inner sum over the last digit
  have hinner : ∀ x : ZMod (p ^ e),
      (∑ t ∈ Finset.range p,
          χ (prodCoord3 p e (ℓ + M - 1) (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)))) = 0 := by
    intro x
    have hpc : ∀ t ∈ Finset.range p,
        χ (prodCoord3 p e (ℓ + M - 1) (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)))
          = (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ t := by
      intro t ht
      have hgt : Gfun x = (∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l) := by rw [hGfun]
      calc χ (prodCoord3 p e (ℓ + M - 1) (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)))
          = χ ((1 + pPow p e (ℓ + M - 1) * Gfun x) ^ t) := by
            rw [prodCoord3_eq_one_add (p := p) (e := e) (ℓ := ℓ + M - 1) h2ℓ'
              (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)), hgt]
            rw [show ((∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l)) * pPow p e (ℓ + M - 1)
                  * ((t : ℕ) : ZMod (p ^ e))
                = (t : ZMod (p ^ e)) * (pPow p e (ℓ + M - 1)
                  * ((∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l))) by ring]
            rw [← one_add_pPow_pow (p := p) (e := e) (ℓ := ℓ + M - 1) h2ℓ'
              ((∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l)) t]
        _ = (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ t := by rw [map_pow]
    rw [Finset.sum_congr rfl hpc, sum_range_pow_eq p (hηpow x), if_neg]
    intro h1
    have hpdiv : p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val := (hζprim.pow_eq_one_iff_dvd _).mp (by
      rw [← hη x]; exact h1)
    refine hκ ?_
    rw [← ZMod.natCast_eq_zero_iff κ p, ← map_natCast (ZMod.castHom hdiv1 (ZMod p))]
    have h2 : ZMod.castHom hdiv1 (ZMod p) ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x) = 0 :=
      (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mpr hpdiv
    rw [map_sub, map_mul, hΔcast, zero_mul, sub_zero] at h2
    exact h2
  -- ### the two-level decomposition of the level sum
  have hdecomp : levelSum3 p e ℓ M χ A C
      = ∑ n' ∈ Finset.range (p ^ (M - 1)),
          χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e)))
            * (∑ t ∈ Finset.range p,
                χ (prodCoord3 p e (ℓ + M - 1) (θA ((n' : ℕ) : ZMod (p ^ e)))
                  (θC ((n' : ℕ) : ZMod (p ^ e))) ((t : ℕ) : ZMod (p ^ e)))) := by
    rw [levelSum3_eq_range_sum]
    have h1 : ∀ n ∈ Finset.range (p ^ M),
        phase3 p e ℓ χ A C ((n : ℕ) : ZMod (p ^ e))
          = χ (prodCoord3 p e ℓ A C ((n : ℕ) : ZMod (p ^ e))) := by
      intro n hn
      exact phase3_eq_chi_prodCoord3 (p := p) (e := e) (ℓ := ℓ) hℓ χ A C _
    rw [Finset.sum_congr rfl h1]
    have h2 : p ^ M = p ^ (M - 1) * p := by
      conv_lhs => rw [show M = (M - 1) + 1 by omega]
      rw [pow_succ]
    rw [h2]
    rw [Commons.Algebra.BigOperators.sum_range_mul_eq
      (fun n => χ (prodCoord3 p e ℓ A C ((n : ℕ) : ZMod (p ^ e)))) (p ^ (M - 1)) p]
    refine Finset.sum_congr rfl fun n' hn' => ?_
    have hpeel : ∀ t ∈ Finset.range p,
        χ (prodCoord3 p e ℓ A C (((n' + p ^ (M - 1) * t : ℕ)) : ZMod (p ^ e)))
          = χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e)))
            * χ (prodCoord3 p e (ℓ + M - 1) (θA ((n' : ℕ) : ZMod (p ^ e)))
                (θC ((n' : ℕ) : ZMod (p ^ e))) ((t : ℕ) : ZMod (p ^ e))) := by
      intro t ht
      rw [show ((n' + p ^ (M - 1) * t : ℕ) : ZMod (p ^ e))
          = ((n' : ℕ) : ZMod (p ^ e)) + ((p : ℕ) ^ (M - 1) : ℕ) * ((t : ℕ) : ZMod (p ^ e)) by
        push_cast; ring]
      rw [prodCoord3_peel (p := p) (e := e) (ℓ := ℓ) (M := M) hℓ (by omega) A C _ _,
        map_mul]
    rw [Finset.sum_congr rfl hpeel, ← Finset.mul_sum]
  rw [hdecomp]
  refine Finset.sum_eq_zero fun n' hn' => ?_
  rw [hinner ((n' : ℕ) : ZMod (p ^ e)), mul_zero]

/-- **Degenerate base case `M = 1` (`r = 3`).**  With a single remaining digit `e = 2ℓ + 1`,
if the linear phase coefficient is a unit (`p ∤ κ`) and the quadratic phase coefficient
vanishes modulo `p` then the level-`ℓ` sum over `ZMod p` is the sum of the powers of a
nontrivial `p`-th root of unity, hence vanishes. -/
theorem levelSum_base_one3_deg {p e ℓ : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hℓ : 1 ≤ ℓ) (heq : e = 2 * ℓ + 1) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A C : Fin 3 → ZMod (p ^ e)) (κ : ℕ)
    (hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (hκ : ¬ (p : ℕ) ∣ κ)
    (hΔ : (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val) :
    levelSum3 p e ℓ 1 χ A C = 0 := by
  have he1 : 1 ≤ e := by omega
  have h3 : e ≤ 3 * ℓ := by omega
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p he1
  set ζ : ℂ := χ (1 + pPow p e (e - 1)) with hζdef
  have hζprim : IsPrimitiveRoot ζ p := by
    rw [hζdef, pPow]
    simpa using chi_one_add_primePow_isPrimitiveRoot p e hp2 (by omega) χ hχ
  set K2 : ZMod (p ^ e) := K2_3 p e A C with hK2def
  -- criticality modulo `p`
  have hcritp : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)) = 0 := by
    rw [hsum, map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_of_dvd_left (by simpa using (pow_dvd_pow p hℓ : p ^ 1 ∣ p ^ ℓ)) κ
  have hcrit : ZMod.castHom hdiv1 (ZMod p) (A 0) + ZMod.castHom hdiv1 (ZMod p) (A 1)
      + ZMod.castHom hdiv1 (ZMod p) (A 2)
      = ZMod.castHom hdiv1 (ZMod p) (C 0) + ZMod.castHom hdiv1 (ZMod p) (C 1)
        + ZMod.castHom hdiv1 (ZMod p) (C 2) := by
    have h := hcritp
    rw [map_sub, map_sum, map_sum,
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (A l)),
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (C l))] at h
    exact sub_eq_zero.mp h
  -- the reduction of `K2`
  have hK2cast : ZMod.castHom hdiv1 (ZMod p) K2
      = (ZMod.castHom hdiv1 (ZMod p) (A 0) * ZMod.castHom hdiv1 (ZMod p) (A 1)
            + ZMod.castHom hdiv1 (ZMod p) (A 0) * ZMod.castHom hdiv1 (ZMod p) (A 2)
            + ZMod.castHom hdiv1 (ZMod p) (A 1) * ZMod.castHom hdiv1 (ZMod p) (A 2))
          + (ZMod.castHom hdiv1 (ZMod p) (C 0) ^ 2 + ZMod.castHom hdiv1 (ZMod p) (C 1) ^ 2
              + ZMod.castHom hdiv1 (ZMod p) (C 2) ^ 2)
          + (ZMod.castHom hdiv1 (ZMod p) (C 0) * ZMod.castHom hdiv1 (ZMod p) (C 1)
            + ZMod.castHom hdiv1 (ZMod p) (C 0) * ZMod.castHom hdiv1 (ZMod p) (C 2)
            + ZMod.castHom hdiv1 (ZMod p) (C 1) * ZMod.castHom hdiv1 (ZMod p) (C 2))
          - (ZMod.castHom hdiv1 (ZMod p) (A 0) + ZMod.castHom hdiv1 (ZMod p) (A 1)
              + ZMod.castHom hdiv1 (ZMod p) (A 2))
            * (ZMod.castHom hdiv1 (ZMod p) (C 0) + ZMod.castHom hdiv1 (ZMod p) (C 1)
              + ZMod.castHom hdiv1 (ZMod p) (C 2)) := by
    rw [hK2def]
    simp only [K2_3, map_add, map_sub, map_mul, map_pow]
  have hΔcast : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2))
      = (ZMod.castHom hdiv1 (ZMod p) (A 0) ^ 2 + ZMod.castHom hdiv1 (ZMod p) (A 1) ^ 2
          + ZMod.castHom hdiv1 (ZMod p) (A 2) ^ 2)
        - (ZMod.castHom hdiv1 (ZMod p) (C 0) ^ 2 + ZMod.castHom hdiv1 (ZMod p) (C 1) ^ 2
          + ZMod.castHom hdiv1 (ZMod p) (C 2) ^ 2) := by
    rw [map_sub, map_sum, map_sum,
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (A l ^ 2)),
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (C l ^ 2)),
      map_pow, map_pow, map_pow, map_pow, map_pow, map_pow]
  have hΔzero : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2))
      = 0 := (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mpr hΔ
  have h2ne : (2 : ZMod p) ≠ 0 := GaussSum.zmod_two_ne_zero p hp2
  have hK2eq : 2 * ZMod.castHom hdiv1 (ZMod p) K2
      = -ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2)) := by
    rw [hK2cast, hΔcast]
    exact two_mul_K2_generic (fun l => ZMod.castHom hdiv1 (ZMod p) (A l))
      (fun l => ZMod.castHom hdiv1 (ZMod p) (C l)) hcrit
  have hK2zero : ZMod.castHom hdiv1 (ZMod p) K2 = 0 := by
    have h := hK2eq
    rw [hΔzero, neg_zero] at h
    exact (mul_eq_zero.mp h).resolve_left h2ne
  -- the second-order expansion of the product coordinate
  have hsum' : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = pPow p e ℓ * ((κ : ℕ) : ZMod (p ^ e)) := by
    rw [hsum, pPow]; push_cast; ring
  have hprod : ∀ w : ZMod (p ^ e), prodCoord3 p e ℓ A C w
      = 1 + pPow p e (e - 1) * (((κ : ℕ) : ZMod (p ^ e)) * w + K2 * w ^ 2) := by
    intro w
    have hPe : pPow p e ℓ * pPow p e ℓ = pPow p e (e - 1) := by
      rw [pPow_mul_pPow, show ℓ + ℓ = e - 1 by omega]
    rw [prodCoord3_quad (p := p) (e := e) (ℓ := ℓ) hℓ h3 ((κ : ℕ) : ZMod (p ^ e)) A C
      hsum' w, hK2def, hPe]
  -- the character value
  have hterm : ∀ n : ℕ, phase3 p e ℓ χ A C ((n : ℕ) : ZMod (p ^ e))
      = ζ ^ (((κ : ZMod p) * (n : ZMod p)).val) := by
    intro n
    have hphase : phase3 p e ℓ χ A C ((n : ℕ) : ZMod (p ^ e))
        = χ (1 + pPow p e (e - 1) * (((κ : ℕ) : ZMod (p ^ e)) * ((n : ℕ) : ZMod (p ^ e))
            + K2 * ((n : ℕ) : ZMod (p ^ e)) ^ 2)) := by
      rw [phase3_eq_chi_prodCoord3 (p := p) (e := e) (ℓ := ℓ) hℓ χ A C, hprod]
    rw [hphase, chi_top_level (p := p) (e := e) (by omega) χ, hζdef]
    refine pow_eq_pow_of_modEq ?_ hζprim.pow_eq_one
    have hred : ZMod.castHom hdiv1 (ZMod p)
        (((κ : ℕ) : ZMod (p ^ e)) * ((n : ℕ) : ZMod (p ^ e))
          + K2 * ((n : ℕ) : ZMod (p ^ e)) ^ 2)
        = (κ : ZMod p) * (n : ZMod p) := by
      rw [map_add, map_mul, map_mul, map_pow, map_natCast, map_natCast, hK2zero, zero_mul,
        add_zero]
    rw [← hred, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact (Nat.mod_modEq _ _).symm
  rw [levelSum3_eq_range_sum, show p ^ 1 = p by norm_num,
    Finset.sum_congr rfl (fun n _ => hterm n)]
  rw [← Commons.NumberTheory.GaussSum.zmod_sum_range p
    (fun x : ZMod p => ζ ^ (((κ : ZMod p) * x).val))]
  rw [show (∑ x : ZMod p, ζ ^ (((κ : ZMod p) * x).val))
      = ∑ x : ZMod p, ζ ^ ((x * (κ : ZMod p)).val) from
    Finset.sum_congr rfl (fun x _ => by rw [mul_comm])]
  rw [CharCorr.geom_sum_zmodChar hζprim (κ : ZMod p),
    if_neg (fun h => hκ ((ZMod.natCast_eq_zero_iff κ p).mp h))]


/-- **`r = 3` level sum: vanishing when the critical class is only critical to first order.**

For an odd prime `p`, `e ≥ 3`, `χ` primitive modulo `p^e`, shifts `a b : Fin 3 → ℕ` and a
residue class `r : ZMod p` at which all six shifts `r + a l`, `r + b l` are units and which is
*critical*, i.e. `∑_l (r+a l)⁻¹ = ∑_l (r+b l)⁻¹` in `ZMod p`: if in addition the criticality
holds only to *first* order — i.e. `p^2` does **not** divide the integer `D.val`, where
`D = ∑_l ((r.val : ZMod (p^e)) + a l)⁻¹ - ∑_l ((r.val : ZMod (p^e)) + b l)⁻¹ ∈ ZMod (p^e)`
(note: the sum of the *inverses*, not the inverse of the sum) —
and the quadratic phase coefficient vanishes, i.e. `∑_l (r+b l)⁻² = ∑_l (r+a l)⁻²` in `ZMod p`,
then the level sum over the `p^(e-2)` lifts `z` of `r` vanishes:
`∑_z χ (∏_l (r + p z + a l)) * conj (χ (∏_l (r + p z + b l))) = 0`.

Numerically verified (p = 7, e = 3, 4): this is precisely the case where the level sum is `0`. -/
theorem charCorrelation6_levelSum_vanishing {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (r : ZMod p)
    (hunit : ∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0 ∧ (r + (b l : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹))
    (hdef : ¬ (p ^ 2 ∣ ((∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ))⁻¹)
            - (∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))⁻¹) : ZMod (p ^ e)).val))
    (hnd : (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹ ^ 2) = (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹ ^ 2)) :
    (∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))) = 0 := by
  rw [target_sum_eq3 p e he χ a b r hunit]
  set A : Fin 3 → ZMod (p ^ e) := fun l => gammaU p e r (a l) with hA
  set C : Fin 3 → ZMod (p ^ e) := fun l => gammaU p e r (b l) with hC
  suffices hzero : levelSum3 p e 1 (e - 2) χ A C = 0 by rw [hzero, mul_zero]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have he1 : 1 ≤ e := by omega
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p he1
  -- the reduction of the residual units to the inverses modulo `p`
  have hinc : ∀ u : ℕ, (r + (u : ZMod p)) ≠ 0 →
      ZMod.castHom hdiv1 (ZMod p) (gammaU p e r u) = (r + (u : ZMod p))⁻¹ := by
    intro u hu
    have h1 : ((((r.val + u : ℕ)) : ZMod (p ^ e))) * gammaU p e r u = 1 :=
      gammaU_mul p e r u hu he1
    have h2 := congrArg (ZMod.castHom hdiv1 (ZMod p)) h1
    rw [map_mul, map_one, map_natCast, Nat.cast_add, ZMod.natCast_zmod_val] at h2
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)
  -- the difference `D = ∑ A - ∑ C` is the object of `hdef`
  have hDval : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)
      = ((∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ))⁻¹)
          - (∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))⁻¹)) := by
    rw [hA, hC]
    congr 1
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      show ((((r.val + a l : ℕ)) : ZMod (p ^ e)))⁻¹
        = (((r.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ))⁻¹
      congr 1; push_cast; ring
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      show ((((r.val + b l : ℕ)) : ZMod (p ^ e)))⁻¹
        = (((r.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))⁻¹
      congr 1; push_cast; ring
  have hdef' : ¬ (p ^ 2 ∣ ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)).val) := by
    rw [hDval]; exact hdef
  -- the reduced criticality
  have hDcast : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)) = 0 := by
    rw [hA, hC, map_sub, map_sum, map_sum,
      Finset.sum_congr rfl (fun l _ => hinc (a l) (hunit l).1),
      Finset.sum_congr rfl (fun l _ => hinc (b l) (hunit l).2), hcrit, sub_self]
  have hpD : p ∣ ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)).val :=
    (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mp hDcast
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)).val = p * κ := hpD
  have hκnot : ¬ (p : ℕ) ∣ κ := by
    intro h
    obtain ⟨j, hj⟩ := h
    exact hdef' ⟨j, by rw [hκ, hj]; ring⟩
  have hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ 1 * κ : ℕ) : ZMod (p ^ e)) := by
    rw [← ZMod.natCast_zmod_val ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)), hκ]
    push_cast
    ring
  -- the quadratic invariant vanishes modulo `p`
  have hΔcast : ZMod.castHom hdiv1 (ZMod p)
      ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2)) = 0 := by
    rw [map_sub, map_sum, map_sum]
    have h1 : ∀ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (A l ^ 2)
        = (r + (a l : ZMod p))⁻¹ ^ 2 := by
      intro l
      show ZMod.castHom hdiv1 (ZMod p) (gammaU p e r (a l) ^ 2)
        = (r + (a l : ZMod p))⁻¹ ^ 2
      rw [map_pow, hinc (a l) (hunit l).1]
    have h2 : ∀ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (C l ^ 2)
        = (r + (b l : ZMod p))⁻¹ ^ 2 := by
      intro l
      show ZMod.castHom hdiv1 (ZMod p) (gammaU p e r (b l) ^ 2)
        = (r + (b l : ZMod p))⁻¹ ^ 2
      rw [map_pow, hinc (b l) (hunit l).2]
    rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_congr rfl (fun l _ => h2 l),
      hnd, sub_self]
  have hΔ : (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val :=
    (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mp hΔcast
  -- the two regimes
  rcases lt_or_ge e 4 with hlt | hge
  · have heq3 : e = 3 := by omega
    subst heq3
    exact levelSum_base_one3_deg (p := p) (e := 3) (ℓ := 1) hp2 le_rfl rfl χ hχ A C κ
      hsum hκnot hΔ
  · exact levelSum_step3_deg (p := p) (e := e) (ℓ := 1) (M := e - 2) hp2 he le_rfl
      (by omega) (by omega) χ hχ A C κ hsum hκnot hΔ
end Commons.NumberTheory.DirichletCharacter
