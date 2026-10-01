import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_levelSum_nondegenerate
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_levelSum_vanishing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

theorem levelSum3_degenerate_step {p e ℓ M : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e)
    (hℓ : 1 ≤ ℓ) (hM : 2 ≤ M) (heq : e = 2 * ℓ + M)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A C : Fin 3 → ZMod (p ^ e)) (κ : ℕ)
    (hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (hΔ : (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val) :
    levelSum3 p e ℓ M χ A C
      = (p : ℂ) * (if (p : ℕ) ∣ κ then levelSum3 p e ℓ (M - 1) χ A C else 0) := by
  by_cases hκ : (p : ℕ) ∣ κ
  · rw [if_pos hκ]
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
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
    -- ### the reduction of `κ - Δ x` modulo `p` (both `κ` and `Δ` vanish mod `p`)
    have hκcast : ZMod.castHom hdiv1 (ZMod p) ((((κ : ℕ)) : ZMod (p ^ e))) = 0 := by
      rw [map_natCast, ZMod.natCast_eq_zero_iff]
      exact hκ
    have hwval : ∀ x : ZMod (p ^ e),
        p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val := by
      intro x
      rw [← castHom_eq_zero_iff_dvd_val_one hdiv1]
      rw [map_sub, map_mul, hΔcast, hκcast, zero_mul, sub_zero]
    have hζone : ∀ x : ZMod (p ^ e),
        ζ ^ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val = 1 := by
      intro x
      obtain ⟨m, hm⟩ := hwval x
      rw [hm, pow_mul, hζprim.pow_eq_one, one_pow]
    -- ### the inner sum over the last digit is a full `p`-term sum of powers of `1`
    have hinner : ∀ x : ZMod (p ^ e),
        (∑ t ∈ Finset.range p,
            χ (prodCoord3 p e (ℓ + M - 1) (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)))) = p := by
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
      rw [Finset.sum_congr rfl hpc, sum_range_pow_eq p (hηpow x),
        if_pos (by rw [hη x]; exact hζone x)]
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
    rw [Finset.sum_congr rfl (fun n' _ => by rw [hinner ((n' : ℕ) : ZMod (p ^ e))])]
    rw [levelSum3_eq_range_sum (p := p) (e := e) (ℓ := ℓ) (M := M - 1) χ A C]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n' _ => ?_)
    rw [phase3_eq_chi_prodCoord3 (p := p) (e := e) (ℓ := ℓ) hℓ χ A C]
    exact mul_comm _ _
  · rw [if_neg hκ, mul_zero]
    exact levelSum_step3_deg (p := p) (e := e) (ℓ := ℓ) (M := M) hp2 he hℓ hM heq χ hχ A C κ
      hsum hκ hΔ

end Commons.NumberTheory.DirichletCharacter
