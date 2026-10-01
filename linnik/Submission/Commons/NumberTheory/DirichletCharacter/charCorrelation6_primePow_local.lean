import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_criticalClasses
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_levelSum_nondegenerate
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_primeMod_sharp
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_primeSq
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_cube_local
import Submission.Commons.NumberTheory.DirichletCharacter.prod_gcd_ge_of_criticalPoly_zero

set_option maxHeartbeats 3200000

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-! ## Transport of the sharp prime-modulus bound along `N = p` -/

theorem primeMod_sharp_transport {p N : ℕ} [Fact p.Prime] [NeZero N] (hN : N = p)
    (χ : DirichletCharacter ℂ N) (h1 : χ ≠ 1)
    (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
        ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j)) :
    ‖∑ x : ZMod N, χ (∏ l : Fin 3, (x + (a l : ZMod N))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod N))))‖
      ≤ 6 * Real.sqrt (p : ℝ) * ∏ j ∈ Finset.univ.erase i,
            (((Nat.gcd N (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
               - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
  classical
  set φ : ZMod N ≃+* ZMod p := ZMod.ringEquivCongr hN with hφdef
  obtain ⟨χ', hχ'val⟩ : ∃ χ' : DirichletCharacter ℂ p, ∀ z : ZMod p, χ' z = χ (φ.symm z) :=
    ⟨MulChar.mk (χ.toMonoidHom.comp φ.symm.toMonoidHom) (by
        intro z hz
        change χ.toMonoidHom (φ.symm z) = 0
        exact MulChar.map_nonunit χ (by
          intro hu
          exact hz (by
            have h2 : IsUnit (φ (φ.symm z)) := hu.map φ.toMonoidHom
            rwa [RingEquiv.apply_symm_apply] at h2))),
      fun z => rfl⟩
  have hχ'ne : χ' ≠ 1 := by
    intro hcon
    refine h1 (MulChar.ext fun u => ?_)
    have hu : IsUnit (φ (u : ZMod N)) := (Units.isUnit u).map φ.toMonoidHom
    have h2 : χ' (φ (u : ZMod N)) = 1 := by rw [hcon]; exact MulChar.one_apply hu
    rw [hχ'val] at h2
    rw [RingEquiv.symm_apply_apply] at h2
    simpa using h2
  have hφsymm : φ.symm = ZMod.ringEquivCongr hN.symm := by
    rw [hφdef, ZMod.ringEquivCongr_symm]
  have hcast : ∀ n : ℕ, φ.symm (n : ZMod p) = (n : ZMod N) := by
    intro n
    rw [hφsymm]
    have h := ZMod.ringEquivCongr_intCast (a := p) (b := N) hN.symm (n : ℤ)
    simpa using h
  have hprod : ∀ (y : ZMod p) (u : Fin 3 → ℕ),
      (∏ l : Fin 3, (φ.symm y + (u l : ZMod N)))
        = φ.symm (∏ l : Fin 3, (y + (u l : ZMod p))) := by
    intro y u
    rw [map_prod]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [map_add, hcast (u l)]
  have hF : ∀ y : ZMod p,
      χ (∏ l : Fin 3, (φ.symm y + (a l : ZMod N)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (φ.symm y + (b l : ZMod N))))
      = χ' (∏ l : Fin 3, (y + (a l : ZMod p)))
        * (starRingEnd ℂ) (χ' (∏ l : Fin 3, (y + (b l : ZMod p)))) := by
    intro y
    rw [hprod y a, hprod y b, ← hχ'val _, ← hχ'val _]
  have hsum : (∑ x : ZMod N, χ (∏ l : Fin 3, (x + (a l : ZMod N))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod N)))))
      = ∑ y : ZMod p, χ' (∏ l : Fin 3, (y + (a l : ZMod p))) *
        (starRingEnd ℂ) (χ' (∏ l : Fin 3, (y + (b l : ZMod p)))) := by
    have hsum' : (∑ x : ZMod N, χ (∏ l : Fin 3, (x + (a l : ZMod N))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod N)))))
        = ∑ y : ZMod p, χ (∏ l : Fin 3, (φ.symm y + (a l : ZMod N))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (φ.symm y + (b l : ZMod N)))) :=
      (Fintype.sum_equiv φ.symm.toEquiv
        (fun y : ZMod p => χ (∏ l : Fin 3, (φ.symm y + (a l : ZMod N))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (φ.symm y + (b l : ZMod N)))))
        (fun x : ZMod N => χ (∏ l : Fin 3, (x + (a l : ZMod N))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod N)))))
        (fun y => rfl)).symm
    rw [hsum']
    exact Finset.sum_congr rfl (fun y _ => hF y)
  rw [hsum]
  refine (charCorrelation6_primeMod_sharp (p := p) χ' hχ'ne a b i hi).trans_eq ?_
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [hN]

/-! ## The inner sum vanishes at a bad (non-unit) residue class -/

lemma innerSum_bad_eq_zero (e : ℕ) (he : 1 ≤ e) (χ : DirichletCharacter ℂ (p ^ e))
    (a b : Fin 3 → ℕ) (r : ZMod p)
    (hbad : (∃ l : Fin 3, (r + (a l : ZMod p)) = 0)
        ∨ (∃ l : Fin 3, (r + (b l : ZMod p)) = 0)) :
    (∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))) = 0 := by
  refine Finset.sum_eq_zero (fun z _ => ?_)
  have harg : ∀ (u : Fin 3 → ℕ) (l : Fin 3),
      (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e))
        + (u l : ℕ)) = (((r.val + p * z.val + u l : ℕ)) : ZMod (p ^ e)) := by
    intro u l; push_cast; ring
  rcases hbad with ⟨l0, hl0⟩ | ⟨l0, hl0⟩
  · have hfac : ¬ IsUnit ((((r.val + p * z.val + a l0 : ℕ)) : ZMod (p ^ e))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he]
      intro hdvd
      have h0 : ((r.val + p * z.val + a l0 : ℕ) : ZMod p) = 0 := by
        push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero, hl0]
      exact hdvd ((ZMod.natCast_eq_zero_iff _ p).mp h0)
    have hprod : ¬ IsUnit (∏ l : Fin 3, ((((r.val + p * z.val + a l : ℕ)) : ZMod (p ^ e)))) := by
      intro hcon
      have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin 3))
        (fun l' : Fin 3 => ((((r.val + p * z.val + a l' : ℕ)) : ZMod (p ^ e)))) (Finset.mem_univ l0)
      rw [← hsplit] at hcon
      exact hfac (IsUnit.mul_iff.mp hcon).2
    rw [Finset.prod_congr rfl (fun l _ => harg a l), MulChar.map_nonunit χ hprod, zero_mul]
  · have hfac : ¬ IsUnit ((((r.val + p * z.val + b l0 : ℕ)) : ZMod (p ^ e))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he]
      intro hdvd
      have h0 : ((r.val + p * z.val + b l0 : ℕ) : ZMod p) = 0 := by
        push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero, hl0]
      exact hdvd ((ZMod.natCast_eq_zero_iff _ p).mp h0)
    have hprod : ¬ IsUnit (∏ l : Fin 3, ((((r.val + p * z.val + b l : ℕ)) : ZMod (p ^ e)))) := by
      intro hcon
      have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin 3))
        (fun l' : Fin 3 => ((((r.val + p * z.val + b l' : ℕ)) : ZMod (p ^ e)))) (Finset.mem_univ l0)
      rw [← hsplit] at hcon
      exact hfac (IsUnit.mul_iff.mp hcon).2
    rw [Finset.prod_congr rfl (fun l _ => harg b l), MulChar.map_nonunit χ hprod,
      map_zero, mul_zero]

/-! ## The trivial bound on a critical class -/

lemma innerSum_norm_le_pow (e : ℕ) (he : 2 ≤ e) (χ : DirichletCharacter ℂ (p ^ e))
    (a b : Fin 3 → ℕ) (r : ZMod p) :
    ‖∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) - 2) := by
  calc ‖∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))‖
      ≤ ∑ _z : ZMod (p ^ (e - 2)), (1 : ℝ) := by
        refine norm_sum_le _ _ |>.trans (Finset.sum_le_sum (fun z _ => ?_))
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
          (DirichletCharacter.norm_le_one χ _)
    _ = ((p ^ (e - 2) : ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card]; simp
    _ = (p : ℝ) ^ ((e : ℝ) - 2) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_sub he,
          show (((2 : ℕ) : ℝ)) = (2 : ℝ) by norm_num]

/-! ## The critical-class level bound -/

theorem criticalSumBound {e : ℕ} (hp2 : p ≠ 2) (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) :
    ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
        then ∑ z : ZMod (p ^ (e - 2)),
              χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
        else 0)‖
      ≤ 2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * ((cF1 p a b).card : ℝ)
        + (p : ℝ) ^ ((e : ℝ) - 2) * ((cF2 p a b).card : ℝ) := by
  have he2 : 2 ≤ e := by omega
  have hpoint : ∀ r : ZMod p,
      ‖(if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
        then ∑ z : ZMod (p ^ (e - 2)),
              χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
        else 0)‖
      ≤ (if r ∈ cF1 p a b then 2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2)
         else if r ∈ cF2 p a b then (p : ℝ) ^ ((e : ℝ) - 2) else 0) := by
    intro r
    by_cases hbad : (∃ l : Fin 3, (r + (a l : ZMod p)) = 0)
        ∨ (∃ l : Fin 3, (r + (b l : ZMod p)) = 0)
    · have hmem1 : r ∉ cF1 p a b := by
        intro h
        rw [cF1, Finset.mem_filter] at h
        rcases hbad with ⟨l, hl⟩ | ⟨l, hl⟩
        · exact h.2.1 l hl
        · exact h.2.2.1 l hl
      have hmem2 : r ∉ cF2 p a b := by
        intro h
        rw [cF2, Finset.mem_filter] at h
        rcases hbad with ⟨l, hl⟩ | ⟨l, hl⟩
        · exact h.2.1 l hl
        · exact h.2.2.1 l hl
      have hz : (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
            - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
          then ∑ z : ZMod (p ^ (e - 2)),
                χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                  + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
                * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                  + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
          else 0) = 0 := by
        rw [innerSum_bad_eq_zero e (by omega) χ a b r hbad]
        split <;> rfl
      rw [hz, if_neg hmem1, if_neg hmem2]
      simp
    · push_neg at hbad
      by_cases hcrit : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
      · by_cases hndeg : (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹) ^ 2)
            ≠ (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹) ^ 2)
        · have hmem1 : r ∈ cF1 p a b := by
            rw [cF1, Finset.mem_filter]
            exact ⟨Finset.mem_univ r, hbad.1, hbad.2, hcrit, hndeg⟩
          rw [if_pos hmem1, if_pos hcrit]
          exact charCorrelation6_levelSum_nondegenerate (p := p) hp2 he χ hχ a b r
            (fun l => ⟨hbad.1 l, hbad.2 l⟩) (sub_eq_zero.mp hcrit) hndeg.symm
        · push_neg at hndeg
          have hmem2 : r ∈ cF2 p a b := by
            rw [cF2, Finset.mem_filter]
            exact ⟨Finset.mem_univ r, hbad.1, hbad.2, hcrit, hndeg⟩
          have hnot1 : ¬ (r ∈ cF1 p a b) := by
            intro hx
            rw [cF1, Finset.mem_filter] at hx
            exact hx.2.2.2.2 hndeg
          rw [if_pos hcrit, if_neg hnot1, if_pos hmem2]
          exact innerSum_norm_le_pow e he2 χ a b r
      · have hn1 : ¬ (r ∈ cF1 p a b) := by
          intro hx; rw [cF1, Finset.mem_filter] at hx; exact hcrit hx.2.2.2.1
        have hn2 : ¬ (r ∈ cF2 p a b) := by
          intro hx; rw [cF2, Finset.mem_filter] at hx; exact hcrit hx.2.2.2.1
        rw [if_neg hcrit, if_neg hn1, if_neg hn2]
        simp
  calc ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
        then ∑ z : ZMod (p ^ (e - 2)),
              χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
        else 0)‖
      ≤ ∑ r : ZMod p, ‖(if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
        then ∑ z : ZMod (p ^ (e - 2)),
              χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
        else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ r : ZMod p, (if r ∈ cF1 p a b then 2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2)
        else if r ∈ cF2 p a b then (p : ℝ) ^ ((e : ℝ) - 2) else 0) :=
        Finset.sum_le_sum (fun r _ => hpoint r)
    _ = 2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * ((cF1 p a b).card : ℝ)
        + (p : ℝ) ^ ((e : ℝ) - 2) * ((cF2 p a b).card : ℝ) := by
        rw [sum_ite_pair (fun r : ZMod p => r ∈ cF1 p a b) (fun r : ZMod p => r ∈ cF2 p a b)
          (by
            intro x hx hx1
            rw [cF2, Finset.mem_filter] at hx
            rw [cF1, Finset.mem_filter] at hx1
            exact hx1.2.2.2.2 hx.2.2.2.2)
          (2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2)) ((p : ℝ) ^ ((e : ℝ) - 2)),
          Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_mem_eq_inter,
          Finset.univ_inter]

/-! ## Main result -/

/-- **Asymptotic cubic correlation bound at a prime power, with the doubly degenerate
correction.** -/
theorem charCorrelation6_primePow_local {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (e : ℕ) (he : 1 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
        ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j)) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e)))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ 10000 * ((p : ℝ) ^ ((e : ℝ) / 2)) * ∏ j ∈ Finset.univ.erase i,
            (((Nat.gcd (p ^ e) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
               - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ)
        + 10000 * ((p : ℝ) ^ ((e : ℝ) - 1)) *
            (((Finset.univ : Finset (ZMod p)).filter (fun r : ZMod p =>
              (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹)
              ∧ (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹)^2) = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹)^2))).card : ℝ) := by
  rcases lt_or_ge e 2 with he1 | he2
  · have heq : e = 1 := by omega
    subst heq
    have htr := primeMod_sharp_transport (p := p) (N := p ^ 1) (pow_one p) χ h1 a b i hi
    refine htr.trans ?_
    have hP : (0 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i,
        (((Nat.gcd (p ^ 1) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
           - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) :=
      Finset.prod_nonneg (fun j _ => by positivity)
    have hK : (0 : ℝ) ≤ (((Finset.univ : Finset (ZMod p)).filter (fun r : ZMod p =>
        (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹)
        ∧ (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹)^2)
            = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹)^2))).card : ℝ) := by positivity
    have hs : (p : ℝ) ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt (p : ℝ) := by
      rw [show (((1 : ℕ) : ℝ) / 2) = ((1 : ℝ) / 2) by norm_num, Real.sqrt_eq_rpow]
    have hk1 : (p : ℝ) ^ (((1 : ℕ) : ℝ) - 1) = 1 := by
      rw [show (((1 : ℕ) : ℝ) - 1) = (0 : ℝ) by norm_num, Real.rpow_zero]
    rw [hs, hk1]
    nlinarith [hP, hK, Real.sqrt_nonneg (p : ℝ)]
  · rcases lt_or_ge e 3 with he2' | he3
    · have heq : e = 2 := by omega
      subst heq
      have htr := charCorrelation6_primeSq (p := p) hp2 χ hχ h1 a b i
      refine htr.trans ?_
      have hP : (0 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i,
          (((Nat.gcd (p ^ 2) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
             - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) :=
        Finset.prod_nonneg (fun j _ => by positivity)
      have hK : (0 : ℝ) ≤ (((Finset.univ : Finset (ZMod p)).filter (fun r : ZMod p =>
          (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹)
          ∧ (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹)^2)
              = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹)^2))).card : ℝ) := by positivity
      have h2 : (p : ℝ) ^ (((2 : ℕ) : ℝ) / 2) = (p : ℝ) := by
        rw [show (((2 : ℕ) : ℝ) / 2) = ((1 : ℝ)) by norm_num, Real.rpow_one]
      have h21 : (p : ℝ) ^ (((2 : ℕ) : ℝ) - 1) = (p : ℝ) := by
        rw [show (((2 : ℕ) : ℝ) - 1) = ((1 : ℝ)) by norm_num, Real.rpow_one]
      rw [h2, h21]
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      nlinarith [hP, hK, hp0]
    · have he2 : 2 ≤ e := by omega
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
      have hcc := charCorrelation6_criticalClasses (p := p) hp2 e he2 χ hχ a b
      rw [hcc, norm_mul, Complex.norm_natCast]
      have hcrit_bd := criticalSumBound (p := p) hp2 he3 χ hχ a b
      set PG : ℝ := ∏ j ∈ Finset.univ.erase i,
          (((Nat.gcd (p ^ e) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
             - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) with hPGdef
      set KZ : ℝ := (((Finset.univ : Finset (ZMod p)).filter (fun r : ZMod p =>
          (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹)
          ∧ (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹)^2)
              = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹)^2))).card : ℝ) with hKZdef
      have hPG1 : (1 : ℝ) ≤ PG := by
        rw [hPGdef]
        refine Finset.one_le_prod₀ (fun j _ => ?_)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.gcd_ne_zero_left (pow_ne_zero e (Fact.out : p.Prime).ne_zero))
      have hPG0 : (0 : ℝ) ≤ PG := le_trans zero_le_one hPG1
      have hKZ0 : (0 : ℝ) ≤ KZ := by rw [hKZdef]; positivity
      have hK2 : ((cF2 p a b).card : ℝ) ≤ KZ := by
        rw [hKZdef]; exact_mod_cast cF2_card_le_K a b
      have hA : (p : ℝ) * (p : ℝ) ^ (((e : ℝ) - 2) / 2) = (p : ℝ) ^ ((e : ℝ) / 2) := by
        have h := Real.rpow_add hp_pos (1 : ℝ) (((e : ℝ) - 2) / 2)
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      have hB : (p : ℝ) * (p : ℝ) ^ ((e : ℝ) - 2) = (p : ℝ) ^ ((e : ℝ) - 1) := by
        have h := Real.rpow_add hp_pos (1 : ℝ) ((e : ℝ) - 2)
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      have hpow2 : (0 : ℝ) ≤ (p : ℝ) ^ (((e : ℝ) - 2) / 2) := Real.rpow_nonneg hp0 _
      have hpow3 : (0 : ℝ) ≤ (p : ℝ) ^ ((e : ℝ) - 2) := Real.rpow_nonneg hp0 _
      have hstep : ∀ C1 C2 : ℝ,
          (p : ℝ) * (2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * C1 + (p : ℝ) ^ ((e : ℝ) - 2) * C2)
            = 2 * (p : ℝ) ^ ((e : ℝ) / 2) * C1 + (p : ℝ) ^ ((e : ℝ) - 1) * C2 := by
        intro C1 C2
        have h1 : (p : ℝ) * (2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * C1)
            = 2 * (p : ℝ) ^ ((e : ℝ) / 2) * C1 := by rw [← hA]; ring
        have h2 : (p : ℝ) * ((p : ℝ) ^ ((e : ℝ) - 2) * C2)
            = (p : ℝ) ^ ((e : ℝ) - 1) * C2 := by rw [← hB]; ring
        rw [mul_add, h1, h2]
      by_cases hH : cH p a b = 0
      · have hPGp : (p : ℝ) ≤ PG := by
          rw [hPGdef]
          exact_mod_cast prod_gcd_ge_of_criticalPoly_zero (p := p) (e := e) he a b i hi hH
        have hF1p : ((cF1 p a b).card : ℝ) ≤ (p : ℝ) := by
          have h1 : (cF1 p a b).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
          rw [ZMod.card] at h1
          exact_mod_cast h1
        have hC10 : (0 : ℝ) ≤ ((cF1 p a b).card : ℝ) := by positivity
        have hpowA : (0 : ℝ) ≤ (p : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_nonneg hp0 _
        have hpowB : (0 : ℝ) ≤ (p : ℝ) ^ ((e : ℝ) - 1) := Real.rpow_nonneg hp0 _
        calc (p : ℝ) * ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
              - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
            then ∑ z : ZMod (p ^ (e - 2)),
                  χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                    + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
                  * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                    + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
            else 0)‖
            ≤ (p : ℝ) * (2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * ((cF1 p a b).card : ℝ)
                + (p : ℝ) ^ ((e : ℝ) - 2) * ((cF2 p a b).card : ℝ)) :=
              mul_le_mul_of_nonneg_left hcrit_bd hp0
          _ ≤ (p : ℝ) * (2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * (p : ℝ)
                + (p : ℝ) ^ ((e : ℝ) - 2) * KZ) := by
              refine mul_le_mul_of_nonneg_left ?_ hp0
              nlinarith [hF1p, hK2, hpow2, hpow3, hp0, hC10, hKZ0]
          _ = 2 * (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) + (p : ℝ) ^ ((e : ℝ) - 1) * KZ := by
              rw [hstep]
          _ ≤ 10000 * (p : ℝ) ^ ((e : ℝ) / 2) * PG
                + 10000 * (p : ℝ) ^ ((e : ℝ) - 1) * KZ := by
              nlinarith [hPGp, hPG0, hpowA, hpowB, hKZ0, hp0]
      · have hF16 : ((cF1 p a b).card : ℝ) ≤ 6 := by
          have h1 : (cF1 p a b).card ≤ (cCcrit p a b).card := cF1_card_le_crit a b
          have h2 : (cCcrit p a b).card ≤ 6 := crit_nonbad_card_le a b hH
          exact_mod_cast le_trans h1 h2
        have hC10 : (0 : ℝ) ≤ ((cF1 p a b).card : ℝ) := by positivity
        have hpowA : (0 : ℝ) ≤ (p : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_nonneg hp0 _
        have hpowB : (0 : ℝ) ≤ (p : ℝ) ^ ((e : ℝ) - 1) := Real.rpow_nonneg hp0 _
        calc (p : ℝ) * ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
              - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
            then ∑ z : ZMod (p ^ (e - 2)),
                  χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                    + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
                  * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
                    + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
            else 0)‖
            ≤ (p : ℝ) * (2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * ((cF1 p a b).card : ℝ)
                + (p : ℝ) ^ ((e : ℝ) - 2) * ((cF2 p a b).card : ℝ)) :=
              mul_le_mul_of_nonneg_left hcrit_bd hp0
          _ ≤ (p : ℝ) * (2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) * 6
                + (p : ℝ) ^ ((e : ℝ) - 2) * KZ) := by
              refine mul_le_mul_of_nonneg_left ?_ hp0
              nlinarith [hF16, hK2, hpow2, hpow3, hC10, hKZ0]
          _ = 2 * (p : ℝ) ^ ((e : ℝ) / 2) * 6 + (p : ℝ) ^ ((e : ℝ) - 1) * KZ := by
              rw [hstep]
          _ ≤ 10000 * (p : ℝ) ^ ((e : ℝ) / 2) * PG
                + 10000 * (p : ℝ) ^ ((e : ℝ) - 1) * KZ := by
              nlinarith [hPG1, hPG0, hpowA, hpowB, hKZ0]

end Commons.NumberTheory.DirichletCharacter
