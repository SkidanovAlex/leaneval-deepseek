import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_content_iff
import Submission.Work.LinnikBurgess.card_hensel_le_sf
import Submission.Work.LinnikBurgess.critN_crossCong_delta_sf
import Submission.Work.LinnikBurgess.critN_deriv2_eval_shift_sf

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Polynomial

/-! ## Generic helpers -/

lemma capAux_pow_cast_dvd {p a b : ℕ} (h : a ≤ b) :
    ((p ^ a : ℕ) : ℤ) ∣ ((p ^ b : ℕ) : ℤ) := by
  rw [Nat.cast_pow, Nat.cast_pow]
  exact pow_dvd_pow _ h

lemma capAux_padicValNat_natAbs_eq_iff_dvd {p k : ℕ} [Fact p.Prime] {x : ℤ} (hx : x ≠ 0)
    (h : padicValNat p x.natAbs = k) :
    ((p ^ k : ℕ) : ℤ) ∣ x ∧ ¬ ((p ^ (k + 1) : ℕ) : ℤ) ∣ x := by
  constructor
  · have h1 : p ^ k ∣ x.natAbs :=
      (padicValNat_dvd_iff k x.natAbs).mpr (Or.inr (le_of_eq h.symm))
    exact (critNcontent.nat_dvd_natAbs_iff (p ^ k) x).mp h1
  · intro hd
    have h1 : p ^ (k + 1) ∣ x.natAbs := (critNcontent.nat_dvd_natAbs_iff (p ^ (k+1)) x).mpr hd
    rw [padicValNat_dvd_iff] at h1
    rcases h1 with h0 | hle
    · exact hx (Int.natAbs_eq_zero.mp h0)
    · omega

lemma capAux_not_dvd_contAB_of_map_ne_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    (hmod : (critN a b).map (Int.castRingHom (ZMod p)) ≠ 0) : ¬ p ∣ contAB a b := by
  intro hdvd
  apply hmod
  have hcoeff : ∀ n, (p : ℤ) ∣ (critN a b).coeff n := by
    intro n
    have h := (critN_content_iff (k := 1) hp5 a b).mpr (by simpa using hdvd) n
    simpa using h
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hcoeff n)

lemma capAux_not_dvd_sh3_of_unitAt {p y : ℕ} [Fact p.Prime] {b : Fin 3 → ℕ}
    (hy : ∀ l : Fin 3, ¬ p ∣ y + b l) : ¬ p ∣ sh3 y b := by
  intro hd
  have hp : p.Prime := Fact.out
  rw [sh3] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · exact hy 0 hd
    · exact hy 1 hd
  · exact hy 2 hd

lemma capAux_sh1_sub_eq_esymm3 (a b : Fin 3 → ℕ) (y : ℕ) :
    (sh1 y a : ℤ) - (sh1 y b : ℤ) = esymm3 a 0 - esymm3 b 0 := by
  simp [sh1, esymm3]; ring

lemma capAux_sh2_sub_eq_esymm3 (a b : Fin 3 → ℕ) (y : ℕ) :
    (sh2 y a : ℤ) - (sh2 y b : ℤ)
      = 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) + (esymm3 a 1 - esymm3 b 1) := by
  simp [sh2, esymm3]; ring

lemma capAux_sh3_sub_eq_esymm3 (a b : Fin 3 → ℕ) (y : ℕ) :
    (sh3 y a : ℤ) - (sh3 y b : ℤ)
      = (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1)
        + (esymm3 a 2 - esymm3 b 2) := by
  simp [sh3, esymm3]; ring

/-! ## The triple vanishing lemma at `k = 1` -/

theorem capAux_critN_tripleVanish_k1 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ) (y : ℕ)
    (hy : UnitAt p y a b)
    (h0 : (p : ℤ) ∣ (critN a b).eval (y : ℤ))
    (h1 : (p : ℤ) ∣ (Polynomial.derivative (critN a b)).eval (y : ℤ))
    (h2 : (p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative (critN a b))).eval (y : ℤ)) :
    p ∣ contAB a b := by
  have hp : Nat.Prime p := Fact.out
  have hv6 : padicValNat p 6 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h23 : p ∣ 2 * 3 := by simpa using h
    rcases hp.dvd_mul.mp h23 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) h2; omega
    · have := Nat.le_of_dvd (by norm_num : 0 < 3) h3; omega
  rw [critN_eval_shift] at h0
  rw [critN_deriv_eval_shift] at h1
  rw [critN_deriv2_eval_shift_sf] at h2
  have hB3 : ¬ (p : ℤ) ∣ (sh3 y b : ℤ) := by
    have hnd : ¬ p ∣ sh3 y b := capAux_not_dvd_sh3_of_unitAt (fun l => (hy l).2)
    rwa [Int.natCast_dvd_natCast]
  have hmain := critN_crossCong_delta_sf (p := p) (k := 1)
      (A1 := (sh1 y a : ℤ)) (A2 := (sh2 y a : ℤ)) (A3 := (sh3 y a : ℤ))
      (B1 := (sh1 y b : ℤ)) (B2 := (sh2 y b : ℤ)) (B3 := (sh3 y b : ℤ)) hB3
      (by simpa using h0) (by simpa using h1) (by simpa using h2)
  obtain ⟨hd1, hd2, hd3⟩ := hmain
  simp only [hv6, Nat.sub_zero, pow_one] at hd1 hd2 hd3
  have hD1 : (p : ℤ) ∣ esymm3 a 0 - esymm3 b 0 := by
    rw [← capAux_sh1_sub_eq_esymm3 a b y]; exact hd1
  have hD2 : (p : ℤ) ∣ esymm3 a 1 - esymm3 b 1 := by
    have hsum : (p : ℤ) ∣ 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0)
        + (esymm3 a 1 - esymm3 b 1) := by
      rw [← capAux_sh2_sub_eq_esymm3 a b y]; exact hd2
    have hk : (p : ℤ) ∣ 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) :=
      dvd_mul_of_dvd_right hD1 (2 * (y : ℤ))
    have h := dvd_sub hsum hk
    have hs : 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) + (esymm3 a 1 - esymm3 b 1)
        - 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) = esymm3 a 1 - esymm3 b 1 := by ring
    rwa [hs] at h
  have hD3 : (p : ℤ) ∣ esymm3 a 2 - esymm3 b 2 := by
    have hsum : (p : ℤ) ∣ (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0)
        + (y : ℤ) * (esymm3 a 1 - esymm3 b 1) + (esymm3 a 2 - esymm3 b 2) := by
      rw [← capAux_sh3_sub_eq_esymm3 a b y]; exact hd3
    have hk1 : (p : ℤ) ∣ (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) :=
      dvd_mul_of_dvd_right hD1 ((y : ℤ) ^ 2)
    have hk2 : (p : ℤ) ∣ (y : ℤ) * (esymm3 a 1 - esymm3 b 1) :=
      dvd_mul_of_dvd_right hD2 (y : ℤ)
    have hrest : (p : ℤ) ∣ (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0)
        + (y : ℤ) * (esymm3 a 1 - esymm3 b 1) := dvd_add hk1 hk2
    have h := dvd_sub hsum hrest
    have hs : (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1)
        + (esymm3 a 2 - esymm3 b 2)
        - ((y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1))
        = esymm3 a 2 - esymm3 b 2 := by ring
    rwa [hs] at h
  have hn1 : p ∣ (esymm3 a 0 - esymm3 b 0).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hD1
  have hn2 : p ∣ (esymm3 a 1 - esymm3 b 1).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hD2
  have hn3 : p ∣ (esymm3 a 2 - esymm3 b 2).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hD3
  rw [contAB]
  exact Nat.dvd_gcd hn1 (Nat.dvd_gcd hn2 hn3)

/-! ## The main theorem -/


/-- The capped part of the support of Lemma A has at most `4` points, when the Wronskian is not
divisible by `p` coefficientwise (`hmod`), the double-critical level `T+1` is not attained
(`hnoDL`), and `N = critN a b` has degree in `[2,4]`.

`capSet p e a b` is the set of support points `y < p^m` with `T ≤ nval y = v_p(N'(y))` (with the
convention `T+1` when `N'(y) = 0`). -/
theorem card_capSet_le_noncontent {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (hdeg2 : 2 ≤ (critN a b).natDegree)
    (hdeg : (critN a b).natDegree ≤ 4)
    (hmod : (critN a b).map (Int.castRingHom (ZMod p)) ≠ 0)
    (hbt : SuppTransfer p e a b) (hnoDL : ¬ DLp p (capLevel p e + 1) a b) :
    (capSet p e a b).card ≤ 4 := by
  have hp : Nat.Prime p := Fact.out
  have hm1 : 1 ≤ cubeLevel p e := one_le_cubeLevel hp5 (by omega)
  have hcont : ¬ p ∣ contAB a b := capAux_not_dvd_contAB_of_map_ne_zero hp5 a b hmod
  have hN : critN a b ≠ 0 := by
    intro h; rw [h] at hdeg2; simp at hdeg2
  have key : ∀ y ∈ capSet p e a b, nval p e a b y = capLevel p e := by
    intro y hy
    obtain ⟨hysup, hle⟩ := Finset.mem_filter.mp hy
    have hpred : suppPred p e a b y := (Finset.mem_filter.mp hysup).2
    by_contra hne
    have hgt : capLevel p e + 1 ≤ nval p e a b y := by omega
    obtain ⟨hbval, hdivN⟩ := hbt y hpred
    have hbvalT : bval p e a b y = capLevel p e := by rw [hbval]; omega
    rw [hbvalT] at hdivN
    have hNdiv : ((p ^ (capLevel p e + 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) :=
      dvd_trans (capAux_pow_cast_dvd (p := p) (by omega : capLevel p e + 1 ≤ cubeLevel p e + capLevel p e))
        hdivN
    have hderiv : ((p ^ (capLevel p e + 1) : ℕ) : ℤ)
        ∣ (Polynomial.derivative (critN a b)).eval (y : ℤ) := by
      rw [nval] at hgt
      split_ifs at hgt with hz
      · rw [hz]; exact dvd_zero _
      · have hd : p ^ (capLevel p e + 1) ∣ ((critN a b).derivative.eval (y : ℤ)).natAbs :=
          (padicValNat_dvd_iff (capLevel p e + 1) _).mpr (Or.inr hgt)
        exact (critNcontent.nat_dvd_natAbs_iff _ _).mp hd
    exact hnoDL ⟨y, hpred.1, hNdiv, hderiv⟩
  have hTm : capLevel p e ≤ cubeLevel p e := by
    rw [capLevel]
    have he3 : e ≤ 3 * cubeLevel p e := e_le_three_mul_cubeLevel (p := p) hp5
    omega
  rcases lt_or_eq_of_le hTm with hlt | heq
  · have hsub : capSet p e a b ⊆ henselSet p (critN a b) (cubeLevel p e) := by
      intro y hy
      have hkey := key y hy
      have hysup : y ∈ suppSet p e a b := (Finset.mem_filter.mp hy).1
      have hpred : suppPred p e a b y := (Finset.mem_filter.mp hysup).2
      have hyr : y < p ^ cubeLevel p e := Finset.mem_range.mp (Finset.mem_filter.mp hysup).1
      obtain ⟨hbval, hdivN⟩ := hbt y hpred
      have hbvalT : bval p e a b y = capLevel p e := by rw [hbval, hkey, min_self]
      rw [hbvalT] at hdivN
      have hNz : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
        intro hz; rw [nval, hz, if_pos rfl] at hkey; omega
      have hpad : padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs = capLevel p e := by
        rw [nval, if_neg hNz] at hkey; exact hkey
      obtain ⟨hd1, hd2⟩ := capAux_padicValNat_natAbs_eq_iff_dvd hNz hpad
      have hmax : max (2 * capLevel p e + 1) (cubeLevel p e + capLevel p e)
          = cubeLevel p e + capLevel p e := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hyr,
        ⟨capLevel p e, hd1, hd2, by rw [hmax]; exact hdivN⟩⟩
    calc (capSet p e a b).card ≤ (henselSet p (critN a b) (cubeLevel p e)).card :=
          Finset.card_le_card hsub
      _ ≤ (critN a b).natDegree := card_hensel_le_sf (critN a b) hN (cubeLevel p e) hm1
      _ ≤ 4 := hdeg
  · have hmT : cubeLevel p e = capLevel p e := heq.symm
    have hsub : capSet p e a b ⊆ henselSet p (critN a b).derivative (cubeLevel p e) := by
      intro y hy
      have hkey := key y hy
      have hysup : y ∈ suppSet p e a b := (Finset.mem_filter.mp hy).1
      have hpred : suppPred p e a b y := (Finset.mem_filter.mp hysup).2
      have hyr : y < p ^ cubeLevel p e := Finset.mem_range.mp (Finset.mem_filter.mp hysup).1
      obtain ⟨hbval, hdivN⟩ := hbt y hpred
      have hbvalT : bval p e a b y = capLevel p e := by rw [hbval, hkey, min_self]
      rw [hbvalT] at hdivN
      have hNz : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
        intro hz; rw [nval, hz, if_pos rfl] at hkey; omega
      have hpad : padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs = capLevel p e := by
        rw [nval, if_neg hNz] at hkey; exact hkey
      obtain ⟨hd1, hd2⟩ := capAux_padicValNat_natAbs_eq_iff_dvd hNz hpad
      have h0 : (p : ℤ) ∣ (critN a b).eval (y : ℤ) := by
        have h1 : (p : ℤ) ∣ ((p ^ (cubeLevel p e + capLevel p e) : ℕ) : ℤ) := by
          rw [Nat.cast_pow]
          exact dvd_pow_self _ (by omega)
        exact dvd_trans h1 hdivN
      have h1' : (p : ℤ) ∣ (Polynomial.derivative (critN a b)).eval (y : ℤ) := by
        have h1 : (p : ℤ) ∣ ((p ^ (capLevel p e) : ℕ) : ℤ) := by
          rw [Nat.cast_pow]
          exact dvd_pow_self _ (by omega)
        exact dvd_trans h1 hd1
      have hmax : max (2 * 0 + 1) (cubeLevel p e + 0) = capLevel p e := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hyr, ⟨0, by simp, ?_, ?_⟩⟩
      · intro hd
        have hd' : (p : ℤ)
            ∣ (Polynomial.derivative (Polynomial.derivative (critN a b))).eval (y : ℤ) := by
          simpa using hd
        exact absurd (capAux_critN_tripleVanish_k1 hp5 a b y hpred.1 h0 h1' hd') hcont
      · rw [hmax]; exact hd1
    have hN' : Polynomial.derivative (critN a b) ≠ 0 := by
      intro h
      have h0 := (Polynomial.derivative_eq_zero (p := critN a b)).mp h
      omega
    calc (capSet p e a b).card
          ≤ (henselSet p (critN a b).derivative (cubeLevel p e)).card := Finset.card_le_card hsub
      _ ≤ ((critN a b).derivative).natDegree := card_hensel_le_sf _ hN' (cubeLevel p e) hm1
      _ ≤ 4 := by
          have hle := Polynomial.natDegree_derivative_le (critN a b)
          omega

end Work.LinnikBurgess
