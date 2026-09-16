import Mathlib
import Submission.Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum
import Submission.Commons.NumberTheory.DivisorBound.pair_lcm_count_bound
import Submission.Commons.NumberTheory.Mertens.coprime_recip_moebius_sum_bound
import Submission.Commons.NumberTheory.DivisorBound.sum_tau_prod_prime_div_le_logsq
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one

open scoped BigOperators
open Finset
open ArithmeticFunction

namespace Commons.NumberTheory.Moebius

lemma coprime_div_gcd_of_squarefree {d e : ℕ} (hsq : Squarefree e) :
    Nat.Coprime (e / Nat.gcd d e) d := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpdiv
  have hps : p ∣ e / Nat.gcd d e := dvd_trans hpdiv (Nat.gcd_dvd_left _ _)
  have hpd : p ∣ d := dvd_trans hpdiv (Nat.gcd_dvd_right _ _)
  have hpe : p ∣ e := dvd_trans hps (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right d e))
  have hpg : p ∣ Nat.gcd d e := Nat.dvd_gcd hpd hpe
  have hpp : p * p ∣ Nat.gcd d e * (e / Nat.gcd d e) := mul_dvd_mul hpg hps
  have hge : Nat.gcd d e * (e / Nat.gcd d e) = e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  rw [hge] at hpp
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hpp

lemma sum_lcm_recip_eq_gcd_decomp (d x V : ℕ) (hd : 1 ≤ d) :
    (∑ e ∈ (Finset.Icc 1 V).filter (fun e => Nat.lcm d e ≤ x),
        (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ))
      = ∑ g ∈ d.divisors, (moebius g : ℝ) *
          ∑ s ∈ (Finset.Icc 1 (min (V / g) (x / d))).filter (fun s => Nat.Coprime s d),
            (moebius s : ℝ) / (s : ℝ) := by
  classical
  have hd0 : 0 < d := by omega
  have hdne : d ≠ 0 := by omega
  set E : Finset ℕ := (Finset.Icc 1 V).filter (fun e => Nat.lcm d e ≤ x) with hEdef
  set Pf : ℕ → Finset ℕ := fun g => (Finset.Icc 1 (min (V / g) (x / d))).filter (fun s => Nat.Coprime s d) with hPfdef
  set P : Finset (Sigma fun _ : ℕ => ℕ) := d.divisors.sigma Pf with hPdef
  set E0 : Finset ℕ := E.filter (fun e => moebius e ≠ 0) with hE0def
  set P0 : Finset (Sigma fun _ : ℕ => ℕ) := P.filter (fun p => moebius (p.1 * p.2) ≠ 0) with hP0def
  set L : ℕ → ℝ := fun e => (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) with hLdef
  set Ph : (Sigma fun _ : ℕ => ℕ) → ℝ := fun p => (moebius p.1 : ℝ) * ((moebius p.2 : ℝ) / (p.2 : ℝ)) with hPhdef
  set Ps : (Sigma fun _ : ℕ => ℕ) → ℝ := fun p => (moebius (p.1 * p.2) : ℝ) / (p.2 : ℝ) with hPsdef
  have hRHS : (∑ g ∈ d.divisors, (moebius g : ℝ) *
          ∑ s ∈ Pf g, (moebius s : ℝ) / (s : ℝ)) = ∑ p ∈ P, Ph p := by
    rw [hPhdef]
    rw [show (∑ g ∈ d.divisors, (moebius g : ℝ) *
          ∑ s ∈ Pf g, (moebius s : ℝ) / (s : ℝ))
        = ∑ g ∈ d.divisors, ∑ s ∈ Pf g, (moebius g : ℝ) * ((moebius s : ℝ) / (s : ℝ)) from by
          apply Finset.sum_congr rfl; intro g hg; rw [Finset.mul_sum]]
    rw [hPdef, Finset.sum_sigma']
  have hPhPs : ∀ p ∈ P, Ph p = Ps p := by
    intro p hp
    rw [hPhdef, hPsdef]; simp only []
    rw [hPdef, Finset.mem_sigma] at hp
    obtain ⟨hpg, hps⟩ := hp
    rw [hPfdef, Finset.mem_filter] at hps
    obtain ⟨_, hcop⟩ := hps
    have hg_dvd : p.1 ∣ d := (Nat.mem_divisors.mp hpg).1
    have hcop' : Nat.Coprime p.1 p.2 := Nat.Coprime.of_dvd_left hg_dvd hcop.symm
    have hmu : moebius (p.1 * p.2) = moebius p.1 * moebius p.2 :=
      (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop'.gcd_eq_one)
    rw [hmu]; push_cast; ring
  have hPΦw : (∑ p ∈ P, Ph p) = ∑ p ∈ P, Ps p := Finset.sum_congr rfl hPhPs
  have hPeq : (∑ p ∈ P, Ps p) = ∑ p ∈ P0, Ps p := by
    rw [hP0def]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : moebius (p.1 * p.2) ≠ 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      have h0 : moebius (p.1 * p.2) = 0 := by simpa using h
      simp [hPsdef, h0]
  have hEeq : (∑ e ∈ E, L e) = ∑ e ∈ E0, L e := by
    rw [hE0def]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : moebius e ≠ 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      have h0 : moebius e = 0 := by simpa using h
      simp [hLdef, h0]
  have hbij : (∑ e ∈ E0, L e) = ∑ p ∈ P0, Ps p := by
    refine Finset.sum_bij'
      (fun e _ => (⟨Nat.gcd d e, e / Nat.gcd d e⟩ : Sigma fun _ : ℕ => ℕ))
      (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
    · intro e he
      rw [hE0def, Finset.mem_filter] at he
      obtain ⟨heE, hmu_e⟩ := he
      rw [hEdef, Finset.mem_filter, Finset.mem_Icc] at heE
      obtain ⟨⟨he1, heV⟩, hlcme⟩ := heE
      have hsq_e : Squarefree e := (moebius_ne_zero_iff_squarefree).mp hmu_e
      have he0 : 0 < e := by omega
      set g := Nat.gcd d e with hgdef
      set s := e / Nat.gcd d e with hsdef
      have hg_dvd_e : g ∣ e := Nat.gcd_dvd_right d e
      have hgs : g * s = e := by rw [hgdef, hsdef]; exact Nat.mul_div_cancel' hg_dvd_e
      have hgpos : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_right d he0
      have hgcop : Nat.Coprime s d := by
        rw [hsdef]; exact coprime_div_gcd_of_squarefree (d := d) hsq_e
      have hs1 : 1 ≤ s := by
        rw [hsdef]; exact (Nat.one_le_div_iff hgpos).mpr (Nat.le_of_dvd he0 hg_dvd_e)
      have hsV : s ≤ V / g := by rw [Nat.le_div_iff_mul_le hgpos, mul_comm, hgs]; exact heV
      have hlcm : Nat.lcm d e = d * s := by
        have hgl : g * Nat.lcm d e = d * e := Nat.gcd_mul_lcm d e
        have h2 : g * Nat.lcm d e = g * (d * s) := by rw [hgl, ← hgs]; ring
        exact Nat.mul_left_cancel hgpos h2
      have hsx : s ≤ x / d := by rw [Nat.le_div_iff_mul_le hd0, mul_comm, ← hlcm]; exact hlcme
      rw [hP0def, Finset.mem_filter, hPdef, Finset.mem_sigma]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Nat.mem_divisors]; exact ⟨Nat.gcd_dvd_left d e, hdne⟩
      · rw [hPfdef, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hs1, le_min hsV hsx⟩, hgcop⟩
      · rw [hgs]; exact hmu_e
    · intro p hp
      rw [hP0def, Finset.mem_filter] at hp
      obtain ⟨hpP, hmu_p⟩ := hp
      rw [hPdef, Finset.mem_sigma] at hpP
      obtain ⟨hpg, hps⟩ := hpP
      rw [hPfdef, Finset.mem_filter, Finset.mem_Icc] at hps
      obtain ⟨hpsI, hcop⟩ := hps
      obtain ⟨hps1, hpsle⟩ := hpsI
      have hg_dvd : p.1 ∣ d := (Nat.mem_divisors.mp hpg).1
      have hgpos : 0 < p.1 := Nat.pos_of_dvd_of_pos hg_dvd hd0
      have hsV : p.2 ≤ V / p.1 := (le_min_iff.mp hpsle).1
      have hsx : p.2 ≤ x / d := (le_min_iff.mp hpsle).2
      have hcop2 : Nat.Coprime (d / p.1) p.2 :=
        Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hg_dvd) hcop.symm
      have hgcd_eq : Nat.gcd d (p.1 * p.2) = p.1 := by
        have hd_eq : d = p.1 * (d / p.1) := (Nat.mul_div_cancel' hg_dvd).symm
        rw [hd_eq, Nat.gcd_mul_left, hcop2.gcd_eq_one, mul_one]
      have hgeV : p.1 * p.2 ≤ V := by
        have := (Nat.le_div_iff_mul_le hgpos).mp hsV; rwa [mul_comm] at this
      have hge1 : 1 ≤ p.1 * p.2 := by
        have := Nat.mul_pos hgpos (by omega : 0 < p.2); omega
      have hlcmx : Nat.lcm d (p.1 * p.2) ≤ x := by
        have hgl : Nat.gcd d (p.1*p.2) * Nat.lcm d (p.1*p.2) = d * (p.1*p.2) := Nat.gcd_mul_lcm d (p.1*p.2)
        rw [hgcd_eq] at hgl
        have hcancel : Nat.lcm d (p.1*p.2) = d * p.2 := by
          have : p.1 * Nat.lcm d (p.1*p.2) = p.1 * (d * p.2) := by rw [hgl]; ring
          exact Nat.mul_left_cancel hgpos this
        rw [hcancel]
        have := (Nat.le_div_iff_mul_le hd0).mp hsx
        rwa [mul_comm] at this
      rw [hE0def, Finset.mem_filter]
      exact ⟨by rw [hEdef, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hge1, hgeV⟩, hlcmx⟩, hmu_p⟩
    · intro e he
      rw [hE0def, Finset.mem_filter] at he
      obtain ⟨heE, _⟩ := he
      rw [hEdef, Finset.mem_filter, Finset.mem_Icc] at heE
      obtain ⟨⟨he1, _⟩, _⟩ := heE
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
    · intro p hp
      rw [hP0def, Finset.mem_filter] at hp
      obtain ⟨hpP, _⟩ := hp
      rw [hPdef, Finset.mem_sigma] at hpP
      obtain ⟨hpg, hps⟩ := hpP
      rw [hPfdef, Finset.mem_filter] at hps
      obtain ⟨_, hcop⟩ := hps
      have hg_dvd : p.1 ∣ d := (Nat.mem_divisors.mp hpg).1
      have hgpos : 0 < p.1 := Nat.pos_of_dvd_of_pos hg_dvd hd0
      have hcop2 : Nat.Coprime (d / p.1) p.2 :=
        Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hg_dvd) hcop.symm
      have hgcd_eq : Nat.gcd d (p.1 * p.2) = p.1 := by
        have hd_eq : d = p.1 * (d / p.1) := (Nat.mul_div_cancel' hg_dvd).symm
        rw [hd_eq, Nat.gcd_mul_left, hcop2.gcd_eq_one, mul_one]
      obtain ⟨g, s⟩ := p
      rw [hgcd_eq, Nat.mul_div_right s hgpos]
    · intro e he
      rw [hE0def, Finset.mem_filter] at he
      obtain ⟨heE, _⟩ := he
      rw [hEdef, Finset.mem_filter, Finset.mem_Icc] at heE
      obtain ⟨⟨he1, heV⟩, _⟩ := heE
      have he0 : 0 < e := by omega
      rw [hLdef, hPsdef]; simp only []
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
      have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_right d he0
      have hgne : (Nat.gcd d e : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hgpos)
      have hsne : ((e / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by
        refine Nat.cast_ne_zero.mpr (ne_of_gt ?_)
        exact Nat.div_pos (Nat.le_of_dvd he0 (Nat.gcd_dvd_right d e)) hgpos
      have heq : (e : ℝ) = (Nat.gcd d e : ℝ) * ((e / Nat.gcd d e : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
      field_simp
      linarith [heq]
  rw [hRHS, hPΦw, hPeq, hEeq, hbij]

end Commons.NumberTheory.Moebius

namespace Commons.NumberTheory.Moebius

lemma lcm_recip_eq (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) :
    ((moebius d : ℝ) * (moebius e : ℝ)) / (Nat.lcm d e : ℝ)
      = ((moebius d : ℝ)/(d:ℝ)) * ((moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e:ℝ)) := by
  have hgl2 : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d:ℝ)*(e:ℝ) := by
    have h0 : Nat.gcd d e * Nat.lcm d e = d * e := Nat.gcd_mul_lcm d e
    exact_mod_cast h0
  have hl : (Nat.lcm d e : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hl]
  field_simp
  have hR : ((moebius d : ℝ) * (moebius e : ℝ) * (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ))
      = (moebius d : ℝ) * (moebius e : ℝ) * (d:ℝ) * (e:ℝ) := by
    calc (moebius d : ℝ) * (moebius e : ℝ) * (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ)
        = (moebius d : ℝ) * (moebius e : ℝ) * ((Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ)) := by ring
      _ = (moebius d : ℝ) * (moebius e : ℝ) * ((d:ℝ) * (e:ℝ)) := by rw [hgl2]
      _ = (moebius d : ℝ) * (moebius e : ℝ) * (d:ℝ) * (e:ℝ) := by ring
  linarith [hR]

theorem sum_moebius_lcm_recip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x V : ℕ, 1 ≤ V →
      |∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          (if Nat.lcm d e ≤ x then (moebius d : ℝ) * (moebius e : ℝ) / (Nat.lcm d e : ℝ) else 0)|
        ≤ C * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
  obtain ⟨C4, hC4pos, hC4⟩ := Commons.NumberTheory.DivisorBound.sum_tau_prod_prime_div_le_logsq
  refine ⟨C4, hC4pos, fun x V hV => ?_⟩
  have hUeq : (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
        (if Nat.lcm d e ≤ x then (moebius d : ℝ) * (moebius e : ℝ) / (Nat.lcm d e : ℝ) else 0))
      = ∑ d ∈ Finset.Icc 1 V, ((moebius d : ℝ) / (d : ℝ)) *
          (∑ e ∈ Finset.Icc 1 V,
            (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0)) := by
    apply Finset.sum_congr rfl; intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e he
    rw [Finset.mem_Icc] at hd he
    by_cases h : Nat.lcm d e ≤ x
    · simp only [h, ↓reduceIte]
      exact lcm_recip_eq d e (by omega) (by omega)
    · simp [h]
  have hJ : ∀ d ∈ Finset.Icc 1 V,
      |∑ e ∈ Finset.Icc 1 V,
          (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0)|
        ≤ ((Nat.divisors d).card : ℝ) * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := hd.1
    have hJeq : (∑ e ∈ Finset.Icc 1 V,
          (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0))
        = ∑ e ∈ (Finset.Icc 1 V).filter (fun e => Nat.lcm d e ≤ x),
            (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) := by
      rw [Finset.sum_filter]
    rw [hJeq, sum_lcm_recip_eq_gcd_decomp d x V hd1]
    calc |∑ g ∈ d.divisors, (moebius g : ℝ) *
            ∑ s ∈ (Finset.Icc 1 (min (V / g) (x / d))).filter (fun s => Nat.Coprime s d),
              (moebius s : ℝ) / (s : ℝ)|
        ≤ ∑ g ∈ d.divisors, |(moebius g : ℝ) *
            ∑ s ∈ (Finset.Icc 1 (min (V / g) (x / d))).filter (fun s => Nat.Coprime s d),
              (moebius s : ℝ) / (s : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g ∈ d.divisors, 1 * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
          apply Finset.sum_le_sum; intro g hg
          rw [abs_mul]
          refine mul_le_mul (Commons.NumberTheory.Moebius.moebius_abs_le_one g) ?_ (abs_nonneg _) (by norm_num)
          exact Commons.NumberTheory.Mertens.coprime_recip_moebius_sum_bound d (min (V / g) (x / d))
      _ = ((Nat.divisors d).card : ℝ) * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; simp
  rw [hUeq]
  calc |∑ d ∈ Finset.Icc 1 V, ((moebius d : ℝ) / (d : ℝ)) *
          (∑ e ∈ Finset.Icc 1 V,
            (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0))|
      ≤ ∑ d ∈ Finset.Icc 1 V, |((moebius d : ℝ) / (d : ℝ))| *
          |(∑ e ∈ Finset.Icc 1 V,
            (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0))| := by
        calc |∑ d ∈ Finset.Icc 1 V, ((moebius d : ℝ) / (d : ℝ)) *
              (∑ e ∈ Finset.Icc 1 V,
                (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0))|
            ≤ ∑ d ∈ Finset.Icc 1 V, |((moebius d : ℝ) / (d : ℝ)) *
              (∑ e ∈ Finset.Icc 1 V,
                (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0))| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ d ∈ Finset.Icc 1 V, |((moebius d : ℝ) / (d : ℝ))| *
              |(∑ e ∈ Finset.Icc 1 V,
                (if Nat.lcm d e ≤ x then (moebius e : ℝ) * (Nat.gcd d e : ℝ) / (e : ℝ) else 0))| := by
                apply Finset.sum_congr rfl; intro d hd; rw [abs_mul]
    _ ≤ ∑ d ∈ Finset.Icc 1 V, (1 / (d : ℝ)) *
          (((Nat.divisors d).card : ℝ) * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))) := by
        apply Finset.sum_le_sum; intro d hd
        rw [Finset.mem_Icc] at hd
        have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hmu : |(moebius d : ℝ) / (d : ℝ)| ≤ 1 / (d : ℝ) := by
          rw [abs_div, abs_of_pos hdpos]
          exact div_le_div_of_nonneg_right (Commons.NumberTheory.Moebius.moebius_abs_le_one d) (le_of_lt hdpos)
        exact mul_le_mul hmu (hJ d (by rw [Finset.mem_Icc]; exact hd)) (abs_nonneg _)
          (by positivity)
    _ ≤ C4 * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
        have heq : (∑ d ∈ Finset.Icc 1 V, (1 / (d : ℝ)) *
              (((Nat.divisors d).card : ℝ) * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))))
            = ∑ d ∈ Finset.Icc 1 V, ((Nat.divisors d).card : ℝ) / (d : ℝ) *
              (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
          apply Finset.sum_congr rfl; intro d hd; ring
        rw [heq]; exact hC4 V

end Commons.NumberTheory.Moebius

namespace Commons.NumberTheory.Moebius

/-- Lemma 3.1(g) of Akbary--Hambrook (after Friedlander--Iwaniec): for `V ≥ 1`
the second moment of the truncated Möbius divisor sums is `O(x (log(e³V))²)`. -/
theorem sum_moebius_small_divisors_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x V : ℕ, 1 ≤ V →
      ∑ k ∈ Finset.Icc 1 x, (∑ d ∈ k.divisors.filter (fun d => d ≤ V), (ArithmeticFunction.moebius d : ℝ)) ^ 2
        ≤ C * (x : ℝ) * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
  obtain ⟨C1, hC1pos, hC1⟩ := sum_moebius_lcm_recip_bound
  refine ⟨C1 + 1, by positivity, fun x V hV => ?_⟩
  rw [Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum x V]
  set S : ℝ := ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
      (if Nat.lcm d e ≤ x then (moebius d : ℝ) * (moebius e : ℝ) / (Nat.lcm d e : ℝ) else 0) with hSdef
  set δ : ℕ → ℕ → ℝ := fun d e =>
      (if Nat.lcm d e ≤ x then (x : ℝ) / (Nat.lcm d e : ℝ) else 0) - ((x / Nat.lcm d e : ℕ) : ℝ) with hδdef
  have hVne : (V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Real.log (Real.exp 3 * (V : ℝ)) = 3 + Real.log V := by
    rw [Real.log_mul (Real.exp_ne_zero 3) hVne, Real.log_exp]
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg (by exact_mod_cast hV)
  have htermeq : ∀ d ∈ Finset.Icc 1 V, ∀ e ∈ Finset.Icc 1 V,
      (moebius d : ℝ) * (moebius e : ℝ) * ((x / Nat.lcm d e : ℕ) : ℝ)
        = (x : ℝ) * (if Nat.lcm d e ≤ x then (moebius d : ℝ) * (moebius e : ℝ) / (Nat.lcm d e : ℝ) else 0)
          - (moebius d : ℝ) * (moebius e : ℝ) * δ d e := by
    intro d hd e he
    rw [Finset.mem_Icc] at hd he
    rw [hδdef]; simp only []
    by_cases h : Nat.lcm d e ≤ x
    · simp only [h, ↓reduceIte]
      have hm0 : (Nat.lcm d e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.lcm_pos (by omega) (by omega)))
      field_simp
      ring
    · simp only [h, ↓reduceIte]
      have hmx : x / Nat.lcm d e = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_le h)
      rw [hmx]; push_cast; ring
  have hT : (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
        (moebius d : ℝ) * (moebius e : ℝ) * ((x / Nat.lcm d e : ℕ) : ℝ))
      = (x : ℝ) * S
        - ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
            (moebius d : ℝ) * (moebius e : ℝ) * δ d e := by
    rw [hSdef]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro d hd
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro e he
    rw [htermeq d hd e he]
  have hδ_nonneg : ∀ d ∈ Finset.Icc 1 V, ∀ e ∈ Finset.Icc 1 V, 0 ≤ δ d e := by
    intro d hd e he
    rw [Finset.mem_Icc] at hd he
    rw [hδdef]; simp only []
    by_cases h : Nat.lcm d e ≤ x
    · rw [if_pos h, sub_nonneg]
      exact Nat.cast_div_le
    · rw [if_neg h]
      have hmx : x / Nat.lcm d e = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_le h)
      rw [hmx]; norm_num
  have hδ_le_one : ∀ d ∈ Finset.Icc 1 V, ∀ e ∈ Finset.Icc 1 V, δ d e ≤ 1 := by
    intro d hd e he
    rw [Finset.mem_Icc] at hd he
    have hm1 : 1 ≤ Nat.lcm d e := Nat.lcm_pos (by omega) (by omega)
    rw [hδdef]; simp only []
    by_cases h : Nat.lcm d e ≤ x
    · rw [if_pos h]
      have hfloor : ((x / Nat.lcm d e : ℕ) : ℝ) = ⌊(x:ℝ) / (Nat.lcm d e : ℝ)⌋₊ := by
        rw [Nat.floor_div_natCast, Nat.floor_natCast]
      rw [hfloor]
      have := Nat.lt_floor_add_one ((x:ℝ) / (Nat.lcm d e : ℝ))
      linarith
    · rw [if_neg h]
      have hmx : x / Nat.lcm d e = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_le h)
      rw [hmx]; norm_num
  have hSbound : |S| ≤ C1 * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
    rw [hSdef]; exact hC1 x V hV
  have hEbound : |∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
        (moebius d : ℝ) * (moebius e : ℝ) * δ d e| ≤ (x : ℝ) * (1 + Real.log V) ^ 2 := by
    have hcard : (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          (if Nat.lcm d e ≤ x then (1:ℝ) else 0))
        = (((Finset.Icc 1 V ×ˢ Finset.Icc 1 V).filter
            (fun q => Nat.lcm q.1 q.2 ≤ x)).card : ℝ) := by
      have hnat : (((Finset.Icc 1 V ×ˢ Finset.Icc 1 V).filter
            (fun q => Nat.lcm q.1 q.2 ≤ x)).card)
          = ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (if Nat.lcm d e ≤ x then (1:ℕ) else 0) := by
        rw [Finset.card_filter, Finset.sum_product]
      exact_mod_cast hnat.symm
    calc |∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (moebius d : ℝ) * (moebius e : ℝ) * δ d e|
        ≤ ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, |(moebius d : ℝ) * (moebius e : ℝ) * δ d e| := by
          calc |∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (moebius d : ℝ) * (moebius e : ℝ) * δ d e|
              ≤ ∑ d ∈ Finset.Icc 1 V, |∑ e ∈ Finset.Icc 1 V, (moebius d : ℝ) * (moebius e : ℝ) * δ d e| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, |(moebius d : ℝ) * (moebius e : ℝ) * δ d e| := by
                apply Finset.sum_le_sum; intro d hd
                exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, δ d e := by
          apply Finset.sum_le_sum; intro d hd
          apply Finset.sum_le_sum; intro e he
          rw [abs_mul, abs_mul]
          have h1 : |(moebius d : ℝ)| ≤ 1 := Commons.NumberTheory.Moebius.moebius_abs_le_one d
          have h2 : |(moebius e : ℝ)| ≤ 1 := Commons.NumberTheory.Moebius.moebius_abs_le_one e
          have h3 : 0 ≤ δ d e := hδ_nonneg d hd e he
          calc |(moebius d : ℝ)| * |(moebius e : ℝ)| * |δ d e|
              ≤ 1 * 1 * δ d e := by
                rw [abs_of_nonneg h3]
                exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) (le_refl _) h3 (by norm_num)
            _ = δ d e := by ring
      _ ≤ ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (if Nat.lcm d e ≤ x then (1:ℝ) else 0) := by
          apply Finset.sum_le_sum; intro d hd
          apply Finset.sum_le_sum; intro e he
          by_cases h : Nat.lcm d e ≤ x
          · rw [if_pos h]; exact hδ_le_one d hd e he
          · rw [if_neg h]
            rw [hδdef]; simp only []
            rw [if_neg h]; simp
      _ = (((Finset.Icc 1 V ×ˢ Finset.Icc 1 V).filter
          (fun q => Nat.lcm q.1 q.2 ≤ x)).card : ℝ) := hcard
      _ ≤ (x : ℝ) * (1 + Real.log V) ^ 2 :=
          Commons.NumberTheory.DivisorBound.pair_lcm_count_bound x V
  rw [hT]
  have hxnn : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  calc (x : ℝ) * S - ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (moebius d : ℝ) * (moebius e : ℝ) * δ d e
      ≤ (x : ℝ) * |S| + |∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (moebius d : ℝ) * (moebius e : ℝ) * δ d e| := by
        have h1 : (x : ℝ) * S ≤ (x : ℝ) * |S| := mul_le_mul_of_nonneg_left (le_abs_self S) hxnn
        have h2 : -(∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (moebius d : ℝ) * (moebius e : ℝ) * δ d e)
            ≤ |∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, (moebius d : ℝ) * (moebius e : ℝ) * δ d e| := neg_le_abs _
        linarith
    _ ≤ (x : ℝ) * (C1 * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2) + (x : ℝ) * (1 + Real.log V) ^ 2 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hSbound hxnn
        · exact hEbound
    _ ≤ (C1 + 1) * (x : ℝ) * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
        have hb : (1 + Real.log V) ^ 2 ≤ (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
          rw [hlog]
          exact pow_le_pow_left₀ (by linarith) (by linarith) 2
        nlinarith [hxnn, sq_nonneg (Real.log (Real.exp 3 * (V:ℝ)))]

end Commons.NumberTheory.Moebius
