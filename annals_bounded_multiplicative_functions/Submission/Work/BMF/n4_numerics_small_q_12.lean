import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4_perr_defs
import Submission.Work.BMF.n4_polylog_le
import Submission.Work.BMF.n4_log_decay_12
import Submission.Work.BMF.n4_omega_le_Pe_12

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **N4, Case B: the numerical comparisons at the reachable error exponent `1/12`.**

With `Perr = n4Perr C₁ c₁ P q = C₁ P exp(-c₁ (log P)^{1/12}) + C₁ ω(q)` and
`E = n4Eee C₁ c₁ P = exp(c₁ (log P)^{1/12})/(C₁ log P)` (`ω(q) = q.primeFactors.card`,
`π₀(P) = pi0 P = P/log P`), for fixed `ℓ ≥ 2`, `c₁ > 0`, `C₁ > 0` there are `C, P₀ > 0`
(depending only on `ℓ, c₁, C₁`) such that for `P ≥ P₀`, `3 ≤ N ≤ P^{ℓ-1}`,
`1/log P ≤ C₀`, `1 ≤ q ≤ (log P)^{ℓ+4}`:

1. `Perr² π₀(P)^{ℓ-1} N log N ≤ C C₀ π₀(P)^{2ℓ}`  (the `N`-part of the mean-value term);
2. `Perr² P^{ℓ-1} log P π₀(P)^{ℓ-1} log N ≤ C π₀(P)^{2ℓ}`  (the `P^{ℓ-1} log P`-part);
3. `E Perr^{2ℓ} log N log P ≤ C π₀(P)^{2ℓ}`  (the small-`|t|` error region). -/
theorem n4_numerics_small_q_12 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (c₁ C₁ : ℝ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 ≤ P₀ ∧ ∀ (P N C₀ : ℝ) (q : ℕ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
      1 / Real.log P ≤ C₀ → 1 ≤ q → q ≤ (Real.log P) ^ (ℓ + 4) →
      n4Perr C₁ c₁ P q ^ 2 * pi0 P ^ (ℓ - 1) * N * Real.log N ≤ C * C₀ * pi0 P ^ (2 * ℓ) ∧
      n4Perr C₁ c₁ P q ^ 2 * P ^ (ℓ - 1) * Real.log P * pi0 P ^ (ℓ - 1) * Real.log N
          ≤ C * pi0 P ^ (2 * ℓ) ∧
      n4Eee C₁ c₁ P * n4Perr C₁ c₁ P q ^ (2 * ℓ) * Real.log N * Real.log P
          ≤ C * pi0 P ^ (2 * ℓ) := by
  obtain ⟨Pω, -, hω⟩ := n4_omega_le_Pe_12 ℓ hℓ c₁ hc₁
  obtain ⟨Pd2, -, hdec2⟩ := n4_log_decay_12 (2*c₁) (by linarith) (ℓ+3)
  have hk1nn : (1:ℝ) ≤ (((2*ℓ-1:ℕ)):ℝ) := by
    have h : 1 ≤ 2*ℓ - 1 := by omega
    exact_mod_cast h
  obtain ⟨Pd3, -, hdec3⟩ := n4_log_decay_12 ((((2*ℓ-1:ℕ)):ℝ) * c₁) (mul_pos (by linarith) hc₁) (2*ℓ+1)
  set C : ℝ := max (4*C₁^2*((ℓ-1:ℕ):ℝ)) ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁) + 1 with hCdef
  have hK1nn : (0:ℝ) ≤ 4*C₁^2*((ℓ-1:ℕ):ℝ) := by positivity
  have hK2nn : (0:ℝ) ≤ (2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁ := by positivity
  have hCpos : 0 < C := by
    rw [hCdef]
    have hmax : (0:ℝ) ≤ max (4*C₁^2*((ℓ-1:ℕ):ℝ)) ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁) :=
      le_trans hK1nn (le_max_left _ _)
    linarith
  have hCK1 : 4*C₁^2*((ℓ-1:ℕ):ℝ) ≤ C := by
    rw [hCdef]
    linarith [le_max_left (4*C₁^2*((ℓ-1:ℕ):ℝ)) ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁)]
  have hCK2 : (2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁ ≤ C := by
    rw [hCdef]
    linarith [le_max_right (4*C₁^2*((ℓ-1:ℕ):ℝ)) ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁)]
  set P₀ : ℝ := max (max (max Pω Pd2) Pd3) 4 with hP₀def
  have hP₀1 : 1 ≤ P₀ := by
    rw [hP₀def]; linarith [le_max_right (max (max Pω Pd2) Pd3) (4:ℝ)]
  have hthω : Pω ≤ P₀ := by
    rw [hP₀def]
    linarith [le_max_left Pω Pd2, le_max_left (max Pω Pd2) Pd3,
      le_max_left (max (max Pω Pd2) Pd3) (4:ℝ)]
  have hth2 : Pd2 ≤ P₀ := by
    rw [hP₀def]
    linarith [le_max_right Pω Pd2, le_max_left (max Pω Pd2) Pd3,
      le_max_left (max (max Pω Pd2) Pd3) (4:ℝ)]
  have hth3 : Pd3 ≤ P₀ := by
    rw [hP₀def]
    linarith [le_max_right (max Pω Pd2) Pd3, le_max_left (max (max Pω Pd2) Pd3) (4:ℝ)]
  have hP₀4 : (4:ℝ) ≤ P₀ := by rw [hP₀def]; exact le_max_right _ _
  refine ⟨C, P₀, hCpos, hP₀1, ?_⟩
  intro P N C₀ q hP hN3 hNle hC₀ hq1 hqle
  have hPωP : Pω ≤ P := le_trans hthω hP
  have hPd2P : Pd2 ≤ P := le_trans hth2 hP
  have hPd3P : Pd3 ≤ P := le_trans hth3 hP
  have hP4 : (4:ℝ) ≤ P := le_trans hP₀4 hP
  have hP1 : (1:ℝ) ≤ P := by linarith
  have hPpos : (0:ℝ) < P := by linarith
  set L : ℝ := Real.log P with hL
  set ee : ℝ := Real.exp (-c₁ * L ^ (1/12:ℝ)) with hee
  set om : ℝ := ((q.primeFactors.card : ℝ)) with hom
  set Perr : ℝ := C₁ * P * ee + C₁ * om with hPerr
  set E : ℝ := Real.exp (c₁ * L ^ (1/12:ℝ)) / (C₁ * L) with hE
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact (Real.le_log_iff_exp_le hPpos).mpr (by linarith [Real.exp_one_lt_three, hP4])
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hNpos : 0 < N := by linarith
  have hNnn : (0:ℝ) ≤ N := by linarith
  have hlogNnn : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have homnn : 0 ≤ om := by rw [hom]; positivity
  have heenn : 0 ≤ ee := by rw [hee]; positivity
  have hPerrnn : 0 ≤ Perr := by rw [hPerr]; positivity
  have hpi : pi0 P = P / L := by rw [pi0, ← hL]
  have hpinn : 0 ≤ pi0 P := by rw [hpi]; positivity
  have hC₀nn : 0 ≤ C₀ := by
    have hpos : (0:ℝ) < 1/Real.log P := by rw [← hL]; exact one_div_pos.mpr hLpos
    linarith
  have hC₀L : 1/L ≤ C₀ := hC₀
  have hpP : P^2 * P^(ℓ-1) = P^(ℓ+1) := by rw [← pow_add]; congr 1; omega
  have hpπ : pi0 P^(ℓ-1) * pi0 P^(ℓ+1) = pi0 P^(2*ℓ) := by rw [← pow_add]; congr 1; omega
  have hpL4 : L^2 * L^(ℓ+1) = L^(ℓ+3) := by rw [← pow_add]; congr 1; omega
  have hpL5 : L * L^(2*ℓ) = L^(2*ℓ+1) := (pow_succ' L (2*ℓ)).symm
  have hpidiv : pi0 P^(ℓ+1) = P^(ℓ+1)/L^(ℓ+1) := by rw [hpi, div_pow]
  have hPerreq : n4Perr C₁ c₁ P q = Perr := by
    rw [hPerr]
    simp only [n4Perr]
    rw [← hL, ← hee, ← hom]
  have hEeq : n4Eee C₁ c₁ P = E := by
    rw [hE]
    simp only [n4Eee]
    rw [← hL]
  have hωle : om ≤ P * ee := by
    rw [hom, hee, hL]
    exact hω P hPωP q hq1 hqle
  have hPerr_le : Perr ≤ 2*C₁*P*ee := by
    rw [hPerr]
    have h2 : C₁ * om ≤ C₁ * (P*ee) := mul_le_mul_of_nonneg_left hωle hC₁.le
    linarith
  have hlogN_le : Real.log N ≤ ((ℓ-1:ℕ):ℝ) * L := by
    calc Real.log N ≤ Real.log (P^(ℓ-1)) := Real.log_le_log hNpos hNle
      _ = ((ℓ-1:ℕ):ℝ) * Real.log P := Real.log_pow P (ℓ-1)
      _ = ((ℓ-1:ℕ):ℝ) * L := by rw [← hL]
  have hdecA : L^(ℓ+3) * ee^2 ≤ 1 := by
    have h1 := hdec2 P hPd2P
    rw [← hL] at h1
    have hE2 : Real.exp (-(2*c₁) * L^(1/12:ℝ)) = ee^2 := by
      rw [hee, ← Real.exp_nat_mul (-c₁ * L^(1/12:ℝ)) 2]
      congr 1
      ring
    rwa [hE2] at h1
  have hdecB : L^(2*ℓ+1) * ee^(2*ℓ-1) ≤ 1 := by
    have h1 := hdec3 P hPd3P
    rw [← hL] at h1
    have hE2 : Real.exp (-((((2*ℓ-1:ℕ)):ℝ) * c₁) * L^(1/12:ℝ)) = ee^(2*ℓ-1) := by
      rw [hee, ← Real.exp_nat_mul (-c₁ * L^(1/12:ℝ)) (2*ℓ-1)]
      congr 1
      ring
    rwa [hE2] at h1
  have hkey1 : ee^2 * L^(ℓ+2) ≤ C₀ := by
    have h1 : ee^2 * L^(ℓ+2) ≤ 1/L := by
      rw [le_div_iff₀ hLpos]
      have hL3 : L^(ℓ+3) = L^(ℓ+2) * L := by
        rw [show ℓ+3 = ℓ+2+1 from by omega, pow_succ]
      have hre : ee^2 * L^(ℓ+2) * L = L^(ℓ+3) * ee^2 := by rw [hL3]; ring
      rw [hre]; exact hdecA
    linarith
  rw [hPerreq, hEeq]
  have hpart1 : Perr^2 * pi0 P^(ℓ-1) * N * Real.log N ≤ C * C₀ * pi0 P^(2*ℓ) := by
    have hPerr2 : Perr^2 ≤ (2*C₁*P*ee)^2 := pow_le_pow_left₀ hPerrnn hPerr_le 2
    have hcoreBL : ee^2 * L ≤ C₀ / L^(ℓ+1) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < L^(ℓ+1))]
      have hre : ee^2 * L * L^(ℓ+1) = ee^2 * L^(ℓ+2) := by
        rw [mul_assoc]
        congr 1
        exact (pow_succ' L (ℓ+1)).symm
      rw [hre]; exact hkey1
    have hcoreB : P^(ℓ+1) * (ee^2*L) ≤ C₀ * (P^(ℓ+1)/L^(ℓ+1)) := by
      rw [show C₀ * (P^(ℓ+1)/L^(ℓ+1)) = P^(ℓ+1) * (C₀/L^(ℓ+1)) from by ring]
      exact mul_le_mul_of_nonneg_left hcoreBL (pow_nonneg hPpos.le _)
    have hstep : Perr^2 * pi0 P^(ℓ-1) * N * Real.log N
        ≤ 4*C₁^2*((ℓ-1:ℕ):ℝ) * (P^(ℓ+1) * (ee^2*L)) * pi0 P^(ℓ-1) := by
      calc Perr^2 * pi0 P^(ℓ-1) * N * Real.log N
          = (Perr^2 * pi0 P^(ℓ-1)) * (N * Real.log N) := by ring
        _ ≤ ((2*C₁*P*ee)^2 * pi0 P^(ℓ-1)) * (P^(ℓ-1) * (((ℓ-1:ℕ):ℝ)*L)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right hPerr2 (pow_nonneg hpinn _)
            · exact mul_le_mul hNle hlogN_le hlogNnn (pow_nonneg hPpos.le _)
            · exact mul_nonneg hNnn hlogNnn
            · exact mul_nonneg (sq_nonneg _) (pow_nonneg hpinn _)
        _ = 4*C₁^2*((ℓ-1:ℕ):ℝ) * (P^2 * P^(ℓ-1)) * (ee^2*L) * pi0 P^(ℓ-1) := by ring
        _ = 4*C₁^2*((ℓ-1:ℕ):ℝ) * (P^(ℓ+1) * (ee^2*L)) * pi0 P^(ℓ-1) := by rw [hpP]; ring
    have hstep2 : 4*C₁^2*((ℓ-1:ℕ):ℝ) * (P^(ℓ+1) * (ee^2*L)) * pi0 P^(ℓ-1)
        ≤ 4*C₁^2*((ℓ-1:ℕ):ℝ) * C₀ * pi0 P^(2*ℓ) := by
      have hfac : (0:ℝ) ≤ 4*C₁^2*((ℓ-1:ℕ):ℝ) * pi0 P^(ℓ-1) :=
        mul_nonneg hK1nn (pow_nonneg hpinn _)
      have hA : 4*C₁^2*((ℓ-1:ℕ):ℝ) * (P^(ℓ+1)*(ee^2*L)) * pi0 P^(ℓ-1)
          ≤ 4*C₁^2*((ℓ-1:ℕ):ℝ) * (C₀ * (P^(ℓ+1)/L^(ℓ+1))) * pi0 P^(ℓ-1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hpinn _)
        exact mul_le_mul_of_nonneg_left hcoreB hK1nn
      have hB : 4*C₁^2*((ℓ-1:ℕ):ℝ) * (C₀ * (P^(ℓ+1)/L^(ℓ+1))) * pi0 P^(ℓ-1)
          = 4*C₁^2*((ℓ-1:ℕ):ℝ) * C₀ * pi0 P^(2*ℓ) := by
        rw [← hpπ, hpidiv]; ring
      linarith [hA, hB.le]
    have h3 : 4*C₁^2*((ℓ-1:ℕ):ℝ) * C₀ * pi0 P^(2*ℓ) ≤ C * C₀ * pi0 P^(2*ℓ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK1 hC₀nn) (pow_nonneg hpinn _)
    linarith [hstep, hstep2, h3]
  have hpart2 : Perr^2 * P^(ℓ-1) * L * pi0 P^(ℓ-1) * Real.log N ≤ C * pi0 P^(2*ℓ) := by
    have hPerr2 : Perr^2 ≤ (2*C₁*P*ee)^2 := pow_le_pow_left₀ hPerrnn hPerr_le 2
    have hcore2 : 4*C₁^2*((ℓ-1:ℕ):ℝ) * ee^2 * L^2 ≤ C / L^(ℓ+1) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < L^(ℓ+1))]
      have hre : 4*C₁^2*((ℓ-1:ℕ):ℝ) * ee^2 * L^2 * L^(ℓ+1)
          = 4*C₁^2*((ℓ-1:ℕ):ℝ) * ee^2 * L^(ℓ+3) := by
        rw [show 4*C₁^2*((ℓ-1:ℕ):ℝ) * ee^2 * L^2 * L^(ℓ+1)
              = 4*C₁^2*((ℓ-1:ℕ):ℝ) * ee^2 * (L^2 * L^(ℓ+1)) from by ring, hpL4]
      rw [hre]
      calc 4*C₁^2*((ℓ-1:ℕ):ℝ) * ee^2 * L^(ℓ+3)
          = 4*C₁^2*((ℓ-1:ℕ):ℝ) * (L^(ℓ+3) * ee^2) := by ring
        _ ≤ 4*C₁^2*((ℓ-1:ℕ):ℝ) * 1 := mul_le_mul_of_nonneg_left hdecA hK1nn
        _ = 4*C₁^2*((ℓ-1:ℕ):ℝ) := mul_one _
        _ ≤ C := hCK1
    have hstep : Perr^2 * P^(ℓ-1) * L * pi0 P^(ℓ-1) * Real.log N
        ≤ (4*C₁^2*((ℓ-1:ℕ):ℝ) * P^(ℓ+1) * ee^2 * L^2) * pi0 P^(ℓ-1) := by
      calc Perr^2 * P^(ℓ-1) * L * pi0 P^(ℓ-1) * Real.log N
          = (Perr^2 * P^(ℓ-1) * L) * (pi0 P^(ℓ-1) * Real.log N) := by ring
        _ ≤ ((2*C₁*P*ee)^2 * P^(ℓ-1) * L) * (pi0 P^(ℓ-1) * (((ℓ-1:ℕ):ℝ)*L)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hPerr2 (pow_nonneg hPpos.le _)) hLnn
            · exact mul_le_mul_of_nonneg_left hlogN_le (pow_nonneg hpinn _)
            · exact mul_nonneg (pow_nonneg hpinn _) hlogNnn
            · exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hPpos.le _)) hLnn
        _ = (4*C₁^2*((ℓ-1:ℕ):ℝ) * (P^2 * P^(ℓ-1)) * ee^2 * L^2) * pi0 P^(ℓ-1) := by ring
        _ = (4*C₁^2*((ℓ-1:ℕ):ℝ) * P^(ℓ+1) * ee^2 * L^2) * pi0 P^(ℓ-1) := by rw [hpP]
    have hstep2 : (4*C₁^2*((ℓ-1:ℕ):ℝ) * P^(ℓ+1) * ee^2 * L^2) * pi0 P^(ℓ-1)
        ≤ C * pi0 P^(2*ℓ) := by
      have hfac : (0:ℝ) ≤ P^(ℓ+1) * pi0 P^(ℓ-1) :=
        mul_nonneg (pow_nonneg hPpos.le _) (pow_nonneg hpinn _)
      have hA : (4*C₁^2*((ℓ-1:ℕ):ℝ) * P^(ℓ+1) * ee^2 * L^2) * pi0 P^(ℓ-1)
          ≤ (C / L^(ℓ+1)) * (P^(ℓ+1) * pi0 P^(ℓ-1)) := by
        rw [show (4*C₁^2*((ℓ-1:ℕ):ℝ) * P^(ℓ+1) * ee^2 * L^2) * pi0 P^(ℓ-1)
              = (4*C₁^2*((ℓ-1:ℕ):ℝ) * ee^2 * L^2) * (P^(ℓ+1) * pi0 P^(ℓ-1)) from by ring]
        exact mul_le_mul_of_nonneg_right hcore2 hfac
      have hB : (C / L^(ℓ+1)) * (P^(ℓ+1) * pi0 P^(ℓ-1)) = C * pi0 P^(2*ℓ) := by
        rw [← hpπ, hpidiv]; ring
      linarith [hA, hB.le]
    linarith [hstep, hstep2]
  have hpart3 : E * Perr^(2*ℓ) * Real.log N * L ≤ C * pi0 P^(2*ℓ) := by
    have hEL : E * L = Real.exp (c₁ * L^(1/12:ℝ)) / C₁ := by
      rw [hE]
      rw [show Real.exp (c₁ * L^(1/12:ℝ)) / (C₁*L) * L
            = (L * Real.exp (c₁ * L^(1/12:ℝ))) / (L * C₁) from by ring]
      rw [mul_div_mul_left _ _ (ne_of_gt hLpos)]
    have hPerrpow : Perr^(2*ℓ) ≤ (2*C₁)^(2*ℓ) * P^(2*ℓ) * ee^(2*ℓ) := by
      have h := pow_le_pow_left₀ hPerrnn hPerr_le (2*ℓ)
      have hexp : (2*C₁*P*ee)^(2*ℓ) = (2*C₁)^(2*ℓ) * P^(2*ℓ) * ee^(2*ℓ) := by
        rw [mul_pow, mul_pow]
      rwa [hexp] at h
    have hexpcomb : Real.exp (c₁ * L^(1/12:ℝ)) * ee^(2*ℓ) = ee^(2*ℓ-1) := by
      have hpow : ee^(2*ℓ) = ee^(2*ℓ-1) * ee := by
        have h := pow_succ ee (2*ℓ-1)
        rw [show (2*ℓ-1)+1 = 2*ℓ from Nat.sub_add_cancel (by omega : 1 ≤ 2*ℓ)] at h
        exact h
      have heeinv : Real.exp (c₁ * L^(1/12:ℝ)) * ee = 1 := by
        rw [hee, ← Real.exp_add]
        have hz : c₁ * L^(1/12:ℝ) + -c₁ * L^(1/12:ℝ) = 0 := by ring
        rw [hz, Real.exp_zero]
      rw [hpow]
      rw [show Real.exp (c₁ * L^(1/12:ℝ)) * (ee^(2*ℓ-1) * ee)
            = ee^(2*ℓ-1) * (Real.exp (c₁ * L^(1/12:ℝ)) * ee) from by ring]
      rw [heeinv, mul_one]
    have hcore3 : (2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁ * ee^(2*ℓ-1) * L ≤ C / L^(2*ℓ) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < L^(2*ℓ))]
      have hre : (2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁ * ee^(2*ℓ-1) * L * L^(2*ℓ)
          = ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁) * (L^(2*ℓ+1) * ee^(2*ℓ-1)) := by
        rw [show (2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁ * ee^(2*ℓ-1) * L * L^(2*ℓ)
              = ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁) * (ee^(2*ℓ-1) * (L * L^(2*ℓ))) from by ring, hpL5]
        ring
      rw [hre]
      calc ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁) * (L^(2*ℓ+1) * ee^(2*ℓ-1))
          ≤ ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁) * 1 := mul_le_mul_of_nonneg_left hdecB hK2nn
        _ = (2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁ := mul_one _
        _ ≤ C := hCK2
    calc E * Perr^(2*ℓ) * Real.log N * L
        = (E*L) * (Perr^(2*ℓ) * Real.log N) := by ring
      _ = (Real.exp (c₁*L^(1/12:ℝ))/C₁) * (Perr^(2*ℓ) * Real.log N) := by rw [hEL]
      _ ≤ (Real.exp (c₁*L^(1/12:ℝ))/C₁) *
            ((2*C₁)^(2*ℓ)*P^(2*ℓ)*ee^(2*ℓ) * (((ℓ-1:ℕ):ℝ)*L)) := by
          apply mul_le_mul
          · exact le_refl _
          · exact mul_le_mul hPerrpow hlogN_le (by positivity) (by positivity)
          · positivity
          · positivity
      _ = ((Real.exp (c₁*L^(1/12:ℝ)) * ee^(2*ℓ))/C₁) *
            ((2*C₁)^(2*ℓ) * ((ℓ-1:ℕ):ℝ) * P^(2*ℓ) * L) := by ring
      _ = (ee^(2*ℓ-1)/C₁) * ((2*C₁)^(2*ℓ) * ((ℓ-1:ℕ):ℝ) * P^(2*ℓ) * L) := by rw [hexpcomb]
      _ = ((2*C₁)^(2*ℓ)*((ℓ-1:ℕ):ℝ)/C₁ * ee^(2*ℓ-1) * L) * P^(2*ℓ) := by ring
      _ ≤ (C / L^(2*ℓ)) * P^(2*ℓ) := mul_le_mul_of_nonneg_right hcore3 (by positivity)
      _ = C * pi0 P^(2*ℓ) := by rw [hpi, div_pow]; ring
  exact ⟨hpart1, hpart2, hpart3⟩

end Work.BMF
