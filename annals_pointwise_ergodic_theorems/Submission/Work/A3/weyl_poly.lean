import Mathlib
import Submission.Work.A3.Weil.iter_differencing
import Submission.Work.A3.Weil.iterDiff_weylPhase_affine
import Submission.Work.A3.Weil.norm_iterCorr_phase_le
import Submission.Work.A3.Weil.oneD_arith
import Submission.Work.A3.Weil.arithSum_le
import Submission.Work.A3.Weil.dirichletApprox
import Submission.Work.A3.Weil.exists_approx_leading
import Submission.Work.A3.Weil.pow_le_of_rpow_le
import Submission.Work.A3.Weil.comparable_densities
import Submission.Work.A3.Weil.pow_mul_zpow_eq
import Submission.Work.A3.card_primeFactors_rpow_le

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-- The constant `4 + 2 D^4`, used to absorb the arithmetic error terms. -/
private def Cfive (D : ℕ) : ℝ := 4 + 2 * (D : ℝ) ^ 4

theorem weyl_poly (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a q →
      |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
      ‖Work.A3.expSum Q N θ‖ ≤ C * (N : ℝ) ^ (1 + ε) *
        (((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-((Polynomial.natDegree Q : ℤ)))) ^
          ((1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1))) := by
  classical
  set d : ℕ := Q.natDegree with hddef
  have hd2 : 2 ≤ d := by rw [hddef]; exact hd
  set k : ℕ := d - 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkd : k + 1 = d := by omega
  have hkd' : k + 1 = Q.natDegree := by rw [hkd, hddef]
  set D : ℕ := Weil.weylConst Q with hDdef
  obtain ⟨c1, hc1pos, hc1⟩ := Weil.iter_differencing k
  obtain ⟨C1, hC1pos, hC1⟩ := Weil.arithSum_le (ε := ε / 2) (by linarith) k
  obtain ⟨C2, hC2pos, hC2⟩ := Weil.oneD_arith (ε := ε / 2) (by linarith)
  have hC5pos : 0 < Cfive D := by rw [Cfive]; positivity
  refine ⟨c1 * C1 * (1 + C2 * Cfive D) + 1, by positivity, ?_⟩
  intro N a q θ hN hq hcop hθ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℤ) < q := by omega
    exact_mod_cast this
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hNkpos : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  -- ## the phase sequence
  have hS : Work.A3.expSum Q N θ
      = ∑ n ∈ Weil.wRange N, Weil.phaseSeq (Weil.weylPhase Q θ) N n :=
    Weil.expSum_eq_sum_phaseSeq Q N θ
  have hsupp : ∀ n : ℤ, n ∉ Weil.wRange N → Weil.phaseSeq (Weil.weylPhase Q θ) N n = 0 := by
    intro n hn
    simp only [Weil.phaseSeq]
    rw [if_neg hn]
  have hdiff := hc1 N hN (Weil.phaseSeq (Weil.weylPhase Q θ) N) hsupp
  -- ## per-tuple bounds
  have htuple : ∀ l ∈ Fintype.piFinset (fun _ : Fin k => Weil.shiftIdx N),
      ‖∑ n ∈ Weil.wRange N, Weil.iterCorr k l (Weil.phaseSeq (Weil.weylPhase Q θ) N) n‖
        ≤ Weil.geomBound N (Weil.weylSlope Q θ k l) := by
    intro l _
    exact Weil.norm_iterCorr_phase_le k l (Weil.weylPhase Q θ) N (Weil.weylSlope Q θ k l)
      (Weil.iterDiff_weylPhase_affine Q θ k hkd' l)
  set Lam : ℝ := -θ * ((Nat.factorial Q.natDegree : ℝ) * ((Q.coeff Q.natDegree : ℤ) : ℝ)) with hLamdef
  have hsum_eq : (∑ l ∈ Fintype.piFinset (fun _ : Fin k => Weil.shiftIdx N),
        Weil.geomBound N (Weil.weylSlope Q θ k l)) = Weil.arithSum N k Lam := by
    unfold Weil.arithSum
    apply Finset.sum_congr rfl
    intro l _
    apply congrArg (Weil.geomBound N)
    simp only [Weil.weylSlope, hLamdef]
  have hsum_le : (∑ l ∈ Fintype.piFinset (fun _ : Fin k => Weil.shiftIdx N),
        ‖∑ n ∈ Weil.wRange N, Weil.iterCorr k l (Weil.phaseSeq (Weil.weylPhase Q θ) N) n‖)
      ≤ Weil.arithSum N k Lam :=
    le_trans (Finset.sum_le_sum htuple) (le_of_eq hsum_eq)
  -- ## the arithmetic inputs
  obtain ⟨a', q', hq'1, hcop', hq'leq, hqleq, happ⟩ :=
    Weil.exists_approx_leading Q θ a q hq hcop hd hθ
  have hq'pos : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq'1)
  set Q₀ : ℕ := 2 * max (N ^ k) q' with hQ₀def
  have hQ₀1 : 1 ≤ Q₀ := by
    rw [hQ₀def]
    have : 1 ≤ max (N ^ k) q' := le_max_of_le_right hq'1
    omega
  have hQ₀pos : (0 : ℝ) < (Q₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ₀1)
  obtain ⟨aD, qD, hqD1, hqDle, hcopD, happD⟩ := Weil.dirichletApprox Lam Q₀ hQ₀1
  have hqDpos : (0 : ℝ) < (qD : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqD1)
  have hQ₀big : 2 * (N ^ k) ≤ Q₀ := by
    rw [hQ₀def]; exact Nat.mul_le_mul_left 2 (le_max_left _ _)
  have hQ₀big' : 2 * q' ≤ Q₀ := by
    rw [hQ₀def]; exact Nat.mul_le_mul_left 2 (le_max_right _ _)
  have hMle : (N : ℤ) ^ k ≤ ((N ^ k : ℕ) : ℤ) := by rw [Nat.cast_pow]
  have hM1 : 1 ≤ N ^ k := one_le_pow₀ hN
  have harith := hC1 N (N ^ k) Lam hN hMle
  have honeD := hC2 N (N ^ k) Q₀ Lam aD (qD : ℤ) hN hM1 hQ₀1 hQ₀big
    (by exact_mod_cast hqD1) (by exact_mod_cast hqDle) hcopD happD
  -- ## comparability
  have hD1 : 1 ≤ D := by
    have h1 : (1 : ℤ) ≤ (D : ℤ) * (q' : ℤ) := le_trans hq hqleq
    have h2 : (0 : ℤ) < (q' : ℤ) := by exact_mod_cast hq'1
    nlinarith
  have hcmp : (q' : ℝ) / (2 * (D : ℝ) ^ 3) ≤ (qD : ℝ) :=
    Weil.comparable_densities hq'1 hcop' hqD1 hcopD hD1 hQ₀big' happ happD
  have hqDbound : (qD : ℝ) ≤ 2 * ((N : ℝ) ^ k + (q : ℝ)) := by
    have h1 : (qD : ℝ) ≤ (Q₀ : ℝ) := by exact_mod_cast hqDle
    have h2 : (Q₀ : ℝ) ≤ 2 * max ((N : ℝ) ^ k) (q' : ℝ) := by
      rw [hQ₀def]; push_cast
      exact le_of_eq (by ring)
    have h3 : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'leq
    have h4 : max ((N : ℝ) ^ k) (q' : ℝ) ≤ (N : ℝ) ^ k + (q : ℝ) := by
      apply max_le
      · linarith [hNkpos, hqpos]
      · linarith [h3, hNkpos]
    linarith
  have hqprim : (1 : ℝ) / (q' : ℝ) ≤ (D : ℝ) / (q : ℝ) := by
    have hDq : (q : ℝ) ≤ (D : ℝ) * (q' : ℝ) := by exact_mod_cast hqleq
    rw [div_le_div_iff₀ hq'pos hqpos]
    linarith
  have hMN : (N : ℝ) ^ k * (N : ℝ) / (qD : ℝ)
      ≤ 2 * (D : ℝ) ^ 4 * ((N : ℝ) ^ (k + 1) / (q : ℝ)) := by
    have h4 : (q' : ℝ) ≤ (2 * (D : ℝ) ^ 3) * (qD : ℝ) := by
      have h5 := hcmp
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (D : ℝ) ^ 3)] at h5
      linarith
    have hinv : (1 : ℝ) / (qD : ℝ) ≤ (2 * (D : ℝ) ^ 3) / (q' : ℝ) := by
      rw [div_le_div_iff₀ hqDpos hq'pos]
      linarith
    have hstep1 : (N : ℝ) ^ k * (N : ℝ) * (1 / (qD : ℝ))
        ≤ (N : ℝ) ^ k * (N : ℝ) * ((2 * (D : ℝ) ^ 3) / (q' : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have hstep2 : (N : ℝ) ^ k * (N : ℝ) * ((2 * (D : ℝ) ^ 3) / (q' : ℝ))
        ≤ (N : ℝ) ^ k * (N : ℝ) * ((2 * (D : ℝ) ^ 3) * ((D : ℝ) / (q : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hqprim (by positivity)
    have hstep3 : (N : ℝ) ^ k * (N : ℝ) * ((2 * (D : ℝ) ^ 3) * ((D : ℝ) / (q : ℝ)))
        = 2 * (D : ℝ) ^ 4 * ((N : ℝ) ^ (k + 1) / (q : ℝ)) := by
      rw [pow_succ]; field_simp; ring
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    linarith [hstep1, hstep2, hstep3]
  -- ## the 1-D estimate in the required form
  have hXnonneg : (0 : ℝ) ≤ (N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ) := by positivity
  have hXge : (N : ℝ) ^ k ≤ (N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ) := by
    linarith [hqpos, hXnonneg, (by positivity : (0:ℝ) ≤ (N:ℝ)^(k+1)/(q:ℝ))]
  have hX : (0 : ℝ) ≤ (N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ) := by positivity
  have hXge : (N : ℝ) ^ k ≤ (N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ) := by
    have h2 : (0 : ℝ) ≤ (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ) := by positivity
    linarith
  have hD4 : (0 : ℝ) ≤ (D : ℝ) ^ 4 := by positivity
  have hdivnn : (0 : ℝ) ≤ (N : ℝ) ^ (k + 1) / (q : ℝ) := by positivity
  have hsum1D : (∑ P ∈ Finset.Icc (-((N ^ k : ℕ) : ℤ)) ((N ^ k : ℕ) : ℤ),
        if P = 0 then 0 else Weil.geomBound N (Lam * (P : ℝ)))
      ≤ C2 * (N : ℝ) ^ (ε / 2)
        * (Cfive D * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))) := by
    refine le_trans honeD ?_
    have hC2nn : 0 ≤ C2 * (N : ℝ) ^ (ε / 2) := by positivity
    apply mul_le_mul_of_nonneg_left _ hC2nn
    push_cast
    have hqDbound' : (qD : ℝ) ≤ 2 * (N : ℝ) ^ k + 2 * (q : ℝ) := by linarith [hqDbound]
    have hkey : (N : ℝ) ^ k + (qD : ℝ) + (N : ℝ) ^ k * (N : ℝ) / (qD : ℝ)
        ≤ 4 * (N : ℝ) ^ k + 2 * (q : ℝ)
          + 2 * (D : ℝ) ^ 4 * ((N : ℝ) ^ (k + 1) / (q : ℝ)) := by
      have h2 : (N : ℝ) ^ k + (qD : ℝ) + (N : ℝ) ^ k * (N : ℝ) / (qD : ℝ)
          ≤ (N : ℝ) ^ k + (2 * (N : ℝ) ^ k + 2 * (q : ℝ))
            + 2 * (D : ℝ) ^ 4 * ((N : ℝ) ^ (k + 1) / (q : ℝ)) :=
        add_le_add (add_le_add le_rfl hqDbound') hMN
      linarith [h2, hNkpos]
    have hfin : 4 * (N : ℝ) ^ k + 2 * (q : ℝ)
          + 2 * (D : ℝ) ^ 4 * ((N : ℝ) ^ (k + 1) / (q : ℝ))
        ≤ Cfive D * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ)) := by
      rw [Cfive]
      nlinarith [hNkpos, hqpos, hD4, hdivnn]
    linarith [hkey, hfin]
  have hNpow1 : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 (by linarith)
  have hNpow2 : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by positivity
  have hC2C5nn : (0 : ℝ) ≤ C2 * Cfive D := by positivity
  have hNk_le : (N : ℝ) ^ k
      ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ)) := by
    have h := mul_le_mul hNpow1 hXge hNkpos.le hNpow2
    simpa using h
  have hinner : (N : ℝ) ^ k + (∑ P ∈ Finset.Icc (-((N ^ k : ℕ) : ℤ)) ((N ^ k : ℕ) : ℤ),
        if P = 0 then 0 else Weil.geomBound N (Lam * (P : ℝ)))
      ≤ (1 + C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
          * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))) := by
    have h1 : C2 * (N : ℝ) ^ (ε / 2)
          * (Cfive D * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ)))
        = (C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
            * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))) := by ring
    have h2 := le_trans hsum1D (le_of_eq h1)
    calc (N : ℝ) ^ k + (∑ P ∈ Finset.Icc (-((N ^ k : ℕ) : ℤ)) ((N ^ k : ℕ) : ℤ),
            (if P = 0 then 0 else Weil.geomBound N (Lam * (P : ℝ))))
        ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))
          + (C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
            * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))) :=
          add_le_add hNk_le h2
      _ = (1 + C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
            * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))) := by ring
  have harith_le : Weil.arithSum N k Lam
      ≤ C1 * (1 + C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
          * ((N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ)))) := by
    refine le_trans harith ?_
    calc C1 * (N : ℝ) ^ (ε / 2)
          * ((N : ℝ) ^ k + ∑ P ∈ Finset.Icc (-((N ^ k : ℕ) : ℤ)) ((N ^ k : ℕ) : ℤ),
              (if P = 0 then 0 else Weil.geomBound N (Lam * (P : ℝ))))
        ≤ C1 * (N : ℝ) ^ (ε / 2) * ((1 + C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
            * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ)))) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = C1 * (1 + C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
            * ((N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ)))) := by
          ring
  have hqnat : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
    have h : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ q)
    exact_mod_cast h
  have hqnat1 : 1 ≤ q.toNat := by
    rw [Int.le_toNat (by omega : (0 : ℤ) ≤ q)]; exact hq
  have hB := Weil.pow_mul_zpow_eq hkd hk1 (N := N) (q := q.toNat) hN hqnat1
  rw [hqnat] at hB
  have h2k : k + 1 ≤ 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    omega
  have hXident : (N : ℝ) ^ (2 ^ k - 1 - k)
        * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))
      = (N : ℝ) ^ (2 ^ k) * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ))) := by
    have e1 : (2 ^ k - 1 - k) + k = 2 ^ k - 1 := by omega
    have e2 : (2 ^ k - 1 - k) + (k + 1) = 2 ^ k := by omega
    rw [mul_add, mul_add, ← mul_div_assoc, ← pow_add, ← pow_add, e1, e2, hB]
  have hpow : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hmain : ‖Work.A3.expSum Q N θ‖ ^ (2 ^ k)
      ≤ c1 * C1 * (1 + C2 * Cfive D) * ((N : ℝ) ^ (2 ^ k) * ((N : ℝ) ^ ε
          * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ))))) := by
    calc ‖Work.A3.expSum Q N θ‖ ^ (2 ^ k)
        = ‖∑ n ∈ Weil.wRange N, Weil.phaseSeq (Weil.weylPhase Q θ) N n‖ ^ (2 ^ k) := by rw [hS]
      _ ≤ c1 * (N : ℝ) ^ (2 ^ k - 1 - k)
            * (∑ l ∈ Fintype.piFinset (fun _ : Fin k => Weil.shiftIdx N),
                ‖∑ n ∈ Weil.wRange N, Weil.iterCorr k l (Weil.phaseSeq (Weil.weylPhase Q θ) N) n‖) := hdiff
      _ ≤ c1 * (N : ℝ) ^ (2 ^ k - 1 - k) * (Weil.arithSum N k Lam) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ ≤ c1 * (N : ℝ) ^ (2 ^ k - 1 - k)
            * (C1 * (1 + C2 * Cfive D) * ((N : ℝ) ^ (ε / 2)
              * ((N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))))) :=
            mul_le_mul_of_nonneg_left harith_le (by positivity)
      _ = c1 * C1 * (1 + C2 * Cfive D) * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2))
            * ((N : ℝ) ^ (2 ^ k - 1 - k)
              * ((N : ℝ) ^ k + (q : ℝ) + (N : ℝ) ^ (k + 1) / (q : ℝ))) := by ring
      _ = c1 * C1 * (1 + C2 * Cfive D) * ((N : ℝ) ^ (2 ^ k) * ((N : ℝ) ^ ε
            * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ))))) := by
            rw [hpow, hXident]; ring
  have hB0 : 0 < (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ)) := by
    have h1 : 0 < (q : ℝ)⁻¹ := by positivity
    have h3 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ (q : ℝ) * (N : ℝ) ^ (-(d : ℤ)) := by positivity
    linarith
  have hcast : (N : ℝ) ^ ((2 ^ k : ℕ) : ℝ) = (N : ℝ) ^ (2 ^ k) := Real.rpow_natCast N (2 ^ k)
  have hC1le : (1 : ℝ) ≤ c1 * C1 * (1 + C2 * Cfive D) + 1 := by
    have h0 : (0 : ℝ) ≤ c1 * C1 * (1 + C2 * Cfive D) := by positivity
    linarith
  have hconv := Weil.pow_le_of_rpow_le (k := k) hk1 hε (S := ‖Work.A3.expSum Q N θ‖)
    (C := c1 * C1 * (1 + C2 * Cfive D) + 1) (N := (N : ℝ))
    (B := (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ)))
    (norm_nonneg _) hC1le hN1 hB0
    (by
      rw [hcast]
      refine le_trans hmain ?_
      have h₁ : c1 * C1 * (1 + C2 * Cfive D) ≤ c1 * C1 * (1 + C2 * Cfive D) + 1 :=
        le_add_of_nonneg_right zero_le_one
      calc c1 * C1 * (1 + C2 * Cfive D)
            * ((N : ℝ) ^ (2 ^ k) * ((N : ℝ) ^ ε
              * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ)))))
          ≤ (c1 * C1 * (1 + C2 * Cfive D) + 1)
            * ((N : ℝ) ^ (2 ^ k) * ((N : ℝ) ^ ε
              * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ))))) :=
            mul_le_mul_of_nonneg_right h₁ (by positivity)
        _ = (c1 * C1 * (1 + C2 * Cfive D) + 1) * (N : ℝ) ^ (2 ^ k) * (N : ℝ) ^ ε
              * ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-(d : ℤ))) := by ring)
  refine le_trans hconv ?_
  have hdcast2 : ((d : ℤ)) = ((Polynomial.natDegree Q : ℤ)) := by rw [hddef]
  have hdcast : (k : ℕ) = Polynomial.natDegree Q - 1 := by rw [← hddef, ← hkdef]
  rw [hdcast2, hdcast]

end

end Work.A3
