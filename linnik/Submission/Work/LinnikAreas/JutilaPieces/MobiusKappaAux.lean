import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.MobiusKappaDefs
import Submission.Work.LinnikAreas.Density4.KappaSum.log_pow_le_const_mul_sqrt
import Submission.Work.LinnikAreas.Density4.KappaSum.kappaLogSum_expansion
import Submission.Work.LinnikAreas.Density4.KappaSum.div_totient_le_two_mul_sHalf
import Submission.Work.LinnikAreas.Density4.ThetaPow.selTheta_asymptotic_pow
import Submission.Commons.NumberTheory.Divisors.card_divisors_le_two_mul_sqrt

/-!
# The `1/κ`-weighted Möbius sum: Selberg-diagonalisation inputs

Supporting material for `Work.LinnikAreas.JutilaPieces.MobiusKappaSum`:

* `sHalf_mul_of_coprime` : `σ_{-1/2}` is multiplicative on coprime arguments;
* `kappaAbsorb` : the logarithmic absorption for the Selberg weights `μ(d)²/(d κ(d)) σ_{-1/2}(d)`;
* `kappaLogSum_err` : the smoothed sum `Sigma μ(n)/κ(n) log(z/n)` differs from its "main term"
  `Σ_d μ(d)²/(dκ(d))·(dr)/φ(dr)` by `O(σ_{-1/2}(r) (log 2z)^{-B})`, via `selTheta_asymptotic_pow`;
* `kappaLogSum_diff` : consequently the map `z ↦ kappaLogSum z r` is Cauchy with decay
  `O(σ_{-1/2}(r)(log(2+min z z'))^{-B})`;
* `kappaSum_c_trick` and `kappaSum_window_bound` : the comparison of `kappaLogSum` at the two
  scales `z` and `z·c`, which recovers the unweighted sum `kappaSum ⌊z⌋ r`.
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas.JutilaPieces

noncomputable section

/-- The weight `n ↦ 1/√n` as an arithmetic function. -/
def invSqrtAF : ArithmeticFunction ℝ :=
  ⟨fun n => (1:ℝ) / Real.sqrt ((n:ℕ):ℝ), by simp⟩

lemma invSqrtAF_apply (n : ℕ) : invSqrtAF n = (1:ℝ) / Real.sqrt ((n:ℕ):ℝ) := rfl

lemma invSqrtAF_isMult : invSqrtAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [invSqrtAF], ?_⟩
  intro a b ha hb hab
  rw [invSqrtAF_apply, invSqrtAF_apply, invSqrtAF_apply, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg a) (b:ℝ)]
  field_simp

lemma sHalf_eq_sum_invSqrt (r : ℕ) :
    Work.LinnikAreas.Density4.sHalf r = ∑ d ∈ r.divisors, invSqrtAF d := by
  rw [Work.LinnikAreas.Density4.sHalf]
  rfl

lemma sHalf_mul_of_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    Work.LinnikAreas.Density4.sHalf (m * n)
      = Work.LinnikAreas.Density4.sHalf m * Work.LinnikAreas.Density4.sHalf n := by
  have hfz : (invSqrtAF * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)).IsMultiplicative :=
    invSqrtAF_isMult.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hkey := hfz.map_mul_of_coprime h
  rw [sHalf_eq_sum_invSqrt, sHalf_eq_sum_invSqrt, sHalf_eq_sum_invSqrt,
    ← ArithmeticFunction.coe_mul_zeta_apply (f := invSqrtAF) (x := m * n),
    ← ArithmeticFunction.coe_mul_zeta_apply (f := invSqrtAF) (x := m),
    ← ArithmeticFunction.coe_mul_zeta_apply (f := invSqrtAF) (x := n), hkey]


lemma sqrt_inv_step (n : ℕ) (hn : 2 ≤ n) :
    (1:ℝ)/((n:ℝ) * Real.sqrt (n:ℝ))
      ≤ 2 * ((1:ℝ)/Real.sqrt (((n-1:ℕ):ℝ)) - (1:ℝ)/Real.sqrt (n:ℝ)) := by
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn1R : ((n-1:ℕ):ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hn1pos : (0:ℝ) < ((n-1:ℕ):ℝ) := by rw [hn1R]; linarith only [hnR]
  set a : ℝ := Real.sqrt (((n-1:ℕ):ℝ)) with ha
  set b : ℝ := Real.sqrt (n:ℝ) with hb
  have hapos : 0 < a := Real.sqrt_pos.mpr hn1pos
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith only [hnR])
  have ha2 : a^2 = ((n-1:ℕ):ℝ) := Real.sq_sqrt hn1pos.le
  have hb2 : b^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
  have hsum : 0 < a + b := by linarith only [hapos, hbpos]
  have hab : a*b ≤ (n:ℝ) + 1 := by
    have hsq : (a*b)^2 ≤ ((n:ℝ)+1)^2 := by
      rw [mul_pow, ha2, hb2, hn1R]
      linarith only [hnR]
    nlinarith only [hsq, mul_nonneg hapos.le hbpos.le, hnR, hapos, hbpos, hn1R, hb2, ha2]
  have hkey : a*(a+b) ≤ 2*b^2 := by
    linarith only [ha2, hb2, hn1R, hab]
  have hba : b - a = 1/(a+b) := by
    rw [eq_div_iff (ne_of_gt hsum)]
    linarith only [ha2, hb2, hn1R]
  have hL : (1:ℝ)/((n:ℝ) * b) = 1/b^3 := by rw [← hb2]; field_simp
  rw [hL]
  have h1 : (1:ℝ)/a - (1:ℝ)/b = (b-a)/(a*b) := by field_simp
  rw [h1, hba]
  rw [show (2:ℝ) * (1/(a+b)/(a*b)) = 2/((a+b)*(a*b)) by field_simp]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < b^3)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (a+b)*(a*b))]
  nlinarith only [hkey, hn1R, hbpos, ha2, hb2, hab]

lemma telescope_inv_sqrt (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc (N+1) M,
        ((1:ℝ)/Real.sqrt (((n-1:ℕ):ℝ)) - (1:ℝ)/Real.sqrt (n:ℝ)))
      = (1:ℝ)/Real.sqrt (N:ℝ) - (1:ℝ)/Real.sqrt (M:ℝ) := by
  induction M, hNM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega : ¬ N + 1 ≤ N), Finset.sum_empty]
      ring
  | succ M hNM ih =>
      rw [Finset.sum_Icc_succ_top (by omega : N + 1 ≤ M + 1), ih]
      have hcast : ((M + 1 - 1 : ℕ) : ℝ) = (M:ℝ) := by
        rw [Nat.add_sub_cancel]
      rw [hcast]
      ring

lemma sum_inv_sqrt_mul_tail (N M : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc (N+1) M, (1:ℝ)/((n:ℝ) * Real.sqrt (n:ℝ)))
      ≤ 2 / Real.sqrt (N:ℝ) := by
  by_cases hMN : M ≤ N
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hNM : N ≤ M := by omega
    calc (∑ n ∈ Finset.Icc (N+1) M, (1:ℝ)/((n:ℝ) * Real.sqrt (n:ℝ)))
        ≤ ∑ n ∈ Finset.Icc (N+1) M,
            2 * ((1:ℝ)/Real.sqrt (((n-1:ℕ):ℝ)) - (1:ℝ)/Real.sqrt (n:ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          exact sqrt_inv_step n (by omega)
      _ = 2 * ((1:ℝ)/Real.sqrt (N:ℝ) - (1:ℝ)/Real.sqrt (M:ℝ)) := by
          rw [← Finset.mul_sum, telescope_inv_sqrt N M hN hNM]
      _ ≤ 2 / Real.sqrt (N:ℝ) := by
          have h1 : 0 ≤ 2 * ((1:ℝ)/Real.sqrt (M:ℝ)) := by positivity
          have h2 : 2 / Real.sqrt (N:ℝ) = 2 * (1/Real.sqrt (N:ℝ)) := by
            rw [div_eq_mul_one_div]
          rw [mul_sub, h2]
          linarith only [h1]

lemma sum_inv_sqrt_mul_le (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, (1:ℝ)/((d:ℝ) * Real.sqrt (d:ℝ))) ≤ 3 := by
  have h1 : (∑ d ∈ Finset.Icc 2 M, (1:ℝ)/((d:ℝ) * Real.sqrt (d:ℝ)))
      ≤ 2 / Real.sqrt (1:ℝ) := by
    simpa using sum_inv_sqrt_mul_tail 1 M le_rfl
  rw [Real.sqrt_one, div_one] at h1
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have hsplit : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have hval : (1:ℝ)/(((1:ℕ):ℝ) * Real.sqrt (((1:ℕ):ℝ))) = 1 := by norm_num
    rw [hval]
    linarith only [h1]

lemma w_sHalf_le (d : ℕ) (hd : 1 ≤ d) :
    mobKappaW d * Work.LinnikAreas.Density4.sHalf d
      ≤ 3 / ((d:ℝ) * Real.sqrt (d:ℝ)) := by
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hsd : (0:ℝ) < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd'
  have hs : Work.LinnikAreas.Density4.sHalf d ≤ 3 * Real.sqrt (d:ℝ) := by
    rw [Work.LinnikAreas.Density4.sHalf]
    have hterm : ∀ e ∈ d.divisors, (1:ℝ)/Real.sqrt (e:ℝ) ≤ 1 := by
      intro e he
      have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
      have hspos : (0:ℝ) < Real.sqrt (e:ℝ) := by
        apply Real.sqrt_pos.mpr; exact_mod_cast (by omega : 0 < e)
      rw [div_le_one hspos]
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast he1)
    have hcard : ((d.divisors.card : ℕ) : ℝ) ≤ 2 * (Nat.sqrt d : ℝ) + 1 := by
      exact_mod_cast Commons.NumberTheory.Divisors.card_divisors_le_two_mul_sqrt d
    have hsqrtle : (Nat.sqrt d : ℝ) ≤ Real.sqrt (d:ℝ) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt d))]
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' d)
    have hspos1 : (1:ℝ) ≤ Real.sqrt (d:ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    calc (∑ e ∈ d.divisors, (1:ℝ)/Real.sqrt (e:ℝ)) ≤ ∑ e ∈ d.divisors, (1:ℝ) :=
          Finset.sum_le_sum hterm
      _ = ((d.divisors.card : ℕ) : ℝ) := by simp
      _ ≤ 2 * (Nat.sqrt d : ℝ) + 1 := hcard
      _ ≤ 3 * Real.sqrt (d:ℝ) := by linarith only [hsqrtle, hspos1]
  have hmk : mobKappaW d ≤ 1/((d:ℝ)^2) := mobKappaW_le_inv_sq hd
  have hsnn : 0 ≤ Work.LinnikAreas.Density4.sHalf d := Work.LinnikAreas.Density4.sHalf_nonneg d
  calc mobKappaW d * Work.LinnikAreas.Density4.sHalf d
      ≤ (1/((d:ℝ)^2)) * (3 * Real.sqrt (d:ℝ)) :=
        mul_le_mul hmk hs hsnn (by positivity)
    _ = 3 / ((d:ℝ) * Real.sqrt (d:ℝ)) := by
        rw [pow_two]
        field_simp
        rw [Real.sq_sqrt hd'.le]

lemma sum_w_sHalf_le (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, mobKappaW d * Work.LinnikAreas.Density4.sHalf d) ≤ 9 := by
  calc (∑ d ∈ Finset.Icc 1 M, mobKappaW d * Work.LinnikAreas.Density4.sHalf d)
      ≤ ∑ d ∈ Finset.Icc 1 M, 3 / ((d:ℝ) * Real.sqrt (d:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_Icc] at hd
        exact w_sHalf_le d hd.1
    _ = 3 * (∑ d ∈ Finset.Icc 1 M, 1 / ((d:ℝ) * Real.sqrt (d:ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [div_eq_mul_one_div]
    _ ≤ 3 * 3 := by
        have := sum_inv_sqrt_mul_le M
        linarith only [this]
    _ = 9 := by norm_num

end


theorem kappaAbsorb (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z : ℝ) (M : ℕ), 1 ≤ z →
      (∑ d ∈ Finset.Icc 1 M, mobKappaW d * Work.LinnikAreas.Density4.sHalf d
          * (Real.log (2 + z / (d : ℝ))) ^ (-B))
        ≤ K * (Real.log (2 + z)) ^ (-B) := by
  obtain ⟨Ks, hKspos, hlogbound⟩ :=
    Work.LinnikAreas.Density4.KappaSum.log_pow_le_const_mul_sqrt (2*B) (by linarith only [hB])
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2nonneg : 0 ≤ Real.log 2 := hlog2pos.le
  have hK2pos : 0 < (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks := by positivity
  refine ⟨9 * 2^B + (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks + 1, by positivity, ?_⟩
  intro z M hz
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hsqrtz1 : 1 ≤ Real.sqrt z := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hz])
  set N : ℕ := ⌊Real.sqrt z⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hsqrtz1)
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNz : (N:ℝ) ≤ Real.sqrt z := Nat.floor_le (Real.sqrt_nonneg z)
  have hNz2 : Real.sqrt z < (N:ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog2zpos : 0 < Real.log (2 + z) := Real.log_pos (by linarith only [hz])
  have hlogszpos : 0 < Real.log (2 + Real.sqrt z) := Real.log_pos (by linarith only [Real.sqrt_nonneg z, hsqrtz1])
  -- ## part 1 : `d ≤ N`
  have hpart1 : (∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ≤ N),
        mobKappaW d * Work.LinnikAreas.Density4.sHalf d
          * (Real.log (2 + z / (d : ℝ))) ^ (-B))
      ≤ 9 * (Real.log (2 + Real.sqrt z)) ^ (-B) := by
    have hw : ∀ d ∈ (Finset.Icc 1 M).filter (fun d => d ≤ N),
        mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + z / (d : ℝ))) ^ (-B)
          ≤ mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + Real.sqrt z)) ^ (-B) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdM⟩, hdle⟩ := hd
      have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hdle' : (d:ℝ) ≤ Real.sqrt z := le_trans (by exact_mod_cast hdle) hNz
      have hzd : Real.sqrt z ≤ z / (d:ℝ) := by
        rw [le_div_iff₀ hdR]
        have hsq : Real.sqrt z * Real.sqrt z = z := by
          rw [← sq, Real.sq_sqrt (le_of_lt hz0)]
        nlinarith only [hdle', Real.sqrt_nonneg z, hsq, hsqrtz1]
      have hlog : Real.log (2 + Real.sqrt z) ≤ Real.log (2 + z/(d:ℝ)) :=
        Real.log_le_log (by linarith only [Real.sqrt_nonneg z, hsqrtz1]) (by linarith only [hzd])
      have hrp := Real.rpow_le_rpow_of_nonpos hlogszpos hlog (by linarith only [hB] : -B ≤ 0)
      exact mul_le_mul_of_nonneg_left hrp
        (mul_nonneg (mobKappaW_nonneg d) (Work.LinnikAreas.Density4.sHalf_nonneg d))
    calc (∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ≤ N),
          mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + z / (d : ℝ))) ^ (-B))
        ≤ ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ≤ N),
          mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + Real.sqrt z)) ^ (-B) := Finset.sum_le_sum hw
      _ = (Real.log (2 + Real.sqrt z)) ^ (-B)
            * ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ≤ N),
                mobKappaW d * Work.LinnikAreas.Density4.sHalf d := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ (Real.log (2 + Real.sqrt z)) ^ (-B) * 9 := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hlogszpos.le _)
            calc (∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ≤ N),
                    mobKappaW d * Work.LinnikAreas.Density4.sHalf d)
                ≤ ∑ d ∈ Finset.Icc 1 M, mobKappaW d * Work.LinnikAreas.Density4.sHalf d :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                    (fun i _ _ => mul_nonneg (mobKappaW_nonneg i)
                      (Work.LinnikAreas.Density4.sHalf_nonneg i))
              _ ≤ 9 := sum_w_sHalf_le M
      _ = 9 * (Real.log (2 + Real.sqrt z)) ^ (-B) := by ring
  -- ## part 2 : `N < d`
  have hpart2 : (∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ≤ N),
        mobKappaW d * Work.LinnikAreas.Density4.sHalf d
          * (Real.log (2 + z / (d : ℝ))) ^ (-B))
      ≤ (Real.log 2) ^ (-B) * (6 / Real.sqrt (N:ℝ)) := by
    have hw : ∀ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ≤ N),
        mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + z / (d : ℝ))) ^ (-B)
          ≤ (Real.log 2) ^ (-B) * (3 / ((d:ℝ) * Real.sqrt (d:ℝ))) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdM⟩, hdN⟩ := hd
      have hzdnn : 0 ≤ z / (d:ℝ) := div_nonneg hz0.le (Nat.cast_nonneg d)
      have hlog : Real.log 2 ≤ Real.log (2 + z/(d:ℝ)) :=
        Real.log_le_log (by norm_num) (by linarith only [hzdnn])
      have hrp := Real.rpow_le_rpow_of_nonpos hlog2pos hlog (by linarith only [hB] : -B ≤ 0)
      have hb := w_sHalf_le d hd1
      have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hbnonneg : 0 ≤ 3 / ((d:ℝ) * Real.sqrt (d:ℝ)) :=
        div_nonneg (by norm_num) (mul_nonneg hdR.le (Real.sqrt_nonneg _))
      calc mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + z / (d : ℝ))) ^ (-B)
          ≤ (3 / ((d:ℝ) * Real.sqrt (d:ℝ))) * (Real.log 2) ^ (-B) :=
            mul_le_mul hb hrp
              (Real.rpow_nonneg (Real.log_nonneg (by linarith only [hzdnn])) _) hbnonneg
        _ = (Real.log 2) ^ (-B) * (3 / ((d:ℝ) * Real.sqrt (d:ℝ))) := by ring
    calc (∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ≤ N),
          mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + z / (d : ℝ))) ^ (-B))
        ≤ ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ≤ N),
            (Real.log 2) ^ (-B) * (3 / ((d:ℝ) * Real.sqrt (d:ℝ))) := Finset.sum_le_sum hw
      _ = (Real.log 2) ^ (-B)
            * ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ≤ N),
                3 / ((d:ℝ) * Real.sqrt (d:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (Real.log 2) ^ (-B) * (6 / Real.sqrt (N:ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hlog2nonneg _)
            calc (∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ≤ N),
                    3 / ((d:ℝ) * Real.sqrt (d:ℝ)))
                ≤ ∑ d ∈ Finset.Icc (N+1) M, 3 / ((d:ℝ) * Real.sqrt (d:ℝ)) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro d hd
                    rw [Finset.mem_filter, Finset.mem_Icc] at hd
                    rw [Finset.mem_Icc]
                    omega
                  · intro i hi _
                    have hi1 : 1 ≤ i := le_trans (by omega : 1 ≤ N + 1) (Finset.mem_Icc.mp hi).1
                    have hiR : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
                    exact div_nonneg (by norm_num) (mul_nonneg hiR.le (Real.sqrt_nonneg _))
              _ = 3 * (∑ d ∈ Finset.Icc (N+1) M, 1 / ((d:ℝ) * Real.sqrt (d:ℝ))) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro d _
                  rw [div_eq_mul_one_div]
              _ ≤ 3 * (2 / Real.sqrt (N:ℝ)) := by
                  have := sum_inv_sqrt_mul_tail N M hN1
                  linarith only [this]
              _ = 6 / Real.sqrt (N:ℝ) := by ring
  -- ## combine
  have hcombined : (∑ d ∈ Finset.Icc 1 M, mobKappaW d * Work.LinnikAreas.Density4.sHalf d
          * (Real.log (2 + z / (d : ℝ))) ^ (-B))
      ≤ 9 * (Real.log (2 + Real.sqrt z)) ^ (-B)
        + (Real.log 2) ^ (-B) * (6 / Real.sqrt (N:ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun d : ℕ => d ≤ N)
      (fun d => mobKappaW d * Work.LinnikAreas.Density4.sHalf d
          * (Real.log (2 + z / (d : ℝ))) ^ (-B))]
    exact add_le_add hpart1 hpart2
  -- ## log conversions
  have hstep1 : 9 * (Real.log (2 + Real.sqrt z)) ^ (-B) ≤ 9 * 2 ^ B * (Real.log (2+z)) ^ (-B) := by
    have hlogle : Real.log (2 + z) ≤ 2 * Real.log (2 + Real.sqrt z) := by
      have h2 : 2 * Real.log (2 + Real.sqrt z) = Real.log ((2 + Real.sqrt z)^2) := by
        rw [Real.log_pow]; norm_num
      rw [h2]
      apply Real.log_le_log (by positivity)
      have hsq : Real.sqrt z ^ 2 = z := Real.sq_sqrt (le_of_lt hz0)
      linarith only [Real.sqrt_nonneg z, hz, hsqrtz1, hsq]
    have hhalf : Real.log (2+z)/2 ≤ Real.log (2 + Real.sqrt z) := by linarith only [hlogle]
    have hp : (Real.log (2 + Real.sqrt z))^(-B) ≤ (Real.log (2+z)/2)^(-B) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith only [hB])
    have heq : (Real.log (2+z)/2)^(-B) = 2 ^ B * (Real.log (2+z)) ^ (-B) := by
      rw [Real.div_rpow hlog2zpos.le (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    rw [heq] at hp
    linarith only [hp]
  have hinvN : 1 / Real.sqrt (N:ℝ) ≤ Real.sqrt 2 / Real.sqrt (Real.sqrt z) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hNpos)
      (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hz0))]
    have hN2 : (N:ℝ) + 1 ≤ 2 * (N:ℝ) := by exact_mod_cast (by omega : N + 1 ≤ 2*N)
    have h1 : Real.sqrt (Real.sqrt z) ≤ Real.sqrt (2 * (N:ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith only [hNz2, hN2]
    have h2 : Real.sqrt (2 * (N:ℝ)) = Real.sqrt 2 * Real.sqrt (N:ℝ) :=
      Real.sqrt_mul (by norm_num) (N:ℝ)
    rw [one_mul, ← h2]
    exact h1
  have hlogB : (Real.log (2+z))^B ≤ Real.sqrt Ks * Real.sqrt (Real.sqrt z) := by
    have h := hlogbound z hz
    rw [show (2:ℝ)*B = B + B by ring, Real.rpow_add hlog2zpos] at h
    have hL : 0 ≤ (Real.log (2+z))^B := Real.rpow_nonneg hlog2zpos.le B
    have h2 : Real.sqrt ((Real.log (2+z))^B * (Real.log (2+z))^B) = (Real.log (2+z))^B :=
      Real.sqrt_mul_self hL
    have hmm := Real.sqrt_le_sqrt h
    rw [h2, Real.sqrt_mul hKspos.le] at hmm
    linarith only [hmm]
  have hsqrt_neg : 1 / Real.sqrt (Real.sqrt z) ≤ Real.sqrt Ks * (Real.log (2+z)) ^ (-B) := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hz0))]
    have hL : 0 < (Real.log (2+z))^B := Real.rpow_pos_of_pos hlog2zpos B
    have hnum : 1 ≤ Real.sqrt Ks * Real.sqrt (Real.sqrt z) / (Real.log (2+z))^B :=
      (one_le_div hL).mpr hlogB
    have heq : (Real.sqrt Ks * Real.sqrt (Real.sqrt z) / (Real.log (2+z))^B)
        = (Real.sqrt Ks * (Real.log (2+z)) ^ (-B)) * Real.sqrt (Real.sqrt z) := by
      rw [Real.rpow_neg hlog2zpos.le]
      ring
    rwa [heq] at hnum
  have hstep2 : (Real.log 2) ^ (-B) * (6 / Real.sqrt (N:ℝ))
      ≤ (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks * (Real.log (2+z)) ^ (-B) := by
    have h1 : (Real.log 2) ^ (-B) * (6 / Real.sqrt (N:ℝ))
        ≤ (Real.log 2) ^ (-B) * (6 * (Real.sqrt 2 / Real.sqrt (Real.sqrt z))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hlog2nonneg _)
      have h6 : (6:ℝ) / Real.sqrt (N:ℝ) = 6 * (1/Real.sqrt (N:ℝ)) := by ring
      rw [h6]
      exact mul_le_mul_of_nonneg_left hinvN (by norm_num)
    have h2 : (Real.log 2) ^ (-B) * (6 * (Real.sqrt 2 / Real.sqrt (Real.sqrt z)))
        ≤ (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks * (Real.log (2+z)) ^ (-B) := by
      have hnn : 0 ≤ (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 := by positivity
      calc (Real.log 2) ^ (-B) * (6 * (Real.sqrt 2 / Real.sqrt (Real.sqrt z)))
          = ((Real.log 2) ^ (-B) * 6 * Real.sqrt 2)
              * (1 / Real.sqrt (Real.sqrt z)) := by ring
        _ ≤ ((Real.log 2) ^ (-B) * 6 * Real.sqrt 2)
              * (Real.sqrt Ks * (Real.log (2+z)) ^ (-B)) :=
              mul_le_mul_of_nonneg_left hsqrt_neg hnn
        _ = (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks * (Real.log (2+z)) ^ (-B) := by
              ring
    linarith only [h1, h2]
  refine le_trans hcombined ?_
  have : 9 * (Real.log (2 + Real.sqrt z)) ^ (-B)
        + (Real.log 2) ^ (-B) * (6 / Real.sqrt (N:ℝ))
      ≤ 9 * 2 ^ B * (Real.log (2+z)) ^ (-B)
        + (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks * (Real.log (2+z)) ^ (-B) :=
    add_le_add hstep1 hstep2
  refine le_trans this ?_
  have hfinal : 9 * 2 ^ B * (Real.log (2+z)) ^ (-B)
        + (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks * (Real.log (2+z)) ^ (-B)
      = (9 * 2 ^ B + (Real.log 2) ^ (-B) * 6 * Real.sqrt 2 * Real.sqrt Ks)
        * (Real.log (2+z)) ^ (-B) := by ring
  rw [hfinal]
  have hL : 0 ≤ (Real.log (2+z)) ^ (-B) := Real.rpow_nonneg hlog2zpos.le _
  linarith only [hL]



theorem kappaLogSum_err (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z : ℝ) (r M : ℕ), 1 ≤ z → 1 ≤ r → ⌊z⌋₊ ≤ M →
      |Work.LinnikAreas.Density4.kappaLogSum z r -
        ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
          mobKappaW d * (((d * r : ℕ) : ℝ) / (Nat.totient (d * r) : ℝ))|
        ≤ K * Work.LinnikAreas.Density4.sHalf r * (Real.log (2+z))^(-B) := by
  obtain ⟨C, hCpos, hΘ⟩ := Work.LinnikAreas.Density4.ThetaPow.selTheta_asymptotic_pow B hB
  obtain ⟨Ka, hKapos, hAbs⟩ := kappaAbsorb B hB
  have h3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set KΘ : ℝ := max C (2 * (Real.log 3)^B) with hKΘdef
  have hKΘpos : 0 < KΘ := lt_of_lt_of_le hCpos (le_max_left _ _)
  have hCΘ : C ≤ KΘ := le_max_left _ _
  have h2Θ : 2 * (Real.log 3)^B ≤ KΘ := le_max_right _ _
  refine ⟨KΘ * Ka, by positivity, ?_⟩
  intro z r M hz hr hM
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hz0 : (0:ℝ) ≤ z := hzpos.le
  have hr1 : 1 ≤ r := hr
  have hterm : ∀ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
      |mobKappaW d * Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d * r)
        - mobKappaW d * (((d*r:ℕ):ℝ) / (Nat.totient (d*r):ℝ))|
      ≤ KΘ * Work.LinnikAreas.Density4.sHalf r *
          (mobKappaW d * Work.LinnikAreas.Density4.sHalf d
            * (Real.log (2 + z/(d:ℝ)))^(-B)) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdM⟩, hdcop⟩ := hd
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hdr1 : 1 ≤ d * r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsh : Work.LinnikAreas.Density4.sHalf (d * r)
        = Work.LinnikAreas.Density4.sHalf d * Work.LinnikAreas.Density4.sHalf r :=
      sHalf_mul_of_coprime d r hdcop
    have hwnn : 0 ≤ mobKappaW d := mobKappaW_nonneg d
    have hshnn : 0 ≤ Work.LinnikAreas.Density4.sHalf d := Work.LinnikAreas.Density4.sHalf_nonneg d
    have hshnnr : 0 ≤ Work.LinnikAreas.Density4.sHalf r := Work.LinnikAreas.Density4.sHalf_nonneg r
    have hlogpos : 0 < Real.log (2 + z/(d:ℝ)) :=
      Real.log_pos (by linarith only [div_nonneg hz0 hd0.le, hz0, hd0])
    have hLnn : 0 ≤ (Real.log (2 + z/(d:ℝ)))^(-B) := Real.rpow_nonneg hlogpos.le _
    by_cases hdle : d ≤ ⌊z⌋₊
    · have hzd1 : 1 ≤ z/(d:ℝ) := by
        rw [one_le_div hd0]
        exact le_trans (by exact_mod_cast hdle) (Nat.floor_le hz0)
      have hb := hΘ (z/(d:ℝ)) hzd1 (d * r) hdr1
      calc |mobKappaW d * Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d * r)
            - mobKappaW d * (((d*r:ℕ):ℝ) / (Nat.totient (d*r):ℝ))|
          = mobKappaW d * |Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d * r)
              - ((d*r:ℕ):ℝ) / (Nat.totient (d*r):ℝ)| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hwnn]
        _ ≤ mobKappaW d * (C * Work.LinnikAreas.Density4.sHalf (d * r)
              * (Real.log (2 + z/(d:ℝ)))^(-B)) :=
            mul_le_mul_of_nonneg_left hb hwnn
        _ ≤ mobKappaW d * (KΘ * (Work.LinnikAreas.Density4.sHalf d
                * Work.LinnikAreas.Density4.sHalf r)
              * (Real.log (2 + z/(d:ℝ)))^(-B)) := by
            apply mul_le_mul_of_nonneg_left _ hwnn
            rw [hsh]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCΘ (mul_nonneg hshnn hshnnr)) hLnn
        _ = KΘ * Work.LinnikAreas.Density4.sHalf r *
              (mobKappaW d * Work.LinnikAreas.Density4.sHalf d
                * (Real.log (2 + z/(d:ℝ)))^(-B)) := by ring
    · have hzdlt : z/(d:ℝ) < 1 := by
        rw [div_lt_one hd0]
        have h2 : (⌊z⌋₊ : ℝ) + 1 ≤ (d:ℝ) := by exact_mod_cast (by omega : ⌊z⌋₊ + 1 ≤ d)
        have h3 := Nat.lt_floor_add_one z
        linarith only [h2, h3]
      have hsel : Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d*r) = 0 :=
        Work.LinnikAreas.Density4.selTheta_eq_zero_of_lt_one hzdlt _
      have hdiv := Work.LinnikAreas.Density4.KappaSum.div_totient_le_two_mul_sHalf (d*r) hdr1
      have hmain_nonneg : 0 ≤ ((d*r:ℕ):ℝ)/(Nat.totient (d*r):ℝ) := by positivity
      have hlog3 : Real.log (2 + z/(d:ℝ)) ≤ Real.log 3 :=
        Real.log_le_log (by linarith only [div_nonneg hz0 hd0.le, hz0, hd0]) (by linarith only [hzdlt])
      have hone : 1 ≤ (Real.log 3)^B * (Real.log (2 + z/(d:ℝ)))^(-B) := by
        have h1 : (Real.log (2 + z/(d:ℝ)))^B ≤ (Real.log 3)^B :=
          Real.rpow_le_rpow hlogpos.le hlog3 hB.le
        have h2 : (Real.log (2 + z/(d:ℝ)))^B * (Real.log (2 + z/(d:ℝ)))^(-B) = 1 := by
          rw [← Real.rpow_add hlogpos]; norm_num
        calc (1:ℝ) = (Real.log (2 + z/(d:ℝ)))^B * (Real.log (2 + z/(d:ℝ)))^(-B) := h2.symm
          _ ≤ (Real.log 3)^B * (Real.log (2 + z/(d:ℝ)))^(-B) :=
              mul_le_mul_of_nonneg_right h1 hLnn
      calc |mobKappaW d * Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d * r)
            - mobKappaW d * (((d*r:ℕ):ℝ) / (Nat.totient (d*r):ℝ))|
          = mobKappaW d * (((d*r:ℕ):ℝ)/(Nat.totient (d*r):ℝ)) := by
            rw [hsel, mul_zero, zero_sub, abs_neg,
              abs_of_nonneg (mul_nonneg hwnn hmain_nonneg)]
        _ ≤ mobKappaW d * (2 * Work.LinnikAreas.Density4.sHalf (d * r)) :=
            mul_le_mul_of_nonneg_left hdiv hwnn
        _ ≤ mobKappaW d * (KΘ * (Work.LinnikAreas.Density4.sHalf d
                * Work.LinnikAreas.Density4.sHalf r)
              * (Real.log (2 + z/(d:ℝ)))^(-B)) := by
            apply mul_le_mul_of_nonneg_left _ hwnn
            rw [hsh]
            have hnn : 0 ≤ Work.LinnikAreas.Density4.sHalf d
                * Work.LinnikAreas.Density4.sHalf r := mul_nonneg hshnn hshnnr
            have h1 : 2 * (Work.LinnikAreas.Density4.sHalf d
                  * Work.LinnikAreas.Density4.sHalf r)
                ≤ (2 * (Real.log 3)^B * (Real.log (2 + z/(d:ℝ)))^(-B))
                  * (Work.LinnikAreas.Density4.sHalf d
                    * Work.LinnikAreas.Density4.sHalf r) := by
              nlinarith only [hone, hnn]
            refine le_trans h1 ?_
            have h2ΘL : 2 * (Real.log 3)^B * (Real.log (2 + z/(d:ℝ)))^(-B)
                ≤ KΘ * (Real.log (2 + z/(d:ℝ)))^(-B) :=
              mul_le_mul_of_nonneg_right h2Θ hLnn
            calc (2 * (Real.log 3)^B * (Real.log (2 + z/(d:ℝ)))^(-B))
                  * (Work.LinnikAreas.Density4.sHalf d * Work.LinnikAreas.Density4.sHalf r)
                ≤ (KΘ * (Real.log (2 + z/(d:ℝ)))^(-B))
                  * (Work.LinnikAreas.Density4.sHalf d * Work.LinnikAreas.Density4.sHalf r) :=
                  mul_le_mul_of_nonneg_right h2ΘL hnn
              _ = KΘ * (Work.LinnikAreas.Density4.sHalf d * Work.LinnikAreas.Density4.sHalf r)
                  * (Real.log (2 + z/(d:ℝ)))^(-B) := by ring
        _ = KΘ * Work.LinnikAreas.Density4.sHalf r *
              (mobKappaW d * Work.LinnikAreas.Density4.sHalf d
                * (Real.log (2 + z/(d:ℝ)))^(-B)) := by ring
  -- ## main computation
  have hkLS : Work.LinnikAreas.Density4.kappaLogSum z r
      = ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
          mobKappaW d * Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d * r) := by
    rw [Work.LinnikAreas.Density4.KappaSum.kappaLogSum_expansion z r hr (M := M) hM]
    apply Finset.sum_congr rfl
    intro d _
    rfl
  calc |Work.LinnikAreas.Density4.kappaLogSum z r -
        ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
          mobKappaW d * (((d * r : ℕ) : ℝ) / (Nat.totient (d * r) : ℝ))|
      = |∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
          (mobKappaW d * Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d * r)
            - mobKappaW d * (((d*r:ℕ):ℝ) / (Nat.totient (d*r):ℝ)))| := by
          rw [hkLS, Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
          |mobKappaW d * Work.LinnikAreas.Density4.selTheta (z/(d:ℝ)) (d * r)
            - mobKappaW d * (((d*r:ℕ):ℝ) / (Nat.totient (d*r):ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
          KΘ * Work.LinnikAreas.Density4.sHalf r *
            (mobKappaW d * Work.LinnikAreas.Density4.sHalf d
              * (Real.log (2 + z/(d:ℝ)))^(-B)) := Finset.sum_le_sum hterm
    _ = KΘ * Work.LinnikAreas.Density4.sHalf r *
          (∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
            mobKappaW d * Work.LinnikAreas.Density4.sHalf d
              * (Real.log (2 + z/(d:ℝ)))^(-B)) := by
          rw [Finset.mul_sum]
    _ ≤ KΘ * Work.LinnikAreas.Density4.sHalf r *
          (∑ d ∈ Finset.Icc 1 M, mobKappaW d * Work.LinnikAreas.Density4.sHalf d
              * (Real.log (2 + z/(d:ℝ)))^(-B)) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg hKΘpos.le (Work.LinnikAreas.Density4.sHalf_nonneg r))
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => mul_nonneg (mul_nonneg (mobKappaW_nonneg i)
              (Work.LinnikAreas.Density4.sHalf_nonneg i))
              (Real.rpow_nonneg (Real.log_nonneg (by
                have h : 0 ≤ z/(i:ℝ) := div_nonneg hz0 (Nat.cast_nonneg i); linarith only [h])) _))
    _ ≤ KΘ * Work.LinnikAreas.Density4.sHalf r *
          (Ka * (Real.log (2+z))^(-B)) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg hKΘpos.le (Work.LinnikAreas.Density4.sHalf_nonneg r))
          exact hAbs z M hz
    _ = (KΘ * Ka) * Work.LinnikAreas.Density4.sHalf r * (Real.log (2+z))^(-B) := by ring

/-- Splitting a sum over `Icc a B` at `N` (`a ≤ N ≤ B`). -/
lemma sum_Icc_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a N B : ℕ}
    (h : a ≤ N) (hNB : N ≤ B) :
    (∑ n ∈ Finset.Icc a B, f n)
      = (∑ n ∈ Finset.Icc a N, f n) + ∑ n ∈ Finset.Icc (N + 1) B, f n := by
  have hdisj : Disjoint (Finset.Icc a N) (Finset.Icc (N + 1) B) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2
    omega
  rw [← Finset.sum_union hdisj]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

/-- Splitting a filtered sum over `Icc a B` at `N` (`a ≤ N ≤ B`). -/
lemma sum_filter_Icc_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p : ℕ → Prop)
    [DecidablePred p] {a N B : ℕ} (h : a ≤ N) (hNB : N ≤ B) :
    (∑ n ∈ (Finset.Icc a B).filter p, f n)
      = (∑ n ∈ (Finset.Icc a N).filter p, f n)
        + ∑ n ∈ (Finset.Icc (N + 1) B).filter p, f n := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    sum_Icc_split (fun n => if p n then f n else 0) h hNB]

/-- Telescoping: `∑_{N < n ≤ M} (log n - log (n-1)) = log M - log N` for `1 ≤ N ≤ M`. -/
lemma sum_Icc_log_sub_tele {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc (N + 1) M, (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)))
      = Real.log (M : ℝ) - Real.log (N : ℝ) := by
  induction M, hNM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega : ¬ N + 1 ≤ N), Finset.sum_empty]
      ring
  | succ M hNM ih =>
      rw [Finset.Icc_eq_cons_Ico (by omega : N + 1 ≤ M + 1), Finset.sum_cons,
        show Finset.Ico (N + 1) (M + 1) = Finset.Icc (N + 1) M by
          ext x
          simp only [Finset.mem_Ico, Finset.mem_Icc]
          omega,
        ih]
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
      have hMpos : (0 : ℝ) < (M : ℝ) := by linarith only [hM1]
      push_cast
      ring_nf

/-- `∑_{N < n ≤ M} 1/n ≤ log (M/N)` for `1 ≤ N ≤ M`. -/
lemma sum_Icc_inv_le_log_div {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc (N + 1) M, (1 : ℝ) / (n : ℝ)) ≤ Real.log ((M : ℝ) / (N : ℝ)) := by
  have hterm : ∀ n ∈ Finset.Icc (N + 1) M,
      (1 : ℝ) / (n : ℝ) ≤ Real.log ((n : ℝ)) - Real.log ((n : ℝ) - 1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hm1pos : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith only [this]
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hnpos hm1pos)
    have heq : 1 - ((n : ℝ) / ((n : ℝ) - 1))⁻¹ = 1 / (n : ℝ) := by
      rw [inv_div]
      field_simp
      ring
    have hlog : Real.log ((n : ℝ) / ((n : ℝ) - 1))
        = Real.log (n : ℝ) - Real.log ((n : ℝ) - 1) :=
      Real.log_div hnpos.ne' hm1pos.ne'
    rw [heq, hlog] at h
    exact h
  calc (∑ n ∈ Finset.Icc (N + 1) M, (1 : ℝ) / (n : ℝ))
      ≤ ∑ n ∈ Finset.Icc (N + 1) M, (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) :=
        Finset.sum_le_sum hterm
    _ = Real.log (M : ℝ) - Real.log (N : ℝ) := sum_Icc_log_sub_tele hN hNM
    _ = Real.log ((M : ℝ) / (N : ℝ)) := by
        rw [Real.log_div (by exact_mod_cast (by omega : M ≠ 0)) (by exact_mod_cast (by omega : N ≠ 0))]

/-- The `c`-trick identity: comparing the log-weighted `κ`-sum at the two scales `z` and `z*c`
produces the unweighted `κ`-sum at `⌊z⌋`, up to a short "window" sum over `⌊z⌋ < n ≤ ⌊z*c⌋`. -/
lemma kappaSum_c_trick (z c : ℝ) (hz : 1 ≤ z) (hc : 1 < c) (r : ℕ) :
    Work.LinnikAreas.Density4.kappaLogSum (z * c) r - Work.LinnikAreas.Density4.kappaLogSum z r =
      Real.log c * Work.LinnikAreas.Density4.kappaSum ⌊z⌋₊ r +
        ∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ)) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hN1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hNM : ⌊z⌋₊ ≤ ⌊z * c⌋₊ := Nat.floor_mono (by nlinarith only [hz, hc])
  have hsplit := sum_filter_Icc_split
    (fun n => (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ)))
    (fun n => Nat.Coprime n r) (a := 1) (N := ⌊z⌋₊) (B := ⌊z * c⌋₊) hN1 hNM
  unfold Work.LinnikAreas.Density4.kappaLogSum Work.LinnikAreas.Density4.kappaSum
  rw [hsplit]
  have hterm : ∀ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
      (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ))
        - (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z / (n : ℝ))
        = (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log c := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, _⟩ := hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hzn : z / (n : ℝ) ≠ 0 := (div_pos hzpos hnpos).ne'
    have hlog : Real.log (z * c / (n : ℝ)) = Real.log (z / (n : ℝ)) + Real.log c := by
      rw [show z * c / (n : ℝ) = z / (n : ℝ) * c by field_simp]
      exact Real.log_mul hzn hcpos.ne'
    rw [hlog]; ring
  have hcomb : (∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ)))
      - (∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z / (n : ℝ)))
      = Real.log c * ∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have hrearr : ((∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ)))
        + ∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ)))
      - (∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z / (n : ℝ)))
      = ((∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ)))
        - (∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z / (n : ℝ))))
        + ∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ)) := by
    ring
  rw [hrearr, hcomb]

/-- The "window" sum in the `c`-trick is at most `log c · log(⌊z*c⌋/⌊z⌋)`. -/
lemma kappaSum_window_bound (z c : ℝ) (hz : 1 ≤ z) (hc : 1 < c) (r : ℕ) :
    |∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ))|
      ≤ Real.log c * Real.log ((⌊z * c⌋₊ : ℝ) / (⌊z⌋₊ : ℝ)) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hN1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hNM : ⌊z⌋₊ ≤ ⌊z * c⌋₊ := Nat.floor_mono (by nlinarith only [hz, hc])
  have hzcpos : (0 : ℝ) < z * c := mul_pos hzpos hcpos
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc.le
  have hterm : ∀ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
      |(ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ))|
        ≤ Real.log c * ((1 : ℝ) / (n : ℝ)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hnlo, hnhi⟩, _⟩ := hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hkpos : 0 < Work.LinnikAreas.Density4.kappaR n := kappaR_pos' hn1
    have hzlt : z < (n : ℝ) := by
      have h2 : (⌊z⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnlo
      have h3 : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
      linarith only [h2, h3]
    have hnle : (n : ℝ) ≤ z * c := by
      have h2 : (n : ℝ) ≤ (⌊z * c⌋₊ : ℝ) := by exact_mod_cast hnhi
      have h3 : ((⌊z * c⌋₊ : ℕ) : ℝ) ≤ z * c := Nat.floor_le hzcpos.le
      linarith only [h2, h3]
    have hlog1 : Real.log (z * c / (n : ℝ)) ≤ Real.log c := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hnpos]
      nlinarith only [hzlt, hc]
    have hlog0 : 0 ≤ Real.log (z * c / (n : ℝ)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hnpos]; linarith only [hnle])
    have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 :=
      Commons.NumberTheory.Moebius.moebius_abs_le_one n
    have h1 : |(ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n| ≤ 1 / (n : ℝ) := by
      rw [abs_div, abs_of_pos hkpos]
      calc |(ArithmeticFunction.moebius n : ℝ)| / Work.LinnikAreas.Density4.kappaR n ≤ 1 / Work.LinnikAreas.Density4.kappaR n :=
            div_le_div_of_nonneg_right hmu hkpos.le
        _ ≤ 1 / (n : ℝ) := one_div_kappaR_le_inv' hn1
    calc |(ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ))|
        = |(ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n| * |Real.log (z * c / (n : ℝ))| :=
          abs_mul _ _
      _ ≤ (1 / (n : ℝ)) * Real.log c := by
          apply mul_le_mul h1 _ (abs_nonneg _) (by positivity)
          rw [abs_of_nonneg hlog0]; exact hlog1
      _ = Real.log c * ((1 : ℝ) / (n : ℝ)) := by ring
  calc |∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ))|
      ≤ ∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
          |(ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n * Real.log (z * c / (n : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
          Real.log c * ((1 : ℝ) / (n : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.log c * ∑ n ∈ (Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊).filter (fun n => Nat.Coprime n r),
          (1 : ℝ) / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.log c * ∑ n ∈ Finset.Icc (⌊z⌋₊ + 1) ⌊z * c⌋₊, (1 : ℝ) / (n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hlogc
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => by positivity)
    _ ≤ Real.log c * Real.log ((⌊z * c⌋₊ : ℝ) / (⌊z⌋₊ : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hlogc
        exact sum_Icc_inv_le_log_div hN1 hNM



theorem kappaLogSum_diff (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z z' : ℝ) (r : ℕ), 1 ≤ z → 1 ≤ z' → 1 ≤ r →
      |Work.LinnikAreas.Density4.kappaLogSum z r - Work.LinnikAreas.Density4.kappaLogSum z' r|
        ≤ K * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + min z z'))^(-B) := by
  obtain ⟨K0, hK0pos, h0⟩ := kappaLogSum_err B hB
  refine ⟨2 * K0, by positivity, ?_⟩
  intro z z' r hz hz' hr
  have hmin1 : 1 ≤ min z z' := le_min hz hz'
  have hlogmin : 0 < Real.log (2 + min z z') := Real.log_pos (by linarith only [hmin1])
  have e1 : (Real.log (2 + z))^(-B) ≤ (Real.log (2 + min z z'))^(-B) :=
    Real.rpow_le_rpow_of_nonpos hlogmin
      (Real.log_le_log (by linarith only [hmin1]) (by linarith only [min_le_left z z']))
      (by linarith only [hB])
  have e2 : (Real.log (2 + z'))^(-B) ≤ (Real.log (2 + min z z'))^(-B) :=
    Real.rpow_le_rpow_of_nonpos hlogmin
      (Real.log_le_log (by linarith only [hmin1]) (by linarith only [min_le_right z z']))
      (by linarith only [hB])
  have hshnn : 0 ≤ Work.LinnikAreas.Density4.sHalf r := Work.LinnikAreas.Density4.sHalf_nonneg r
  set M : ℕ := max ⌊z⌋₊ ⌊z'⌋₊ with hMdef
  have hzM : ⌊z⌋₊ ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hz'M : ⌊z'⌋₊ ≤ M := by rw [hMdef]; exact le_max_right _ _
  set T : ℝ := ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
      mobKappaW d * (((d * r : ℕ) : ℝ) / (Nat.totient (d * r) : ℝ)) with hTdef
  have h1 := h0 z r M hz hr hzM
  have h2 := h0 z' r M hz' hr hz'M
  have htri : |Work.LinnikAreas.Density4.kappaLogSum z r
      - Work.LinnikAreas.Density4.kappaLogSum z' r| ≤
      |Work.LinnikAreas.Density4.kappaLogSum z r - T|
        + |Work.LinnikAreas.Density4.kappaLogSum z' r - T| := by
    have := abs_sub_le (Work.LinnikAreas.Density4.kappaLogSum z r) T
      (Work.LinnikAreas.Density4.kappaLogSum z' r)
    rw [abs_sub_comm T] at this
    exact this
  have hb1 : K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + z))^(-B)
      ≤ K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + min z z'))^(-B) :=
    mul_le_mul_of_nonneg_left e1 (mul_nonneg hK0pos.le hshnn)
  have hb2 : K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + z'))^(-B)
      ≤ K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + min z z'))^(-B) :=
    mul_le_mul_of_nonneg_left e2 (mul_nonneg hK0pos.le hshnn)
  calc |Work.LinnikAreas.Density4.kappaLogSum z r - Work.LinnikAreas.Density4.kappaLogSum z' r|
      ≤ |Work.LinnikAreas.Density4.kappaLogSum z r - T|
          + |Work.LinnikAreas.Density4.kappaLogSum z' r - T| := htri
    _ ≤ K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + z))^(-B)
          + K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + z'))^(-B) :=
        add_le_add h1 h2
    _ ≤ K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + min z z'))^(-B)
          + K0 * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + min z z'))^(-B) :=
        add_le_add hb1 hb2
    _ = 2 * K0 * Work.LinnikAreas.Density4.sHalf r
          * (Real.log (2 + min z z'))^(-B) := by ring


/-- The logarithm absorbs the reciprocal of `Q - 1`: for `Q ≥ 2`,
`1/(Q-1) ≤ K (log (2+Q))^{-E}` for a constant `K` depending only on `E > 0`. -/
lemma inv_pred_le_log_rpow (E : ℝ) (hE : 0 < E) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, 2 ≤ Q → 1/(Q-1) ≤ K * (Real.log (2+Q))^(-E) := by
  obtain ⟨K4, hK4pos, hK4⟩ :=
    Work.LinnikAreas.Density4.KappaSum.log_pow_le_const_mul_sqrt (4*E) (by linarith only [hE])
  refine ⟨2 * K4 ^ ((1:ℝ)/4), by positivity, ?_⟩
  intro Q hQ
  have hQ0 : 0 < Q := by linarith only [hQ]
  have hlogpos : 0 < Real.log (2 + Q) := Real.log_pos (by linarith only [hQ])
  have hEQ : (Real.log (2+Q))^E ≤ K4 ^ ((1:ℝ)/4) * Q := by
    have h4 := hK4 Q (by linarith only [hQ])
    have hEq : (Real.log (2+Q))^E = ((Real.log (2+Q))^(4*E)) ^ ((1:ℝ)/4) := by
      rw [← Real.rpow_mul hlogpos.le]
      congr 1
      ring
    rw [hEq]
    calc ((Real.log (2+Q))^(4*E)) ^ ((1:ℝ)/4)
        ≤ (K4 * Real.sqrt Q) ^ ((1:ℝ)/4) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hlogpos.le _) h4 (by norm_num)
      _ = K4 ^ ((1:ℝ)/4) * (Real.sqrt Q) ^ ((1:ℝ)/4) := by
          rw [Real.mul_rpow hK4pos.le (Real.sqrt_nonneg Q)]
      _ ≤ K4 ^ ((1:ℝ)/4) * Q := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hK4pos.le _)
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hQ0) ((1:ℝ)/2) ((1:ℝ)/4)]
          simpa using Real.rpow_le_rpow_of_exponent_le (by linarith only [hQ] : (1:ℝ) ≤ Q)
            (by norm_num : ((1:ℝ)/2) * (1/4) ≤ 1)
  have hL : 0 < (Real.log (2+Q))^E := Real.rpow_pos_of_pos hlogpos E
  have h2 : 1/Q ≤ K4 ^ ((1:ℝ)/4) * (Real.log (2+Q))^(-E) := by
    rw [div_le_iff₀ hQ0]
    have heq : K4 ^ ((1:ℝ)/4) * (Real.log (2+Q))^(-E) * Q
        = K4 ^ ((1:ℝ)/4) * Q / (Real.log (2+Q))^E := by
      rw [Real.rpow_neg hlogpos.le]; ring
    rw [heq]
    exact (one_le_div hL).mpr hEQ
  have h1 : 1/(Q-1) ≤ 2/Q := by
    rw [div_le_div_iff₀ (by linarith only [hQ] : (0:ℝ) < Q-1) hQ0]
    linarith only [hQ]
  have h3 : 2/Q ≤ 2 * (K4 ^ ((1:ℝ)/4) * (Real.log (2+Q))^(-E)) := by
    rw [show (2:ℝ)/Q = 2 * (1/Q) by ring]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : 2 * (K4 ^ ((1:ℝ)/4) * (Real.log (2+Q))^(-E))
      = 2 * K4 ^ ((1:ℝ)/4) * (Real.log (2+Q))^(-E) := by ring
  linarith only [h1, h3, h4]

end Work.LinnikAreas.JutilaPieces
