import Mathlib
import Submission.Work.A3.Weil.Defs
import Submission.Work.A3.Weil.card_prod_fiber_le
import Submission.Work.A3.Weil.card_piFinset_zero_prod_le

/-!
# The `k`-fold arithmetic sum of the Weyl differencing is bounded by a one-dimensional sum

Weyl differencing produces the sum

`arithSum N k Λ = ∑_{l ∈ (shiftIdx N)^k} geomBound N (Λ · ∏ i, l i)`

over the `k`-tuples of admissible shifts `|l i| ≤ N - 1`, where
`geomBound N x = 1 / max (intDist x) (1/N)`.  This file bounds it by the *one-dimensional*
sum `∑_{|P| ≤ M} geomBound N (Λ · P)` over a range `M ≥ N^k`, up to a factor `C · N^ε`:

`arithSum N k Λ ≤ C N^ε (N^k + ∑_{|P| ≤ M, P ≠ 0} geomBound N (Λ · P))`.

**Proof.**  Group the tuples by the value of the product `P = ∏ i, l i`:

`arithSum N k Λ = ∑_{P ∈ [-M,M]} #(fibre of P) · geomBound N (Λ · P)`.

Since every `l i` is a divisor of `P` (up to sign), the fibre of `P ≠ 0` has at most
`C N^ε` elements (`Work.A3.Weil.card_prod_fiber_le`, the `k`-fold divisor bound); this is where
the hypothesis `M ≥ N^k` enters, since `|P| ≤ (N-1)^k`.  The fibre of `P = 0` consists of the
tuples with a zero coordinate, of which there are at most `k (2N)^(k-1)`
(`Work.A3.Weil.card_piFinset_zero_prod_le`); since `geomBound N 0 = N`, this contributes at most
`k · 2^(k-1) · N^k`, which is absorbed by the `N^k` term of the bound.
-/

set_option autoImplicit false

namespace Work.A3.Weil

open Finset

/-- `geomBound` is nonnegative. -/
lemma geomBound_nonneg (N : ℕ) (x : ℝ) : 0 ≤ geomBound N x := by
  rw [geomBound]
  exact inv_nonneg.mpr (le_trans (Submission.VanDerCorput.intDist_nonneg x) (le_max_left _ _))

/-- `intDist 0 = 0`, hence `geomBound N 0 = N`. -/
lemma geomBound_zero (N : ℕ) : geomBound N 0 = N := by
  rw [geomBound]
  have hd : Submission.VanDerCorput.intDist 0 = 0 := by
    simp [Submission.VanDerCorput.intDist, Int.fract]
  rw [hd, max_eq_right (by positivity : (0:ℝ) ≤ (N:ℝ)⁻¹), inv_inv]

/-- **Fibre decomposition of a sum over tuples.**  If all products `∏ i, l i` of tuples in the box
`T^k` lie in `Pset`, then a sum over the box can be regrouped according to the value of the
product. -/
lemma sum_prod_fiber {k : ℕ} (T : Finset ℤ) (G : ℤ → ℝ) (Pset : Finset ℤ)
    (hsub : ∀ l ∈ Fintype.piFinset (fun _ : Fin k => T), (∏ i, l i) ∈ Pset) :
    (∑ l ∈ Fintype.piFinset (fun _ : Fin k => T), G (∏ i, l i))
      = ∑ P ∈ Pset, (((Fintype.piFinset (fun _ : Fin k => T)).filter
            (fun l => ∏ i, l i = P)).card : ℝ) * G P := by
  classical
  calc ∑ l ∈ Fintype.piFinset (fun _ : Fin k => T), G (∏ i, l i)
      = ∑ l ∈ Fintype.piFinset (fun _ : Fin k => T),
          ∑ P ∈ Pset, (if (∏ i, l i) = P then G P else 0) := by
        refine Finset.sum_congr rfl (fun l hl => ?_)
        rw [Finset.sum_ite_eq Pset (∏ i, l i) G, if_pos (hsub l hl)]
    _ = ∑ P ∈ Pset, ∑ l ∈ Fintype.piFinset (fun _ : Fin k => T),
          (if (∏ i, l i) = P then G P else 0) := Finset.sum_comm
    _ = ∑ P ∈ Pset, (((Fintype.piFinset (fun _ : Fin k => T)).filter
            (fun l => ∏ i, l i = P)).card : ℝ) * G P := by
        refine Finset.sum_congr rfl (fun P _ => ?_)
        rw [Finset.card_filter]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        by_cases h : (∏ i, l i) = P <;> simp [h]

/-- The product of a tuple of shifts of size at most `N - 1` has absolute value at most `N^k`, so
it lands in `[-M, M]` whenever `N^k ≤ M`. -/
lemma prod_mem_Icc_shiftIdx {N k M : ℕ} (hN : 1 ≤ N) (hM : (N:ℤ)^k ≤ (M:ℤ))
    {l : Fin k → ℤ} (hl : ∀ i, l i ∈ shiftIdx N) :
    (∏ i, l i) ∈ Finset.Icc (-(M:ℤ)) (M:ℤ) := by
  have h1 : ∀ i, |l i| ≤ ((N - 1 : ℕ) : ℤ) := by
    intro i
    have h := hl i
    rw [shiftIdx, Finset.mem_Icc] at h
    obtain ⟨ha, hb⟩ := h
    have hcast : (((N - 1 : ℕ)) : ℤ) = (N : ℤ) - 1 := by rw [Nat.cast_sub hN]; norm_num
    rw [abs_le, hcast]
    constructor <;> omega
  have hprod : |∏ i, l i| ≤ ((N:ℤ))^k := by
    calc |∏ i, l i| = ∏ i, |l i| := by rw [Finset.abs_prod]
      _ ≤ ∏ _i : Fin k, (((N - 1 : ℕ)) : ℤ) :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => h1 i)
      _ = (((N - 1 : ℕ)) : ℤ)^k := by simp [Finset.prod_const]
      _ ≤ ((N:ℤ))^k := by
            apply pow_le_pow_left₀ (by positivity)
            have : (((N - 1 : ℕ)) : ℤ) = (N:ℤ) - 1 := by rw [Nat.cast_sub hN]; norm_num
            rw [this]; omega
  rw [Finset.mem_Icc]
  rw [abs_le] at hprod
  obtain ⟨ha, hb⟩ := hprod
  constructor <;> omega

/-- `arithSum N k Λ` regrouped by the value of the product `∏ i, l i ∈ [-M, M]`. -/
lemma arithSum_eq_sum_fiber (N k : ℕ) (Λ : ℝ) {M : ℕ} (hN : 1 ≤ N) (hM : (N:ℤ)^k ≤ (M:ℤ)) :
    arithSum N k Λ
      = ∑ P ∈ Finset.Icc (-(M:ℤ)) (M:ℤ),
          (((Fintype.piFinset (fun _ : Fin k => shiftIdx N)).filter
              (fun l => ∏ i, l i = P)).card : ℝ) * geomBound N (Λ * (P:ℝ)) := by
  have hcast : arithSum N k Λ
      = ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
          geomBound N (Λ * ((∏ i, l i : ℤ) : ℝ)) := by
    simp only [arithSum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Int.cast_prod]
  rw [hcast]
  exact sum_prod_fiber (shiftIdx N) (fun P => geomBound N (Λ * (P:ℝ)))
    (Finset.Icc (-(M:ℤ)) (M:ℤ))
    (fun l hl => prod_mem_Icc_shiftIdx hN hM (Fintype.mem_piFinset.mp hl))

/-- **The arithmetic sum of the `k`-fold Weyl differencing.**  For every `ε > 0` and `k` there is
`C > 0` with, for all `N, M, Λ` satisfying `N ≥ 1` and `N^k ≤ M`,

`arithSum N k Λ ≤ C N^ε (N^k + ∑_{-M ≤ P ≤ M, P ≠ 0} geomBound N (Λ · P))`. -/
theorem arithSum_le {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N M : ℕ) (Λ : ℝ), 1 ≤ N → (N : ℤ) ^ k ≤ (M : ℤ) →
      Work.A3.Weil.arithSum N k Λ ≤ C * (N : ℝ) ^ ε *
        ((N : ℝ) ^ k +
          ∑ P ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            if P = 0 then 0 else Work.A3.Weil.geomBound N (Λ * (P : ℝ))) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the only tuple is the empty one, i.e. a single `geomBound N Λ`
    subst hk0
    refine ⟨1, one_pos, ?_⟩
    intro N M Λ hN hM
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hNr : (1:ℝ) ≤ (N:ℝ)^ε := Real.one_le_rpow hN1 hε.le
    have hNεnn : (0:ℝ) ≤ (N:ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
    have harith : arithSum N 0 Λ = geomBound N Λ := by simp [arithSum]
    rw [harith]
    set SUM : ℝ := ∑ P ∈ Finset.Icc (-(M:ℤ)) (M:ℤ),
      (if P = 0 then (0:ℝ) else geomBound N (Λ * (P:ℝ))) with hSUM
    rw [pow_zero, one_mul]
    have hmem : (1:ℤ) ∈ Finset.Icc (-(M:ℤ)) (M:ℤ) := by
      have hM1 : (1:ℤ) ≤ (M:ℤ) := by simpa using hM
      rw [Finset.mem_Icc]; omega
    have hnonneg : ∀ P ∈ Finset.Icc (-(M:ℤ)) (M:ℤ),
        0 ≤ (if P = 0 then (0:ℝ) else geomBound N (Λ * (P:ℝ))) := by
      intro P _
      by_cases h : P = 0
      · simp [h]
      · simp only [if_neg h]; exact geomBound_nonneg N _
    have hsingle : geomBound N Λ ≤ SUM := by
      rw [hSUM]
      simpa using Finset.single_le_sum hnonneg hmem
    have hSnn : (0:ℝ) ≤ SUM := by
      rw [hSUM]; exact Finset.sum_nonneg hnonneg
    have step2 : SUM ≤ (N:ℝ)^ε * SUM := by
      simpa using mul_le_mul_of_nonneg_right hNr hSnn
    have step3 : (N:ℝ)^ε * SUM ≤ (N:ℝ)^ε * (1 + SUM) := by
      rw [mul_add, mul_one]
      exact le_add_of_nonneg_left hNεnn
    exact le_trans hsingle (le_trans step2 step3)
  · -- `k ≥ 1`: group by the product and bound the two kinds of fibres
    obtain ⟨CA, hCApos, hA⟩ := card_prod_fiber_le k hε
    refine ⟨max CA ((k:ℝ)*2^(k-1)), lt_of_lt_of_le hCApos (le_max_left _ _), ?_⟩
    intro N M Λ hN hM
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hNr : (1:ℝ) ≤ (N:ℝ)^ε := Real.one_le_rpow hN1 hε.le
    have hNεnn : (0:ℝ) ≤ (N:ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
    set Pset : Finset ℤ := Finset.Icc (-(M:ℤ)) (M:ℤ) with hPset
    set SR : ℝ := ∑ P ∈ Pset, (if P = 0 then (0:ℝ) else geomBound N (Λ * (P:ℝ))) with hSR
    set fib : ℤ → ℝ := fun P => (((Fintype.piFinset (fun _ : Fin k => shiftIdx N)).filter
        (fun l => ∏ i, l i = P)).card : ℝ) with hfib
    set G : ℤ → ℝ := fun P => geomBound N (Λ * (P:ℝ)) with hG
    have hGnn : ∀ P, 0 ≤ G P := fun P => geomBound_nonneg N _
    have harith : arithSum N k Λ = ∑ P ∈ Pset, fib P * G P := by
      rw [hPset, hfib, hG]
      exact arithSum_eq_sum_fiber N k Λ hN hM
    have hsplit : ∑ P ∈ Pset, fib P * G P
        = (∑ P ∈ Pset.filter (fun P => P = 0), fib P * G P)
          + (∑ P ∈ Pset.filter (fun P => P ≠ 0), fib P * G P) :=
      (Finset.sum_filter_add_sum_filter_not Pset (fun P => P = 0)
        (fun P => fib P * G P)).symm
    have h0mem : (0:ℤ) ∈ Pset := by
      rw [hPset, Finset.mem_Icc]
      have h0 : (0:ℤ) ≤ (N:ℤ)^k := by positivity
      constructor <;> omega
    -- the fibre of `P = 0`
    have hzero_val : ∑ P ∈ Pset.filter (fun P => P = 0), fib P * G P = fib 0 * (N:ℝ) := by
      have hf : Pset.filter (fun P => P = 0) = {0} := by
        ext P; constructor
        · intro h; rw [Finset.mem_singleton]; exact (Finset.mem_filter.mp h).2
        · intro h
          rw [Finset.mem_singleton] at h
          subst h
          exact Finset.mem_filter.mpr ⟨h0mem, rfl⟩
      rw [hf, Finset.sum_singleton]
      congr 1
      rw [hG]
      simp [Int.cast_zero, geomBound_zero]
    have hfib0 : fib 0 ≤ (k:ℝ) * (2*(N:ℝ))^(k-1) := by
      simp only [hfib]
      have hb := card_piFinset_zero_prod_le (shiftIdx N) k hkpos
      have hT : (((shiftIdx N).card : ℕ) : ℝ) ≤ 2*(N:ℝ) := by
        have h1 : (shiftIdx N).card ≤ 2*N := by rw [shiftIdx, Int.card_Icc]; omega
        have h2 : ((2*N : ℕ) : ℝ) = 2*(N:ℝ) := by push_cast; ring
        rw [← h2]; exact_mod_cast h1
      have hTnn : (0:ℝ) ≤ (((shiftIdx N).card : ℕ) : ℝ) := by positivity
      have hcast : ((k * (shiftIdx N).card ^ (k-1) : ℕ) : ℝ)
          = (k:ℝ) * (((shiftIdx N).card : ℕ) : ℝ)^(k-1) := by push_cast; ring
      calc (((Fintype.piFinset (fun _ : Fin k => shiftIdx N)).filter
              (fun l => ∏ i, l i = 0)).card : ℝ)
          ≤ ((k * (shiftIdx N).card ^ (k-1) : ℕ) : ℝ) := by exact_mod_cast hb
        _ = (k:ℝ) * (((shiftIdx N).card : ℕ) : ℝ)^(k-1) := hcast
        _ ≤ (k:ℝ) * (2*(N:ℝ))^(k-1) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact pow_le_pow_left₀ hTnn hT (k-1)
    have hzero_le : fib 0 * (N:ℝ) ≤ ((k:ℝ)*2^(k-1)) * (N:ℝ)^k := by
      have hNk : (N:ℝ)^k = (N:ℝ)^(k-1) * (N:ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel hkpos]
      have h2 : ((k:ℝ)*2^(k-1)) * (N:ℝ)^k = ((k:ℝ) * (2*(N:ℝ))^(k-1)) * (N:ℝ) := by
        calc ((k:ℝ)*2^(k-1)) * (N:ℝ)^k
            = ((k:ℝ)*2^(k-1)) * ((N:ℝ)^(k-1) * (N:ℝ)) := by rw [hNk]
          _ = ((k:ℝ) * (2^(k-1) * (N:ℝ)^(k-1))) * (N:ℝ) := by ring
          _ = ((k:ℝ) * (2*(N:ℝ))^(k-1)) * (N:ℝ) := by rw [← mul_pow]
      have h1 := mul_le_mul_of_nonneg_right hfib0 (Nat.cast_nonneg N)
      rw [← h2] at h1
      exact h1
    -- the fibres of `P ≠ 0`: the `k`-fold divisor bound
    have hfib_le : ∀ P ∈ Pset.filter (fun P => P ≠ 0), fib P ≤ CA * (N:ℝ)^ε := by
      intro P hP
      rw [Finset.mem_filter] at hP
      obtain ⟨_, hPne⟩ := hP
      have hsub : (Fintype.piFinset (fun _ : Fin k => shiftIdx N)).filter (fun l => ∏ i, l i = P)
          ⊆ (Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N:ℤ)) (N:ℤ))).filter
              (fun l => ∏ i, l i = P) := by
        intro l hl
        rw [Finset.mem_filter] at hl ⊢
        refine ⟨?_, hl.2⟩
        rw [Fintype.mem_piFinset] at hl ⊢
        intro i
        have h := hl.1 i
        rw [shiftIdx, Finset.mem_Icc] at h
        rw [Finset.mem_Icc]
        obtain ⟨h1, h2⟩ := h
        constructor <;> omega
      have hcard : fib P ≤ (((Fintype.piFinset (fun _ : Fin k =>
          Finset.Icc (-(N:ℤ)) (N:ℤ))).filter (fun l => ∏ i, l i = P)).card : ℝ) := by
        simp only [hfib]
        exact_mod_cast Finset.card_le_card hsub
      exact le_trans hcard (hA N P hN hPne)
    have hnz : ∑ P ∈ Pset.filter (fun P => P ≠ 0), fib P * G P ≤ (CA * (N:ℝ)^ε) * SR := by
      have hSR' : SR = ∑ P ∈ Pset.filter (fun P => P ≠ 0), G P := by
        rw [hSR, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun P _ => ?_)
        by_cases h : P = 0 <;> simp [h, hG]
      rw [hSR', Finset.mul_sum]
      refine Finset.sum_le_sum (fun P hP => ?_)
      exact mul_le_mul_of_nonneg_right (hfib_le P hP) (hGnn P)
    have hSRnn : 0 ≤ SR := by
      rw [hSR]
      exact Finset.sum_nonneg (fun P _ => by
        by_cases h : P = 0
        · simp [h]
        · simp only [if_neg h]; exact geomBound_nonneg N _)
    have hNknn : (0:ℝ) ≤ (N:ℝ)^k := by positivity
    -- the two contributions are absorbed by the right-hand side
    have hA1 : ((k:ℝ)*2^(k-1)) * (N:ℝ)^k
        ≤ (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε * (N:ℝ)^k := by
      have h1 : (k:ℝ)*2^(k-1) ≤ (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε := by
        calc (k:ℝ)*2^(k-1) = ((k:ℝ)*2^(k-1)) * 1 := (mul_one _).symm
          _ ≤ ((k:ℝ)*2^(k-1)) * (N:ℝ)^ε := mul_le_mul_of_nonneg_left hNr (by positivity)
          _ ≤ (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hNεnn
      calc ((k:ℝ)*2^(k-1)) * (N:ℝ)^k
          ≤ ((max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε) * (N:ℝ)^k :=
            mul_le_mul_of_nonneg_right h1 hNknn
        _ = (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε * (N:ℝ)^k := by ring
    have hA2 : CA * (N:ℝ)^ε * SR ≤ (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε * SR := by
      apply mul_le_mul_of_nonneg_right _ hSRnn
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hNεnn
    have hfinal : ∑ P ∈ Pset, fib P * G P
        ≤ (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε * ((N:ℝ)^k + SR) := by
      calc ∑ P ∈ Pset, fib P * G P
          = (∑ P ∈ Pset.filter (fun P => P = 0), fib P * G P)
            + (∑ P ∈ Pset.filter (fun P => P ≠ 0), fib P * G P) := hsplit
        _ = fib 0 * (N:ℝ) + (∑ P ∈ Pset.filter (fun P => P ≠ 0), fib P * G P) := by
              rw [hzero_val]
        _ ≤ ((k:ℝ)*2^(k-1)) * (N:ℝ)^k + (CA * (N:ℝ)^ε) * SR := add_le_add hzero_le hnz
        _ ≤ (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε * (N:ℝ)^k
              + (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε * SR := add_le_add hA1 hA2
        _ = (max CA ((k:ℝ)*2^(k-1))) * (N:ℝ)^ε * ((N:ℝ)^k + SR) := by ring
    rw [harith]
    simpa only [hPset, hSR] using hfinal

end Work.A3.Weil
