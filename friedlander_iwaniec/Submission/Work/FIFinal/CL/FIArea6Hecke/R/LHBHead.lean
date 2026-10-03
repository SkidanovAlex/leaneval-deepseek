import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.LamSumFibre
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea7CF.card_pairs_gBox_absDelta_lt
import Submission.Work.FIArea7.P231M.Aux2
import Submission.Commons.Analysis.ExpLog.sum_Icc_one_div_le_log_add_one

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIPlan

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Lattice bound for the reciprocal norms.**  The sum of `1/|z|²` over the Gaussian integers
`z` of the box `gBox M` with `1 ≤ |z|² ≤ M` is `≤ 24 log (M+2)`.  Partitioning by the Chebyshev
radius `Work.FIArea7.gRadius z = max |Re z| |Im z|` (whose shell `gRadius = k` has `8k` points,
`Work.FIArea7.card_filter_gRadius_eq_le`) turns the sum into `∑_{k ≤ M} 8/k ≤ 8(1 + log M)`, and
`1 + log M ≤ 3 log (M+2)` because `log 2 > 1/2`. -/
theorem latticeInvGnormSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      (∑ z ∈ (Work.FIPlan.gBox (M : ℤ)).filter
          (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ M),
        (1 : ℝ) / (Work.FIPlan.gnorm z : ℝ)) ≤ C * Real.log ((M : ℝ) + 2) := by
  refine ⟨24, by norm_num, ?_⟩
  intro M
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · have hemp : (Work.FIPlan.gBox (M : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ M) = ∅ := by
      rw [hM0]
      exact Finset.filter_eq_empty_iff.mpr
        (fun z _ h => by have h1 := h.1; have h2 := h.2; omega)
    rw [hemp, Finset.sum_empty, hM0]
    have hlog : (0:ℝ) < Real.log (((0:ℕ):ℝ) + 2) := by
      apply Real.log_pos; norm_num
    linarith
  · set S : Finset GaussianInt :=
      (Work.FIPlan.gBox (M : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ M) with hS
    have hgnorm0 : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
      simp [Work.FIPlan.gnorm]
    have hmaps : ∀ z ∈ S, Work.FIArea7.gRadius z ∈ Finset.Icc 1 M := by
      intro z hz
      rw [hS, Finset.mem_filter] at hz
      obtain ⟨hzbox, hz1, hzM⟩ := hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [hgnorm0] at hz1
        omega
      refine Finset.mem_Icc.mpr ⟨Work.FIArea7.one_le_gRadius_of_ne_zero hz0, ?_⟩
      have h := (Work.FIArea7.mem_gBox_iff_gRadius (R := (M:ℤ))
        (by positivity : (0:ℤ) ≤ (M:ℤ))).mp hzbox
      simpa using h
    have hpt : ∀ z ∈ S, (1:ℝ)/(Work.FIPlan.gnorm z : ℝ) ≤
        (1:ℝ)/(((Work.FIArea7.gRadius z : ℝ))^2) := by
      intro z hz
      rw [hS, Finset.mem_filter] at hz
      obtain ⟨-, hz1, -⟩ := hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [hgnorm0] at hz1
        omega
      have hk1 : Work.FIArea7.gRadius z ≠ 0 :=
        ne_of_gt (Work.FIArea7.one_le_gRadius_of_ne_zero hz0)
      have hle : ((Work.FIArea7.gRadius z : ℝ))^2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
        have h : (Work.FIArea7.P231M.mfun z)^2 ≤ Work.FIPlan.gnorm z :=
          Work.FIArea7.P231M.sq_mfun_le_gnorm z
        have heq : Work.FIArea7.P231M.mfun z = Work.FIArea7.gRadius z := rfl
        rw [← heq]
        exact_mod_cast h
      have hpos : (0:ℝ) < ((Work.FIArea7.gRadius z : ℝ))^2 :=
        pow_pos (by positivity) 2
      exact one_div_le_one_div_of_le hpos hle
    calc (∑ z ∈ S, (1:ℝ)/(Work.FIPlan.gnorm z : ℝ))
        ≤ ∑ z ∈ S, (1:ℝ)/(((Work.FIArea7.gRadius z : ℝ))^2) := Finset.sum_le_sum hpt
      _ = ∑ k ∈ Finset.Icc 1 M,
            ∑ z ∈ S.filter (fun z => Work.FIArea7.gRadius z = k),
              (1:ℝ)/(((Work.FIArea7.gRadius z : ℝ))^2) := by
          rw [Finset.sum_fiberwise_of_maps_to hmaps (f := fun z : GaussianInt =>
            (1:ℝ)/(((Work.FIArea7.gRadius z : ℝ))^2))]
      _ ≤ ∑ k ∈ Finset.Icc 1 M, (8:ℝ)/(k:ℝ) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_Icc] at hk
          obtain ⟨hk1, hkM⟩ := hk
          have hcard : (S.filter (fun z => Work.FIArea7.gRadius z = k)).card ≤ 8 * k := by
            refine le_trans (Finset.card_le_card ?_)
              (Work.FIArea7.card_filter_gRadius_eq_le M k hk1 hkM)
            intro z hz
            rw [Finset.mem_filter] at hz ⊢
            exact ⟨by
              have hz1 : z ∈ S := hz.1
              rw [hS] at hz1
              exact (Finset.mem_filter.mp hz1).1, hz.2⟩
          have hsum1 : (∑ z ∈ S.filter (fun z => Work.FIArea7.gRadius z = k),
                (1:ℝ)/(((Work.FIArea7.gRadius z : ℝ))^2))
              = ∑ _z ∈ S.filter (fun z => Work.FIArea7.gRadius z = k),
                (1:ℝ)/(((k:ℝ))^2) := by
            refine Finset.sum_congr rfl (fun z hz => ?_)
            rw [(Finset.mem_filter.mp hz).2]
          rw [hsum1, Finset.sum_const, nsmul_eq_mul]
          calc ((S.filter (fun z => Work.FIArea7.gRadius z = k)).card : ℝ) * (1/((k:ℝ))^2)
              ≤ ((8*k : ℕ) : ℝ) * (1/((k:ℝ))^2) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact_mod_cast hcard
            _ = 8/(k:ℝ) := by
                have hkne : ((k:ℝ)) ≠ 0 := ne_of_gt (by exact_mod_cast hk1)
                push_cast
                field_simp
      _ = 8 * ∑ k ∈ Finset.Icc 1 M, (1:ℝ)/(k:ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k hk => by ring)
      _ ≤ 8 * (Real.log (M:ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Commons.Analysis.ExpLog.sum_Icc_one_div_le_log_add_one hM1
      _ ≤ 24 * Real.log ((M:ℝ) + 2) := by
          have hMnn : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
          have h2 : Real.log 2 ≤ Real.log ((M:ℝ)+2) :=
            Real.log_le_log (by norm_num) (by linarith)
          have h3 : Real.log ((M:ℕ):ℝ) ≤ Real.log ((M:ℝ)+2) :=
            Real.log_le_log (by exact_mod_cast hM1) (by linarith)
          linarith [Real.log_two_gt_d9]

/-- **Pointwise Hecke eigenvalue bound.**  For `‖χ‖ ≤ 1`, `λ(n) = ∑_{z primary, |z|²=n} ψ(z)` is
a sum of at most `#{z ∈ gBox M : |z|² = n}` terms of modulus `≤ 1` (`norm_psi_le_one`), because
`gBox n ⊆ gBox M` when `n ≤ M`. -/
lemma heckeLam_norm_le_fibre_card (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {n M : ℕ} (hnM : n ≤ M) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi k n‖
      ≤ (((Work.FIPlan.gBox (M : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℝ) := by
  classical
  have hbox : Work.FIPlan.gBox (n : ℤ) ⊆ Work.FIPlan.gBox (M : ℤ) := by
    intro z hz
    rw [Work.FIArea5.S16Hecke.mem_gBox_iff] at hz ⊢
    exact ⟨Finset.Icc_subset_Icc (by omega) (by omega) hz.1,
      Finset.Icc_subset_Icc (by omega) (by omega) hz.2⟩
  have hsub : (Work.FIPlan.gBox (n : ℤ)).filter
        (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n)
      ⊆ (Work.FIPlan.gBox (M : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n) := by
    intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hbox hz1, hz3⟩
  calc ‖Work.FIArea5.S16Hecke.heckeLam chi k n‖
      ≤ ∑ z ∈ (Work.FIPlan.gBox (n : ℤ)).filter
            (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n),
          ‖Work.FIArea5.S16Hecke.psi chi k z‖ := by
        unfold Work.FIArea5.S16Hecke.heckeLam
        exact norm_sum_le _ _
    _ ≤ ∑ _z ∈ (Work.FIPlan.gBox (n : ℤ)).filter
            (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n), (1 : ℝ) :=
        Finset.sum_le_sum (fun z _ => Work.FIArea5.S16Hecke.norm_psi_le_one chi k hchi z)
    _ = ((( Work.FIPlan.gBox (n : ℤ)).filter
            (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (((Work.FIPlan.gBox (M : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub

/-- On a norm fibre `{|z|² = n}` the reciprocal norm is the constant `1/n`. -/
lemma fib_sum_inv_eq (M n : ℕ) :
    (∑ z ∈ (Work.FIPlan.gBox (M:ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
        (1:ℝ)/(Work.FIPlan.gnorm z : ℝ))
      = (((Work.FIPlan.gBox (M:ℤ)).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℝ)
          / (n : ℝ) := by
  have h1 : (∑ z ∈ (Work.FIPlan.gBox (M:ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
        (1:ℝ)/(Work.FIPlan.gnorm z : ℝ))
      = ∑ _z ∈ (Work.FIPlan.gBox (M:ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
        (1:ℝ)/(n:ℝ) := by
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [(Finset.mem_filter.mp hz).2]
  rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **The "head" bound** for the Hecke eigenvalue sequence `λ(n) = heckeLam chi 0 n`
(`χ` coefficient-bounded): `∑_{n ≤ M} ‖λ(n)‖/n ≤ K log(M+2)` with `K` an absolute constant.
(`‖heckeLam chi 0 n‖` is at most the number `r(n)` of Gaussian integers of norm `n`, and
`∑_{n ≤ M} r(n)/n ≪ log M`.) -/
theorem LHBHead :
    ∃ K : ℝ, 0 < K ∧ ∀ (chi : GaussianInt → ℂ), (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ M : ℕ,
        ∑ n ∈ Finset.Icc 1 M, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ)
          ≤ K * Real.log (M + 2) := by
  obtain ⟨C, hCpos, hC⟩ := latticeInvGnormSum_le
  refine ⟨max C 1, lt_max_of_lt_left hCpos, ?_⟩
  intro chi hchi M
  have hstep1 : (∑ n ∈ Finset.Icc 1 M,
        ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 M,
          ∑ z ∈ (Work.FIPlan.gBox (M : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
            (1 : ℝ) / (Work.FIPlan.gnorm z : ℝ) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hb := heckeLam_norm_le_fibre_card chi 0 hchi hnM
    rw [fib_sum_inv_eq M n]
    exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg n)
  calc (∑ n ∈ Finset.Icc 1 M, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ))
      ≤ _ := hstep1
    _ = ∑ z ∈ (Work.FIPlan.gBox (M : ℤ)).filter
            (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ M),
          (1 : ℝ) / (Work.FIPlan.gnorm z : ℝ) := LamSumFibre M _
    _ ≤ C * Real.log ((M : ℝ) + 2) := hC M
    _ ≤ max C 1 * Real.log ((M : ℝ) + 2) := by
        refine mul_le_mul_of_nonneg_right (le_max_left C 1) ?_
        apply Real.log_nonneg
        have h : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
        linarith

end

end Work.FIArea6Hecke.R
