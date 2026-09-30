import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.sum_range_eq_sum_mod
import Submission.Work.BMF.SD.abel_geom_bound
import Submission.Work.BMF.SD.eC_conj_sum
import Submission.Work.BMF.SD.a_one_bound_perturb
import Submission.Work.BMF.SD.geom_block_bound
import Submission.Work.BMF.SD.sum_range_split_pow
import Submission.Work.BMF.SD.a_one_bound_final_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD.FreeA

open Finset Complex Real

/-! ### Elementary facts about the additive character `eC t = exp(2πit)` -/

/-- `eC m = 1` for an integer `m`. -/
lemma eC_int (m : ℤ) : Work.BMF.eC (m : ℝ) = 1 := by
  rw [Work.BMF.eC]
  have h : (2 : ℂ) * ↑Real.pi * Complex.I * ↑(m : ℝ) = (↑m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `eC` takes values of modulus one. -/
lemma norm_eC (t : ℝ) : ‖Work.BMF.eC t‖ = 1 := by
  rw [Work.BMF.eC]
  have h : (2 : ℂ) * ↑Real.pi * Complex.I * ↑t = (↑(2 * Real.pi * t) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- Periodicity of `eC` under shifting by an integer. -/
lemma eC_shift (t : ℝ) (m : ℤ) : Work.BMF.eC (t - (m:ℝ)) = Work.BMF.eC t := by
  have h := eC_add (t - (m:ℝ)) (m:ℝ)
  rw [eC_int m, mul_one, sub_add_cancel] at h
  exact h

/-- Upper bound for `‖eC t - 1‖` in terms of the distance of `t` to an integer. -/
lemma eC_sub_one_le (t : ℝ) (m : ℤ) :
    ‖Work.BMF.eC t - 1‖ ≤ 2 * Real.pi * |t - (m:ℝ)| := by
  rw [← eC_shift t m, Work.BMF.eC]
  have h2 : (2 : ℂ) * ↑Real.pi * Complex.I * ↑(t - ↑m) = Complex.I * ↑(2 * Real.pi * (t - ↑m)) := by
    push_cast; ring
  rw [h2, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have h3 : |(2:ℝ)| = 2 := by norm_num
  rw [h3]
  calc 2 * |Real.sin ((2 * Real.pi * (t - ↑m)) / 2)|
      = 2 * |Real.sin (Real.pi * (t - ↑m))| := by
        congr 2; ring_nf
      _ ≤ 2 * (Real.pi * |t - ↑m|) := by
        have := Real.abs_sin_le_abs (x := Real.pi * (t - ↑m))
        rw [abs_mul, abs_of_pos Real.pi_pos] at this
        linarith [this]
      _ = 2 * Real.pi * |t - (m:ℝ)| := by ring

/-- Lower bound for `‖eC t - 1‖` by the distance of `t` to the nearest integer. -/
lemma eC_sub_one_ge (t : ℝ) : 4 * |t - (round t : ℝ)| ≤ ‖Work.BMF.eC t - 1‖ := by
  rw [show ‖Work.BMF.eC t - 1‖ = 2 * |Real.sin (Real.pi * t)| from by
    rw [Work.BMF.eC]
    have h2 : (2 : ℂ) * ↑Real.pi * Complex.I * ↑t = Complex.I * ↑(2 * Real.pi * t) := by
      push_cast; ring
    rw [h2, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
    rw [show |(2:ℝ)| = 2 by norm_num]
    congr 2
    ring_nf]
  set ρ := t - (round t : ℝ) with hρ
  have hρle : |ρ| ≤ 1/2 := abs_sub_round t
  have ht : t = ρ + ((round t : ℤ) : ℝ) := by rw [hρ]; ring
  have hsin : |Real.sin (Real.pi * t)| = |Real.sin (Real.pi * ρ)| := by
    rw [ht]
    have : Real.pi * (ρ + ((round t : ℤ) : ℝ)) = Real.pi * ρ + (round t : ℤ) * Real.pi := by
      ring
    rw [this, Real.sin_add_int_mul_pi, abs_mul]
    simp
  rw [hsin]
  have h1 : 2 / Real.pi * |Real.pi * ρ| ≤ |Real.sin (Real.pi * ρ)| := by
    apply Real.mul_abs_le_abs_sin
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [abs_mul, abs_of_pos Real.pi_pos] at h1
  have h2 : 2 / Real.pi * (Real.pi * |ρ|) = 2 * |ρ| := by field_simp
  rw [h2] at h1
  rw [hρ] at h1
  linarith

/-- `eC t = 1` exactly when `t` is an integer. -/
lemma eC_eq_one_iff (t : ℝ) : Work.BMF.eC t = 1 ↔ ∃ m : ℤ, t = m := by
  constructor
  · intro h
    rw [Work.BMF.eC] at h
    rcases Complex.exp_eq_one_iff.mp h with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2 : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    have h3 : (↑t : ℂ) * (2 * ↑Real.pi * Complex.I) = (↑m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      rw [← hm]; ring
    have h4 := mul_right_cancel₀ h2 h3
    have h5 : (↑t : ℂ) = (↑(m : ℝ) : ℂ) := by simpa using h4
    exact Complex.ofReal_inj.mp h5
  · rintro ⟨m, rfl⟩; exact eC_int m

/-- A unit complex number times its conjugate is one. -/
lemma mul_star_self {ζ : ℂ} (h : ‖ζ‖ = 1) : ζ * star ζ = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

/-- The `q`-shift identity for the polynomial phase `Σ_j a j n^j`: shifting `n` by `q` multiplies
`eC` of the phase by `eC (q * a 1)` times the perturbation `eC` of the higher-degree difference. -/
lemma eC_step (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ) (n q : ℕ) :
    Work.BMF.eC (∑ j ∈ Finset.range (k+1), a j * (((n+q:ℕ):ℝ)^j))
      = Work.BMF.eC (∑ j ∈ Finset.range (k+1), a j * ((n:ℝ)^j))
        * Work.BMF.eC ((q:ℝ) * a 1)
        * Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) := by
  have hsplit := sum_range_split_pow k hk a n q
  have hsub : (∑ j ∈ Finset.range (k+1), a j * (((n+q:ℕ):ℝ)^j))
      - (∑ j ∈ Finset.range (k+1), a j * ((n:ℝ)^j))
      = (q:ℝ) * a 1 + ∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j)) := by
    rw [← Finset.sum_sub_distrib]
    rw [show (∑ j ∈ Finset.range (k+1), (a j * (((n+q:ℕ):ℝ)^j) - a j * ((n:ℝ)^j)))
        = ∑ j ∈ Finset.range (k+1), a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j)) from by
      apply Finset.sum_congr rfl; intro j _; ring]
    exact hsplit
  have hmain : (∑ j ∈ Finset.range (k+1), a j * (((n+q:ℕ):ℝ)^j))
      = (∑ j ∈ Finset.range (k+1), a j * ((n:ℝ)^j))
        + ((q:ℝ) * a 1 + ∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) := by
    linarith
  rw [hmain, ← eC_add, ← eC_add]
  ring

theorem a_one_bound (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, 0 < C ∧ ∀ (L q : ℕ) (a : ℕ → ℝ) (C₂ : ℝ),
      2 ≤ L → C₀ ≤ (L:ℝ) → 1 ≤ q → (q:ℝ) ≤ C₀ → 0 ≤ C₂ →
      (∀ j ∈ Finset.Icc 2 k, ∃ m : ℤ, |(q:ℝ) * a j - m| ≤ C₂ / (L:ℝ)^j) →
      δ * (L:ℝ) ≤ ‖∑ n ∈ Finset.range L, Work.BMF.eC (∑ j ∈ Finset.range (k+1), a j * (n:ℝ)^j)‖ →
      ∃ m : ℤ, |(q:ℝ) * a 1 - m| ≤ C * (C₂ + 1) / (L:ℝ) := by
  intro C₀ hC₀
  set C : ℝ := 2 * Real.pi * (4:ℝ)^(k+1) * C₀ / (2 * δ) + 1 with hCdef
  have hCpos : 0 < C := by
    have hA : (0:ℝ) < 2 * Real.pi * (4:ℝ)^(k+1) := by positivity
    have h2 : (0:ℝ) < 2 * δ := by linarith
    have hC0pos : (0:ℝ) < C₀ := by linarith
    have h3 : (0:ℝ) < 2 * Real.pi * (4:ℝ)^(k+1) * C₀ / (2 * δ) :=
      div_pos (mul_pos hA hC0pos) h2
    rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro L q a C₂ hL2 hC0L hq1 hqC0 hC2 hcoeff hbig
  have hqL' : q ≤ L := by exact_mod_cast (le_trans hqC0 hC0L)
  have hLpos : (0:ℝ) < (L:ℝ) := by
    have : (2:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL2
    linarith
  have hL1 : 1 ≤ L := by omega
  have hqL : (q:ℝ) ≤ (L:ℝ) := le_trans hqC0 hC0L
  have hqnn : (0:ℝ) ≤ q := Nat.cast_nonneg q
  set β : ℝ := (q:ℝ) * a 1 with hβdef
  set bnd : ℝ := C * (C₂ + 1) / (L:ℝ) with hbnddef
  have hbndnn : 0 ≤ bnd := by
    rw [hbnddef]
    exact div_nonneg (by positivity) (le_of_lt hLpos)
  by_cases hex : ∃ m : ℤ, |β - (m:ℝ)| ≤ bnd
  · exact hex
  · push Not at hex
    exfalso
    set d : ℝ := |β - (round β : ℝ)| with hddef
    have hd : bnd < d := by rw [hddef]; exact hex (round β)
    have hdnn : 0 < d := lt_of_le_of_lt hbndnn hd
    set ζ : ℂ := Work.BMF.eC β with hζdef
    have hζnorm : ‖ζ‖ = 1 := by rw [hζdef]; exact norm_eC β
    have hζ1 : ζ ≠ 1 := by
      intro hcon
      rw [hζdef] at hcon
      rcases (eC_eq_one_iff β).mp hcon with ⟨m, hm⟩
      have h := hex m
      rw [hm] at h
      simp at h
      linarith [hbndnn]
    have hζsub : 4 * d ≤ ‖ζ - 1‖ := by
      rw [hddef, hζdef]; exact eC_sub_one_ge β
    let z : ℕ → ℂ := fun n => Work.BMF.eC (∑ j ∈ Finset.range (k+1), a j * (n:ℝ)^j)
    have hz1 : ∀ n, ‖z n‖ = 1 := by intro n; exact norm_eC _
    set E : ℝ := 2 * Real.pi * ((4:ℝ)^(k+1) * C₂ / (L:ℝ)) with hEdef
    have hEnn : 0 ≤ E := by
      rw [hEdef]
      apply mul_nonneg (by positivity)
      exact div_nonneg (by positivity) (le_of_lt hLpos)
    -- per-step estimate
    have hstep : ∀ (r m : ℕ), r < q → m < (L + q - 1 - r)/q →
        ‖z ((m+1)*q + r) * star ζ - z (m*q+r)‖ ≤ E := by
      intro r m hr hm
      set n : ℕ := m*q + r with hndef
      have hnq : (m+1)*q + r = n + q := by rw [hndef]; ring
      have hn2L : ((n + q : ℕ) : ℝ) ≤ 2 * L := by
        have hm1 : m + 1 ≤ (L + q - 1 - r)/q := Nat.succ_le_of_lt hm
        have h1 : (m+1)*q ≤ L + q - 1 - r :=
          le_trans (Nat.mul_le_mul_right q hm1) (Nat.div_mul_le_self _ _)
        have hrle : r ≤ L + q - 1 := by omega
        have h2 : (m+1)*q + r ≤ L + q - 1 := by omega
        have h3 : n + q ≤ L + q - 1 := by rw [← hnq]; exact h2
        have hcast : ((L+q-1:ℕ):ℝ) = (L:ℝ) + (q:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ L + q)]; push_cast; ring
        have h4 : ((n+q:ℕ):ℝ) ≤ (L:ℝ) + (q:ℝ) - 1 := by
          calc ((n+q:ℕ):ℝ) ≤ ((L+q-1:ℕ):ℝ) := by exact_mod_cast h3
            _ = (L:ℝ) + (q:ℝ) - 1 := hcast
        linarith [hqL]
      have hstepid : z (n+q) = z n * ζ *
          Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) := by
        show Work.BMF.eC (∑ j ∈ Finset.range (k+1), a j * (((n+q:ℕ):ℝ)^j))
          = Work.BMF.eC (∑ j ∈ Finset.range (k+1), a j * ((n:ℝ)^j)) * ζ
            * Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j)))
        rw [hζdef, hβdef, eC_step k hk a n q]
      obtain ⟨M, hM⟩ := a_one_bound_perturb k q L a C₂ hq1 hL1 hqL hC2 hcoeff n hn2L
      have hΘ : ‖Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) - 1‖
          ≤ E := by
        rw [hEdef]
        have h1 := eC_sub_one_le (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) M
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hM (by positivity)
      rw [hnq]
      have hA : z (n+q) * star ζ - z n =
          z n * (Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) - 1) := by
        rw [hstepid]
        have hζζ : ζ * star ζ = 1 := mul_star_self hζnorm
        calc (z n * ζ * Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j)))) * star ζ - z n
            = z n * Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) * (ζ * star ζ) - z n := by ring
          _ = z n * (Work.BMF.eC (∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) - 1) := by rw [hζζ]; ring
      rw [hA, norm_mul, hz1 n, one_mul]
      exact hΘ
    have hblock : ∀ r ∈ Finset.range q,
        ‖∑ m ∈ Finset.range ((L+q-1-r)/q), z (m*q+r)‖ ≤ (1 + (L:ℝ) * E) * (2/‖ζ-1‖) := by
      intro r hr
      rw [Finset.mem_range] at hr
      have hb := geom_block_bound ζ z q r ((L+q-1-r)/q) E hζnorm hζ1 hEnn hz1
          (fun m hm => hstep r m hr hm)
      have hML : (((L+q-1-r)/q : ℕ) : ℝ) ≤ (L:ℝ) := by
        have h4 : (L + q - 1 - r)/q ≤ L := by
          by_contra hcon
          have h' : L + 1 ≤ (L + q - 1 - r)/q := by omega
          have h2 : (L+1)*q ≤ L + q - 1 - r :=
            le_trans (Nat.mul_le_mul_right q h') (Nat.div_mul_le_self _ _)
          have h3 : L + q ≤ (L+1)*q := by
            have h5 : (L+1)*q = L*q + q := by ring
            have h6 : L ≤ L * q := by
              simpa using Nat.mul_le_mul_left L (show 1 ≤ q by omega)
            omega
          omega
        exact_mod_cast h4
      have hnn : (0:ℝ) ≤ 2/‖ζ-1‖ := div_nonneg (by norm_num) (norm_nonneg _)
      have hb2 : (0:ℝ) ≤ 1 + (L:ℝ) * E := by nlinarith [hLpos.le, hEnn]
      refine le_trans hb ?_
      apply mul_le_mul _ (min_le_right _ _) (le_min (Nat.cast_nonneg _) hnn) hb2
      nlinarith [hML, hEnn]
    have hSle : ‖∑ n ∈ Finset.range L, z n‖
        ≤ ∑ r ∈ Finset.range q, ‖∑ m ∈ Finset.range ((L + q - 1 - r)/q), z (m*q+r)‖ := by
      rw [sum_range_eq_sum_mod q L hq1 z]
      exact norm_sum_le _ _
    have hsum : ∑ r ∈ Finset.range q, ‖∑ m ∈ Finset.range ((L + q - 1 - r)/q), z (m*q+r)‖
        ≤ (q:ℝ) * ((1 + (L:ℝ) * E) * (2/‖ζ-1‖)) := by
      calc _ ≤ ∑ r ∈ Finset.range q, (1 + (L:ℝ) * E) * (2/‖ζ-1‖) := Finset.sum_le_sum hblock
        _ = (q:ℝ) * ((1 + (L:ℝ) * E) * (2/‖ζ-1‖)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hbig' : δ * (L:ℝ) ≤ ‖∑ n ∈ Finset.range L, z n‖ := hbig
    have hfin : (q:ℝ) * ((1 + (L:ℝ) * E) * (2/‖ζ-1‖)) < δ * (L:ℝ) := by
      rw [hEdef] at *
      exact a_one_bound_final_arith k δ C₀ C C₂ (L:ℝ) (q:ℝ) d ζ hδ hC₀ hC2 hLpos hqnn hqC0 hCdef hd hζsub
    linarith [hSle, hsum, hbig', hfin]

end Work.BMF.SD.FreeA
