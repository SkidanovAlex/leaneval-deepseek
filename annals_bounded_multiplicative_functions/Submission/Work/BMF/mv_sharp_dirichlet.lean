import Mathlib
import Submission.Work.BMF.Defs
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp (log-free) mean square bound for a short Dirichlet polynomial

`Work.BMF.mv_sharp_dirichlet`: for `|a n| ≤ 1/n` and `Y ≥ 4`, `T ≥ 1`,

`∫_{-2T}^{2T} ‖Σ_{Y ≤ n ≤ 3Y} a n · n^{-it}‖² dt ≤ C (T + Y)/Y`.

The proof is the Montgomery–Vaughan large sieve inequality
`Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies`,
applied to the `δ`-separated frequencies `μ n = -log n` with `δ = 1/(3Y)`.
-/

namespace Work.BMF

open MeasureTheory
open scoped BigOperators

/-! ### Helper lemmas -/

/-- The complex power `n^{-it}` of a positive natural number, in exponential form. -/
private lemma cpow_neg_I_eq_exp_log (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp (Complex.I * ((-(Real.log (n : ℝ)) : ℂ) * (t : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    exact_mod_cast (ne_of_gt this)
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  congr 1
  ring

/-- Distinct naturals in `[Y, 3Y]`, `Y ≥ 4`, have `log`-separated values by at least `1/(3Y)`. -/
private lemma log_sep_natIcc {Y : ℝ} (hY : 4 ≤ Y) {m n : ℕ}
    (hm : m ∈ Work.BMF.natIcc Y (3 * Y)) (hn : n ∈ Work.BMF.natIcc Y (3 * Y)) (hmn : m ≠ n) :
    1 / (3 * Y) ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hYpos : 0 < Y := by linarith
  have aux : ∀ {p q : ℕ}, p ∈ Work.BMF.natIcc Y (3 * Y) → q ∈ Work.BMF.natIcc Y (3 * Y) →
      p < q → 1 / (3 * Y) ≤ Real.log (q : ℝ) - Real.log (p : ℝ) := by
    intro p q hp hq hpq
    simp only [Work.BMF.natIcc, Finset.mem_Icc] at hp hq
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hq1, hq2⟩ := hq
    have hp1' : (1 : ℝ) ≤ (p : ℝ) := by
      have h2 : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
      have h3 : ((⌈Y⌉₊ : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
      linarith
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hq_pos : (0 : ℝ) < (q : ℝ) := by
      have h : p + 1 ≤ q := by omega
      have h' : ((p : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast h
      linarith
    have hq3Y : (q : ℝ) ≤ 3 * Y :=
      le_trans (by exact_mod_cast hq2) (Nat.floor_le (by linarith))
    have hpq1 : (1 : ℝ) ≤ (q : ℝ) - (p : ℝ) := by
      have h : p + 1 ≤ q := by omega
      have h' : ((p : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast h
      linarith
    have h1 : (1 : ℝ) - (p : ℝ) / (q : ℝ) ≤ Real.log (q : ℝ) - Real.log (p : ℝ) := by
      have hr : 0 < (p : ℝ) / (q : ℝ) := by positivity
      have h := Real.log_le_sub_one_of_pos hr
      rw [Real.log_div hp_pos.ne' hq_pos.ne'] at h
      linarith
    have h2 : (1 : ℝ) / (3 * Y) ≤ (1 : ℝ) - (p : ℝ) / (q : ℝ) := by
      have heq : (1 : ℝ) - (p : ℝ) / (q : ℝ) = ((q : ℝ) - (p : ℝ)) / (q : ℝ) := by
        rw [sub_div, div_self hq_pos.ne']
      rw [heq]
      have hstep : (1 : ℝ) / (q : ℝ) ≤ ((q : ℝ) - (p : ℝ)) / (q : ℝ) :=
        div_le_div_of_nonneg_right hpq1 (le_of_lt hq_pos)
      have hstep2 : (1 : ℝ) / (3 * Y) ≤ (1 : ℝ) / (q : ℝ) :=
        one_div_le_one_div_of_le hq_pos hq3Y
      linarith
    linarith
  have hYle : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hmpos : (0 : ℝ) < (m : ℝ) := by
      simp only [Work.BMF.natIcc, Finset.mem_Icc] at hm
      have h3 : ((⌈Y⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
      have : (1 : ℝ) ≤ (m : ℝ) := by linarith
      linarith
    have hlt' : Real.log (m : ℝ) < Real.log (n : ℝ) :=
      Real.log_lt_log hmpos (by exact_mod_cast hlt)
    rw [abs_of_neg (by linarith : Real.log (m : ℝ) - Real.log (n : ℝ) < 0)]
    have := aux hm hn hlt
    linarith
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      simp only [Work.BMF.natIcc, Finset.mem_Icc] at hn
      have h3 : ((⌈Y⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have : (1 : ℝ) ≤ (n : ℝ) := by linarith
      linarith
    have hgt' : Real.log (n : ℝ) < Real.log (m : ℝ) :=
      Real.log_lt_log hnpos (by exact_mod_cast hgt)
    rw [abs_of_pos (by linarith : 0 < Real.log (m : ℝ) - Real.log (n : ℝ))]
    exact aux hn hm hgt

/-- The `ℓ²` mass of `a` over `[Y, 3Y]` is `≤ 3/Y` when `‖a n‖ ≤ 1/n`. -/
private lemma sum_normsq_natIcc_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1 / n) {Y : ℝ}
    (hY : 1 ≤ Y) :
    ∑ n ∈ Work.BMF.natIcc Y (3 * Y), ‖a n‖ ^ 2 ≤ 3 / Y := by
  have hYpos : 0 < Y := by linarith
  have hcard : (((Work.BMF.natIcc Y (3 * Y)).card : ℕ) : ℝ) ≤ 2 * Y + 1 := by
    rw [Work.BMF.natIcc, Nat.card_Icc]
    by_cases h : ⌈Y⌉₊ ≤ ⌊3 * Y⌋₊
    · rw [Nat.cast_sub (by omega : ⌈Y⌉₊ ≤ ⌊3 * Y⌋₊ + 1)]
      push_cast
      have h1 : ((⌊3 * Y⌋₊ : ℕ) : ℝ) ≤ 3 * Y := Nat.floor_le (by linarith)
      have h2 : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
      linarith
    · have hle : ⌊3 * Y⌋₊ + 1 ≤ ⌈Y⌉₊ := by omega
      rw [Nat.sub_eq_zero_of_le hle]
      push_cast
      linarith
  have hterm : ∀ n ∈ Work.BMF.natIcc Y (3 * Y), ‖a n‖ ^ 2 ≤ 1 / Y ^ 2 := by
    intro n hn
    simp only [Work.BMF.natIcc, Finset.mem_Icc] at hn
    have hnY : Y ≤ (n : ℝ) := le_trans (Nat.le_ceil Y) (by exact_mod_cast hn.1)
    have hna : ‖a n‖ ≤ 1 / Y := by
      have h1 : ‖a n‖ ≤ 1 / (n : ℝ) := ha n
      have h2 : (1 : ℝ) / (n : ℝ) ≤ 1 / Y := one_div_le_one_div_of_le hYpos hnY
      linarith
    have hsq : ‖a n‖ ^ 2 ≤ (1 / Y) ^ 2 := by
      nlinarith [hna, norm_nonneg (a n), (by positivity : (0:ℝ) ≤ 1 / Y)]
    have heq : (1 / Y) ^ 2 = 1 / Y ^ 2 := by rw [div_pow]; norm_num
    rwa [heq] at hsq
  calc ∑ n ∈ Work.BMF.natIcc Y (3 * Y), ‖a n‖ ^ 2
      ≤ ∑ n ∈ Work.BMF.natIcc Y (3 * Y), 1 / Y ^ 2 := Finset.sum_le_sum hterm
    _ = (((Work.BMF.natIcc Y (3 * Y)).card : ℕ) : ℝ) * (1 / Y ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Y + 1) * (1 / Y ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 3 / Y := by
        have hY2 : (0 : ℝ) < Y ^ 2 := by positivity
        have key : (2 * Y + 1) * (1 / Y ^ 2) * Y ^ 2 ≤ (3 / Y) * Y ^ 2 := by
          have e1 : (2 * Y + 1) * (1 / Y ^ 2) * Y ^ 2 = 2 * Y + 1 := by
            rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hY2), mul_one]
          have e2 : 3 / Y * Y ^ 2 = 3 * Y := by
            rw [div_mul_eq_mul_div, mul_div_assoc,
              show Y ^ 2 / Y = Y by
                rw [pow_two, mul_div_assoc, div_self (ne_of_gt hYpos), mul_one]]
          rw [e1, e2]; nlinarith [hY]
        exact le_of_mul_le_mul_right key hY2

/-! ### The main theorem -/

theorem mv_sharp_dirichlet :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1 / n) →
      ∀ (Y T : ℝ), 4 ≤ Y → 1 ≤ T →
        (∫ t in -(2 * T)..(2 * T),
            ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
          ≤ C * (T + Y) / Y := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨2 * max 12 (9 * C₀), by positivity, ?_⟩
  intro a ha Y T hY hT
  have hYpos : 0 < Y := by linarith
  set e : ↥(Work.BMF.natIcc Y (3 * Y)) ≃ Fin (Work.BMF.natIcc Y (3 * Y)).card :=
    Finset.equivFin (Work.BMF.natIcc Y (3 * Y)) with he
  set b : Fin (Work.BMF.natIcc Y (3 * Y)).card → ℂ :=
    fun i => a (((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) with hb
  set μ : Fin (Work.BMF.natIcc Y (3 * Y)).card → ℝ :=
    fun i => -(Real.log ((((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) : ℝ)) with hmu
  -- separation of the frequencies
  have hsep : ∀ i j : Fin (Work.BMF.natIcc Y (3 * Y)).card, i ≠ j →
      1 / (3 * Y) ≤ |μ i - μ j| := by
    intro i j hij
    have hne : (((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ))
        ≠ (((e.symm j : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) := by
      intro h'
      exact hij (e.symm.injective (Subtype.coe_injective h'))
    have hi : (((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) ∈ Work.BMF.natIcc Y (3 * Y) :=
      (e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))).2
    have hj : (((e.symm j : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) ∈ Work.BMF.natIcc Y (3 * Y) :=
      (e.symm j : ↥(Work.BMF.natIcc Y (3 * Y))).2
    have hkey := log_sep_natIcc hY hi hj hne
    rw [hmu]
    simp only
    rw [show -(Real.log ((((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) : ℝ))
          - -(Real.log ((((e.symm j : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) : ℝ))
        = Real.log ((((e.symm j : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) : ℝ)
          - Real.log ((((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) : ℝ) by ring]
    rw [abs_sub_comm]
    exact hkey
  -- the large sieve, applied at `δ = 1/(3Y)`
  have hls := hC₀ (1 / (3 * Y)) (by positivity) (Work.BMF.natIcc Y (3 * Y)).card μ b hsep
    (-(2 * T)) (2 * T) (by linarith)
  have hcoef : 2 * T - (-(2 * T)) + C₀ / (1 / (3 * Y)) = 4 * T + 3 * C₀ * Y := by
    field_simp
    ring
  -- rewriting the integral in the goal
  have hsum_eq : ∀ t : ℝ,
      (∑ n ∈ Work.BMF.natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ))))
        = ∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card,
            b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ))) := by
    intro t
    have h1 : (∑ n ∈ Work.BMF.natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ))))
        = ∑ x : ↥(Work.BMF.natIcc Y (3 * Y)),
            a ((x : ℕ)) * (((x : ℕ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
      rw [← Finset.sum_attach (Work.BMF.natIcc Y (3 * Y))
            (fun n => a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))),
          ← Finset.univ_eq_attach (Work.BMF.natIcc Y (3 * Y))]
    rw [h1, ← Equiv.sum_comp e.symm
      (fun x : ↥(Work.BMF.natIcc Y (3 * Y)) =>
        a ((x : ℕ)) * (((x : ℕ)) : ℂ) ^ (-(Complex.I * (t : ℂ))))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hb, hmu]
    have hn1 : 1 ≤ (((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) := by
      have hmem : (((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ))
          ∈ Work.BMF.natIcc Y (3 * Y) := (e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))).2
      simp only [Work.BMF.natIcc, Finset.mem_Icc] at hmem
      have h2 : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
      have h3 : ((⌈Y⌉₊ : ℕ) : ℝ)
          ≤ ((((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) : ℝ) := by
        exact_mod_cast hmem.1
      have : (1 : ℝ) ≤ ((((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) : ℝ) := by linarith
      exact_mod_cast this
    rw [cpow_neg_I_eq_exp_log (((e.symm i : ↥(Work.BMF.natIcc Y (3 * Y))) : ℕ)) hn1 t]
    simp only [Complex.ofReal_neg]
  have hint : (∫ t in -(2 * T)..(2 * T),
        ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
      = ∫ t in -(2 * T)..(2 * T),
          ‖∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card,
              b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    show ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
        = ‖∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card,
              b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2
    rw [hsum_eq t]
  -- the `ℓ²` mass
  have hS1 : (∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card, ‖b i‖ ^ 2)
      = ∑ x : ↥(Work.BMF.natIcc Y (3 * Y)), ‖a ((x : ℕ))‖ ^ 2 := by
    rw [← Equiv.sum_comp e.symm (fun x : ↥(Work.BMF.natIcc Y (3 * Y)) => ‖a ((x : ℕ))‖ ^ 2)]
  have hS2 : (∑ x : ↥(Work.BMF.natIcc Y (3 * Y)), ‖a ((x : ℕ))‖ ^ 2)
      = ∑ n ∈ Work.BMF.natIcc Y (3 * Y), ‖a n‖ ^ 2 := by
    rw [Finset.univ_eq_attach (Work.BMF.natIcc Y (3 * Y)),
        Finset.sum_attach (Work.BMF.natIcc Y (3 * Y)) (fun n => ‖a n‖ ^ 2)]
  have hS : (∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card, ‖b i‖ ^ 2)
      = ∑ n ∈ Work.BMF.natIcc Y (3 * Y), ‖a n‖ ^ 2 := hS1.trans hS2
  have hSle : (∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card, ‖b i‖ ^ 2) ≤ 3 / Y := by
    rw [hS]; exact sum_normsq_natIcc_le ha (by linarith)
  have h4T : (0 : ℝ) ≤ 4 * T + 3 * C₀ * Y := by
    have hC₀nn : (0 : ℝ) ≤ C₀ := le_of_lt hC₀pos
    nlinarith [hT, hYpos]
  have hmain : (∫ t in -(2 * T)..(2 * T),
        ‖∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card,
            b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2)
      ≤ (4 * T + 3 * C₀ * Y) * (3 / Y) := by
    refine hls.trans ?_
    rw [hcoef]
    exact mul_le_mul_of_nonneg_left hSle h4T
  rw [hint]
  calc (∫ t in -(2 * T)..(2 * T),
        ‖∑ i : Fin (Work.BMF.natIcc Y (3 * Y)).card,
            b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2)
      ≤ (4 * T + 3 * C₀ * Y) * (3 / Y) := hmain
    _ = 12 * T / Y + 9 * C₀ := by field_simp; ring
    _ ≤ max 12 (9 * C₀) * (T / Y + 1) := by
        have h1 : 12 * T / Y ≤ max 12 (9 * C₀) * (T / Y) := by
          rw [show (12 : ℝ) * T / Y = 12 * (T / Y) by ring]
          exact mul_le_mul_of_nonneg_right (le_max_left 12 (9 * C₀)) (by positivity)
        have h2 : 9 * C₀ ≤ max 12 (9 * C₀) * 1 := by
          have := le_max_right (12 : ℝ) (9 * C₀); linarith
        have hexp : max 12 (9 * C₀) * (T / Y + 1)
            = max 12 (9 * C₀) * (T / Y) + max 12 (9 * C₀) := by ring
        rw [hexp]; linarith
    _ ≤ 2 * max 12 (9 * C₀) * (T + Y) / Y := by
        have hMnn : (0 : ℝ) ≤ max 12 (9 * C₀) := by
          have := le_max_left (12 : ℝ) (9 * C₀); linarith
        have hle : T / Y + 1 ≤ 2 * (T + Y) / Y := by
          have h : 2 * (T + Y) / Y - (T / Y + 1) = (T + Y) / Y := by field_simp; ring
          have hnn : 0 ≤ (T + Y) / Y := by positivity
          linarith
        calc max 12 (9 * C₀) * (T / Y + 1) ≤ max 12 (9 * C₀) * (2 * (T + Y) / Y) :=
              mul_le_mul_of_nonneg_left hle hMnn
          _ = 2 * max 12 (9 * C₀) * (T + Y) / Y := by ring

end Work.BMF
