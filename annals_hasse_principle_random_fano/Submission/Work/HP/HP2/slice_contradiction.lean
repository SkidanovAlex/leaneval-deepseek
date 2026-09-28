import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP2.sliceDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open Finset Polynomial

namespace Work.HP.HP2

/-- The indeterminate `X` over `ℝ`, with the base ring made explicit. -/
abbrev XP : Polynomial ℝ := Polynomial.X

/-! ## Scaling of the Veronese embedding and of the norms -/

lemma veronese_smul {d n : ℕ} (T : ℝ) (u : Fin (n + 1) → ℝ) :
    veronese d n (fun i => T * u i) = fun m => T ^ d * veronese d n u m := by
  funext m
  simp only [veronese]
  rw [Finset.prod_congr rfl (fun i _ => mul_pow T (u i) (m.1 i)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum Finset.univ (fun i => (m.1 i : ℕ)) T,
    show (∑ i : Fin (n + 1), ((m.1 i : Fin (d + 1)) : ℕ)) = d from m.2]

lemma dotR_smul {ι : Type*} [Fintype ι] (T : ℝ) (w t : ι → ℝ) :
    dotR (fun i => T * w i) t = T * dotR w t := by
  rw [dotR, dotR, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma rNorm_smul {ι : Type*} [Fintype ι] (v : ι → ℝ) (c : ℝ) :
    rNorm (fun i => c * v i) = |c| * rNorm v := by
  rw [rNorm, rNorm]
  have h : (∑ i, (c * v i) ^ 2) = c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

lemma rNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ rNorm v := by
  simp only [rNorm]; exact Real.sqrt_nonneg _

/-- The hypothesis of the slice contradiction, available for every `x` (not just in the ball). -/
lemma h_ball_to_all {d n : ℕ} (b : Mon d n → ℝ) (α : ℝ)
    (h : ∀ x : Fin (n + 1) → ℝ, rNorm x ≤ 1 →
      4 * α ^ 2 * (dotR (veronese d n x) b) ^ 2 = (rNorm (veronese d n x)) ^ 2) :
    ∀ x : Fin (n + 1) → ℝ,
      4 * α ^ 2 * (dotR (veronese d n x) b) ^ 2 = (rNorm (veronese d n x)) ^ 2 := by
  intro x
  set T : ℝ := (rNorm x + 1)⁻¹ with hTdef
  have hx1 : (0 : ℝ) < rNorm x + 1 := by linarith [rNorm_nonneg' x]
  have hTpos : 0 < T := by rw [hTdef]; exact inv_pos.mpr hx1
  have hle : rNorm (fun i => T * x i) ≤ 1 := by
    rw [rNorm_smul, abs_of_pos hTpos]
    have hlt : T * rNorm x < 1 := by
      calc T * rNorm x < T * (rNorm x + 1) :=
            mul_lt_mul_of_pos_left (by linarith [rNorm_nonneg' x]) hTpos
        _ = 1 := by rw [hTdef, inv_mul_cancel₀ (ne_of_gt hx1)]
    exact le_of_lt hlt
  have hh := h (fun i => T * x i) hle
  have hh1 : dotR (veronese d n (fun i => T * x i)) b = T ^ d * dotR (veronese d n x) b := by
    rw [veronese_smul T x]; exact dotR_smul (T ^ d) (veronese d n x) b
  have hh2 : rNorm (veronese d n (fun i => T * x i)) = T ^ d * rNorm (veronese d n x) := by
    rw [veronese_smul T x, rNorm_smul, abs_of_nonneg (pow_nonneg hTpos.le d)]
  rw [hh1, hh2, mul_pow, mul_pow] at hh
  have hTd : (T ^ d) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero d (ne_of_gt hTpos))
  have h2 : (T ^ d) ^ 2 * (4 * α ^ 2 * (dotR (veronese d n x) b) ^ 2)
      = (T ^ d) ^ 2 * (rNorm (veronese d n x)) ^ 2 := by
    rw [← hh]; ring
  exact mul_left_cancel₀ hTd h2

/-! ## The algebraic core -/

lemma eq_C_of_dvd_X_pow {p : Polynomial ℝ} (h0 : p.coeff 0 ≠ 0) :
    ∀ n : ℕ, p ∣ XP ^ n → ∃ a : ℝ, p = Polynomial.C a := by
  intro n
  induction n with
  | zero =>
      intro h
      obtain ⟨q, hq⟩ := h
      have hu : IsUnit p := isUnit_of_dvd_one ⟨q, by simpa using hq⟩
      obtain ⟨a, ha⟩ := Polynomial.isUnit_iff.mp hu
      exact ⟨a, ha.2.symm⟩
  | succ n ih =>
      intro h
      obtain ⟨q, hq⟩ := h
      have hp_not : ¬ XP ∣ p := by
        rw [Polynomial.X_dvd_iff]; exact h0
      have hXq : XP ∣ q := by
        have hX : XP ∣ p * q := by
          refine ⟨XP ^ n, ?_⟩
          rw [← hq, pow_succ']
        rcases Polynomial.prime_X.dvd_or_dvd hX with h1 | h1
        · exact absurd h1 hp_not
        · exact h1
      obtain ⟨q₁, hq₁⟩ := hXq
      have hXn : XP ^ n = p * q₁ := by
        have h1 : XP ^ (n + 1) = XP * (p * q₁) := by rw [hq, hq₁]; ring
        have h2 : XP ^ (n + 1) = XP * XP ^ n := pow_succ' _ _
        rw [h2] at h1
        exact mul_left_cancel₀ Polynomial.monic_X.ne_zero h1
      exact ih ⟨q₁, hXn⟩

lemma poly_not_sq (d : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc : c ≠ 0) (p : Polynomial ℝ)
    (hp : Polynomial.C c * p ^ 2 = ∑ k : Fin (d + 1), XP ^ (2 * (k : ℕ))) : False := by
  rw [Fin.sum_univ_eq_sum_range (fun k => XP ^ (2 * k)) (d + 1)] at hp
  set Rg : Polynomial ℝ := ∑ k ∈ Finset.range (d + 1), XP ^ (2 * k) with hRdef
  have hpC : Polynomial.C c * p ^ 2 = Rg := by rw [hRdef]; exact hp
  have htel : (XP ^ 2 - 1) * Rg = XP ^ (2 * d + 2) - 1 := by
    rw [hRdef]
    calc (XP ^ 2 - 1) * (∑ k ∈ Finset.range (d + 1), XP ^ (2 * k))
        = ∑ k ∈ Finset.range (d + 1), (XP ^ 2 - 1) * XP ^ (2 * k) := by
          rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range (d + 1), (XP ^ (2 * (k + 1)) - XP ^ (2 * k)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [sub_mul, one_mul, ← pow_add, show 2 + 2 * k = 2 * (k + 1) from by ring]
      _ = XP ^ (2 * (d + 1)) - XP ^ (2 * 0) :=
          Finset.sum_range_sub (fun k => XP ^ (2 * k)) (d + 1)
      _ = XP ^ (2 * d + 2) - 1 := by
          rw [show 2 * (d + 1) = 2 * d + 2 from by ring]; simp
  have hdp2 : Polynomial.derivative (p ^ 2) = Polynomial.C (2 : ℝ) * p * Polynomial.derivative p := by
    rw [Polynomial.derivative_pow, pow_one, Nat.cast_two]
  have hLHS : Polynomial.derivative ((XP ^ 2 - 1) * Rg)
      = (Polynomial.C 2 * XP) * Rg + (XP ^ 2 - 1) * Polynomial.derivative Rg := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
      Polynomial.derivative_X_sq]
  have hRHS : Polynomial.derivative (XP ^ (2 * d + 2) - 1)
      = Polynomial.C (((2 * d + 1 : ℕ) : ℝ) + 1) * XP ^ (2 * d + 1) := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
      show (XP : Polynomial ℝ) ^ (2 * d + 2) = XP ^ ((2 * d + 1) + 1) from by
        rw [show (2 * d + 2 : ℕ) = (2 * d + 1) + 1 from by ring],
      Polynomial.derivative_X_pow_succ (2 * d + 1)]
  have hder : (Polynomial.C 2 * XP) * Rg + (XP ^ 2 - 1) * Polynomial.derivative Rg
      = Polynomial.C (((2 * d + 1 : ℕ) : ℝ) + 1) * XP ^ (2 * d + 1) := by
    rw [← hLHS, ← hRHS]
    exact congrArg Polynomial.derivative htel
  have hR : p ∣ Rg := ⟨Polynomial.C c * p, by rw [← hpC]; ring⟩
  have hRp : p ∣ Polynomial.derivative Rg := by
    refine ⟨Polynomial.C c * Polynomial.C (2 : ℝ) * Polynomial.derivative p, ?_⟩
    rw [← hpC, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add, hdp2]
    ring
  have hdvd : p ∣ (Polynomial.C 2 * XP) * Rg + (XP ^ 2 - 1) * Polynomial.derivative Rg := by
    have h1 : p ∣ (Polynomial.C 2 * XP) * Rg := by
      obtain ⟨q, hq⟩ := hR
      exact ⟨Polynomial.C 2 * XP * q, by rw [hq]; ring⟩
    have h2 : p ∣ (XP ^ 2 - 1) * Polynomial.derivative Rg := by
      obtain ⟨q, hq⟩ := hRp
      exact ⟨(XP ^ 2 - 1) * q, by rw [hq]; ring⟩
    exact dvd_add h1 h2
  rw [hder] at hdvd
  have hK : (((2 * d + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  have hunit : IsUnit (Polynomial.C (((2 * d + 1 : ℕ) : ℝ) + 1)) :=
    Polynomial.isUnit_C.mpr hK.isUnit
  have hdvdX : p ∣ XP ^ (2 * d + 1) := hunit.dvd_mul_left.mp hdvd
  have hXR : ¬ XP ∣ Rg := by
    intro hx
    have h1 : XP ∣ XP ^ (2 * d + 2) := ⟨XP ^ (2 * d + 1), by rw [pow_succ']⟩
    have h2 : XP ∣ XP ^ (2 * d + 2) - 1 := by
      rw [← htel]
      exact dvd_mul_of_dvd_right hx _
    have h3 : IsUnit XP := by
      refine isUnit_of_dvd_one ?_
      have hd := dvd_sub h1 h2
      have heq : XP ^ (2 * d + 2) - (XP ^ (2 * d + 2) - 1) = 1 := by ring
      rwa [heq] at hd
    exact Polynomial.prime_X.not_unit h3
  have hp0 : p.coeff 0 ≠ 0 := by
    intro h0
    have hXp : (Polynomial.X : Polynomial ℝ) ∣ p := Polynomial.X_dvd_iff.mpr h0
    refine hXR ?_
    rw [← hpC]
    have hpp : XP ∣ p * p := dvd_mul_of_dvd_left hXp p
    simpa [pow_two] using dvd_mul_of_dvd_right hpp (Polynomial.C c)
  obtain ⟨a, ha⟩ := eq_C_of_dvd_X_pow hp0 (2 * d + 1) hdvdX
  have hR2 : Rg.coeff 2 = 0 := by
    rw [← hpC, ha]
    have hC : Polynomial.C c * (Polynomial.C a) ^ 2 = Polynomial.C (c * a ^ 2) := by
      rw [← Polynomial.C_pow, ← Polynomial.C_mul]
    rw [hC, Polynomial.coeff_C]
    simp
  have hR2' : Rg.coeff 2 = 1 := by
    have hcoeff : Rg.coeff 2 = ∑ k ∈ Finset.range (d + 1), (XP ^ (2 * k)).coeff 2 := by
      rw [hRdef]
      exact map_sum (Polynomial.lcoeff ℝ 2) (fun k => XP ^ (2 * k)) (Finset.range (d + 1))
    rw [hcoeff, Finset.sum_eq_single (1 : ℕ)]
    · rw [Polynomial.coeff_X_pow]; simp
    · intro k _ hk
      rw [Polynomial.coeff_X_pow, if_neg]
      intro hc
      exact hk (by omega)
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hR2] at hR2'
  exact zero_ne_one hR2'

/-! ## The slice contradiction -/

theorem slice_contradiction (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (b : Mon d n → ℝ) (α : ℝ) (hb : rNorm b = 1) (hα : α ≠ 0)
    (h : ∀ x : Fin (n + 1) → ℝ, rNorm x ≤ 1 →
      4 * α ^ 2 * (dotR (veronese d n x) b) ^ 2 = (rNorm (veronese d n x)) ^ 2) : False := by
  have hAll := h_ball_to_all b α h
  set P : Polynomial ℝ := ∑ k : Fin (d + 1), Polynomial.C (b (sliceMon d n hn k)) * XP ^ (k : ℕ) with hP
  set Q : Polynomial ℝ := ∑ k : Fin (d + 1), XP ^ (2 * (k : ℕ)) with hQ
  have hPQ : Polynomial.C (4 * α ^ 2) * P ^ 2 = Q := by
    apply Polynomial.funext
    intro t
    have hPev : P.eval t = ∑ k : Fin (d + 1), b (sliceMon d n hn k) * t ^ (k : ℕ) := by
      rw [hP]; simp [Polynomial.eval_finsetSum]
    have hQev : Q.eval t = ∑ k : Fin (d + 1), t ^ (2 * (k : ℕ)) := by
      rw [hQ]; simp [Polynomial.eval_finsetSum]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, hPev, hQev,
      ← dotR_veronese_slice d n hn t b, hAll (slicePt n t), rNorm_veronese_slice d n hn t]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.mul_comm 2 (k : ℕ), pow_mul]
  have hc : 4 * α ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hα)
  refine poly_not_sq d hd (4 * α ^ 2) hc P ?_
  rw [hPQ, hQ]

end Work.HP.HP2
