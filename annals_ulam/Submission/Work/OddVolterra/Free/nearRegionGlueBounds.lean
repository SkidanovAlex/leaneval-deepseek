import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup

namespace Work.OddVolterra.Free

open scoped Topology ContDiff

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

/-! ## Elementary bounds -/

private lemma pow_sub_one_abs_le {p e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) (hp : |p - 1| ≤ e)
    (m : ℕ) : |p ^ m - 1| ≤ 2 ^ m * e := by
  have hp2 : |p| ≤ 2 := by
    have h1 : |p| ≤ |p - 1| + |(1:ℝ)| := by
      calc |p| = |(p - 1) + 1| := by ring_nf
        _ ≤ |p - 1| + |(1:ℝ)| := abs_add_le _ _
    rw [abs_one] at h1
    linarith
  have key : ∀ m, |p ^ m - 1| ≤ ((2:ℝ)^m - 1) * e := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have hstep : p ^ (k+1) - 1 = p * (p ^ k - 1) + (p - 1) := by ring
      have h4 : 0 ≤ (((2:ℝ)^k - 1) * e) := by
        have : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
        exact mul_nonneg (by linarith) he
      have h2 : |p * (p^k - 1)| ≤ 2 * (((2:ℝ)^k - 1) * e) := by
        rw [abs_mul]
        exact mul_le_mul hp2 ih (abs_nonneg _) (by norm_num)
      calc |p^(k+1) - 1| = |p * (p^k - 1) + (p-1)| := by rw [hstep]
        _ ≤ |p * (p^k-1)| + |p - 1| := abs_add_le _ _
        _ ≤ 2 * (((2:ℝ)^k - 1)*e) + e := by linarith
        _ = ((2:ℝ)^(k+1) - 1) * e := by ring
  have hbound : ((2:ℝ)^m - 1) * e ≤ 2^m * e := by
    apply mul_le_mul_of_nonneg_right _ he
    have : (1:ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
    linarith
  exact (key m).trans hbound

private lemma abs_pow_le {p : ℝ} (hp : |p| ≤ 2) (m : ℕ) : |p ^ m| ≤ 2 ^ m := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hp m

private lemma abs_mul_le_mul {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  have hA : (0:ℝ) ≤ A := le_trans (abs_nonneg a) ha
  rw [abs_mul]; gcongr

private lemma abs_mul3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C := by
  have hA : (0:ℝ) ≤ A := le_trans (abs_nonneg a) ha
  have hB : (0:ℝ) ≤ B := le_trans (abs_nonneg b) hb
  have hC : (0:ℝ) ≤ C := le_trans (abs_nonneg c) hc
  rw [abs_mul, abs_mul]; gcongr

private lemma abs_mul4_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) : |a * b * c * d| ≤ A * B * C * D := by
  have hA : (0:ℝ) ≤ A := le_trans (abs_nonneg a) ha
  have hB : (0:ℝ) ≤ B := le_trans (abs_nonneg b) hb
  have hC : (0:ℝ) ≤ C := le_trans (abs_nonneg c) hc
  have hD : (0:ℝ) ≤ D := le_trans (abs_nonneg d) hd
  rw [abs_mul, abs_mul, abs_mul]; gcongr

private lemma mul_pow_le_K (n : ℕ) {c : ℝ} {j : ℕ} (hc : c ≤ (2*(n:ℝ)+4)^3)
    (hj : j ≤ 2*n+4) :
    c * 2^j ≤ (2*(n:ℝ)+4)^3 * (2:ℝ)^(2*n+4) + 1 := by
  have h2 : (2:ℝ)^j ≤ (2:ℝ)^(2*n+4) := pow_le_pow_right₀ (by norm_num) hj
  have h3 : (0:ℝ) ≤ (2:ℝ)^(2*n+4) := by positivity
  have h4 : (0:ℝ) ≤ (2*(n:ℝ)+4)^3 := by positivity
  calc c * 2^j ≤ (2*(n:ℝ)+4)^3 * (2:ℝ)^(2*n+4) := mul_le_mul hc h2 (by positivity) h4
    _ ≤ _ + 1 := by linarith

/-! ## Numerical constants fitting under `K` -/

private lemma two_mul_two_n_add_two_le (n : ℕ) : 2 * (↑(2*n+2) : ℝ) ≤ (2*(n:ℝ)+4)^3 := by
  have hcast : (↑(2*n+2) : ℝ) = 2*(n:ℝ)+2 := by push_cast; ring
  rw [hcast]
  have h1 : 2*(2*(n:ℝ)+2) ≤ (2*(n:ℝ)+4)^2 := by
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n:ℝ)]
  have h2 : (2*(n:ℝ)+4)^2 ≤ (2*(n:ℝ)+4)^3 :=
    pow_le_pow_right₀ (by have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith) (by norm_num)
  linarith

private lemma two_mul_two_n_add_one_le (n : ℕ) : 2 * (↑(2*n+1) : ℝ) ≤ (2*(n:ℝ)+4)^3 := by
  have hcast : (↑(2*n+1) : ℝ) = 2*(n:ℝ)+1 := by push_cast; ring
  rw [hcast]
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n:ℝ)]

private lemma three_sq_two_n_add_two_le (n : ℕ) : 3 * (2*(n:ℝ)+2)^2 ≤ (2*(n:ℝ)+4)^3 := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n:ℝ)]

private lemma three_sq_two_n_add_one_le (n : ℕ) : 3 * (2*(n:ℝ)+1)^2 ≤ (2*(n:ℝ)+4)^3 := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n:ℝ)]

private lemma four_le_cube (n : ℕ) : (4:ℝ) ≤ (2*(n:ℝ)+4)^3 := by
  have hx : (1:ℝ) ≤ 2*(n:ℝ)+4 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
  have h1 : (2*(n:ℝ)+4)^1 ≤ (2*(n:ℝ)+4)^3 := pow_le_pow_right₀ hx (by norm_num)
  simp only [pow_one] at h1
  have h4 : (4:ℝ) ≤ 2*(n:ℝ)+4 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
  linarith

/-! ## Derivative bookkeeping for the two composed functions -/

private lemma hasDerivAt_rho_cos {ρ : ℝ → ℝ} {α : ℝ}
    (h : DifferentiableAt ℝ ρ (Real.cos α)) :
    HasDerivAt (fun β : ℝ => ρ (Real.cos β)) (deriv ρ (Real.cos α) * (-Real.sin α)) α := by
  have h2 : HasDerivAt (ρ ∘ Real.cos) (deriv ρ (Real.cos α) * (-Real.sin α)) α :=
    (h.hasDerivAt).comp α (Real.hasDerivAt_cos α)
  simpa [Function.comp_def] using h2

private lemma hasDerivAt_rho_negcos {ρ : ℝ → ℝ} {α : ℝ}
    (h : DifferentiableAt ℝ ρ (-Real.cos α)) :
    HasDerivAt (fun β : ℝ => ρ (-Real.cos β)) (deriv ρ (-Real.cos α) * Real.sin α) α := by
  have h2 : HasDerivAt (ρ ∘ (-Real.cos)) (deriv ρ (-Real.cos α) * (-(-Real.sin α))) α :=
    (h.hasDerivAt).comp α (Real.hasDerivAt_cos α).neg
  simpa [Function.comp_def, Pi.neg_apply] using h2

private lemma hasDerivAt_rho_cos_pow {ρ : ℝ → ℝ} {α : ℝ} (m : ℕ)
    (h : DifferentiableAt ℝ ρ (Real.cos α)) :
    HasDerivAt (fun β : ℝ => ρ (Real.cos β) ^ m)
      ((m:ℝ) * ρ (Real.cos α) ^ (m-1) * (deriv ρ (Real.cos α) * (-Real.sin α))) α := by
  have h2 := hasDerivAt_rho_cos h
  have h5 : HasDerivAt (fun u : ℝ => u ^ m) ((m:ℝ) * (ρ (Real.cos α))^(m-1))
      (ρ (Real.cos α)) := by
    simpa using hasDerivAt_pow m (ρ (Real.cos α))
  simpa [Function.comp_def, mul_assoc] using h5.comp α h2

private lemma hasDerivAt_rho_negcos_pow {ρ : ℝ → ℝ} {α : ℝ} (m : ℕ)
    (h : DifferentiableAt ℝ ρ (-Real.cos α)) :
    HasDerivAt (fun β : ℝ => ρ (-Real.cos β) ^ m)
      ((m:ℝ) * ρ (-Real.cos α) ^ (m-1) * (deriv ρ (-Real.cos α) * Real.sin α)) α := by
  have h2 := hasDerivAt_rho_negcos h
  have h5 : HasDerivAt (fun u : ℝ => u ^ m) ((m:ℝ) * (ρ (-Real.cos α))^(m-1))
      (ρ (-Real.cos α)) := by
    simpa using hasDerivAt_pow m (ρ (-Real.cos α))
  simpa [Function.comp_def, mul_assoc] using h5.comp α h2

private lemma hasDerivAt_derivRho_cos {ρ : ℝ → ℝ} {α : ℝ}
    (h : DifferentiableAt ℝ (deriv ρ) (Real.cos α)) :
    HasDerivAt (fun β : ℝ => deriv ρ (Real.cos β))
      (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) α := by
  have h2 : HasDerivAt ((deriv ρ) ∘ Real.cos) (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) α :=
    (h.hasDerivAt).comp α (Real.hasDerivAt_cos α)
  simpa [Function.comp_def] using h2

private lemma hasDerivAt_derivRho_negcos {ρ : ℝ → ℝ} {α : ℝ}
    (h : DifferentiableAt ℝ (deriv ρ) (-Real.cos α)) :
    HasDerivAt (fun β : ℝ => deriv ρ (-Real.cos β))
      (deriv (deriv ρ) (-Real.cos α) * Real.sin α) α := by
  have h2 : HasDerivAt ((deriv ρ) ∘ (-Real.cos))
      (deriv (deriv ρ) (-Real.cos α) * (-(-Real.sin α))) α :=
    (h.hasDerivAt).comp α (Real.hasDerivAt_cos α).neg
  simpa [Function.comp_def, Pi.neg_apply] using h2

/-- The explicit first derivative of `α ↦ ρ(cos α)^(2n+2) + ρ(-cos α)^(2n+2) - 2`. -/
private def Flat (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun β => ((↑(2*n+2) : ℝ) * Real.sin β) *
    (ρ (-Real.cos β) ^ (2*n+2-1) * deriv ρ (-Real.cos β)
      - ρ (Real.cos β) ^ (2*n+2-1) * deriv ρ (Real.cos β))

/-- The explicit first derivative of `α ↦ ρ(cos α)^(2n+1) - ρ(-cos α)^(2*n+1)`. -/
private def Hlat (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun β => -(((↑(2*n+1) : ℝ) * Real.sin β) *
    (ρ (Real.cos β) ^ (2*n+1-1) * deriv ρ (Real.cos β)
      + ρ (-Real.cos β) ^ (2*n+1-1) * deriv ρ (-Real.cos β)))

/-- **Bounds near the equator for the glue function.**
Given a smooth `ρ` on `(-1,1)` which is within `C₁ ε` of the constant function `1` in value and in
its first two derivatives on `|u| < 4/5`, the two functions
`ρ(cos α)^{2n+2} + ρ(-cos α)^{2n+2} - 2` and `ρ(cos α)^{2n+1} - ρ(-cos α)^{2n+1}`, together with
their first two derivatives, are bounded by `K (C₁+1) ε` for `|cos α| < 4/5`. -/
theorem nearRegionGlueBounds (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ε C₁ : ℝ} {ρ : ℝ → ℝ} {α : ℝ},
      0 < ε → C₁ * ε ≤ 1 →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1) →
      (∀ u : ℝ, |u| < 4 / 5 →
        |ρ u - 1| ≤ C₁ * ε ∧ |deriv ρ u| ≤ C₁ * ε ∧ |deriv (deriv ρ) u| ≤ C₁ * ε) →
      |Real.cos α| < 4 / 5 →
      |ρ (Real.cos α) ^ (2 * n + 2) + ρ (-Real.cos α) ^ (2 * n + 2) - 2| ≤ K * (C₁ + 1) * ε ∧
      |ρ (Real.cos α) ^ (2 * n + 1) - ρ (-Real.cos α) ^ (2 * n + 1)| ≤ K * (C₁ + 1) * ε ∧
      |deriv (fun α : ℝ => ρ (Real.cos α) ^ (2 * n + 2) + ρ (-Real.cos α) ^ (2 * n + 2) - 2) α|
        ≤ K * (C₁ + 1) * ε ∧
      |deriv (deriv (fun α : ℝ => ρ (Real.cos α) ^ (2 * n + 2) + ρ (-Real.cos α) ^ (2 * n + 2) - 2)) α|
        ≤ K * (C₁ + 1) * ε ∧
      |deriv (fun α : ℝ => ρ (Real.cos α) ^ (2 * n + 1) - ρ (-Real.cos α) ^ (2 * n + 1)) α|
        ≤ K * (C₁ + 1) * ε ∧
      |deriv (deriv (fun α : ℝ => ρ (Real.cos α) ^ (2 * n + 1) - ρ (-Real.cos α) ^ (2 * n + 1))) α|
        ≤ K * (C₁ + 1) * ε := by
  let K : ℝ := (2 * (n:ℝ) + 4)^3 * (2:ℝ)^(2*n+4) + 1
  have hKpos : 0 < K := by
    have hh : (0:ℝ) < (2 * (n:ℝ) + 4)^3 * (2:ℝ)^(2*n+4) + 1 := by positivity
    exact hh
  have hKnn : (0:ℝ) ≤ K := le_of_lt hKpos
  refine ⟨K, hKpos, ?_⟩
  intro ε C₁ ρ α hε hC1 hρ hbnd hcos
  have hρdiffOn : DifferentiableOn ℝ ρ (Set.Ioo (-1:ℝ) 1) := hρ.differentiableOn (by simp)
  have hρ'sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv ρ) (Set.Ioo (-1:ℝ) 1) :=
    hρ.deriv_of_isOpen isOpen_Ioo (le_refl _)
  have hρ'diffOn : DifferentiableOn ℝ (deriv ρ) (Set.Ioo (-1:ℝ) 1) :=
    hρ'sm.differentiableOn (by simp)
  obtain ⟨hcl, hcr⟩ := abs_lt.mp hcos
  have ha : Real.cos α ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hb : -Real.cos α ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hρa : DifferentiableAt ℝ ρ (Real.cos α) :=
    hρdiffOn.differentiableAt (isOpen_Ioo.mem_nhds ha)
  have hρb : DifferentiableAt ℝ ρ (-Real.cos α) :=
    hρdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hb)
  have hρ'a : DifferentiableAt ℝ (deriv ρ) (Real.cos α) :=
    hρ'diffOn.differentiableAt (isOpen_Ioo.mem_nhds ha)
  have hρ'b : DifferentiableAt ℝ (deriv ρ) (-Real.cos α) :=
    hρ'diffOn.differentiableAt (isOpen_Ioo.mem_nhds hb)
  obtain ⟨hA1, hA2, hA3⟩ := hbnd (Real.cos α) hcos
  obtain ⟨hB1, hB2, hB3⟩ := hbnd (-Real.cos α) (by rwa [abs_neg])
  have he0 : 0 ≤ C₁ * ε := le_trans (abs_nonneg _) (hbnd 0 (by norm_num)).1
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpA : |ρ (Real.cos α)| ≤ 2 := by
    have h : |ρ (Real.cos α) - 1 + 1| ≤ |ρ (Real.cos α) - 1| + |(1:ℝ)| := abs_add_le _ _
    rw [sub_add_cancel, abs_one] at h
    linarith
  have hpB : |ρ (-Real.cos α)| ≤ 2 := by
    have h : |ρ (-Real.cos α) - 1 + 1| ≤ |ρ (-Real.cos α) - 1| + |(1:ℝ)| := abs_add_le _ _
    rw [sub_add_cancel, abs_one] at h
    linarith
  have hsinc : |Real.cos α| ≤ 1 := Real.abs_cos_le_one α
  have hsin : |Real.sin α| ≤ 1 := Real.abs_sin_le_one α
  have hneg : |-Real.sin α| ≤ 1 := by rw [abs_neg]; exact hsin
  have hconv : K * (C₁*ε) ≤ K * (C₁+1) * ε := by
    have h1 : C₁*ε ≤ (C₁+1)*ε := by nlinarith [hε]
    calc K * (C₁*ε) ≤ K * ((C₁+1)*ε) := mul_le_mul_of_nonneg_left h1 hKnn
      _ = K * (C₁+1) * ε := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) value bound for the `2n+2` composition
    have hmain : |ρ (Real.cos α) ^ (2*n+2) + ρ (-Real.cos α) ^ (2*n+2) - 2| ≤ K * (C₁*ε) := by
      have heq : ρ (Real.cos α) ^ (2*n+2) + ρ (-Real.cos α) ^ (2*n+2) - 2
          = (ρ (Real.cos α) ^ (2*n+2) - 1) + (ρ (-Real.cos α) ^ (2*n+2) - 1) := by ring
      rw [heq]
      calc |(ρ (Real.cos α) ^ (2*n+2) - 1) + (ρ (-Real.cos α) ^ (2*n+2) - 1)|
          ≤ |ρ (Real.cos α) ^ (2*n+2) - 1| + |ρ (-Real.cos α) ^ (2*n+2) - 1| := abs_add_le _ _
        _ ≤ 2^(2*n+2) * (C₁*ε) + 2^(2*n+2) * (C₁*ε) :=
              add_le_add (pow_sub_one_abs_le he0 hC1 hA1 (2*n+2))
                (pow_sub_one_abs_le he0 hC1 hB1 (2*n+2))
        _ = 2^(2*n+2) * (C₁*ε) * 2 := by ring
        _ ≤ 4 * 2^(2*n+2) * (C₁*ε) := by
              have hnn : (0:ℝ) ≤ 2^(2*n+2) * (C₁*ε) := mul_nonneg (by positivity) he0
              nlinarith
        _ ≤ K * (C₁*ε) := by
              have := mul_pow_le_K n (c := 4) (j := 2*n+2) (four_le_cube n) (by omega)
              exact mul_le_mul_of_nonneg_right (by simpa [K] using this) he0
    exact hmain.trans hconv
  · -- (2) value bound for the `2n+1` composition
    have hmain : |ρ (Real.cos α) ^ (2*n+1) - ρ (-Real.cos α) ^ (2*n+1)| ≤ K * (C₁*ε) := by
      have heq : ρ (Real.cos α) ^ (2*n+1) - ρ (-Real.cos α) ^ (2*n+1)
          = (ρ (Real.cos α) ^ (2*n+1) - 1) - (ρ (-Real.cos α) ^ (2*n+1) - 1) := by ring
      rw [heq, sub_eq_add_neg]
      calc |(ρ (Real.cos α) ^ (2*n+1) - 1) + -((ρ (-Real.cos α)) ^ (2*n+1) - 1)|
          ≤ |ρ (Real.cos α) ^ (2*n+1) - 1| + |-((ρ (-Real.cos α)) ^ (2*n+1) - 1)| :=
              abs_add_le _ _
        _ = |ρ (Real.cos α) ^ (2*n+1) - 1| + |ρ (-Real.cos α) ^ (2*n+1) - 1| := by rw [abs_neg]
        _ ≤ 2^(2*n+1) * (C₁*ε) + 2^(2*n+1) * (C₁*ε) :=
              add_le_add (pow_sub_one_abs_le he0 hC1 hA1 (2*n+1))
                (pow_sub_one_abs_le he0 hC1 hB1 (2*n+1))
        _ = 2^(2*n+1) * (C₁*ε) * 2 := by ring
        _ ≤ 4 * 2^(2*n+1) * (C₁*ε) := by
              have hnn : (0:ℝ) ≤ 2^(2*n+1) * (C₁*ε) := mul_nonneg (by positivity) he0
              nlinarith
        _ ≤ K * (C₁*ε) := by
              have := mul_pow_le_K n (c := 4) (j := 2*n+1) (four_le_cube n) (by omega)
              exact mul_le_mul_of_nonneg_right (by simpa [K] using this) he0
    exact hmain.trans hconv
  · -- (3) first derivative of the `2n+2` composition
    have hdf : HasDerivAt (fun β : ℝ => ρ (Real.cos β) ^ (2*n+2) + ρ (-Real.cos β) ^ (2*n+2) - 2)
        ((↑(2*n+2) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1) * (deriv ρ (Real.cos α) * (-Real.sin α))
         + (↑(2*n+2) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1)
             * (deriv ρ (-Real.cos α) * Real.sin α)) α := by
      have h := ((hasDerivAt_rho_cos_pow (2*n+2) hρa).add
        (hasDerivAt_rho_negcos_pow (2*n+2) hρb)).sub_const 2
      simpa using h
    rw [hdf.deriv]
    have hbnd3 : |(↑(2*n+2) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1) * (deriv ρ (Real.cos α) * -Real.sin α)
        + (↑(2*n+2) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1)
            * (deriv ρ (-Real.cos α) * Real.sin α)| ≤ K * (C₁*ε) := by
      have hT1 : |(↑(2*n+2) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1)
            * (deriv ρ (Real.cos α) * -Real.sin α)|
          ≤ (↑(2*n+2) : ℝ) * 2^(2*n+2-1) * (C₁*ε) := by
        have h1 : |(↑(2*n+2) : ℝ)| ≤ (↑(2*n+2) : ℝ) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have h4 : |deriv ρ (Real.cos α) * -Real.sin α| ≤ C₁*ε := by
          have := abs_mul_le_mul hA2 hneg; simpa using this
        exact abs_mul3_le h1 (abs_pow_le hpA (2*n+2-1)) h4
      have hT2 : |(↑(2*n+2) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1)
            * (deriv ρ (-Real.cos α) * Real.sin α)|
          ≤ (↑(2*n+2) : ℝ) * 2^(2*n+2-1) * (C₁*ε) := by
        have h1 : |(↑(2*n+2) : ℝ)| ≤ (↑(2*n+2) : ℝ) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have h4 : |deriv ρ (-Real.cos α) * Real.sin α| ≤ C₁*ε := by
          have := abs_mul_le_mul hB2 hsin; simpa using this
        exact abs_mul3_le h1 (abs_pow_le hpB (2*n+2-1)) h4
      calc |(↑(2*n+2) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1) * (deriv ρ (Real.cos α) * -Real.sin α)
            + (↑(2*n+2) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1)
                * (deriv ρ (-Real.cos α) * Real.sin α)|
          ≤ |(↑(2*n+2) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1) * (deriv ρ (Real.cos α) * -Real.sin α)|
            + |(↑(2*n+2) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1)
                * (deriv ρ (-Real.cos α) * Real.sin α)| := abs_add_le _ _
        _ ≤ (↑(2*n+2) : ℝ) * 2^(2*n+2-1) * (C₁*ε)
            + (↑(2*n+2) : ℝ) * 2^(2*n+2-1) * (C₁*ε) := add_le_add hT1 hT2
        _ = (2 * (↑(2*n+2) : ℝ)) * 2^(2*n+2-1) * (C₁*ε) := by ring
        _ ≤ K * (C₁*ε) := by
              have := mul_pow_le_K n (c := 2 * (↑(2*n+2) : ℝ)) (j := 2*n+2-1)
                (two_mul_two_n_add_two_le n) (by omega)
              exact mul_le_mul_of_nonneg_right (by simpa [K] using this) he0
    exact hbnd3.trans hconv
  · -- (4) second derivative of the `2n+2` composition
    have hU : ∀ᶠ β in 𝓝 α, Real.cos β ∈ Set.Ioo (-1:ℝ) 1 := by
      have hmem : Set.Ioo (-1:ℝ) 1 ∈ 𝓝 (Real.cos α) := isOpen_Ioo.mem_nhds ha
      exact Real.continuous_cos.continuousAt.preimage_mem_nhds hmem
    have hev : deriv (fun γ : ℝ => ρ (Real.cos γ) ^ (2*n+2) + ρ (-Real.cos γ) ^ (2*n+2) - 2)
        =ᶠ[𝓝 α] Flat n ρ := by
      filter_upwards [hU] with β hβ
      have hbβ : -Real.cos β ∈ Set.Ioo (-1:ℝ) 1 := by
        obtain ⟨h1, h2⟩ := hβ; exact ⟨by linarith, by linarith⟩
      have h3 : HasDerivAt
          (fun γ : ℝ => ρ (Real.cos γ) ^ (2*n+2) + ρ (-Real.cos γ) ^ (2*n+2) - 2)
          (Flat n ρ β) β := by
        have h := ((hasDerivAt_rho_cos_pow (2*n+2)
            (hρdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hβ))).add
          (hasDerivAt_rho_negcos_pow (2*n+2)
            (hρdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hbβ)))).sub_const 2
        refine h.congr_deriv ?_
        simp only [Flat]; ring
      exact h3.deriv
    have hFhas : HasDerivAt (Flat n ρ)
        ((↑(2*n+2) : ℝ) * Real.cos α *
            (ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
              - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))
          + (↑(2*n+2) : ℝ) * Real.sin α *
            ( ( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )
              - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) ) )) α := by
      have h1a := hasDerivAt_rho_cos_pow (2*n+2-1) hρa
      have h1b := hasDerivAt_rho_negcos_pow (2*n+2-1) hρb
      have h2a := hasDerivAt_derivRho_cos hρ'a
      have h2b := hasDerivAt_derivRho_negcos hρ'b
      have hP := h1a.mul h2a
      have hQ := h1b.mul h2b
      have hinner := hQ.sub hP
      have hsin' := Real.hasDerivAt_sin α
      exact (hsin'.const_mul (↑(2*n+2) : ℝ)).mul hinner
    rw [hev.deriv_eq, hFhas.deriv]
    have hbnd4 : |(↑(2*n+2) : ℝ) * Real.cos α *
          (ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
            - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))
        + (↑(2*n+2) : ℝ) * Real.sin α *
          ( ( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
              + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )
            - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                + ρ (Real.cos α) ^ (2*n+2-1)
                    * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) ) )|
        ≤ K * (C₁*ε) := by
      have hMnn : (0:ℝ) ≤ (↑(2*n+2) : ℝ) := Nat.cast_nonneg _
      have hM1nn : (0:ℝ) ≤ (↑(2*n+2-1) : ℝ) := Nat.cast_nonneg _
      have hPα : |ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α)|
          ≤ 2^(2*n+2-1) * (C₁*ε) :=
        abs_mul_le_mul (abs_pow_le hpA (2*n+2-1)) hA2
      have hQα : |ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)|
          ≤ 2^(2*n+2-1) * (C₁*ε) :=
        abs_mul_le_mul (abs_pow_le hpB (2*n+2-1)) hB2
      have hPs : |deriv ρ (Real.cos α) * (-Real.sin α)| ≤ C₁*ε := by
        have := abs_mul_le_mul hA2 hneg; simpa using this
      have hQs : |deriv ρ (-Real.cos α) * Real.sin α| ≤ C₁*ε := by
        have := abs_mul_le_mul hB2 hsin; simpa using this
      have hPs'' : |deriv (deriv ρ) (Real.cos α) * (-Real.sin α)| ≤ C₁*ε := by
        have := abs_mul_le_mul hA3 hneg; simpa using this
      have hQs'' : |deriv (deriv ρ) (-Real.cos α) * Real.sin α| ≤ C₁*ε := by
        have := abs_mul_le_mul hB3 hsin; simpa using this
      have hPv1 : |(↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
            * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)|
          ≤ (↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) * (C₁*ε) * (C₁*ε) := by
        have h1 : |(↑(2*n+2-1) : ℝ)| ≤ (↑(2*n+2-1) : ℝ) := by rw [abs_of_nonneg hM1nn]
        exact abs_mul4_le h1 (abs_pow_le hpA (2*n+2-1-1)) hPs hA2
      have hQv1 : |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
            * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)|
          ≤ (↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) * (C₁*ε) * (C₁*ε) := by
        have h1 : |(↑(2*n+2-1) : ℝ)| ≤ (↑(2*n+2-1) : ℝ) := by rw [abs_of_nonneg hM1nn]
        exact abs_mul4_le h1 (abs_pow_le hpB (2*n+2-1-1)) hQs hB2
      have hsq : (C₁*ε) * (C₁*ε) ≤ C₁*ε := mul_le_of_le_one_right he0 hC1
      have hPv2 : |ρ (Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))|
          ≤ 2^(2*n+2-1) * (C₁*ε) := abs_mul_le_mul (abs_pow_le hpA (2*n+2-1)) hPs''
      have hQv2 : |ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)|
          ≤ 2^(2*n+2-1) * (C₁*ε) := abs_mul_le_mul (abs_pow_le hpB (2*n+2-1)) hQs''
      have hPv : |(↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
              * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
            + ρ (Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))|
          ≤ ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε) := by
        have h0 : (0:ℝ) ≤ (↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) :=
          mul_nonneg hM1nn (by positivity)
        calc |(↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
              + ρ (Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))|
            ≤ |(↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)|
              + |ρ (Real.cos α) ^ (2*n+2-1)
                  * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))| := abs_add_le _ _
          _ ≤ (↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) * (C₁*ε) * (C₁*ε)
              + 2^(2*n+2-1) * (C₁*ε) := add_le_add hPv1 hPv2
          _ ≤ ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε) := by
              nlinarith [hsq, h0]
      have hQv : |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
              * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
            + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)|
          ≤ ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε) := by
        have h0 : (0:ℝ) ≤ (↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) :=
          mul_nonneg hM1nn (by positivity)
        calc |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
              + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)|
            ≤ |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)|
              + |ρ (-Real.cos α) ^ (2*n+2-1)
                  * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)| := abs_add_le _ _
          _ ≤ (↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) * (C₁*ε) * (C₁*ε)
              + 2^(2*n+2-1) * (C₁*ε) := add_le_add hQv1 hQv2
          _ ≤ ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε) := by
              nlinarith [hsq, h0]
      have hX : |ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
            - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α)|
          ≤ 2 * 2^(2*n+2-1) * (C₁*ε) := by
        rw [sub_eq_add_neg]
        calc |ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
              + -(ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))|
            ≤ |ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)|
              + |-(ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))| := abs_add_le _ _
          _ ≤ 2^(2*n+2-1) * (C₁*ε) + 2^(2*n+2-1) * (C₁*ε) := by
              rw [abs_neg]; exact add_le_add hQα hPα
          _ = 2 * 2^(2*n+2-1) * (C₁*ε) := by ring
      have hY : |( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )
              - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )|
          ≤ 2 * ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε) := by
        rw [sub_eq_add_neg]
        calc |( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )
              + -( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )|
            ≤ |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)|
              + |-(( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) ))| := abs_add_le _ _
          _ ≤ ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε)
              + ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε) := by
              rw [abs_neg]; exact add_le_add hQv hPv
          _ = 2 * ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε) := by ring
      have hcosle : |(↑(2*n+2) : ℝ) * Real.cos α *
            (ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
              - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))|
          ≤ (↑(2*n+2) : ℝ) * |ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
              - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α)| := by
        have h1 : |(↑(2*n+2) : ℝ)| ≤ (↑(2*n+2) : ℝ) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have h2 : |(↑(2*n+2) : ℝ) * Real.cos α * (ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
              - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))|
            ≤ (↑(2*n+2) : ℝ) * 1
              * |ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
                  - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α)| :=
          abs_mul3_le h1 hsinc (le_refl _)
        simpa using h2
      have hsinle : |(↑(2*n+2) : ℝ) * Real.sin α *
            ( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
              + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)
              - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                + ρ (Real.cos α) ^ (2*n+2-1)
                    * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) ) )|
          ≤ (↑(2*n+2) : ℝ) *
            |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
              + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)
              - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                + ρ (Real.cos α) ^ (2*n+2-1)
                    * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )| := by
        have h1 : |(↑(2*n+2) : ℝ)| ≤ (↑(2*n+2) : ℝ) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have h2 : |(↑(2*n+2) : ℝ) * Real.sin α *
              ( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)
                - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                      * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) ) )|
            ≤ (↑(2*n+2) : ℝ) * 1 *
              |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)
                - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                      * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )| :=
          abs_mul3_le h1 hsin (le_refl _)
        simpa using h2
      have hpowA : (2:ℝ)^(2*n+2-1) ≤ 2^(2*n+2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hpowB : (2:ℝ)^(2*n+2-1-1) ≤ 2^(2*n+2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hMc : (↑(2*n+2) : ℝ) = 2*(n:ℝ)+2 := by push_cast; ring
      have hM1c : (↑(2*n+2-1) : ℝ) = 2*(n:ℝ)+1 := by
        have : 2*n+2-1 = 2*n+1 := by omega
        rw [this]; push_cast; ring
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hC0 : (0:ℝ) ≤ 2^(2*n+2) := by positivity
      have hbig : (↑(2*n+2) : ℝ) * (2 * 2^(2*n+2) * (C₁*ε))
            + (↑(2*n+2) : ℝ)
              * (2 * ((↑(2*n+2-1) : ℝ) * 2^(2*n+2) + 2^(2*n+2)) * (C₁*ε))
          ≤ 3 * (2*(n:ℝ)+2)^2 * 2^(2*n+2) * (C₁*ε) := by
        rw [hMc, hM1c]
        have h1 : (0:ℝ) ≤ (2 * (n:ℝ) + 2) * (2 * (n:ℝ) + 2 - 2) := by
          have h2 : (0:ℝ) ≤ 2 * (n:ℝ) + 2 - 2 := by linarith
          exact mul_nonneg (by positivity) h2
        have h2 : (0:ℝ) ≤ (C₁*ε) * ((2 * (n:ℝ) + 2) * (2 * (n:ℝ) + 2 - 2)) :=
          mul_nonneg he0 h1
        nlinarith [h2, hC0, he0]
      calc |(↑(2*n+2) : ℝ) * Real.cos α *
              (ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
                - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))
            + (↑(2*n+2) : ℝ) * Real.sin α *
              ( ( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                    * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )
                - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                      * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) ) )|
          ≤ |(↑(2*n+2) : ℝ) * Real.cos α *
              (ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
                - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α))|
            + |(↑(2*n+2) : ℝ) * Real.sin α *
              ( (↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)
                - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                      * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) ) )| := abs_add_le _ _
        _ ≤ (↑(2*n+2) : ℝ) * |ρ (-Real.cos α) ^ (2*n+2-1) * deriv ρ (-Real.cos α)
              - ρ (Real.cos α) ^ (2*n+2-1) * deriv ρ (Real.cos α)|
            + (↑(2*n+2) : ℝ) *
              |(↑(2*n+2-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+2-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+2-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)
                - ( (↑(2*n+2-1) : ℝ) * ρ (Real.cos α) ^ (2*n+2-1-1)
                      * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+2-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )| :=
              add_le_add hcosle hsinle
        _ ≤ (↑(2*n+2) : ℝ) * (2 * 2^(2*n+2-1) * (C₁*ε))
            + (↑(2*n+2) : ℝ)
              * (2 * ((↑(2*n+2-1) : ℝ) * 2^(2*n+2-1-1) + 2^(2*n+2-1)) * (C₁*ε)) :=
              add_le_add (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _))
                (mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg _))
        _ ≤ (↑(2*n+2) : ℝ) * (2 * 2^(2*n+2) * (C₁*ε))
            + (↑(2*n+2) : ℝ)
              * (2 * ((↑(2*n+2-1) : ℝ) * 2^(2*n+2) + 2^(2*n+2)) * (C₁*ε)) := by
              gcongr
        _ ≤ 3 * (2*(n:ℝ)+2)^2 * 2^(2*n+2) * (C₁*ε) := hbig
        _ ≤ K * (C₁*ε) := by
              have := mul_pow_le_K n (c := 3 * (2*(n:ℝ)+2)^2) (j := 2*n+2)
                (three_sq_two_n_add_two_le n) (by omega)
              exact mul_le_mul_of_nonneg_right (by simpa [K] using this) he0
    exact hbnd4.trans hconv
  · -- (5) first derivative of the `2n+1` composition
    have hdg : HasDerivAt (fun β : ℝ => ρ (Real.cos β) ^ (2*n+1) - ρ (-Real.cos β) ^ (2*n+1))
        ((↑(2*n+1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1) * (deriv ρ (Real.cos α) * (-Real.sin α))
         - (↑(2*n+1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1)
             * (deriv ρ (-Real.cos α) * Real.sin α)) α :=
      (hasDerivAt_rho_cos_pow (2*n+1) hρa).sub (hasDerivAt_rho_negcos_pow (2*n+1) hρb)
    rw [hdg.deriv]
    have hbnd5 : |(↑(2*n+1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1) * (deriv ρ (Real.cos α) * -Real.sin α)
        - (↑(2*n+1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1)
            * (deriv ρ (-Real.cos α) * Real.sin α)| ≤ K * (C₁*ε) := by
      have hT1 : |(↑(2*n+1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1)
            * (deriv ρ (Real.cos α) * -Real.sin α)|
          ≤ (↑(2*n+1) : ℝ) * 2^(2*n+1-1) * (C₁*ε) := by
        have h1 : |(↑(2*n+1) : ℝ)| ≤ (↑(2*n+1) : ℝ) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have h4 : |deriv ρ (Real.cos α) * -Real.sin α| ≤ C₁*ε := by
          have := abs_mul_le_mul hA2 hneg; simpa using this
        exact abs_mul3_le h1 (abs_pow_le hpA (2*n+1-1)) h4
      have hT2 : |(↑(2*n+1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1)
            * (deriv ρ (-Real.cos α) * Real.sin α)|
          ≤ (↑(2*n+1) : ℝ) * 2^(2*n+1-1) * (C₁*ε) := by
        have h1 : |(↑(2*n+1) : ℝ)| ≤ (↑(2*n+1) : ℝ) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have h4 : |deriv ρ (-Real.cos α) * Real.sin α| ≤ C₁*ε := by
          have := abs_mul_le_mul hB2 hsin; simpa using this
        exact abs_mul3_le h1 (abs_pow_le hpB (2*n+1-1)) h4
      rw [sub_eq_add_neg]
      calc |(↑(2*n+1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1) * (deriv ρ (Real.cos α) * -Real.sin α)
            + -((↑(2*n+1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α))|
          ≤ |(↑(2*n+1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1) * (deriv ρ (Real.cos α) * -Real.sin α)|
            + |-((↑(2*n+1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α))| := abs_add_le _ _
        _ = |(↑(2*n+1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1) * (deriv ρ (Real.cos α) * -Real.sin α)|
            + |(↑(2*n+1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α)| := by rw [abs_neg]
        _ ≤ (↑(2*n+1) : ℝ) * 2^(2*n+1-1) * (C₁*ε)
            + (↑(2*n+1) : ℝ) * 2^(2*n+1-1) * (C₁*ε) := add_le_add hT1 hT2
        _ = (2 * (↑(2*n+1) : ℝ)) * 2^(2*n+1-1) * (C₁*ε) := by ring
        _ ≤ K * (C₁*ε) := by
              have := mul_pow_le_K n (c := 2 * (↑(2*n+1) : ℝ)) (j := 2*n+1-1)
                (two_mul_two_n_add_one_le n) (by omega)
              exact mul_le_mul_of_nonneg_right (by simpa [K] using this) he0
    exact hbnd5.trans hconv
  · -- (6) second derivative of the `2n+1` composition
    have hU : ∀ᶠ β in 𝓝 α, Real.cos β ∈ Set.Ioo (-1:ℝ) 1 := by
      have hmem : Set.Ioo (-1:ℝ) 1 ∈ 𝓝 (Real.cos α) := isOpen_Ioo.mem_nhds ha
      exact Real.continuous_cos.continuousAt.preimage_mem_nhds hmem
    have hev : deriv (fun γ : ℝ => ρ (Real.cos γ) ^ (2*n+1) - ρ (-Real.cos γ) ^ (2*n+1))
        =ᶠ[𝓝 α] Hlat n ρ := by
      filter_upwards [hU] with β hβ
      have hbβ : -Real.cos β ∈ Set.Ioo (-1:ℝ) 1 := by
        obtain ⟨h1, h2⟩ := hβ; exact ⟨by linarith, by linarith⟩
      have h3 : HasDerivAt
          (fun γ : ℝ => ρ (Real.cos γ) ^ (2*n+1) - ρ (-Real.cos γ) ^ (2*n+1))
          (Hlat n ρ β) β := by
        have h := (hasDerivAt_rho_cos_pow (2*n+1)
            (hρdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hβ))).sub
          (hasDerivAt_rho_negcos_pow (2*n+1)
            (hρdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hbβ)))
        refine h.congr_deriv ?_
        simp only [Hlat]; ring
      exact h3.deriv
    have hGhas : HasDerivAt (Hlat n ρ)
        (-((↑(2*n+1) : ℝ) * Real.cos α *
              (ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α))
            + (↑(2*n+1) : ℝ) * Real.sin α *
              ( ( (↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )
                + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                      * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) ) ))) α := by
      have h1a := hasDerivAt_rho_cos_pow (2*n+1-1) hρa
      have h1b := hasDerivAt_rho_negcos_pow (2*n+1-1) hρb
      have h2a := hasDerivAt_derivRho_cos hρ'a
      have h2b := hasDerivAt_derivRho_negcos hρ'b
      have hP := h1a.mul h2a
      have hQ := h1b.mul h2b
      have hinner := hP.add hQ
      have hsin' := Real.hasDerivAt_sin α
      exact ((hsin'.const_mul (↑(2*n+1) : ℝ)).mul hinner).neg
    rw [hev.deriv_eq, hGhas.deriv]
    rw [abs_neg]
    have hbnd6 : |(↑(2*n+1) : ℝ) * Real.cos α *
              (ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α))
            + (↑(2*n+1) : ℝ) * Real.sin α *
              ( ( (↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )
                + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                      * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) ) )|
        ≤ K * (C₁*ε) := by
      have hMnn : (0:ℝ) ≤ (↑(2*n+1) : ℝ) := Nat.cast_nonneg _
      have hM1nn : (0:ℝ) ≤ (↑(2*n+1-1) : ℝ) := Nat.cast_nonneg _
      have hPα : |ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)|
          ≤ 2^(2*n+1-1) * (C₁*ε) := abs_mul_le_mul (abs_pow_le hpA (2*n+1-1)) hA2
      have hQα : |ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α)|
          ≤ 2^(2*n+1-1) * (C₁*ε) := abs_mul_le_mul (abs_pow_le hpB (2*n+1-1)) hB2
      have hPs : |deriv ρ (Real.cos α) * (-Real.sin α)| ≤ C₁*ε := by
        have := abs_mul_le_mul hA2 hneg; simpa using this
      have hQs : |deriv ρ (-Real.cos α) * Real.sin α| ≤ C₁*ε := by
        have := abs_mul_le_mul hB2 hsin; simpa using this
      have hPs'' : |deriv (deriv ρ) (Real.cos α) * (-Real.sin α)| ≤ C₁*ε := by
        have := abs_mul_le_mul hA3 hneg; simpa using this
      have hQs'' : |deriv (deriv ρ) (-Real.cos α) * Real.sin α| ≤ C₁*ε := by
        have := abs_mul_le_mul hB3 hsin; simpa using this
      have hPv1 : |(↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
            * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)|
          ≤ (↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) * (C₁*ε) * (C₁*ε) := by
        have h1 : |(↑(2*n+1-1) : ℝ)| ≤ (↑(2*n+1-1) : ℝ) := by rw [abs_of_nonneg hM1nn]
        exact abs_mul4_le h1 (abs_pow_le hpA (2*n+1-1-1)) hPs hA2
      have hQv1 : |(↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
            * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)|
          ≤ (↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) * (C₁*ε) * (C₁*ε) := by
        have h1 : |(↑(2*n+1-1) : ℝ)| ≤ (↑(2*n+1-1) : ℝ) := by rw [abs_of_nonneg hM1nn]
        exact abs_mul4_le h1 (abs_pow_le hpB (2*n+1-1-1)) hQs hB2
      have hsq : (C₁*ε) * (C₁*ε) ≤ C₁*ε := mul_le_of_le_one_right he0 hC1
      have hPv2 : |ρ (Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))|
          ≤ 2^(2*n+1-1) * (C₁*ε) := abs_mul_le_mul (abs_pow_le hpA (2*n+1-1)) hPs''
      have hQv2 : |ρ (-Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)|
          ≤ 2^(2*n+1-1) * (C₁*ε) := abs_mul_le_mul (abs_pow_le hpB (2*n+1-1)) hQs''
      have hPv : |(↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
              * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
            + ρ (Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))|
          ≤ ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε) := by
        have h0 : (0:ℝ) ≤ (↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) :=
          mul_nonneg hM1nn (by positivity)
        calc |(↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
              + ρ (Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))|
            ≤ |(↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)|
              + |ρ (Real.cos α) ^ (2*n+1-1)
                  * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))| := abs_add_le _ _
          _ ≤ (↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) * (C₁*ε) * (C₁*ε)
              + 2^(2*n+1-1) * (C₁*ε) := add_le_add hPv1 hPv2
          _ ≤ ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε) := by
              nlinarith [hsq, h0]
      have hQv : |(↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
              * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
            + ρ (-Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)|
          ≤ ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε) := by
        have h0 : (0:ℝ) ≤ (↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) :=
          mul_nonneg hM1nn (by positivity)
        calc |(↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
              + ρ (-Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)|
            ≤ |(↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)|
              + |ρ (-Real.cos α) ^ (2*n+1-1)
                  * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)| := abs_add_le _ _
          _ ≤ (↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) * (C₁*ε) * (C₁*ε)
              + 2^(2*n+1-1) * (C₁*ε) := add_le_add hQv1 hQv2
          _ ≤ ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε) := by
              nlinarith [hsq, h0]
      have hZ : |ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
            + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α)|
          ≤ 2 * 2^(2*n+1-1) * (C₁*ε) := by
        calc |ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
              + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α)|
            ≤ |ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)|
              + |ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α)| := abs_add_le _ _
          _ ≤ 2^(2*n+1-1) * (C₁*ε) + 2^(2*n+1-1) * (C₁*ε) := add_le_add hPα hQα
          _ = 2 * 2^(2*n+1-1) * (C₁*ε) := by ring
      have hW : |( (↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )
                + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                      * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )|
          ≤ 2 * ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε) := by
        calc |( (↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )
                + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                      * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )|
            ≤ |(↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                  * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                + ρ (Real.cos α) ^ (2*n+1-1)
                    * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))|
              + |(↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                  * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+1-1)
                    * (deriv (deriv ρ) (-Real.cos α) * Real.sin α)| := abs_add_le _ _
          _ ≤ ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε)
              + ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε) :=
              add_le_add hPv hQv
          _ = 2 * ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε) := by ring
      have hpowA : (2:ℝ)^(2*n+1-1) ≤ 2^(2*n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hpowB : (2:ℝ)^(2*n+1-1-1) ≤ 2^(2*n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hMc : (↑(2*n+1) : ℝ) = 2*(n:ℝ)+1 := by push_cast; ring
      have hM1c : (↑(2*n+1-1) : ℝ) = 2*(n:ℝ) := by
        have : 2*n+1-1 = 2*n := by omega
        rw [this]; push_cast; ring
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hC0 : (0:ℝ) ≤ 2^(2*n+1) := by positivity
      have hbig : (↑(2*n+1) : ℝ) * (2 * 2^(2*n+1) * (C₁*ε))
            + (↑(2*n+1) : ℝ)
              * (2 * ((↑(2*n+1-1) : ℝ) * 2^(2*n+1) + 2^(2*n+1)) * (C₁*ε))
          ≤ 3 * (2*(n:ℝ)+1)^2 * 2^(2*n+1) * (C₁*ε) := by
        rw [hMc, hM1c]
        have h1 : (0:ℝ) ≤ (2 * (n:ℝ) + 1) * (2 * (n:ℝ) + 1 - 2) := by
          have h2 : (0:ℝ) ≤ 2 * (n:ℝ) + 1 - 2 := by linarith
          exact mul_nonneg (by positivity) h2
        have h2 : (0:ℝ) ≤ (C₁*ε) * ((2 * (n:ℝ) + 1) * (2 * (n:ℝ) + 1 - 2)) :=
          mul_nonneg he0 h1
        nlinarith [h2, hC0, he0, hn1]
      calc |(↑(2*n+1) : ℝ) * Real.cos α *
              (ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α))
            + (↑(2*n+1) : ℝ) * Real.sin α *
              ( ( (↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                    * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                  + ρ (Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α)) )
                + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                      * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) ) )|
          ≤ |(↑(2*n+1) : ℝ) * Real.cos α *
              (ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
                + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α))|
            + |(↑(2*n+1) : ℝ) * Real.sin α *
              ( (↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                  * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                + ρ (Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))
                + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                      * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) ) )| := abs_add_le _ _
        _ ≤ (↑(2*n+1) : ℝ) * |ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
              + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α)|
            + (↑(2*n+1) : ℝ) *
              |(↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                  * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                + ρ (Real.cos α) ^ (2*n+1-1) * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))
                + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                      * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                  + ρ (-Real.cos α) ^ (2*n+1-1)
                      * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )| := by
              refine add_le_add ?_ ?_
              · have h1 : |(↑(2*n+1) : ℝ)| ≤ (↑(2*n+1) : ℝ) := by
                  rw [abs_of_nonneg (Nat.cast_nonneg _)]
                have h2 : |(↑(2*n+1) : ℝ) * Real.cos α *
                      (ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
                        + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α))|
                    ≤ (↑(2*n+1) : ℝ) * 1 *
                      |ρ (Real.cos α) ^ (2*n+1-1) * deriv ρ (Real.cos α)
                        + ρ (-Real.cos α) ^ (2*n+1-1) * deriv ρ (-Real.cos α)| :=
                  abs_mul3_le h1 hsinc (le_refl _)
                simpa using h2
              · have h1 : |(↑(2*n+1) : ℝ)| ≤ (↑(2*n+1) : ℝ) := by
                  rw [abs_of_nonneg (Nat.cast_nonneg _)]
                have h2 : |(↑(2*n+1) : ℝ) * Real.sin α *
                      ( (↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                            * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                          + ρ (Real.cos α) ^ (2*n+1-1)
                              * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))
                        + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                              * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                          + ρ (-Real.cos α) ^ (2*n+1-1)
                              * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) ) )|
                    ≤ (↑(2*n+1) : ℝ) * 1 *
                      |(↑(2*n+1-1) : ℝ) * ρ (Real.cos α) ^ (2*n+1-1-1)
                            * (deriv ρ (Real.cos α) * (-Real.sin α)) * deriv ρ (Real.cos α)
                          + ρ (Real.cos α) ^ (2*n+1-1)
                              * (deriv (deriv ρ) (Real.cos α) * (-Real.sin α))
                        + ( (↑(2*n+1-1) : ℝ) * ρ (-Real.cos α) ^ (2*n+1-1-1)
                              * (deriv ρ (-Real.cos α) * Real.sin α) * deriv ρ (-Real.cos α)
                          + ρ (-Real.cos α) ^ (2*n+1-1)
                              * (deriv (deriv ρ) (-Real.cos α) * Real.sin α) )| :=
                  abs_mul3_le h1 hsin (le_refl _)
                simpa using h2
        _ ≤ (↑(2*n+1) : ℝ) * (2 * 2^(2*n+1-1) * (C₁*ε))
            + (↑(2*n+1) : ℝ)
              * (2 * ((↑(2*n+1-1) : ℝ) * 2^(2*n+1-1-1) + 2^(2*n+1-1)) * (C₁*ε)) :=
              add_le_add (mul_le_mul_of_nonneg_left hZ (Nat.cast_nonneg _))
                (mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _))
        _ ≤ (↑(2*n+1) : ℝ) * (2 * 2^(2*n+1) * (C₁*ε))
            + (↑(2*n+1) : ℝ)
              * (2 * ((↑(2*n+1-1) : ℝ) * 2^(2*n+1) + 2^(2*n+1)) * (C₁*ε)) := by
              gcongr
        _ ≤ 3 * (2*(n:ℝ)+1)^2 * 2^(2*n+1) * (C₁*ε) := hbig
        _ ≤ K * (C₁*ε) := by
              have := mul_pow_le_K n (c := 3 * (2*(n:ℝ)+1)^2) (j := 2*n+1)
                (three_sq_two_n_add_one_le n) (by omega)
              exact mul_le_mul_of_nonneg_right (by simpa [K] using this) he0
    exact hbnd6.trans hconv

end

end Work.OddVolterra.Free
