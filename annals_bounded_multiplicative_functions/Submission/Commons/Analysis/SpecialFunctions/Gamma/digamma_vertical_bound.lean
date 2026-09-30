import Mathlib.Analysis.PSeries
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_lim_log_sub_sum_inv
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_series_norm_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter
open scoped Real Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- The digamma term `1/(n+1) − 1/(s+n)`. -/
noncomputable def dgTermC (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℂ) + 1)⁻¹) - ((s + (n : ℂ))⁻¹)

lemma ne_zero_add_nat (s : ℂ) (hs : 0 < s.re) (n : ℕ) : s + (n : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.add_re] at hre
  simp at hre
  have hle : 0 < s.re + (n : ℝ) := by positivity
  linarith

lemma nat_add_one_ne_zero (n : ℕ) : (n : ℂ) + 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.add_re] at hre
  simp at hre
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  linarith

lemma dgTerm_eq_mul (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    dgTermC s n = (s - 1) * ((((n : ℂ) + 1)⁻¹) * ((s + (n : ℂ))⁻¹)) := by
  have hnn : (n : ℂ) + 1 ≠ 0 := nat_add_one_ne_zero n
  have hsn : s + (n : ℂ) ≠ 0 := ne_zero_add_nat s hs n
  dsimp [dgTermC]
  field_simp [hnn, hsn]
  ring

lemma norm_inv_add_nat_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ‖(s + (n : ℂ))⁻¹‖ ≤ (s.re + (n : ℝ))⁻¹ := by
  have hnz : s + (n : ℂ) ≠ 0 := ne_zero_add_nat s hs n
  rw [norm_inv]
  have hαpos : 0 < s.re + (n : ℝ) := by positivity
  have hnormpos : 0 < ‖s + (n : ℂ)‖ := norm_pos_iff.mpr hnz
  have hge : s.re + (n : ℝ) ≤ ‖s + (n : ℂ)‖ := by
    have h1 := Complex.re_le_norm (s + (n : ℂ))
    rw [Complex.add_re] at h1
    simpa using h1
  exact (inv_le_inv₀ hnormpos hαpos).mpr hge

lemma norm_nat_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  have h : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by norm_num
  rw [← h]
  exact Complex.norm_of_nonneg (by positivity)

lemma dgTerm_norm_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ‖dgTermC s n‖ ≤ ‖s - 1‖ * ((((n : ℝ) + 1)⁻¹) * ((s.re + (n : ℝ))⁻¹)) := by
  rw [dgTerm_eq_mul s hs]
  calc
    ‖(s - 1) * ((((n : ℂ) + 1)⁻¹) * ((s + (n : ℂ))⁻¹))‖
        = ‖s - 1‖ * (‖((n : ℂ) + 1)⁻¹‖ * ‖(s + (n : ℂ))⁻¹‖) := by rw [norm_mul, norm_mul]
    _ = ‖s - 1‖ * ((((n : ℝ) + 1)⁻¹) * ‖(s + (n : ℂ))⁻¹‖) := by
          rw [norm_inv, norm_nat_add_one]
    _ ≤ ‖s - 1‖ * ((((n : ℝ) + 1)⁻¹) * ((s.re + (n : ℝ))⁻¹)) := by
          have h2 : ‖(s + (n : ℂ))⁻¹‖ ≤ (s.re + (n : ℝ))⁻¹ := norm_inv_add_nat_le s hs n
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (norm_nonneg _)

lemma dgTerm_partial_sum (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, dgTermC s n) =
      (harmonic N : ℂ) - (∑ k ∈ Finset.range N, ((s + (k : ℂ))⁻¹)) := by
  simp only [dgTermC]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ n ∈ Finset.range N, (((n : ℂ) + 1)⁻¹)) = (harmonic N : ℂ) := by
    rw [harmonic]
    norm_num
  rw [h1]

lemma harmonic_cast_complex (N : ℕ) : (harmonic N : ℂ) = ((harmonic N : ℝ) : ℂ) := by
  norm_num

lemma summable_inv_sq_shift : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    simpa using (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num : 1 < 2)
  have hfun : (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) =
      (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) ∘ Nat.succ := by
    funext n
    simp [Function.comp_apply, Nat.cast_succ]
  rw [hfun]
  exact h.comp_injective Nat.succ_injective

lemma summable_dgTerm_norm (s : ℂ) (hs4 : (1 : ℝ) / 4 ≤ s.re) :
    Summable (fun n : ℕ => ‖dgTermC s n‖) := by
  have hpos : 0 < s.re := by linarith
  have hb : ∀ n : ℕ, ‖dgTermC s (n + 1)‖ ≤ ‖s - 1‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    intro n
    have hle1 := dgTerm_norm_le s hpos (n + 1)
    have hf1 : ((n : ℝ) + 1 + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := by
      exact (inv_le_inv₀ (by positivity : 0 < (n : ℝ) + 1 + 1) (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith)
    have hf2 : ((s.re + (n : ℝ) + 1)⁻¹) ≤ ((n : ℝ) + 1)⁻¹ := by
      exact (inv_le_inv₀ (by positivity : 0 < s.re + (n : ℝ) + 1) (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith)
    have hmul : (((n : ℝ) + 1 + 1)⁻¹ * ((s.re + (n : ℝ) + 1)⁻¹)) ≤ (((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹) := by
      exact mul_le_mul hf1 hf2 (by positivity) (by positivity)
    calc
      ‖dgTermC s (n + 1)‖ ≤ ‖s - 1‖ * (((n : ℝ) + 1 + 1)⁻¹ * ((s.re + (n : ℝ) + 1)⁻¹)) := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hle1
      _ ≤ ‖s - 1‖ * ((((n : ℝ) + 1)⁻¹) * (((n : ℝ) + 1)⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hmul (norm_nonneg _)
      _ = ‖s - 1‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
        have hne : (n : ℝ) + 1 ≠ 0 := by positivity
        congr 1
        field_simp [pow_two, hne]
  have hsum' : Summable (fun n : ℕ => ‖s - 1‖ * (((n : ℝ) + 1) ^ 2)⁻¹) := by
    exact Summable.mul_left ‖s - 1‖ summable_inv_sq_shift
  have hsucc : Summable (fun n : ℕ => ‖dgTermC s (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hsum'
  exact (summable_nat_add_iff (f := fun n : ℕ => ‖dgTermC s n‖) 1).mp hsucc

/-- The digamma function on the right half-plane (with real part ≥ 1/4) is the absolutely
convergent series `digamma s = −γ + ∑' n, (1/(n+1) − 1/(s+n))`. -/
lemma digamma_eq_euler_sub_tsum (s : ℂ) (hs4 : (1 : ℝ) / 4 ≤ s.re) :
    Complex.digamma s = -(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, dgTermC s n := by
  have hs : 0 < s.re := by linarith
  let A : ℕ → ℂ := fun N => (Real.log ((N : ℝ) + 1) : ℂ) -
      ∑ k ∈ Finset.range (N + 1), ((s + (k : ℂ))⁻¹)
  let P : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, dgTermC s n
  have hA : Tendsto A atTop (𝓝 (Complex.digamma s)) := by
    simpa [A] using digamma_eq_lim_log_sub_sum_inv s hs
  have hAP : Tendsto (fun N : ℕ => A N - P N) atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have h1 : (fun N : ℕ => A N - P N) =ᶠ[atTop]
        (fun N : ℕ => ((Real.log ((N : ℝ) + 1) : ℂ) - ((harmonic N : ℝ) : ℂ)) - (s + (N : ℂ))⁻¹) := by
      refine Eventually.of_forall (fun N => ?_)
      dsimp [A, P]
      rw [dgTerm_partial_sum, harmonic_cast_complex]
      have hsum : (∑ k ∈ Finset.range (N + 1), ((s + (k : ℂ))⁻¹)) =
          (∑ k ∈ Finset.range N, ((s + (k : ℂ))⁻¹)) + (s + (N : ℂ))⁻¹ := by
        rw [Finset.sum_range_succ]
      rw [hsum]
      ring
    have hreal : Tendsto (fun N : ℕ => ((harmonic N : ℝ) - Real.log ((N : ℝ) + 1))) atTop
        (𝓝 Real.eulerMascheroniConstant) := by
      simpa using (Real.tendsto_harmonic_sub_log_add_one)
    have hneg : Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) - (harmonic N : ℝ))) atTop
        (𝓝 (-Real.eulerMascheroniConstant)) := by
      have := hreal.neg
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hc := (Complex.continuous_ofReal.tendsto (-Real.eulerMascheroniConstant)).comp hneg
    have hcast : (fun N : ℕ => (((Real.log ((N : ℝ) + 1) - (harmonic N : ℝ)) : ℝ) : ℂ)) =ᶠ[atTop]
        (fun N : ℕ => ((Real.log ((N : ℝ) + 1) : ℂ) - ((harmonic N : ℝ) : ℂ))) := by
      refine Eventually.of_forall (fun N => ?_)
      change (((Real.log ((N : ℝ) + 1) - (harmonic N : ℝ)) : ℝ) : ℂ) =
        ((Real.log ((N : ℝ) + 1) : ℂ) - ((harmonic N : ℝ) : ℂ))
      rw [Complex.ofReal_sub]
    have hc' : Tendsto (fun N : ℕ => ((Real.log ((N : ℝ) + 1) : ℂ) - ((harmonic N : ℝ) : ℂ)))
        atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
      simpa [Complex.ofReal_neg] using (hc.congr' hcast)
    have htend : Tendsto (fun N : ℕ => (s + (N : ℂ))⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have ht0 : Tendsto (fun N : ℕ => (s.re + (N : ℝ))⁻¹) atTop (𝓝 0) := by
        have ht : Tendsto (fun N : ℕ => s.re + (N : ℝ)) atTop atTop :=
          Filter.tendsto_atTop_add_const_left atTop s.re tendsto_natCast_atTop_atTop
        exact tendsto_inv_atTop_zero.comp ht
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht0
        (fun N => norm_nonneg _) (norm_inv_add_nat_le s hs)
    have hfin : Tendsto (fun N : ℕ => ((Real.log ((N : ℝ) + 1) : ℂ) - ((harmonic N : ℝ) : ℂ)) - (s + (N : ℂ))⁻¹)
        atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
      simpa using hc'.sub htend
    exact hfin.congr' h1.symm
  have hPlim : Tendsto P atTop (𝓝 (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ))) := by
    have hsub : (fun N : ℕ => A N - (A N - P N)) =ᶠ[atTop] P := by
      refine Eventually.of_forall (fun N => ?_)
      ring
    have h := hA.sub hAP
    simpa [sub_eq_add_neg, add_assoc] using h.congr' hsub
  have hsum : Summable (dgTermC s) := Summable.of_norm (summable_dgTerm_norm s hs4)
  have hPtsum : Tendsto P atTop (𝓝 (∑' n : ℕ, dgTermC s n)) := by
    simpa [P] using hsum.hasSum.tendsto_sum_nat
  have hEq : ∑' n : ℕ, dgTermC s n = Complex.digamma s + (Real.eulerMascheroniConstant : ℂ) := by
    exact (tendsto_nhds_unique hPlim hPtsum).symm
  rw [hEq]
  abel

/-- The Euler–Mascheroni constant is at most `1`. -/
lemma eulerMascheroniConstant_le_one : Real.eulerMascheroniConstant ≤ 1 := by
  have h : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  linarith

/-- Explicit vertical bound for the complex digamma function on a right half-strip:
`‖digamma (x + y·I)‖ ≤ log (2 + |y|) + 8` for `1/4 ≤ x ≤ 8` and all real `y`. -/
theorem digamma_vertical_bound (x y : ℝ) (hx1 : (1 : ℝ) / 4 ≤ x) (hx2 : x ≤ 8) :
    ‖Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.log (2 + |y|) + 8 := by
  let s : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hspos : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have hx1s : (1 : ℝ) / 4 ≤ s.re := by
    dsimp [s]
    simp
    simpa using hx1
  have hrepr := digamma_eq_euler_sub_tsum s hx1s
  have hsum : Summable (fun n : ℕ => ‖dgTermC s n‖) := summable_dgTerm_norm s hx1s
  have hnorm1 : ‖Complex.digamma s‖ ≤
      Real.eulerMascheroniConstant + (∑' n : ℕ, ‖dgTermC s n‖) := by
    calc
      ‖Complex.digamma s‖ = ‖-(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, dgTermC s n‖ := by
        rw [hrepr]
      _ ≤ ‖-(Real.eulerMascheroniConstant : ℂ)‖ + ‖∑' n : ℕ, dgTermC s n‖ := by
        exact norm_add_le _ _
      _ ≤ Real.eulerMascheroniConstant + (∑' n : ℕ, ‖dgTermC s n‖) := by
        have hgamma_nonneg : 0 ≤ Real.eulerMascheroniConstant := by
          have hpos : 1 / 2 < Real.eulerMascheroniConstant :=
            Real.one_half_lt_eulerMascheroniConstant
          linarith
        have hnorm_g : ‖(Real.eulerMascheroniConstant : ℂ)‖ = Real.eulerMascheroniConstant :=
          Complex.norm_of_nonneg hgamma_nonneg
        rw [norm_neg, hnorm_g]
        exact add_le_add_right (norm_tsum_le_tsum_norm hsum) Real.eulerMascheroniConstant
  have hbound : (∑' n : ℕ, ‖dgTermC s n‖) ≤ Real.log (2 + |y|) + 7 := by
    have h := digamma_series_norm_bound x y hx1 hx2
    simpa [s, dgTermC] using h
  calc
    ‖Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)‖
        = ‖Complex.digamma s‖ := by simp [s]
    _ ≤ Real.eulerMascheroniConstant + (∑' n : ℕ, ‖dgTermC s n‖) := hnorm1
    _ ≤ Real.eulerMascheroniConstant + (Real.log (2 + |y|) + 7) := by
      exact add_le_add_right hbound Real.eulerMascheroniConstant
    _ ≤ Real.log (2 + |y|) + 8 := by
      have hγ : Real.eulerMascheroniConstant ≤ 1 := eulerMascheroniConstant_le_one
      linarith

end Commons.Analysis.SpecialFunctions.Gamma