import Mathlib
import Submission.Work.BW.split_aux
import Submission.Work.BW.split_E1_clearing
import Submission.Work.BW.split_E1_rhsK

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BW

/-- The (E1) condition of BW §21 for the range `m ≥ 1`, in the *exact* (non-floored) form:
with `𝒟 = calD`, `𝒮 = calS`, `𝒯 = calT` and `M = pD r d σ / (r · 2^{pI r d})`,

  `(r+1).descFactorial (m+1) · 𝒟₀ · M^{m} < (𝒮/(2r)) · (𝒯/(2r))^{m+1} / (m+1)!`.

This is the inequality that the half-split bound `split_E1` (via `halfSplit` and the binomial
coefficient) is derived from; it is the `m ≥ 1` companion of `split_E1_case0` (which handles
the degenerate `m = 0` range where step `0` of the split gets the larger budget `𝒮/2`). -/
theorem split_E1_casepos {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    ∀ m, 1 ≤ m → m < r →
      (((r + 1).descFactorial (m + 1) : ℕ) : ℝ) * calD r d h σ 0 *
          (pD r d σ / ((r : ℝ) * (2 : ℝ) ^ (pI r d))) ^ m <
        (calS r d h / (2 * (r : ℝ))) * (calT r d σ / (2 * (r : ℝ))) ^ (m + 1) /
          ((m + 1).factorial : ℝ) := by
  intro m hm1 hm
  have hmpos : 0 < m := hm1
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (le_trans (by norm_num : 1≤2) hr)
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hh0 : (0:ℝ) ≤ (h:ℝ) := by linarith
  have hL3 : (4:ℝ)/3 ≤ Real.log (2*r*d) := log_2rd_ge hr hd
  have hL0 : 0 < Real.log (2*r*d) := log_2rd_pos hr hd
  have hLne : Real.log (2*r*d) ≠ 0 := ne_of_gt hL0
  have hxi7 : (0.7:ℝ) ≤ pxi r := pxi_ge hr
  have hxi0 : 0 < pxi r := pxi_pos hr
  have hTh := theta_ge hr hd
  have hTge := pT_ge hr hd σ hσ
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hDnn : (0:ℝ) ≤ pD r d σ := le_of_lt hDpos
  have hD00 : (pD0 r d σ : ℝ) + 1 ≤ (r:ℝ)*pD r d σ/(2*Real.log (2*r*d)) + 1 := by
    have := pD0_le hr hd σ hσ
    linarith
  have hDlow := pD_low2 hr hd σ hσ
  have hm0' : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
  let Qf : ℕ → ℝ := fun k => ((r+1).descFactorial (k+1) : ℝ) * ((k+1).factorial : ℝ) * (r:ℝ) / (r:ℝ)^k
  let Gf : ℕ → ℝ := fun k => Qf k * 2^k / ((3.85:ℝ)^k * (2*(r:ℝ)*(d:ℝ))^(2*k))
  have hQfpos : ∀ k, k ≤ r → 0 < Qf k := by
    intro k hk
    have h4 : (0:ℝ) < (((r+1).descFactorial (k+1) : ℕ) : ℝ) := by
      exact_mod_cast (descFactorial_pos_le (by omega : k+1 ≤ r+1))
    have h2 : (0:ℝ) < (((k+1).factorial : ℕ) : ℝ) := by exact_mod_cast (k+1).factorial_pos
    have h3 : (0:ℝ) < (r:ℝ)^k := by positivity
    simp only [Qf]
    exact div_pos (mul_pos (mul_pos h4 h2) hr0) h3
  have hGfpos : ∀ k, k ≤ r → 0 < Gf k := by
    intro k hk
    have h1 := hQfpos k hk
    simp only [Gf]
    have h2 : (0:ℝ) < (2:ℝ)^k := by positivity
    have h3 : (0:ℝ) < (3.85:ℝ)^k := by positivity
    have h4 : (0:ℝ) < (2*(r:ℝ)*(d:ℝ))^(2*k) := by positivity
    exact div_pos (mul_pos h1 h2) (mul_pos h3 h4)
  have hGfanti : ∀ k, k < r → Gf (k+1) ≤ Gf k := by
    intro k hk
    have h1 : ((r:ℝ) - k) * ((k:ℝ)+2) * 2 / ((r:ℝ) * 3.85 * (2*(r:ℝ)*(d:ℝ))^2) ≤ 1 :=
      gf_factor_le hr hd hk
    have heq : Gf (k+1) = Gf k * (((r:ℝ) - k) * ((k:ℝ)+2) * 2 / ((r:ℝ) * 3.85 * (2*(r:ℝ)*(d:ℝ))^2)) := by
      simp only [Gf, Qf]
      exact gf_step r d k hk
    rw [heq]
    have h3 := hGfpos k (le_of_lt hk)
    nlinarith [h1, h3]
  have hGfle1 : Gf m ≤ Gf 1 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hmpos
    have key : ∀ t, 1 + t ≤ m → Gf (1+t) ≤ Gf 1 := by
      intro t
      induction t with
      | zero => intro _; exact le_rfl
      | succ j ih =>
          intro hj
          have h1 : Gf (1+(j+1)) ≤ Gf (1+j) := by
            have h2 : Gf ((1+j)+1) ≤ Gf (1+j) := hGfanti (1+j) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2
          exact le_trans h1 (ih (by omega))
    rw [hn]
    exact key n (le_of_eq hn.symm)
  have hGf1 : Gf 1 = ((r:ℝ)+1)/(3.85 * (r:ℝ) * (d:ℝ)^2) := by
    simp only [Gf, Qf]
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
    push_cast
    field_simp
    ring
  have hQmeq : Qf m = Gf m * ((3.85:ℝ)^m * (2*(r:ℝ)*(d:ℝ))^(2*m) / 2^m) := by
    simp only [Gf]
    field_simp
  have hclear : Qf m * (1/(2*Real.log (2*r*d)) + 1/((r:ℝ)*pD r d σ))
      < 16*(d:ℝ)*(5.5*(pxi r))^(m+1) * ((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m := by
    have h1 : 1/((r:ℝ)*pD r d σ) ≤ 1/(2*Real.log (2*r*d)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have h2 : (r:ℝ)*(2*(r:ℝ)^2*(d:ℝ)*Real.log (2*r*d)) ≤ (r:ℝ)*pD r d σ :=
        mul_le_mul_of_nonneg_left hDlow (le_of_lt hr0)
      have h3 : (1:ℝ) ≤ (r:ℝ)^3*(d:ℝ) := by
        have h6 : (1:ℝ) ≤ (r:ℝ)^3 := one_le_pow₀ hr1
        have h7 := mul_le_mul h6 hd1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (r:ℝ)^3)
        simpa using h7
      have h4 : 2*Real.log (2*r*d) ≤ (r:ℝ)*(2*(r:ℝ)^2*(d:ℝ)*Real.log (2*r*d)) := by
        nlinarith [h3, hL0, hr0, hd0]
      linarith
    have hQmnn : (0:ℝ) ≤ Qf m := le_of_lt (hQfpos m (le_of_lt hm))
    have hstep1 : Qf m * (1/(2*Real.log (2*r*d)) + 1/((r:ℝ)*pD r d σ)) ≤ Qf m/Real.log (2*r*d) := by
      have h2 : 1/(2*Real.log (2*r*d)) + 1/((r:ℝ)*pD r d σ) ≤ 1/Real.log (2*r*d) := by
        have h3 : 1/Real.log (2*r*d) = 1/(2*Real.log (2*r*d)) + 1/(2*Real.log (2*r*d)) := by ring
        linarith
      have h2' := mul_le_mul_of_nonneg_left h2 hQmnn
      simpa [one_div, div_eq_mul_inv] using h2'
    have hstep2 : Qf m/Real.log (2*r*d)
        ≤ Gf 1 * ((3.85:ℝ)^m * (2*(r:ℝ)*(d:ℝ))^(2*m) / 2^m)/Real.log (2*r*d) := by
      rw [hQmeq]
      apply div_le_div_of_nonneg_right _ (le_of_lt hL0)
      exact mul_le_mul_of_nonneg_right hGfle1 (by positivity)
    have hG1lt : Gf 1 < 16*(d:ℝ)*3.85*Real.log (2*r*d) := by
      rw [hGf1]
      rw [div_lt_iff₀ (by positivity)]
      have h1 : (r:ℝ)+1 ≤ 2*(r:ℝ) := by linarith
      have h6 : (1:ℝ) ≤ (d:ℝ)^3*Real.log (2*r*d) := by
        have h4 : (1:ℝ) ≤ (d:ℝ)^3 := one_le_pow₀ hd1
        have h5 : (1:ℝ) ≤ Real.log (2*r*d) := by linarith [hL3]
        have h9 := mul_le_mul h4 h5 (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (d:ℝ)^3)
        simpa using h9
      have h7 : (2:ℝ)*(r:ℝ) ≤ (237.16*((d:ℝ)^3*Real.log (2*r*d)))*(r:ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [h6]) (le_of_lt hr0)
      have heq : (16*(d:ℝ)*3.85*Real.log (2*r*d)) * (3.85*(r:ℝ)*(d:ℝ)^2)
          = (237.16*((d:ℝ)^3*Real.log (2*r*d)))*(r:ℝ) := by ring
      rw [heq]
      linarith [h1, h7]
    have hstep3 : Gf 1 * ((3.85:ℝ)^m * (2*(r:ℝ)*(d:ℝ))^(2*m) / 2^m)/Real.log (2*r*d)
        < 16*(d:ℝ)*3.85*((3.85:ℝ)^m * (2*(r:ℝ)*(d:ℝ))^(2*m) / 2^m) := by
      set X : ℝ := (3.85:ℝ)^m * (2*(r:ℝ)*(d:ℝ))^(2*m) / 2^m with hXdef
      have hX : (0:ℝ) < X := by rw [hXdef]; positivity
      have h2 : Gf 1 / Real.log (2*r*d) < 16*(d:ℝ)*3.85 := by
        rw [div_lt_iff₀ hL0]
        nlinarith [hG1lt]
      calc Gf 1 * X / Real.log (2*r*d) = (Gf 1 / Real.log (2*r*d)) * X := by ring
        _ < (16*(d:ℝ)*3.85) * X := mul_lt_mul_of_pos_right h2 hX
    have hstep4 : 16*(d:ℝ)*3.85*((3.85:ℝ)^m * (2*(r:ℝ)*(d:ℝ))^(2*m) / 2^m)
        ≤ 16*(d:ℝ)*(5.5*(pxi r))^(m+1) * ((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m := by
      have h2 : (((2*(r:ℝ)*(d:ℝ))^2)/2)^m = (2*(r:ℝ)*(d:ℝ))^(2*m)/2^m := by
        rw [div_pow, ← pow_mul]
      have h1 : (((2*(r:ℝ)*(d:ℝ))^2)/2)^m ≤ ((2:ℝ)^(pI r d) * (pxi r)^(r*pI r d))^m :=
        pow_le_pow_left₀ (by positivity) hTh m
      have h1' : (2*(r:ℝ)*(d:ℝ))^(2*m)/2^m ≤ ((2:ℝ)^(pI r d) * (pxi r)^(r*pI r d))^m := by
        rw [← h2]; exact h1
      have h3 : (3.85:ℝ)^(m+1) ≤ (5.5*(pxi r))^(m+1) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [hxi7]) _
      have h4 : (3.85:ℝ)^(m+1) * ((2*(r:ℝ)*(d:ℝ))^(2*m)/2^m)
          ≤ (5.5*(pxi r))^(m+1) * (((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m) := by
        have h5 := mul_le_mul h3 h1' (by positivity) (by positivity)
        have h6 : ((2:ℝ)^(pI r d) * (pxi r)^(r*pI r d))^m
            = ((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m := mul_pow _ _ _
        rw [h6] at h5
        exact h5
      calc 16*(d:ℝ)*3.85*((3.85:ℝ)^m * (2*(r:ℝ)*(d:ℝ))^(2*m) / 2^m)
          = 16*(d:ℝ)*((3.85:ℝ)^(m+1) * ((2*(r:ℝ)*(d:ℝ))^(2*m)/2^m)) := by
            rw [pow_succ]; ring
        _ ≤ 16*(d:ℝ)*((5.5*(pxi r))^(m+1) * (((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 16*(d:ℝ)*(5.5*(pxi r))^(m+1) * ((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m := by ring
    linarith [hstep1, hstep2, hstep3, hstep4]
  -- The positive factor `K` carrying `h·D^{m+1}` (with the `2^{Im}` and `(m+1)!` in the denominator).
  have hKpos : (0:ℝ) < (h:ℝ) * (pD r d σ)^(m+1) / (((2:ℝ)^(pI r d))^m * ((m+1).factorial:ℝ)) := by
    have h1 : (0:ℝ) < (h:ℝ) := by linarith [hh1]
    have h2 : (0:ℝ) < (pD r d σ)^(m+1) := pow_pos hDpos _
    have h3 : (0:ℝ) < ((2:ℝ)^(pI r d))^m := pow_pos (by norm_num) _
    have h4 : (0:ℝ) < ((m+1).factorial : ℝ) := by exact_mod_cast (m+1).factorial_pos
    exact div_pos (mul_pos h1 h2) (mul_pos h3 h4)
  -- The `Q`-bound of the previous steps, with `Q` unfolded (the shape in which it is multiplied).
  have hclear' : (((r+1).descFactorial (m+1) : ℕ) : ℝ) * ((m+1).factorial : ℝ) * (r:ℝ) / (r:ℝ)^m
        * (1/(2*Real.log (2*r*d)) + 1/((r:ℝ)*pD r d σ))
      < 16*(d:ℝ)*(5.5*(pxi r))^(m+1) * ((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m := by
    simpa only [Qf] using hclear
  have hAB : (((r+1).descFactorial (m+1) : ℕ) : ℝ) * ((h:ℝ) * ((r:ℝ)*pD r d σ/(2*Real.log (2*r*d)) + 1))
        * (pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)))^m
      < 16*(d:ℝ)*(h:ℝ)*(pxi r)^(-((r*pI r d:ℕ):ℤ))*(5.5*(pxi r)^(r*pI r d+1)*pD r d σ)^(m+1) / ((m+1).factorial:ℝ) := by
    rw [split_E1_clearing σ hr0 hDpos hL0, ← split_E1_rhsK σ hxi0]
    exact mul_lt_mul_of_pos_right hclear' hKpos
  have hA : ((r+1).descFactorial (m+1) : ℝ) * ((h:ℝ) * ((pD0 r d σ : ℝ) + 1))
        * (pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)))^m
      ≤ ((r+1).descFactorial (m+1) : ℝ)
        * ((h:ℝ) * ((r:ℝ)*pD r d σ/(2*Real.log (2*r*d)) + 1))
        * (pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)))^m := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD00 hh0) (Nat.cast_nonneg _)
  have h2le : 5.5*(pxi r)^(r*pI r d+1)*pD r d σ ≤ calT r d σ/(2*(r:ℝ)) := by
    rw [calT_div_two_r]
    have hx1 : (pxi r)^(r*pI r d+1) = (pxi r)^(r*pI r d) * (pxi r) := by rw [pow_succ]
    have h3 : (11:ℝ)*(r:ℝ)*pD r d σ ≤ (pT r d σ : ℝ) := hTge
    have h4 : 5.5*pD r d σ ≤ (pT r d σ : ℝ)/(2*(r:ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h3]
    have h5 : (0:ℝ) ≤ (pxi r) * (pxi r)^(r*pI r d) := by positivity
    calc 5.5*(pxi r)^(r*pI r d+1)*pD r d σ
        = 5.5*((pxi r)^(r*pI r d)*(pxi r))*pD r d σ := by rw [hx1]
      _ = ((pxi r)*(pxi r)^(r*pI r d)) * (5.5*pD r d σ) := by ring
      _ ≤ ((pxi r)*(pxi r)^(r*pI r d)) * ((pT r d σ:ℝ)/(2*(r:ℝ))) :=
          mul_le_mul_of_nonneg_left h4 h5
      _ = (pxi r)*(pxi r)^(r*pI r d)*(pT r d σ:ℝ)/(2*(r:ℝ)) := by ring
  have hrne : r ≠ 0 := by omega
  have h3eq : calS r d h/(2*(r:ℝ)) = 16*(d:ℝ)*(h:ℝ)*(pxi r)^(-((r*pI r d:ℕ):ℤ)) := by
    rw [calS_div_two_r (r := r) (d := d) (h := h) hrne]
    ring
  have hcore : ((r+1).descFactorial (m+1) : ℝ) * ((h:ℝ) * ((pD0 r d σ : ℝ) + 1))
        * (pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)))^m
      < (calS r d h/(2*(r:ℝ))) * (calT r d σ/(2*(r:ℝ)))^(m+1) / ((m+1).factorial : ℝ) := by
    have hB : 16*(d:ℝ)*(h:ℝ)*(pxi r)^(-((r*pI r d:ℕ):ℤ))
          * (5.5*(pxi r)^(r*pI r d+1)*pD r d σ)^(m+1)/((m+1).factorial:ℝ)
        ≤ (calS r d h/(2*(r:ℝ))) * (calT r d σ/(2*(r:ℝ)))^(m+1)/((m+1).factorial:ℝ) := by
      rw [h3eq]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2le (m+1)) (by positivity)
    linarith [hA, hAB, hB]
  rw [calD_zero]
  exact hcore

end Work.BW
