import Mathlib
import Submission.Work.KMTContract.Defs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- The elementary growth fact behind `goodScaleArith`: for fixed reals `A`, `B` the function
`x ↦ A·2^{x/4} + B·x + 4` is eventually dominated by `2^x`.  Indeed `2^{x/4} = o(2^x)` and
`x = o(2^x)` as `x → ∞`, and a constant is `o(2^x)` since `2^x → ∞`. -/
lemma goodScaleArith_aux (A B : ℝ) :
    ∃ M : ℝ, ∀ x : ℝ, M ≤ x → A * (2:ℝ) ^ (x/4) + B * x + 4 ≤ (2:ℝ) ^ x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2rpow : ∀ x : ℝ, (2:ℝ)^x = Real.exp (Real.log 2 * x) := fun x => by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]
  have hAe : (fun x : ℝ => Real.exp ((Real.log 2 / 4) * x)) =o[atTop]
      (fun x : ℝ => Real.exp (Real.log 2 * x)) := by
    have h := isLittleO_exp_mul_rpow_of_lt (k := (0:ℝ)) (a := Real.log 2 / 4)
      (b := Real.log 2) (by linarith)
    exact h.congr (fun t => by rw [Real.rpow_zero, mul_one]) (fun t => rfl)
  have hid : (fun x : ℝ => x) =o[atTop] (fun x : ℝ => (2:ℝ)^x) := by
    have h := isLittleO_rpow_exp_pos_mul_atTop (1:ℝ) hlog2
    exact h.congr (fun x => by rw [Real.rpow_one]) (fun x => (h2rpow x).symm)
  have hA : (fun x : ℝ => A * (2:ℝ)^(x/4)) =o[atTop] (fun x : ℝ => (2:ℝ)^x) := by
    have h := hAe.const_mul_left A
    exact h.congr (fun x => by rw [h2rpow (x/4)]; ring_nf) (fun x => (h2rpow x).symm)
  have hB : (fun x : ℝ => B * x) =o[atTop] (fun x : ℝ => (2:ℝ)^x) := hid.const_mul_left B
  have h4 : (fun _ : ℝ => (4:ℝ)) =o[atTop] (fun x : ℝ => (2:ℝ)^x) :=
    (Asymptotics.isLittleO_const_id_atTop (4:ℝ)).trans hid
  have hev : ∀ᶠ x : ℝ in atTop, A * (2:ℝ)^(x/4) + B * x + 4 ≤ (2:ℝ)^x := by
    have h := (hA.add hB).add h4
    filter_upwards [h.eventuallyLE] with x hx
    rw [Real.norm_eq_abs] at hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) x)] at hx
    exact le_trans (le_abs_self _) hx
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  exact ⟨M, fun x hx => hM x hx⟩

theorem goodScaleArith (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / (4 * (C₀ : ℝ))) (R : ℝ) (hR : 1 ≤ R) :
    ∃ B₀ : ℕ, ∀ (lmax N : ℕ), B₀ ≤ lmax → lmax ≤ Work.Analysis.EndVar.heightScale C₀ N →
      (lmax : ℝ) + R * (2 : ℝ) ^ (ρ * (lmax : ℝ)) + 2 ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
  obtain ⟨M, hM⟩ := goodScaleArith_aux R (C₀ : ℝ)
  refine ⟨C₀ * max (Nat.ceil M) 1, ?_⟩
  intro lmax N hB hle
  have hC₀pos : (0:ℝ) < (C₀:ℝ) := by exact_mod_cast hC₀
  set k : ℕ := Work.Analysis.EndVar.logLogN N with hk
  set x : ℕ := Nat.log 2 (max N 2) with hx
  have hk_eq : k = Nat.log 2 (x + 2) := by
    rw [hk, hx]; rfl
  have hlmax_le_nat : lmax ≤ C₀ * k := by
    rw [Work.Analysis.EndVar.heightScale, ← hk] at hle
    exact hle
  have hKk : max (Nat.ceil M) 1 ≤ k := by
    refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < C₀)
    exact le_trans hB hlmax_le_nat
  have hkM : M ≤ (k:ℝ) := by
    have h1 : M ≤ ((Nat.ceil M : ℕ) : ℝ) := Nat.le_ceil M
    have h2 : ((Nat.ceil M : ℕ) : ℝ) ≤ ((max (Nat.ceil M) 1 : ℕ) : ℝ) := by
      exact_mod_cast le_max_left (Nat.ceil M) 1
    have h3 : ((max (Nat.ceil M) 1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hKk
    linarith
  have hk_ineq : R * (2:ℝ) ^ ((k:ℝ)/4) + (C₀:ℝ) * (k:ℝ) + 4 ≤ (2:ℝ)^((k:ℝ)) :=
    hM (k:ℝ) hkM
  have hρC₀ : ρ * (C₀:ℝ) ≤ 1/4 := by
    have h4C₀ : (0:ℝ) < 4 * (C₀:ℝ) := by positivity
    have h : ρ * (4 * (C₀:ℝ)) ≤ 1 := (le_div_iff₀ h4C₀).mp hρ1
    nlinarith
  have hlmax_le : (lmax:ℝ) ≤ (C₀:ℝ) * (k:ℝ) := by exact_mod_cast hlmax_le_nat
  have hexp_le : ρ * (lmax:ℝ) ≤ (k:ℝ)/4 := by
    have h1 : ρ * (lmax:ℝ) ≤ ρ * ((C₀:ℝ) * (k:ℝ)) := mul_le_mul_of_nonneg_left hlmax_le hρ.le
    have h2 : ρ * ((C₀:ℝ) * (k:ℝ)) = (ρ * (C₀:ℝ)) * (k:ℝ) := by ring
    have h3 : (ρ * (C₀:ℝ)) * (k:ℝ) ≤ (1/4) * (k:ℝ) :=
      mul_le_mul_of_nonneg_right hρC₀ (Nat.cast_nonneg k)
    linarith
  have hrpow : (2:ℝ) ^ (ρ * (lmax:ℝ)) ≤ (2:ℝ) ^ ((k:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
  have hRnonneg : 0 ≤ R := le_trans zero_le_one hR
  have hstep : (lmax:ℝ) + R * (2:ℝ) ^ (ρ*(lmax:ℝ)) + 2 ≤ (2:ℝ)^((k:ℝ)) - 2 := by
    have hmul : R * (2:ℝ)^(ρ*(lmax:ℝ)) ≤ R * (2:ℝ)^((k:ℝ)/4) :=
      mul_le_mul_of_nonneg_left hrpow hRnonneg
    linarith
  have h2k : 2 ^ k ≤ x + 2 := by
    rw [hk_eq]; exact Nat.pow_log_le_self 2 (by omega)
  have hx2 : (2:ℝ)^((k:ℝ)) ≤ (x:ℝ) + 2 := by
    have h : ((2:ℕ)^k : ℝ) ≤ ((x+2 : ℕ) : ℝ) := by exact_mod_cast h2k
    push_cast at h
    rwa [Real.rpow_natCast]
  calc (lmax:ℝ) + R * (2:ℝ) ^ (ρ*(lmax:ℝ)) + 2 ≤ (2:ℝ)^((k:ℝ)) - 2 := hstep
    _ ≤ (x:ℝ) := by linarith
    _ = ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
        rw [Work.Analysis.EndVar.logN, ← hx]; norm_num

end Work.KMTPlan.A6
