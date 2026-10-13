import Mathlib
import Submission.Work.WilE2.integral_curve_unique_global
import Submission.Work.WilE2.period_subgroup
import Submission.Work.WilE2.closed_addSubgroup_eq_zmultiples
import Submission.Work.WilE2.periodSubgroup_sub_mem

/-!
# Existence of a fundamental period

For an integral curve `γ` of a `C¹` autonomous vector field `X` on `ℝ^m` that never vanishes
along `γ`, and which is periodic with period `T > 0`, there is a *fundamental period* `T₀ > 0`:

* `T₀` is a period of `γ`;
* `T` is a positive integer multiple of `T₀`;
* `γ` is injective on every half-open interval of length `< T₀`.

The argument is the classical one.  The set `P` of periods of `γ` is an additive subgroup of `ℝ`
(closed, because `γ` is continuous).  Because `X` does not vanish along `γ`, `γ` is not constant,
so `P ≠ ⊤`; a closed subgroup of `ℝ` is therefore `T₀ℤ` for a unique `T₀ > 0`
(`closed_addSubgroup_eq_zmultiples`).  The multiple `k` and the injectivity clause are then read
off the description `P = T₀ℤ`, global ODE uniqueness (`integral_curve_unique_global`) supplying
the fact that `γ t = γ t'` forces `t' - t ∈ P`.
-/

open Filter
open scoped Topology

namespace Work.WilE2

variable {m : ℕ}

/-- An integer multiple `n • a` of a positive real `a` which is nonnegative and `< a` must be `0`. -/
theorem eq_zero_of_zsmul_nonneg_lt {a x : ℝ} (ha : 0 < a) {n : ℤ} (hx : x = n • a)
    (h0 : 0 ≤ x) (hlt : x < a) : n = 0 := by
  rw [hx, zsmul_eq_mul] at h0 hlt
  have h1 : (0 : ℝ) ≤ (n : ℝ) := (mul_nonneg_iff_of_pos_right ha).mp h0
  have h2 : (n : ℝ) < 1 := by
    have ha1 : (n : ℝ) * a < 1 * a := by simpa using hlt
    exact (mul_lt_mul_iff_of_pos_right ha).mp ha1
  have hn0 : 0 ≤ n := by exact_mod_cast h1
  have hn1 : n < 1 := by exact_mod_cast h2
  omega

/-- A positive element of `AddSubgroup.zmultiples a` with `a > 0` is a positive *natural* multiple
of `a`. -/
theorem exists_nat_pos_mul_of_mem_zmultiples {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hmem : T ∈ AddSubgroup.zmultiples a) : ∃ k : ℕ, 0 < k ∧ T = k * a := by
  obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp (by
    have hcl : T ∈ AddSubgroup.closure ({a} : Set ℝ) := by
      rw [← AddSubgroup.zmultiples_eq_closure]; exact hmem
    exact hcl)
  have hnpos : 0 < n := by
    have h0 : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) * a := by rw [← zsmul_eq_mul, hn]; exact hT
      exact (mul_pos_iff_of_pos_right ha).mp this
    exact_mod_cast h0
  refine ⟨n.toNat, ?_, ?_⟩
  · have : (0 : ℤ) < (n.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (le_of_lt hnpos)]; exact hnpos
    exact_mod_cast this
  · have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (le_of_lt hnpos)]
    rw [← hn, zsmul_eq_mul, hcast]

theorem exists_fundamental_period {m : ℕ} (X : (Fin m → ℝ) → (Fin m → ℝ)) (hX : ContDiff ℝ 1 X)
    (γ : ℝ → Fin m → ℝ) (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) (hX0 : ∀ t, X (γ t) ≠ 0)
    {T : ℝ} (hT : 0 < T) (hper : ∀ t, γ (t + T) = γ t) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ (∀ t, γ (t + T₀) = γ t) ∧ (∃ k : ℕ, 0 < k ∧ T = k * T₀) ∧
      (∀ t t', 0 ≤ t' - t → t' - t < T₀ → γ t = γ t' → t = t') := by
  -- The period subgroup is closed and not all of `ℝ`.
  have hPclosed := isClosed_periodSubgroup (X := X) hγ
  have hPne := periodSubgroup_ne_top (X := X) hγ hX0
  have hTmem : T ∈ periodSubgroup γ := (mem_periodSubgroup T).mpr hper
  -- Classify it: it is `T₀ℤ` for some `T₀ > 0`.
  obtain ⟨T₀, hT₀pos, hPz⟩ :=
    closed_addSubgroup_eq_zmultiples (periodSubgroup γ) hPclosed ⟨T, hT, hTmem⟩ hPne
  have hT₀mem : T₀ ∈ periodSubgroup γ := by
    rw [hPz]; exact AddSubgroup.mem_zmultiples T₀
  refine ⟨T₀, hT₀pos, fun t => (mem_periodSubgroup T₀).mp hT₀mem t, ?_, ?_⟩
  -- `T` is a positive natural multiple of `T₀`.
  · exact exists_nat_pos_mul_of_mem_zmultiples hT₀pos hT (by rw [← hPz]; exact hTmem)
  -- Injectivity on intervals shorter than `T₀`.
  · intro t t' h0 hlt heq
    have hdmem : t' - t ∈ periodSubgroup γ := periodSubgroup_sub_mem (X := X) hX hγ heq
    have hdz : t' - t ∈ AddSubgroup.zmultiples T₀ := by rw [← hPz]; exact hdmem
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp (by
      have hcl : t' - t ∈ AddSubgroup.closure ({T₀} : Set ℝ) := by
        rw [← AddSubgroup.zmultiples_eq_closure]; exact hdz
      exact hcl)
    have hn0 : n = 0 := eq_zero_of_zsmul_nonneg_lt hT₀pos hn.symm h0 hlt
    have : t' - t = 0 := by rw [← hn, hn0]; simp
    linarith

end Work.WilE2
