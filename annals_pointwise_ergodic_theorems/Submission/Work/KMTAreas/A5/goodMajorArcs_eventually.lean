import Mathlib
import Submission.Work.KMTAreas.A5.scale_bounds_logb
import Submission.Work.KMTAreas.A5.natCast_rpow_le_two_pow
import Submission.Work.KMTAreas.A5.pow_log_eventually_le

/-!
# The good major arcs are attained eventually

This is the elementary estimate of §5 of Krause--Mirek--Tao behind the definition of the
*good major arcs*: with `Log N = log₂ max(N,2)`, `LogLog N = log₂(Log N + 2)` and
`l_{(N)} = C₀ LogLog N =` `heightScale C₀ N`, the pair `(l_{(N)}, -Log N + l_{(N)})` is a
good major arc pair as soon as

`C_ρ · 2^{ρ l_{(N)}} + 1 ≤ Log N - l_{(N)}`,

i.e. exactly the inequality proved here (for all sufficiently large `N`).  Equivalently the
height `l_{(N)}` satisfies `-Log N + l_{(N)} ≤ -C_ρ 2^{ρ l_{(N)}} - 1`.

The constants are arbitrary: `C₀ ≥ 1`, `ρ > 0` with `ρ C₀ < 1`, and `C_ρ > 0`.  The only
content is that `C₀ LogLog N` is `O(log log N)` while `Log N` grows like `log N`, so the
left hand side `C_ρ 2^{ρ C₀ LogLog N} = O((Log N)^{ρ C₀})` is `o(Log N)` because `ρ C₀ < 1`,
while the subtracted term `C₀ LogLog N = o(Log N)` as well (indeed `2 ^ l_{(N)} ≤ Log N + 2`).

The real-analytic core ("polynomial and logarithmic growth are beaten by the identity") is
isolated in `Work.KMTAreas.A5.pow_log_eventually_le`; here we only translate it to `ℕ` using
`2 ^ LogLog N ≤ Log N + 2`, which is `Nat.pow_log_le_self` applied to `Log N + 2`.
-/

namespace Work.KMTAreas.A5

open Filter

/-- **The good major arcs are attained eventually.**  For every `C₀ ≥ 1`, `ρ > 0`, `C_ρ > 0`
with `ρ C₀ < 1` there is `n₀ ≥ 1` such that for all `n ≥ n₀`

`C_ρ * 2 ^ (ρ * l_{(n)}) + 1 ≤ Log n - l_{(n)}`,  `l_{(n)} = heightScale C₀ n`. -/
theorem goodMajorArcs_eventually {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 0 < Cρ)
    (hρC₀ : ρ * (C₀ : ℝ) < 1) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      Cρ * (2 : ℝ) ^ (ρ * ((Work.Analysis.EndVar.heightScale C₀ n : ℕ) : ℝ)) + 1
        ≤ ((Work.Analysis.EndVar.logN n : ℤ) : ℝ)
          - ((Work.Analysis.EndVar.heightScale C₀ n : ℕ) : ℝ) := by
  -- the real-analytic input, with `s = ρ C₀ < 1`
  obtain ⟨x₀, hx₀⟩ := pow_log_eventually_le hρC₀ Cρ (C₀ : ℝ)
  -- we take `n₀ = 2 ^ max 1 ⌈x₀⌉₊`, so that `Log n ≥ max 1 ⌈x₀⌉₊ ≥ x₀`
  refine ⟨2 ^ max 1 ⌈x₀⌉₊, Nat.one_le_two_pow, ?_⟩
  intro n hn
  -- the two logarithmic scales, with `heightScale C₀ n = C₀ * M` and `logN n = L`
  set L : ℕ := Nat.log 2 (max n 2) with hLdef
  set M : ℕ := Nat.log 2 (L + 2) with hMdef
  have hM_eq : Work.Analysis.EndVar.logLogN n = M := rfl
  have hL_eq : ((Work.Analysis.EndVar.logN n : ℤ) : ℝ) = (L : ℝ) := rfl
  have hcast : ((Work.Analysis.EndVar.heightScale C₀ n : ℕ) : ℝ) = (C₀ : ℝ) * (M : ℝ) := by
    simp [Work.Analysis.EndVar.heightScale, hM_eq, Nat.cast_mul]
  -- `2 ^ M ≤ L + 2`, i.e. `LogLog n ≤ logb 2 (Log n + 2)`
  have hMpow : (2 : ℝ) ^ M ≤ (L : ℝ) + 2 := by
    exact_mod_cast (show (2 : ℕ) ^ M ≤ L + 2 from by
      have h := Nat.pow_log_le_self 2 (show L + 2 ≠ 0 by omega)
      rwa [← hMdef] at h)
  have hM_le : (M : ℝ) ≤ Real.logb 2 ((L : ℝ) + 2) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
    have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hpos hMpow
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
  -- `L ≥ max 1 ⌈x₀⌉₊`, hence `(L : ℝ) ≥ x₀`
  have hxL : x₀ ≤ (L : ℝ) := by
    have hclog : max 1 ⌈x₀⌉₊ ≤ L := by
      rw [hLdef]
      calc max 1 ⌈x₀⌉₊ = Nat.log 2 (2 ^ max 1 ⌈x₀⌉₊) := (Nat.log_pow (by norm_num) _).symm
        _ ≤ Nat.log 2 n := Nat.log_mono_right hn
        _ ≤ Nat.log 2 (max n 2) := Nat.log_mono_right (le_max_left n 2)
    have h1 : x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil x₀
    have h2 : ((⌈x₀⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈x₀⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 1 ⌈x₀⌉₊
    have h3 : ((max 1 ⌈x₀⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hclog
    linarith
  have hmain := hx₀ (L : ℝ) hxL
  rw [hL_eq, hcast]
  -- `2 ^ (ρ C₀ M) ≤ (L + 2) ^ (ρ C₀)`: exponentiate `2 ^ M ≤ L + 2`
  have hpow2 : (2 : ℝ) ^ (ρ * ((C₀ : ℝ) * (M : ℝ))) ≤ ((L : ℝ) + 2) ^ (ρ * (C₀ : ℝ)) := by
    have h2M : (2 : ℝ) ^ (M : ℝ) ≤ (L : ℝ) + 2 := by
      rw [Real.rpow_natCast]; exact hMpow
    calc (2 : ℝ) ^ (ρ * ((C₀ : ℝ) * (M : ℝ)))
        = (2 : ℝ) ^ ((M : ℝ) * (ρ * (C₀ : ℝ))) := by ring_nf
      _ = ((2 : ℝ) ^ (M : ℝ)) ^ (ρ * (C₀ : ℝ)) := Real.rpow_mul (by norm_num) _ _
      _ ≤ ((L : ℝ) + 2) ^ (ρ * (C₀ : ℝ)) := Real.rpow_le_rpow (by positivity) h2M (by positivity)
  have hnC₀ : (0 : ℝ) ≤ (C₀ : ℝ) := by positivity
  have h1 : Cρ * (2 : ℝ) ^ (ρ * ((C₀ : ℝ) * (M : ℝ))) ≤ Cρ * ((L : ℝ) + 2) ^ (ρ * (C₀ : ℝ)) :=
    mul_le_mul_of_nonneg_left hpow2 hCρ.le
  have h2 : (C₀ : ℝ) * (M : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((L : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hM_le hnC₀
  linarith

end Work.KMTAreas.A5
