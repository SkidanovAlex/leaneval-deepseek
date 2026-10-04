import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pd_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pdVec_const_seriesFun`: repeated differentiation of a Fourier series

For a coefficient family `c` with finite weighted `ℓ¹` norms `Σ_m ⟨m⟩^N ‖c m‖` (all `N`),
differentiating the series `seriesFun c = fun x => Σ_m c m · exp (2πi m·x)`
`k` times in the *same* coordinate `i` multiplies the `m`-th coefficient by `(2πi mᵢ)^k`:

`∂ᵢ^k (seriesFun c) = seriesFun (fun m => (2πi mᵢ)^k · c m)`.

This is the iterated form of `pd_seriesFun` (the `k = 1` case), proved by induction: the
multiplier family `dmulPow i k c` is again admissible, i.e. has finite weighted `ℓ¹` norms,
because `|mᵢ| ≤ ⟨m⟩ = wt m`.

* `dmulPow i k c = fun m => (2πi mᵢ)^k · c m` is the multiplier of `∂ᵢ^k`;
* `summable_dmulPow` says it preserves the admissibility class;
* `pdVec_const_succ` writes the `(k+1)`-fold derivative as `∂ᵢ` of the `k`-fold one.
-/

noncomputable section

namespace Work.Diff.STE

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Fourier multiplier of `∂ᵢ^k`, i.e. `(2πi mᵢ)^k` acting on the coefficient family. -/
def dmulPow (i : ι) (j : ℕ) (c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ :=
  fun m => (2 * Real.pi * Complex.I * (m i : ℂ)) ^ j * c m

/-- `‖2πi mᵢ‖ = 2π |mᵢ| ≤ 2π ⟨m⟩`. -/
lemma norm_const_mul_int_le (i : ι) (m : ι → ℤ) :
    ‖2 * Real.pi * Complex.I * (m i : ℂ)‖ ≤ 2 * Real.pi * wt m := by
  have h : ‖2 * Real.pi * Complex.I * (m i : ℂ)‖ = 2 * Real.pi * |((m i : ℤ) : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg, Complex.norm_intCast]
  rw [h]
  exact mul_le_mul_of_nonneg_left (abs_intCast_le_wt m i) (by positivity)

/-- The multiplier of `∂ᵢ^j` grows at most like `(2π ⟨m⟩)^j`. -/
lemma norm_dmulPow_le (i : ι) (j : ℕ) (m : ι → ℤ) :
    ‖(2 * Real.pi * Complex.I * (m i : ℂ)) ^ j‖ ≤ (2 * Real.pi) ^ j * (wt m) ^ j := by
  rw [norm_pow]
  calc ‖2 * Real.pi * Complex.I * (m i : ℂ)‖ ^ j
      ≤ (2 * Real.pi * wt m) ^ j :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_const_mul_int_le i m) j
    _ = (2 * Real.pi) ^ j * (wt m) ^ j := mul_pow _ _ _

/-- The admissibility class `∀ N, Summable (fun m => ⟨m⟩^N ‖c m‖)` is preserved by the
multiplier `dmulPow i j` of `∂ᵢ^j`. -/
lemma summable_dmulPow (i : ι) (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => wt m ^ N * ‖c m‖)) (j : ℕ) :
    ∀ N : ℕ, Summable (fun m : ι → ℤ => wt m ^ N * ‖dmulPow i j c m‖) := by
  intro N
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) N)
      (norm_nonneg _)) (fun m => ?_)
    ((hc (N + j)).mul_left ((2 * Real.pi) ^ j))
  rw [dmulPow, norm_mul]
  calc wt m ^ N * (‖(2 * Real.pi * Complex.I * (m i : ℂ)) ^ j‖ * ‖c m‖)
      ≤ wt m ^ N * (((2 * Real.pi) ^ j * (wt m) ^ j) * ‖c m‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (wt_pos m)) N)
        exact mul_le_mul_of_nonneg_right (norm_dmulPow_le i j m) (norm_nonneg _)
    _ = (2 * Real.pi) ^ j * (wt m ^ (N + j) * ‖c m‖) := by rw [pow_add]; ring

omit [Fintype ι] in
/-- `∂ᵢ` applied to the `k`-fold derivative `∂ᵢ^k f` is the `(k+1)`-fold derivative. -/
lemma pdVec_const_succ (k : ℕ) (i : ι) (f : (ι → ℝ) → ℂ) :
    pdVec (k + 1) (fun _ : Fin (k + 1) => i) f
      = pd i (pdVec k (fun _ : Fin k => i) f) := by
  simp only [pdVec, pdList, List.ofFn_const, List.replicate_succ, List.foldr_cons]

theorem pdVec_const_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (i : ι) (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * ‖c m‖))
    (x : ι → ℝ) :
    Work.Diff.STE.pdVec k (fun _ : Fin k => i) (Work.Diff.STE.seriesFun c) x
      = Work.Diff.STE.seriesFun
          (fun m : ι → ℤ => (2 * Real.pi * Complex.I * (m i : ℂ)) ^ k * c m) x := by
  have key : ∀ k : ℕ, ∀ x : ι → ℝ,
      pdVec k (fun _ : Fin k => i) (seriesFun c) x = seriesFun (dmulPow i k c) x := by
    intro k
    induction k with
    | zero =>
      intro x
      simp only [pdVec, pdList, List.ofFn_zero, List.foldr_nil, dmulPow, pow_zero, one_mul,
        seriesFun]
    | succ k ih =>
      intro x
      rw [pdVec_const_succ]
      have hfun : pdVec k (fun _ : Fin k => i) (seriesFun c) = seriesFun (dmulPow i k c) :=
        funext ih
      rw [hfun, pd_seriesFun i (dmulPow i k c) (summable_dmulPow i c hc k) x]
      rw [show dmul i (dmulPow i k c) = dmulPow i (k + 1) c from by
        funext m
        simp only [dmul, dmulPow]
        rw [pow_succ]
        ring]
  exact key k x

end Work.Diff.STE
