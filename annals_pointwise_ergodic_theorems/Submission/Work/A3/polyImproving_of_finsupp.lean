import Mathlib
import Submission.Work.A3.fhat_conv
import Submission.Work.A3.parseval_finsupp
import Submission.Port.Aesm

/-!
# From finitely supported functions to all of `ℓᵖ` for the polynomial average

`Work.A3.polyImproving_of_finsupp` upgrades the `ℓᵖ`-improving estimate for the polynomial average
`A_N f(x) = N⁻¹ ∑_{n ≤ N} f(x - Q(n))` from test functions with finite support to *all* functions
`f : ℤ → ℂ`.

The upgrade is purely measure-theoretic and needs no hypothesis on `Q`, `p` or `C`: the finite
support version is the substantive input (it is what Plancherel + Hausdorff–Young give), while the
general version follows by approximation.  Fixing `N, f`, the truncated functions
`truncZ f k = f · 1_{[-k,k]}` are finitely supported, so the hypothesis bounds
`eLpNorm (A_N (truncZ f k)) 2` by `K * ‖f‖_{ℓᵖ}` uniformly in `k`; and `A_N (truncZ f k) → A_N f`
pointwise (for fixed `x` only finitely many values `x - Q(n)`, `n ≤ N`, are tested, and `truncZ f k`
agrees with `f` on them once `k` is large).  Fatou's lemma for the `ℒᵖ` seminorm
(`Lp.eLpNorm_le_of_ae_tendsto`) then passes the bound to the limit.
-/

set_option linter.unusedVariables false

namespace Work.A3

open MeasureTheory Filter
open scoped Topology

/-- Truncation of `f : ℤ → ℂ` to the symmetric interval `[-k,k]`. -/
private noncomputable def truncZ (f : ℤ → ℂ) (k : ℕ) (x : ℤ) : ℂ :=
  if x ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) then f x else 0

/-- `truncZ f k` is finitely supported. -/
private lemma truncZ_supp (f : ℤ → ℂ) (k : ℕ) : ∃ s : Finset ℤ, ∀ x ∉ s, truncZ f k x = 0 :=
  ⟨Finset.Icc (-(k : ℤ)) (k : ℤ), fun x hx => by simp [truncZ, hx]⟩

/-- Truncation does not increase pointwise norms. -/
private lemma norm_truncZ_le (f : ℤ → ℂ) (k : ℕ) (x : ℤ) : ‖truncZ f k x‖ ≤ ‖f x‖ := by
  by_cases hx : x ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) <;> simp [truncZ, hx]

/-- The truncations converge to `f` pointwise. -/
private lemma tendsto_truncZ (f : ℤ → ℂ) (y : ℤ) :
    Tendsto (fun k : ℕ => truncZ f k y) atTop (𝓝 (f y)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop y.natAbs] with k hk
  have hk' : |y| ≤ (k : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hk
  simp only [truncZ]
  rw [if_pos (by rw [Finset.mem_Icc]; exact abs_le.mp hk')]

theorem polyImproving_of_finsupp (Q : Polynomial ℤ) (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (C : ENNReal) (hC0 : C ≠ 0) (hCt : C ≠ ⊤) : (∀ (N : ℕ), 1 ≤ N → ∀ f : ℤ → ℂ, (∃ s : Finset ℤ, ∀ x ∉ s, f x = 0) → MeasureTheory.eLpNorm (fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n : ℤ) Q)) 2 MeasureTheory.Measure.count ≤ C * ENNReal.ofReal ((N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) * (1 / 2 - 1 / p))) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count) → (∀ (N : ℕ) (f : ℤ → ℂ), 1 ≤ N → MeasureTheory.eLpNorm (fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n : ℤ) Q)) 2 MeasureTheory.Measure.count ≤ C * ENNReal.ofReal ((N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) * (1 / 2 - 1 / p))) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count) := by
  intro H N f hN
  -- The hypothesis bounds the averaged truncations, uniformly in `k`.
  have hbound : ∀ k : ℕ,
      eLpNorm (fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
        truncZ f k (x - Polynomial.eval (n : ℤ) Q)) 2 Measure.count
      ≤ C * ENNReal.ofReal ((N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) * (1 / 2 - 1 / p)))
        * eLpNorm f (ENNReal.ofReal p) Measure.count := by
    intro k
    refine (H N hN (truncZ f k) (truncZ_supp f k)).trans ?_
    exact mul_le_mul_right (eLpNorm_mono (hf := by pw_aesm) (fun x => norm_truncZ_le f k x)) _
  -- The averaged truncations converge pointwise to the average of `f`.
  have hconv : ∀ x : ℤ,
      Tendsto (fun k : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
        truncZ f k (x - Polynomial.eval (n : ℤ) Q)) atTop
        (𝓝 ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n : ℤ) Q))) := by
    intro x
    refine Tendsto.const_mul ((N : ℂ)⁻¹) ?_
    refine tendsto_finsetSum (Finset.Icc 1 N) (fun n hn => ?_)
    exact tendsto_truncZ f (x - Polynomial.eval (n : ℤ) Q)
  -- Fatou for the `ℒᵖ` seminorm passes the uniform bound to the limit.
  exact Lp.eLpNorm_le_of_ae_tendsto (hg := by pw_aesm) (p := 2) (μ := Measure.count) (u := atTop)
    (f := fun k : ℕ => fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
      truncZ f k (x - Polynomial.eval (n : ℤ) Q))
    (g := fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n : ℤ) Q))
    (C := C * ENNReal.ofReal ((N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) * (1 / 2 - 1 / p)))
      * eLpNorm f (ENNReal.ofReal p) Measure.count)
    (Eventually.of_forall hbound)
    (fun k => (by measurability : Measurable (fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
      truncZ f k (x - Polynomial.eval (n : ℤ) Q))).aestronglyMeasurable)
    (Eventually.of_forall hconv)

end Work.A3
