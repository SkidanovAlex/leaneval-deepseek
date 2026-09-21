import Submission.Work.OddVolterra.SweptDefs
import Submission.Work.OddVolterra.Swept.Pder

/-!
# The Leibniz expansion of `∂_u^j ((σ-u)^p · A u σ)`

We prove that the explicit expansion `ks A p j u σ` of `SweptDefs` coincides with the honest
`j`-th iterated derivative of `x ↦ (σ - x)^p * A x σ` at `u`, for `u < σ`.

The two ingredients are Mathlib's product rule for iterated derivatives (`iteratedDeriv_mul`)
and the one-variable computation of the iterated derivative of `x ↦ (σ - x)^p`.
-/

noncomputable section

namespace Work.OddVolterra.Swept

open Work.OddVolterra
open Filter
open scoped Topology

/-- The `i`-th iterated derivative of `x ↦ (σ - x)^p` away from `x = σ`. -/
theorem iteratedDeriv_const_sub_rpow (p : ℝ) (i : ℕ) {σ u : ℝ} (hu : u ≠ σ) :
    iteratedDeriv i (fun x : ℝ => (σ - x) ^ p) u
      = (-1 : ℝ) ^ i * rff p i * (σ - u) ^ (p - i) := by
  induction i generalizing u with
  | zero => simp [rff]
  | succ i ih =>
    rw [iteratedDeriv_succ]
    have hfuneq : iteratedDeriv i (fun x : ℝ => (σ - x) ^ p) =ᶠ[𝓝 u]
        (fun x : ℝ => (-1 : ℝ) ^ i * rff p i * (σ - x) ^ (p - i)) := by
      filter_upwards [isOpen_ne.mem_nhds hu] with x hx
      exact ih hx
    rw [Filter.EventuallyEq.deriv_eq hfuneq]
    have hsub : (σ - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have hrpow : HasDerivAt (fun y : ℝ => y ^ (p - i)) ((p - i) * (σ - u) ^ (p - i - 1))
        (σ - u) := Real.hasDerivAt_rpow_const (Or.inl hsub)
    have hinner : HasDerivAt (fun x : ℝ => σ - x) (-1) u := (hasDerivAt_id u).const_sub σ
    have hcomp : HasDerivAt (fun x : ℝ => (σ - x) ^ (p - i))
        (((p - i) * (σ - u) ^ (p - i - 1)) * (-1)) u := hrpow.comp u hinner
    have hmain : HasDerivAt (fun x : ℝ => (-1 : ℝ) ^ i * rff p i * (σ - x) ^ (p - i))
        ((-1 : ℝ) ^ i * rff p i * (((p - i) * (σ - u) ^ (p - i - 1)) * (-1))) u :=
      hcomp.const_mul ((-1 : ℝ) ^ i * rff p i)
    rw [hmain.deriv, rff_succ]
    have hexp : p - (i : ℝ) - 1 = p - ((i + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, pow_succ]
    ring

/-- **The Leibniz expansion of the iterated derivative of `(σ - ·)^p · A · σ`.** -/
theorem iteratedDeriv_rpow_mul {A : ℝ → ℝ → ℝ} {p : ℝ} {j : ℕ} {u σ : ℝ}
    (hσ : u < σ) (hA : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) (u, σ)) :
    iteratedDeriv j (fun x : ℝ => (σ - x) ^ p * A x σ) u = ks A p j u σ := by
  have hne : u ≠ σ := ne_of_lt hσ
  have hsub : (σ - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hf : ContDiffAt ℝ (j : ℕ∞) (fun x : ℝ => (σ - x) ^ p) u := by
    have h1 : ContDiffAt ℝ (j : ℕ∞) (fun y : ℝ => y ^ p) (σ - u) :=
      Real.contDiffAt_rpow_const (Or.inl hsub)
    have h2 : ContDiffAt ℝ (j : ℕ∞) (fun x : ℝ => σ - x) u := by fun_prop
    have h3 := h1.comp u h2
    simpa [Function.comp_def] using h3
  have hg : ContDiffAt ℝ (j : ℕ∞) (fun x : ℝ => A x σ) u := by
    have h2 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (x, σ)) u := by fun_prop
    have h3 := hA.comp u h2
    have h4 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) ((fun q : ℝ × ℝ => A q.1 q.2) ∘ fun x : ℝ => (x, σ)) u := h3
    have hle : ((j : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [WithTop.coe_le_coe]
      exact le_top
    simpa [Function.comp_def] using h4.of_le hle
  have hfun : (fun x : ℝ => (σ - x) ^ p * A x σ)
      = (fun x : ℝ => (σ - x) ^ p) * (fun x : ℝ => A x σ) := by
    funext x; rfl
  rw [hfun, iteratedDeriv_mul hf hg]
  rw [ks]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiter : iteratedDeriv i (fun x : ℝ => (σ - x) ^ p) u
      = (-1 : ℝ) ^ i * rff p i * (σ - u) ^ (p - i) := iteratedDeriv_const_sub_rpow p i hne
  have hiter2 : iteratedDeriv (j - i) (fun x : ℝ => A x σ) u = pder A (j - i) u σ := rfl
  rw [hiter, hiter2, lcoef]
  ring

end Work.OddVolterra.Swept
