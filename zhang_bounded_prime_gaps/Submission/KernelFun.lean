import Mathlib
import Submission.KernelLimit
import Submission.CrudeKernelCoord

open scoped BigOperators Topology
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The single-coordinate kernel as a function of the Fourier variables

P8 (41) is proved for *fixed* Fourier variables in `Submission.KernelLimit`
(and uniformly on a cube in `KernelLimitFamily`).  For the ξ-truncation step of
Lemma 4.1 one needs the kernel as a genuine function of `(ξ, ξ′)`: measurable
(so that its integral against Schwartz transforms makes sense), bounded by the
crude estimate `≪ log³x` (input (b) of the truncation), and equal pointwise to
the Euler product.

This module provides that function: `kernelFun q a b` is the limit of the finite
Euler products `∏_{p ∈ Sfilter q n} locK p a b` (via `Filter.limUnder`, which
equals the limit whenever the latter exists), together with

  * `tendsto_kernelFun` — the defining convergence;
  * `norm_kernelFun_le` — transfer of a uniform bound on the finite products to
    the kernel (the crude `≪ log³x` estimate of `CrudeKernelCoord`);
  * `measurable_kernelFun` — measurability of
    `(ξ, ξ′) ↦ kernelFun q (logZ (−2πξ) x) (logZ (−2πξ′) x)`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The single-coordinate kernel of P8 (38)/(39): the Euler product
`∏_{p ∤ q} K_p`, realized as the limit of the finite products. -/
noncomputable def kernelFun (q : ℕ) (a b : ℂ) : ℂ :=
  (atTop : Filter ℕ).limUnder fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b

/-- The defining convergence of `kernelFun`. -/
theorem tendsto_kernelFun (q : ℕ) (hq : q ≠ 0) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b) atTop (𝓝 (kernelFun q a b)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_locKprod q hq ha hb
  have h1 : kernelFun q a b = L := hL.limUnder_eq
  rw [h1]
  exact hL

/-- The pointwise value of `kernelFun` at any point where the Euler product
converges. -/
theorem kernelFun_eq_of_tendsto {q : ℕ} {a b : ℂ} {L : ℂ}
    (h : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b) atTop (𝓝 L)) :
    kernelFun q a b = L := h.limUnder_eq

/-- **Transfer of the crude bound.**  If every finite Euler product is bounded
by `C`, so is the kernel. -/
theorem norm_kernelFun_le {q : ℕ} (hq : q ≠ 0) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    {C : ℝ} (hC : ∀ n : ℕ, ‖∏ p ∈ Sfilter q n, locK p a b‖ ≤ C) :
    ‖kernelFun q a b‖ ≤ C := by
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ C} := isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto (tendsto_kernelFun q hq ha hb) (Eventually.of_forall hC)

/-- The `k = 1` instance of `coordLocalK` is `locK` (for `p ≠ 0`; at `p = 0`
the two `cpow` groupings genuinely differ). -/
lemma coordLocalK_one (p : ℕ) (hp : p ≠ 0) (a b : ℂ) :
    coordLocalK p (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) = locK p a b := by
  rw [coordLocalK_eq p hp, Fin.sum_univ_one]
  unfold locK
  ring

/-! ## Continuity / measurability -/

/-- `locK p · ·` is continuous in the pair of exponents as soon as `p ≠ 0`. -/
lemma continuous_locK (p : ℕ) (hp : p ≠ 0) :
    Continuous fun z : ℂ × ℂ => locK p z.1 z.2 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hA : Continuous fun z : ℂ × ℂ => (p : ℂ) ^ (-(1 + z.1)) :=
    (by fun_prop : Continuous fun z : ℂ × ℂ => -(1 + z.1)).const_cpow (Or.inl hpC)
  have hB : Continuous fun z : ℂ × ℂ => (p : ℂ) ^ (-(1 + z.2)) :=
    (by fun_prop : Continuous fun z : ℂ × ℂ => -(1 + z.2)).const_cpow (Or.inl hpC)
  have hC : Continuous fun z : ℂ × ℂ => (p : ℂ) ^ (-(1 + z.1 + z.2)) :=
    (by fun_prop : Continuous fun z : ℂ × ℂ => -(1 + z.1 + z.2)).const_cpow (Or.inl hpC)
  have : (fun z : ℂ × ℂ => locK p z.1 z.2) =
      fun z : ℂ × ℂ => 1 - (p : ℂ) ^ (-(1 + z.1)) - (p : ℂ) ^ (-(1 + z.2)) +
        (p : ℂ) ^ (-(1 + z.1 + z.2)) := by
    funext z; rfl
  rw [this]
  exact ((continuous_const.sub hA).sub hB).add hC

/-- The kernel at the sieve's Fourier variables is measurable in `(ξ, ξ′)`. -/
theorem measurable_kernelFun (q x : ℕ) :
    Measurable fun p : ℝ × ℝ =>
      kernelFun q (logZ (-(2 * Real.pi * p.1)) x) (logZ (-(2 * Real.pi * p.2)) x) := by
  have hstep : ∀ n : ℕ, StronglyMeasurable fun p : ℝ × ℝ =>
      ∏ p' ∈ Sfilter q n, locK p' (logZ (-(2 * Real.pi * p.1)) x)
        (logZ (-(2 * Real.pi * p.2)) x) := by
    intro n
    have hξ : Continuous fun p : ℝ × ℝ => logZ (-(2 * Real.pi * p.1)) x := by
      unfold logZ
      fun_prop
    have hξ' : Continuous fun p : ℝ × ℝ => logZ (-(2 * Real.pi * p.2)) x := by
      unfold logZ
      fun_prop
    have hpairs : Continuous fun p : ℝ × ℝ =>
        (logZ (-(2 * Real.pi * p.1)) x, logZ (-(2 * Real.pi * p.2)) x) := hξ.prodMk hξ'
    have hcont : Continuous fun p : ℝ × ℝ =>
        ∏ p' ∈ Sfilter q n, locK p' (logZ (-(2 * Real.pi * p.1)) x)
          (logZ (-(2 * Real.pi * p.2)) x) := by
      refine continuous_finsetProd _ (fun p' hp' => ?_)
      exact (continuous_locK p'
        (Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p' hp')).ne_zero).comp hpairs
    exact hcont.stronglyMeasurable
  exact (StronglyMeasurable.limUnder hstep).measurable

end Commons.NumberTheory.MaynardSieve
