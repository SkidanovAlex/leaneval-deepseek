import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.kernel_arcSymbol_torsion
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel
import Submission.Work.BourgainPlan.IonescuWainger.opArc_arcShift
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs
import Submission.Work.BourgainPlan.Maximal.varRhoSplitting

/-!
# The symbol disposal for the torsion arcs (Tao's `main`, step (iv); KMSZ §3.8)

Tao, arXiv:2008.05066, proof of Theorem `main`: the theorem is reduced to the family of *arc-shifted*
projections `(Op_{m;α+Σ_{A₀}}f)_{α ∈ Σ_{(A₀)}}` by the dichotomy "at this point the symbol `m` can be
disposed of using the Marcinkiewicz–Zygmund theorem".  Concretely: the Magyar–Stein–Wainger sampling
principle supplies a *single-operator* bound for the torsion multiplier `Op_{m;𝕋[Q]}` (in this
corpus `Work.BourgainPlan.IonescuWainger.msw_torsion_kernel`, whose kernel is the decimated kernel
`j ↦ Q·[Q ∣ j]·ĥ(j)`), and the Marcinkiewicz–Zygmund theorem
(`mz_square_function_finsupp`) upgrades it to the **family** (vector-valued, square-function) bound
for the shifted arcs, uniformly in the shift; the shift is handled by the modulation identity
`opArc_arcShift`.

This file proves that upgrade.  The single-operator input is taken in the *kernel* form in which
`msw_torsion_kernel` states it, so that the two compose directly:

* `opArc_sigmaSubAFinset_eq_torsionKernel`: the torsion multiplier `Op_{φ;Σ_{⊆A}}` is the
  convolution with the decimated kernel `torsionKernel A K`;
* **`torsion_family_bound`**: the family bound
  `‖(Op_{φ;α_i+Σ_{A₀}}F_i)_i‖_{ℓ^{2r}(ℤ;ℓ²)} ≤ C·B·‖(F_i)_i‖_{ℓ^{2r}(ℤ;ℓ²)}`.

Note on conventions: the kernel in the hypothesis of `torsion_family_bound` is built from the
coefficients `K j = ∫ φ · star (fourier j)` (the corpus's convention, `star (fourier j) = e^{-2πij·}`),
whereas `msw_torsion_kernel` uses the coefficients `∫ m ξ e^{+2πi j ξ}dξ` of the *reflected* symbol
`ξ ↦ m(-ξ)`.  The hypothesis below is stated for the corpus's `K`, so composing with
`msw_torsion_kernel` requires that reflection (one change of variables).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal lp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The decimated (torsion) kernel** attached to a coefficient sequence `K` and a set `A`:
`j ↦ Q_A · [Q_A ∣ j] · K j`.  It is the kernel of the torsion-arc multiplier `Op_{φ;Σ_{⊆A}}` when
`K j = ∫ φ · star (fourier j)`. -/
def torsionKernel (A : Finset ℕ) (K : ℤ → ℂ) (j : ℤ) : ℂ :=
  (QA A : ℂ) * (if (QA A : ℤ) ∣ j then K j else 0)

/-- **The torsion multiplier is the convolution with the decimated kernel** (Tao's `Op_{φ;Σ_{⊆A}}`,
with the coefficients `K j = ∫ φ · star (fourier j)`), for finitely supported inputs. -/
theorem opArc_sigmaSubAFinset_eq_torsionKernel {A : Finset ℕ}
    (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ j : ℤ, ∫ ξ, φ ξ * star (fourier j ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K j)
    (g : ℤ →₀ ℂ) (n : ℤ) :
    opArc φ hφ (sigmaSubAFinset A) (⇑g) (memℓp_finsupp g) n
      = ∑ k ∈ g.support, g k * torsionKernel A K (n - k) := by
  rw [opArc_eq_tsum_kernel φ hφ hK (sigmaSubAFinset A) (⇑g) (memℓp_finsupp g) n,
    tsum_eq_sum (s := g.support) (fun m hm => by
      rw [Finsupp.notMem_support_iff.mp hm, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kernelArc_charSum_sigmaSubAFinset A (n - k), torsionKernel]
  by_cases h : (QA A : ℤ) ∣ (n - k)
  · simp only [if_pos h]
  · simp only [if_neg h, zero_mul, mul_zero]

/-- The arc multiplier depends only on the function (not on the `Memℓp` proof). -/
theorem opArc_congr_fn (φ : Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {E : Finset Circle} {f g : ℤ → ℂ}
    (hf : Memℓp f 2) (hg : Memℓp g 2) (h : f = g) : opArc φ hφ E f hf = opArc φ hφ E g hg := by
  have hft : ftLp f hf = ftLp g hg := ftLp_congr_memℓp h hf hg
  funext n
  simp only [opArc, opMul, opMulLp, hft]

/-- `‖e^{2πi m θ}‖ₑ = 1`. -/
theorem enorm_fourier (m : ℤ) (θ : Circle) : ‖fourier m θ‖ₑ = 1 := by
  rw [← ofReal_norm, norm_fourier_apply', ENNReal.ofReal_one]

/-- The `enorm` of a modulated sequence is that of the original one. -/
theorem enorm_modSeq (ρ : ℤ → ℂ) (θ : Circle) (m : ℤ) : ‖modSeq ρ θ m‖ₑ = ‖ρ m‖ₑ := by
  rw [modSeq, enorm_mul, enorm_fourier, mul_one]

end

end Work.BourgainPlan.IonescuWainger
