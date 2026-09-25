import Submission.Work.BourgainPlan.Thm52.Defs
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function_finsupp
import Submission.Work.BourgainPlan.IonescuWainger.kernel_arcSymbol_torsion
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel
import Submission.Work.BourgainPlan.IonescuWainger.opArc_arcShift
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear

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

/-- **The symbol disposal for the torsion arcs** (Tao's `main`, step (iv)): if the single torsion
multiplier with the decimated kernel satisfies the `ℓ^{2r}` bound with constant `B` — which is what
the Magyar–Stein–Wainger sampling principle `msw_torsion_kernel` supplies — then the *family* of
arc-shifted multipliers `Op_{φ;α_i+Σ_{A₀}}`, one per shift `α i`, satisfies the same bound in the
vector-valued (square-function) sense `ℓ^{2r}(ℤ;ℓ²)`, by Marcinkiewicz–Zygmund
(`mz_square_function_finsupp`) and the modulation identity `opArc_arcShift`. -/
theorem torsion_family_bound {A : Finset ℕ} (r : ℕ) (hr : 1 ≤ r) {B : ℝ} (hB : 0 ≤ B)
    (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ j : ℤ, ∫ ξ, φ ξ * star (fourier j ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K j)
    (hkernel : ∀ (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ n, n ∉ s → a n = 0),
      ∫⁻ n : ℤ, ‖∑ k ∈ s, a k * torsionKernel A K (n - k)‖ₑ ^ ((2 * r : ℕ) : ℝ)
          ∂Measure.count
        ≤ ENNReal.ofReal (B ^ ((2 * r : ℕ) : ℝ))
          * ∫⁻ n : ℤ, ‖a n‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι] (α : ι → Circle) (F : ι → ℤ →₀ ℂ),
      ∫⁻ n : ℤ, (∑ i : ι, ‖opArc φ hφ (arcShift (sigmaSubAFinset A) (α i)) (⇑(F i))
          (memℓp_finsupp (F i)) n‖ₑ ^ (2 : ℝ)) ^ (r : ℝ) ∂Measure.count
        ≤ ENNReal.ofReal ((C * B) ^ ((2 * r : ℕ) : ℝ))
          * ∫⁻ n : ℤ, (∑ i : ι, ‖(⇑(F i) : ℤ → ℂ) n‖ₑ ^ (2 : ℝ)) ^ (r : ℝ) ∂Measure.count := by
  classical
  obtain ⟨Cmz, hCmzpos, hmz⟩ :=
    mz_square_function_finsupp (p := ((2 * r : ℕ) : ℝ))
      (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2 * r))
  refine ⟨Cmz ^ (1 / ((2 * r : ℕ) : ℝ)),
    Real.rpow_pos_of_pos hCmzpos (1 / ((2 * r : ℕ) : ℝ)), ?_⟩
  intro ι _ α F
  -- ## the single-operator bound for the torsion multiplier, from the kernel hypothesis
  set M : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) := opArcLM φ hφ (sigmaSubAFinset A) with hM
  have hsingle : ∀ (ω : Unit → Bool) (g : ℤ →₀ ℂ),
      ∫⁻ y : ℤ, ‖∑ i : Unit, (if ω i then (1 : ℂ) else -1) * M g y‖ₑ ^ ((2 * r : ℕ) : ℝ)
          ∂Measure.count
        ≤ ENNReal.ofReal (B ^ ((2 * r : ℕ) : ℝ))
          * ∫⁻ y : ℤ, ‖(⇑g : ℤ → ℂ) y‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂Measure.count := by
    intro ω g
    have hpt : ∀ y : ℤ, ‖∑ i : Unit, (if ω i then (1 : ℂ) else -1) * M g y‖ₑ
          ^ ((2 * r : ℕ) : ℝ)
        = ‖M g y‖ₑ ^ ((2 * r : ℕ) : ℝ) := by
      intro y
      rw [Fintype.sum_unique]
      by_cases h : ω () = true
      · rw [if_pos h, one_mul]
      · rw [if_neg h, neg_mul, enorm_neg, one_mul]
    calc ∫⁻ y : ℤ, ‖∑ i : Unit, (if ω i then (1 : ℂ) else -1) * M g y‖ₑ
            ^ ((2 * r : ℕ) : ℝ) ∂Measure.count
        = ∫⁻ y : ℤ, ‖M g y‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂Measure.count :=
          lintegral_congr hpt
      _ = ∫⁻ y : ℤ, ‖opArc φ hφ (sigmaSubAFinset A) (⇑g) (memℓp_finsupp g) y‖ₑ
            ^ ((2 * r : ℕ) : ℝ) ∂Measure.count := by
          refine lintegral_congr fun y => ?_
          rw [hM, opArcLM_apply]
      _ = ∫⁻ y : ℤ, ‖∑ k ∈ g.support, g k * torsionKernel A K (y - k)‖ₑ
            ^ ((2 * r : ℕ) : ℝ) ∂Measure.count := by
          refine lintegral_congr fun y => ?_
          rw [opArc_sigmaSubAFinset_eq_torsionKernel (A := A) φ hφ hK g y]
      _ ≤ _ := hkernel g.support (⇑g) (fun n hn => Finsupp.notMem_support_iff.mp hn)
  -- ## the modulated family, as finitely supported sequences
  set G : ι → ℤ →₀ ℂ := fun t => Finsupp.onFinset (F t).support
    (fun n => modSeq (⇑(F t)) (α t) n)
    (fun n hn => by
      by_contra hmem
      exact hn (by simp only [modSeq, Finsupp.notMem_support_iff.mp hmem, zero_mul])) with hG
  have hGcoe : ∀ t : ι, ⇑(G t) = modSeq (⇑(F t)) (α t) := fun t => Finsupp.coe_onFinset ..
  -- ## Marcinkiewicz–Zygmund
  have key := hmz (fun _ : Unit => (M : (ℤ →₀ ℂ) → (ℤ → ℂ)))
    (fun _ => IsLinearMap.mk (fun a b => M.map_add a b) (fun c a => M.map_smul c a))
    (fun _ g => (measurable_of_countable (M g)).aemeasurable) B hB hsingle G
  -- ## identification of the two sides
  have hleft : ∀ y : ℤ, (∑ _i : Unit, ∑ t : ι, ‖M (G t) y‖ₑ ^ (2 : ℝ))
      = (∑ t : ι, ‖opArc φ hφ (arcShift (sigmaSubAFinset A) (α t)) (⇑(F t))
          (memℓp_finsupp (F t)) y‖ₑ ^ (2 : ℝ)) := by
    intro y
    rw [Fintype.sum_unique]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    have hstep : ‖opArc φ hφ (arcShift (sigmaSubAFinset A) (α t)) (⇑(F t))
          (memℓp_finsupp (F t)) y‖ₑ
        = ‖M (G t) y‖ₑ := by
      rw [opArc_arcShift φ hφ (sigmaSubAFinset A) (α t) (⇑(F t)) (memℓp_finsupp (F t))]
      rw [hM, opArcLM_apply]
      rw [opArc_congr_fn φ hφ (memℓp_modSeq (memℓp_finsupp (F t)) (α t))
        (memℓp_finsupp (G t)) (hGcoe t).symm]
      rw [enorm_modSeq]
    exact hstep.symm
  have hright : ∀ y : ℤ, (∑ t : ι, ‖(⇑(G t) : ℤ → ℂ) y‖ₑ ^ (2 : ℝ))
      = (∑ t : ι, ‖(⇑(F t) : ℤ → ℂ) y‖ₑ ^ (2 : ℝ)) := by
    intro y
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hGcoe t, enorm_modSeq]
  have hp2 : ((2 * r : ℕ) : ℝ) / 2 = (r : ℝ) := by push_cast; ring
  have hL : ∫⁻ n : ℤ, (∑ t : ι, ‖opArc φ hφ (arcShift (sigmaSubAFinset A) (α t)) (⇑(F t))
        (memℓp_finsupp (F t)) n‖ₑ ^ (2 : ℝ)) ^ (r : ℝ) ∂Measure.count
      = ∫⁻ n : ℤ, (∑ _i : Unit, ∑ t : ι, ‖M (G t) n‖ₑ ^ (2 : ℝ))
          ^ (((2 * r : ℕ) : ℝ) / 2) ∂Measure.count := by
    refine lintegral_congr fun n => ?_
    rw [← hleft n, hp2]
  have hR : ∫⁻ n : ℤ, (∑ t : ι, ‖(⇑(F t) : ℤ → ℂ) n‖ₑ ^ (2 : ℝ)) ^ (r : ℝ) ∂Measure.count
      = ∫⁻ n : ℤ, (∑ t : ι, ‖(⇑(G t) : ℤ → ℂ) n‖ₑ ^ (2 : ℝ))
          ^ (((2 * r : ℕ) : ℝ) / 2) ∂Measure.count := by
    refine lintegral_congr fun n => ?_
    rw [← hright n, hp2]
  rw [hL, hR]
  refine key.trans ?_
  -- ## the constant
  have hC : ((Cmz ^ (1 / ((2 * r : ℕ) : ℝ)) * B) ^ ((2 * r : ℕ) : ℝ))
      = Cmz * B ^ ((2 * r : ℕ) : ℝ) := by
    rw [Real.mul_rpow (by positivity) hB, ← Real.rpow_mul (le_of_lt hCmzpos),
      show (1 / ((2 * r : ℕ) : ℝ)) * ((2 * r : ℕ) : ℝ) = 1 by field_simp, Real.rpow_one]
  rw [hC]

end

end Work.BourgainPlan.IonescuWainger
