import Mathlib
import Submission.Work.Analysis.CzShift.l2_bound_of_fourier_symbol
import Submission.Work.Analysis.CzShift.fourier_shiftKernelC
import Submission.Work.Analysis.CzShift.lacunary_multiplier_sum_norm_le
import Submission.Work.Analysis.CzShift.offdiag_le

/-!
# The `L²` bound for the shifted kernel family `shiftKernelFam`

This module proves `Work.Analysis.CzShift.l2_bound_shiftKernelFam`: the `p = 2` case of the
shifted Calderón–Zygmund theorem of Appendix B of Krause–Mirek–Tao, *Pointwise ergodic
theorems for non-conventional bilinear polynomial averages*, Annals of Math. **195** (2022).

For a `λ`-lacunary family of scales `σ : ι → ℝ` (`LacunaryFam λ D σ`), arbitrary shifts `t`, a
rescaled Schwartz seed `Ψ` (`IsCZSeed Ψ Ψ' B`) with symbol `ψ = 𝓕 Ψ` supported in `[-C,C]` and
obeying `‖ψ ξ‖ ≤ C min 1 |ξ|`, and signs `‖ε i‖ ≤ 1`, the operator

  `T_ε = ∑_{i ∈ D} ε_i (K_i ⋆ ·)`,  `K_i x = σ_i⁻¹ Ψ((x - t_i σ_i)/σ_i)`,

satisfies `‖T_ε f‖₂ ≤ Cm ‖f‖₂`, with `Cm` depending only on `λ` and `C` — in particular it is
*uniform* in the index type `ι`, the family `D`, the scales, the shifts, the seed size `B` and
the signs `ε`.

The proof is in three steps.

* **The Fourier symbol.**  By `fourier_shiftKernelC`, the symbol of the kernel `K_i` is
  `𝓕 K_i (ξ) = ψ(σ_i ξ) e(-t_i σ_i ξ)`; the phase factor has modulus one, so
  `‖∑_{i ∈ D} ε_i 𝓕 K_i (ξ)‖ ≤ ∑_{i ∈ D} ‖ψ(σ_i ξ)‖`.
* **The lacunary sum.**  `lacunary_multiplier_sum_norm_le` bounds `∑_{i ∈ D} ‖ψ(σ_i ξ)‖`
  uniformly in the (lacunary) family and in `ξ`.  That lemma is stated for a *fixed* index type,
  while the present statement needs one constant valid for all `ι`; we therefore apply it with
  index type `ℝ`, reindexing the sum along `σ` (which is injective on `D` by lacunarity, so that
  `∑_{i ∈ D} f (σ i) = ∑_{s ∈ σ '' D} f s` and the image family is again lacunary).
* **Plancherel.**  `l2_bound_of_fourier_symbol` turns the uniform bound on the symbol into the
  `L²` bound, given integrability and boundedness of the kernels, which are the first two
  conclusions of `kernel_bounds` (`offdiag_le` provides the integrability).
-/

namespace Work.Analysis.CzShift

open MeasureTheory Finset
open scoped FourierTransform

theorem l2_bound_shiftKernelFam (lam C : ℝ) (hlam : 1 < lam) (hC : 0 < C) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (σ t : ι → ℝ) (Ψ Ψ' : ℝ → ℝ) (B : ℝ) (ε : ι → ℂ)
      (hlac : LacunaryFam lam D σ) (hseed : IsCZSeed Ψ Ψ' B) (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
      (hψsupp : ∀ ξ : ℝ, C < |ξ| →
        FourierTransform.fourier (fun u => (Ψ u : ℂ)) ξ = 0)
      (hψbd : ∀ ξ : ℝ,
        ‖FourierTransform.fourier (fun u => (Ψ u : ℂ)) ξ‖ ≤ C * min 1 |ξ|),
      ∀ f : ℝ → H, MeasureTheory.Integrable f → MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal Cm * MeasureTheory.eLpNorm f 2 MeasureTheory.volume := by
  -- The constant of the lacunary multiplier-sum lemma, taken at the fixed index type `ℝ`.
  obtain ⟨Cm, hCmpos, hsum⟩ := lacunary_multiplier_sum_norm_le (ι := ℝ) lam C hlam hC
  refine ⟨Cm, hCmpos, ?_⟩
  intro ι H _ _ _ D σ t Ψ Ψ' B ε hlac hseed hε hψsupp hψbd f hf hf2
  classical
  set ψc : ℝ → ℂ := FourierTransform.fourier (fun u => (Ψ u : ℂ)) with hψc
  -- ### Integrability of the complexified seed
  have hdiff : Differentiable ℝ Ψ := fun u => (hseed.hasDerivAt u).differentiableAt
  have hΨcont : Continuous Ψ := hdiff.continuous
  have hIntΨ : Integrable (fun u => (Ψ u : ℂ)) := by
    have hbump : Integrable (fun u : ℝ => B * (1 + u ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul B
    refine Integrable.mono' hbump (Complex.continuous_ofReal.comp hΨcont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hseed.bound u
    rw [div_eq_mul_inv] at h1
    simpa using h1
  -- ### Integrability and boundedness of the shifted kernels
  have hIntK : ∀ i ∈ D, Integrable (shiftKernelFam Ψ σ t i) :=
    fun i hi => integrable_shiftKernel hseed (hlac.1 i hi)
  have hBddK : ∀ i ∈ D, ∃ c : ℝ, ∀ x, ‖shiftKernelFam Ψ σ t i x‖ ≤ c :=
    fun i hi => ⟨B / σ i, (kernel_bounds hseed).1 (σ i) (t i) (hlac.1 i hi)⟩
  have hsupp' : ∀ ξ : ℝ, C < |ξ| → ψc ξ = 0 := fun ξ hξ => by rw [hψc]; exact hψsupp ξ hξ
  have hbd' : ∀ ξ : ℝ, ‖ψc ξ‖ ≤ C * min 1 |ξ| := fun ξ => by rw [hψc]; exact hψbd ξ
  -- ### Lacunarity of the image family and injectivity of `σ` on `D`
  have hinj : Set.InjOn σ ↑D := by
    intro i hi j hj heq
    by_contra hne
    have h := hlac.2 i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hne
    simp only [heq, min_self, max_self] at h
    have hpos : 0 < σ j := hlac.1 j (Finset.mem_coe.mp hj)
    have h1 : lam ≤ 1 := by
      have h' : lam * σ j ≤ 1 * σ j := by simpa using h
      exact (mul_le_mul_iff_of_pos_right hpos).mp h'
    linarith
  have hlacImage : LacunaryFam lam (D.image σ) id := by
    constructor
    · intro s hs
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      simpa using hlac.1 i hi
    · intro s hs s' hs' hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs'
      have hij : i ≠ j := fun h => hne (by rw [h])
      simpa using hlac.2 i hi j hj hij
  -- ### The bound on the Fourier symbol
  have hsym : ∀ ξ : ℝ,
      ‖∑ i ∈ D, ε i * FourierTransform.fourier (shiftKernelFam Ψ σ t i) ξ‖ ≤ Cm := by
    intro ξ
    have hterm : ∀ i ∈ D,
        ‖ε i * FourierTransform.fourier (shiftKernelFam Ψ σ t i) ξ‖ ≤ ‖ψc (σ i * ξ)‖ := by
      intro i hi
      have hσ : 0 < σ i := hlac.1 i hi
      have hfour : FourierTransform.fourier (shiftKernelFam Ψ σ t i) ξ
          = ψc (σ i * ξ)
            * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t i * σ i * ξ : ℝ) : ℂ))) := by
        have h := fourier_shiftKernelC (fun u => (Ψ u : ℂ)) (σ i) (t i) hσ hIntΨ ξ
        rw [← shiftKernel_eq_shiftKernelC] at h
        rw [hψc]
        simpa only [shiftKernelFam] using h
      have hph : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
          ((t i * σ i * ξ : ℝ) : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]
        have hre : (-(2 * (Real.pi : ℂ) * Complex.I * ((t i * σ i * ξ : ℝ) : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre, Real.exp_zero]
      rw [hfour, norm_mul, norm_mul, hph, mul_one]
      exact mul_le_of_le_one_left (norm_nonneg _) (hε i hi)
    calc ‖∑ i ∈ D, ε i * FourierTransform.fourier (shiftKernelFam Ψ σ t i) ξ‖
        ≤ ∑ i ∈ D, ‖ε i * FourierTransform.fourier (shiftKernelFam Ψ σ t i) ξ‖ :=
          norm_sum_le D _
      _ ≤ ∑ i ∈ D, ‖ψc (σ i * ξ)‖ := Finset.sum_le_sum hterm
      _ = ∑ s ∈ D.image σ, ‖ψc (s * ξ)‖ := by
          rw [Finset.sum_image (f := fun s => ‖ψc (s * ξ)‖) (s := D) (g := σ) hinj]
      _ ≤ Cm := hsum (D.image σ) id ψc hlacImage hsupp' hbd' ξ
  -- ### Plancherel
  exact l2_bound_of_fourier_symbol D (shiftKernelFam Ψ σ t) ε Cm hCmpos.le hIntK hBddK hsym
    f hf hf2

end Work.Analysis.CzShift
