import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBoxFock.PCFU.Ksfr_eq_lowKer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.integral_Ksfr_slot_split`

**The slot-split of the `s`-frame integral.**  Let `ℓ = ellH v μ`,
`κ = ((paramsAt μ (a v)).d²·sideAt μ (a v))⁻¹` and let `ψ : X n → ℝ` be a bounded measurable
state, `x : X n` a configuration and `j : Fin n` a slot.  Then

    ∫_{acube ℓ} Ksfr v fc μ N (u − x_j)·ψ(x[j↦u]) du
      = ℓ³·∫_{acube ℓ} (Σ'_d lowKer fc κ (u − x_j + ℓ•latVec d))·ψ(x[j↦u]) du
          − ℓ³·aP ℓ j ψ x .

The mathematical content is exactly the pointwise evaluation `Ksfr_eq_lowKer`

    Ksfr v fc μ N z = ℓ³·Σ'_d lowKer fc κ (z + ℓ•latVec d) − 1 ,

together with the definitional identity `ℓ³·aP ℓ j ψ x = ∫_{acube ℓ} ψ(x[j↦u]) du` (the slot
mean `aP`, `Submission/Q0Sector.lean`, is `ℓ⁻³` times the *unnormalised* integral over the
centred cube).  Everything else is the bookkeeping of the Bochner integral: the constant
factor `−1` produced by `Ksfr_eq_lowKer` is precisely the `aP` term.

## The three ingredients

* `continuous_Ksfr` / `norm_Ksfr_le` — `Ksfr` is a *finite* sum of plane waves (over the excited
  labels `Lab N`), hence continuous and uniformly bounded by `Σ_s |f_L(s)|`.  Uniform
  boundedness (independent of the argument) is what makes the slot integrand integrable on the
  cube.
* `pow_mul_aP_eq_integral` / `ofReal_pow_mul_aP_eq_integral` — the definitional unfolding of
  `aP` (no integrability condition: both sides are the same integral up to the invertible
  normalisation `ℓ³`).
* `integral_slot_split_core` — the abstract integration step: given a *pointwise* identity
  `Ksfr(u − x_j) = ℓ³·S u − 1` and the integrability of the two slot functions, the integral
  identity follows from `integral_sub` (the only place integrability is used), the
  `aP`-identity and `integral_congr_ae`/`integral_const_mul` (hypothesis-free).

Everything here is `sorry`-free.
-/

/-- `Ksfr` is continuous in its argument: it is a finite sum of plane waves with fixed
coefficients. -/
lemma continuous_Ksfr {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} :
    Continuous (fun z : E3 => Work.BoseBoxFock.Ksfr v fc μ N z) := by
  simp only [Work.BoseBoxFock.Ksfr]
  apply continuous_finsetSum
  intro s _
  apply Continuous.mul continuous_const
  apply Complex.continuous_exp.comp
  apply Continuous.mul continuous_const
  apply Complex.continuous_ofReal.comp
  exact continuous_const.inner continuous_id

/-- **Uniform bound on the `s`-frame**: `‖Ksfr z‖ ≤ Σ_{s ∈ excited} |f_L(s)|`, for *every* `z`.
The sum is over the finite excited label set and the coefficients `f_L(s)` are the real weights;
each plane wave has modulus `1`. -/
lemma norm_Ksfr_le {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} (z : E3) :
    ‖Work.BoseBoxFock.Ksfr v fc μ N z‖
      ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |Work.BoseBoxFock.fLh v fc μ N s| := by
  simp only [Work.BoseBoxFock.Ksfr]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul]
  have hexp : ‖Complex.exp (Complex.I * ((inner ℝ
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) z : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [hexp, mul_one]
  exact le_of_eq (RCLike.norm_ofReal (Work.BoseBoxFock.fLh v fc μ N s))

/-- **The `aP` normalisation, real form.**  The slot mean `aP ℓ j ψ x` is `ℓ⁻³` times the
unnormalised integral of `u ↦ ψ(x[j↦u])` over the centred cube; multiplying by `ℓ³` shows that
the unnormalised slot integral is `ℓ³·aP ℓ j ψ x`.  (Both sides are *the same* integral, so no
integrability hypothesis is needed.) -/
lemma pow_mul_aP_eq_integral {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    (ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    ℓ ^ 3 * Submission.BoseGases.aP ℓ j ψ x
      = ∫ u in Submission.BoseGases.acube ℓ, ψ (Function.update x j u) := by
  rw [Submission.BoseGases.aP]
  rw [← mul_assoc, one_div, mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

/-- **The `aP` normalisation, complex form**: the complexified version of
`pow_mul_aP_eq_integral`. -/
lemma ofReal_pow_mul_aP_eq_integral {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    (ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    ((ℓ : ℂ)) ^ 3 * ((Submission.BoseGases.aP ℓ j ψ x : ℝ) : ℂ)
      = ∫ u in Submission.BoseGases.acube ℓ, ((ψ (Function.update x j u) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, pow_mul_aP_eq_integral hℓ j ψ x]
  exact (integral_complex_ofReal).symm

/-- **The abstract integration core.**  Suppose the frame takes the pointwise form
`Ksfr v fc μ N (u − x_j) = ℓ³·S u − 1` on the cube, the two slot functions
`u ↦ (Ksfr(·−x_j)+1)·ψ_u` and `u ↦ ψ_u` are integrable on the cube, and the slot mean satisfies
`ℓ³·aP ℓ j ψ x = ∫_{acube ℓ} ψ_u`.  Then

    ∫_{acube ℓ} Ksfr(·−x_j)·ψ_u = ℓ³·∫_{acube ℓ} S u·ψ_u − ℓ³·aP ℓ j ψ x .

Proof: `integral_sub` splits `∫ ((Ksfr+1)·ψ − ψ) = ∫ (Ksfr+1)·ψ − ∫ ψ` (this is the *only* use of
integrability), both `∫ (Ksfr+1)·ψ = ℓ³∫ S·ψ` and `∫ (Ksfr·ψ) = ∫ ((Ksfr+1)·ψ − ψ)` are pointwise
(`integral_congr_ae`), and `ℓ³∫ S·ψ = ∫ ℓ³·(S·ψ)` is `integral_const_mul`. -/
private lemma integral_slot_split_core {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    {n : ℕ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    {ℓ : ℝ} (S : E3 → ℂ)
    (hpt : ∀ u : E3, Work.BoseBoxFock.Ksfr v fc μ N (u - x j) = ((ℓ : ℂ)) ^ 3 * S u - 1)
    (hI : Integrable (fun u : E3 => (Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
      * ((ψ (Function.update x j u) : ℝ) : ℂ)) (volume.restrict (Submission.BoseGases.acube ℓ)))
    (hJ : Integrable (fun u : E3 => ((ψ (Function.update x j u) : ℝ) : ℂ))
      (volume.restrict (Submission.BoseGases.acube ℓ)))
    (hAP : ((ℓ : ℂ)) ^ 3 * ((Submission.BoseGases.aP ℓ j ψ x : ℝ) : ℂ)
      = ∫ u in Submission.BoseGases.acube ℓ, ((ψ (Function.update x j u) : ℝ) : ℂ)) :
    (∫ u in Submission.BoseGases.acube ℓ, Work.BoseBoxFock.Ksfr v fc μ N (u - x j)
        * ((ψ (Function.update x j u) : ℝ) : ℂ))
      = ((ℓ : ℂ)) ^ 3 * (∫ u in Submission.BoseGases.acube ℓ,
          S u * ((ψ (Function.update x j u) : ℝ) : ℂ))
        - ((ℓ : ℂ)) ^ 3 * ((Submission.BoseGases.aP ℓ j ψ x : ℝ) : ℂ) := by
  have hsub := integral_sub hI hJ
  -- the integrand of `∫ ((Ksfr+1)·ψ − ψ)` is `Ksfr·ψ`
  have hleft : (∫ u in Submission.BoseGases.acube ℓ,
        ((Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1) * ((ψ (Function.update x j u) : ℝ) : ℂ)
          - ((ψ (Function.update x j u) : ℝ) : ℂ)))
      = ∫ u in Submission.BoseGases.acube ℓ, Work.BoseBoxFock.Ksfr v fc μ N (u - x j)
          * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
    have hfun : (fun u : E3 => (Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
          * ((ψ (Function.update x j u) : ℝ) : ℂ) - ((ψ (Function.update x j u) : ℝ) : ℂ))
        = fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - x j)
            * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
      funext u; ring
    rw [hfun]
  -- the pointwise frame identity turns `(Ksfr+1)·ψ` into `ℓ³·(S·ψ)`
  have hright : (∫ u in Submission.BoseGases.acube ℓ,
        (Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
        * ((ψ (Function.update x j u) : ℝ) : ℂ))
      = ((ℓ : ℂ)) ^ 3 * (∫ u in Submission.BoseGases.acube ℓ,
          S u * ((ψ (Function.update x j u) : ℝ) : ℂ)) := by
    have hfun : (fun u : E3 => (Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
          * ((ψ (Function.update x j u) : ℝ) : ℂ))
        = fun u : E3 => ((ℓ : ℂ)) ^ 3 * (S u * ((ψ (Function.update x j u) : ℝ) : ℂ)) := by
      funext u; rw [hpt u]; ring
    rw [hfun, integral_const_mul]
  rw [hleft, hright, ← hAP] at hsub
  exact hsub

theorem integral_Ksfr_slot_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {fc : Work.BoseBoxFix.LowCut}
    {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    {n : ℕ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ) (hψm : Measurable ψ)
    (hψb : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C) (x : Submission.BoseGases.X n) :
    ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        Work.BoseBoxFock.Ksfr v fc μ N (u - x j) * ((ψ (Function.update x j u) : ℝ) : ℂ)
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                    (u - x j + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                * ((ψ (Function.update x j u) : ℝ) : ℂ))
        - ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j ψ x : ℝ) : ℂ) := by
  -- ### the pointwise `lowKer` form of the frame (`Ksfr_eq_lowKer`)
  have hpt := fun u : E3 => Ksfr_eq_lowKer (v := v) (fc := fc) (μ := μ) (N := N)
    hℓ hκ hN (u - x j)
  -- ### measurability and boundedness of the slot-lifted state
  obtain ⟨Cψ, hCψ⟩ := hψb
  have hCψ0 : 0 ≤ Cψ := le_trans (norm_nonneg _) (hCψ (0 : Submission.BoseGases.X n))
  have hψaesm : AEStronglyMeasurable
      (fun u : E3 => ((ψ (Function.update x j u) : ℝ) : ℂ))
      (volume.restrict (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))) :=
    ((Complex.continuous_ofReal.measurable).comp
      (hψm.comp (by fun_prop : Measurable
        (fun u : E3 => Function.update x j u)))).aestronglyMeasurable
  have hcube_lt : (volume : Measure E3)
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) < ⊤ :=
    Submission.BoseGases.acube_lt_top _ hℓ.le
  -- ### integrability of the two slot functions on the cube (bounded functions, finite volume)
  have hJ : IntegrableOn (fun u : E3 => ((ψ (Function.update x j u) : ℝ) : ℂ))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound hcube_lt hψaesm Cψ (Filter.Eventually.of_forall fun u => by
      simpa using hCψ (Function.update x j u))
  have hKaesm : AEStronglyMeasurable
      (fun u : E3 => (Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
        * ((ψ (Function.update x j u) : ℝ) : ℂ))
      (volume.restrict (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))) := by
    have h1 : AEStronglyMeasurable
        (fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
        (volume.restrict (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))) :=
      (((continuous_Ksfr.comp (by fun_prop : Continuous (fun u : E3 => u - x j))).add
        continuous_const).aestronglyMeasurable)
    exact h1.mul hψaesm
  have hIbdd : ∀ u : E3, ‖(Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
        * ((ψ (Function.update x j u) : ℝ) : ℂ)‖
      ≤ ((∑ s ∈ Work.BoseB7.excited (Lab N), |Work.BoseBoxFock.fLh v fc μ N s|) + 1) * Cψ := by
    intro u
    have hBK0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |Work.BoseBoxFock.fLh v fc μ N s| :=
      Finset.sum_nonneg fun s _ => abs_nonneg _
    rw [norm_mul]
    refine mul_le_mul (le_trans (norm_add_le _ _)
      (add_le_add (norm_Ksfr_le (u - x j)) (by simp)))
      (by simpa using hCψ (Function.update x j u)) (norm_nonneg _)
      (add_nonneg hBK0 zero_le_one)
  have hI : IntegrableOn (fun u : E3 => (Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1)
        * ((ψ (Function.update x j u) : ℝ) : ℂ))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound hcube_lt hKaesm _
      (Filter.Eventually.of_forall hIbdd)
  -- ### the slot mean `aP`
  have hAP : ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
        * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j ψ x : ℝ) : ℂ)
      = ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
          ((ψ (Function.update x j u) : ℝ) : ℂ) :=
    ofReal_pow_mul_aP_eq_integral hℓ j ψ x
  exact integral_slot_split_core (v := v) (fc := fc) (μ := μ) (N := N) j ψ x
    (fun u : E3 => ∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (u - x j + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
    hpt hI hJ hAP

end Work.BoseBoxFock.PCFU
