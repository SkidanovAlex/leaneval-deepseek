import Mathlib
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLUInv.local_invariance_of_ae_haar

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Work.EKLContract

/-- `U` is normalised by the whole diagonal group, hence by all powers of `aDiag t0`. -/
lemma pow_conj_mem (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ) {u : SL3} (hu : u ∈ U)
    (n : ℕ) : aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹ ∈ U := by
  induction n with
  | zero => simpa using hu
  | succ k ih =>
    have hpow : aDiag t0 ^ (k + 1) = aDiag t0 * aDiag t0 ^ k := pow_succ' _ _
    rw [hpow]
    have key : aDiag t0 * aDiag t0 ^ k * u * (aDiag t0 * aDiag t0 ^ k)⁻¹
        = aDiag t0 * (aDiag t0 ^ k * u * (aDiag t0 ^ k)⁻¹) * (aDiag t0)⁻¹ := by group
    rw [key]
    exact hU.2.1 t0 _ ih

/-- **The `α`-iterates of a measure preserving `α`-action are measure preserving.** -/
lemma measurePreserving_aDiag_pow (μ : Measure X3) [IsProbabilityMeasure μ] (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ) (n : ℕ) :
    MeasurePreserving (fun x : X3 => aDiag t0 ^ n • x) μ μ := by
  induction n with
  | zero =>
    have h0 : (fun x : X3 => aDiag t0 ^ 0 • x) = id := by funext x; simp
    rw [h0]; exact MeasurePreserving.id μ
  | succ k ih =>
    have hcomp : MeasurePreserving
        ((fun x : X3 => aDiag t0 • x) ∘ (fun x : X3 => aDiag t0 ^ k • x)) μ μ := ht0.comp ih
    have heq : (fun x : X3 => aDiag t0 ^ (k + 1) • x)
        = (fun x : X3 => aDiag t0 • x) ∘ (fun x : X3 => aDiag t0 ^ k • x) := by
      funext x
      simp only [Function.comp_apply, pow_succ', mul_smul]
    rwa [heq]

/-- **The inverse maps of the `α`-iterates are measure preserving as well.**  If `μ.map φ = μ` for
`φ : x ↦ a^n • x`, then for `ψ : x ↦ (a^n)⁻¹ • x` we have `ψ ∘ φ = id`, hence
`μ.map ψ = (μ.map φ).map ψ = μ.map (ψ ∘ φ) = μ`. -/
lemma measurePreserving_aDiag_pow_inv (μ : Measure X3) [IsProbabilityMeasure μ]
    (t0 : Fin 3 → ℝ) (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ) (n : ℕ) :
    MeasurePreserving (fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x) μ μ := by
  have hpow := measurePreserving_aDiag_pow μ t0 ht0 n
  refine ⟨(continuous_const_smul _).measurable, ?_⟩
  have hcomp : (fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x) ∘ (fun x : X3 => aDiag t0 ^ n • x) = id := by
    funext x
    simp only [Function.comp_apply, id_eq, smul_smul, inv_mul_cancel, one_smul]
  calc μ.map (fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x)
      = (μ.map (fun x : X3 => aDiag t0 ^ n • x)).map (fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x) := by
        rw [hpow.map_eq]
    _ = μ.map ((fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x) ∘ (fun x : X3 => aDiag t0 ^ n • x)) := by
        rw [Measure.map_map (f := fun x : X3 => aDiag t0 ^ n • x)
              (g := fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x) (by fun_prop) (by fun_prop)]
    _ = μ := by rw [hcomp, Measure.map_id]

/-- **From the local invariance at the identity to the global invariance.**  If `μ` is preserved
by `x ↦ aDiag t0 • x`, `U` is a closed subgroup normalised by `aDiag` and contracted along the
powers of `aDiag t0`, then invariance of `μ` under the elements of `U` that are sufficiently
close to `1` implies invariance under all of `U`: for `u ∈ U` pick `n` with
`v := α^n u α^{-n} ∈ U ∩ V ε`; then `T_u = T_{α^{-n}} ∘ T_v ∘ T_{α^n}` and all three factors
preserve `μ`. -/
theorem isUInvariant_of_local (μ : Measure X3) [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ u ∈ U, u ∈ V ε → MeasurePreserving (fun x : X3 => u • x) μ μ) :
    IsUInvariant μ U := by
  intro u hu
  have hVnhds : V ε ∈ 𝓝 (1 : SL3) :=
    (Work.EKLContract.Lemmas.V_open_one ε hε).1.mem_nhds (Work.EKLContract.Lemmas.V_open_one ε hε).2
  obtain ⟨n, hn⟩ := ((hcontr u hu).eventually hVnhds).exists
  have hmem : aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹ ∈ U := pow_conj_mem U hU t0 hu n
  have hlocn := hloc _ hmem hn
  have hcomp : MeasurePreserving
      ((fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x)
        ∘ ((fun x : X3 => (aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) • x)
            ∘ (fun x : X3 => aDiag t0 ^ n • x))) μ μ :=
    (measurePreserving_aDiag_pow_inv μ t0 ht0 n).comp
      (hlocn.comp (measurePreserving_aDiag_pow μ t0 ht0 n))
  have heqfun : ((fun x : X3 => ((aDiag t0) ^ n)⁻¹ • x)
        ∘ ((fun x : X3 => (aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) • x)
            ∘ (fun x : X3 => aDiag t0 ^ n • x))) = (fun x : X3 => u • x) := by
    funext x
    simp only [Function.comp_apply]
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  rwa [heqfun] at hcomp

/-- **A.e. Haar leafwise measures imply invariance.**  Pisa 6.27 (⟸) / EKL (6): if the leafwise
measures of `μ` for the horospherical subgroup `U` are a.e. right-`U`-Haar, then `μ` is
`U`-invariant.  The analytic content (invariance of `μ` under the elements of `U` that are close
to the identity) is `Work.EKLUInv.local_invariance_of_ae_haar`; the passage to all of `U` is
`isUInvariant_of_local`, using the contraction `hcontr` and the `aDiag t0`-invariance `ht0`. -/
theorem isUInvariant_of_ae_translation (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hae : Work.EKLRelCross.AeHaar μ U ν) :
    Work.EKLContract.IsUInvariant μ U := by
  obtain ⟨ε, hε, hloc⟩ :=
    Work.EKLUInv.local_invariance_of_ae_haar h2 μ U hU t0 ht0 hcontr ν X' hL hae
  exact isUInvariant_of_local μ U hU t0 ht0 hcontr hε hloc

end

end Work.EKLRelCross
