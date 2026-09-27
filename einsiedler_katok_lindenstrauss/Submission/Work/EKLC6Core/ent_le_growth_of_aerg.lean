import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core.HcondSig_eq_growth_free
import Submission.Work.EKLC6Core.Ch_ent_le_HcondSig_gen
import Submission.Work.EKLC6Core.exists_plaque_alg_gen_modmu
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.ent_le_growth_of_aerg` — the `aDiag t`-ergodic case of Pisa 7.6(ii), equality

For an `aDiag t`-ergodic probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a leaf-wise system
`ν = μ_x^{U}` for the full contracted horospherical subgroup `U = Uminus t`, and
`growthFun (Uminus t) ν t x = -log ν x (conjBox (Uminus t) t)`, the Kolmogorov–Sinai entropy of
`aDiag t ·` is bounded by the integral of the growth function:

`ent μ (aDiag t ·) ≤ ofReal (∫ growthFun (Uminus t) ν t dμ)`.

This is the equality case of Pisa 7.6(ii) for `U = G⁻(t)`.

The proof splits in two.

* **Degenerate case `Uminus t = ⊥`** (equivalently `aDiag t = 1`): the entropy vanishes
  (`Basic.ent_aDiag_eq_zero_of_uminus_eq_bot`) and the integrand is `0` a.e. because the
  conjugated box is `{1}`, on which a leaf-wise system is normalised
  (`growthFun_eq_zero_ae_of_uminus_eq_bot` below).

* **Main case.**  The geometric input `Work.EKLC6Core.exists_plaque_alg_gen_modmu`
  (Pisa 7.37/7.38 + 7.43 in the *modulo `μ`* form) provides a countable Borel family `S` and a
  `μ`-conull set `Z` such that
  * the past σ-algebra `A = pastSigSet t S = ⨆ n, comap ((aDiag t ·)^[n]) σ(S)` is a plaque
    algebra for `Uminus t` on `Z`,
  * `S` generates `borel X₃` modulo `μ` (`GeneratesModMuSet μ t S`), and
  * `σ(S)` has finite entropy in the sense `HcondSig μ (σ(S)) ⊥ ≠ ⊤`.
  The measure-theoretic core `Work.EKLC6Core.ent_le_HcondSig_of_genData_modMu` (Pisa 7.43 ⇒ 7.6(ii)
  equality, the mod-`μ` Kolmogorov–Sinai generating theorem
  `Ch_ent_le_iSup_hPart_of_modMu_gen` followed by Lévy from above for `HcondSig`) then gives

  `ent μ (aDiag t ·) ≤ HcondSig μ A (comap (aDiag t ·) A)`,

  and Pisa 7.34/7.35 (`Work.EKLC6Core.HcondSig_eq_growth_free`) identifies the right-hand side
  with `ofReal (∫ growthFun (Uminus t) ν t)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `Box1` of the trivial subgroup is the identity. -/
theorem box1_bot : Box1 (⊥ : Subgroup SL3) = {1} := by
  ext g
  simp only [Box1, Set.mem_ofPred_eq, Subgroup.mem_bot, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hg, -⟩
    exact hg
  · intro hg
    subst hg
    refine ⟨rfl, ?_⟩
    intro i j
    simp [Matrix.one_apply]

/-- Conjugation fixes the identity. -/
theorem conjBy_singleton_one (t : Fin 3 → ℝ) : conjBy t ({1} : Set SL3) = {1} := by
  ext g
  simp only [conjBy, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    subst hh
    simp
  · intro hg
    refine ⟨1, rfl, ?_⟩
    subst hg
    simp

/-- In the degenerate case `Uminus t = ⊥` the growth function vanishes a.e. -/
theorem growthFun_eq_zero_ae_of_uminus_eq_bot {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ (⊥ : Subgroup SL3) ν X') :
    ∀ᵐ x ∂μ, Work.EKLC6Core.growthFun (⊥ : Subgroup SL3) ν t x = 0 := by
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := MeasureTheory.ae_iff.mpr hL.conull
  have hconjBox : conjBox (⊥ : Subgroup SL3) t = {1} := by
    rw [conjBox, box1_bot, conjBy_singleton_one]
  filter_upwards [hX'] with x hx
  have hn : ν x (conjBox (⊥ : Subgroup SL3) t) = 1 := by
    rw [hconjBox, ← box1_bot]
    exact hL.normalised x hx
  rw [growthFun, hn, ENNReal.toReal_one, Real.log_one, neg_zero]

theorem ent_le_growth_of_aerg {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hqerg : ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E →
      μ E = 0 ∨ μ Eᶜ = 0)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ) :
    Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ≤
      ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  by_cases hU : Work.EKLC6Core.Uminus t = ⊥
  · -- degenerate case: `Uminus t = ⊥`, so that `aDiag t = 1` and the growth function vanishes
    have hzero : (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) = 0 := by
      have hae : ∀ᵐ x ∂μ, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x = 0 := by
        have h := growthFun_eq_zero_ae_of_uminus_eq_bot (μ := μ) (ν := ν) (X' := X') t
          (hU ▸ hL)
        filter_upwards [h] with x hx
        rwa [hU]
      rw [integral_congr_ae hae, integral_zero]
    have hent : Work.EKLContract.ent μ
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) = 0 :=
      ent_aDiag_eq_zero_of_uminus_eq_bot t hU
    rw [hent, hzero, ENNReal.ofReal_zero]
  · -- the main case: the countable generator of Pisa 7.43 and the measure-theoretic core
    obtain ⟨S, Z, hS, hplq, hZ, hgen, hfin⟩ :=
      Work.EKLC6Core.exists_plaque_alg_gen_modmu (μ := μ) t hmp hqerg hU
    -- Pisa 7.43 ⇒ Pisa 7.6(ii) equality: `ent μ T ≤ HcondSig μ A (comap T A)`
    have h1 : Work.EKLContract.ent μ
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
        ≤ Work.EKLC6Core.HcondSig μ (Work.EKLC6Core.pastSigSet t S)
            (MeasurableSpace.comap
              (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
              (Work.EKLC6Core.pastSigSet t S)) :=
      Work.EKLC6Core.ent_le_HcondSig_of_genData_modMu (μ := μ) t hmp S hS hgen hfin
    -- Pisa 7.34/7.35: the conditional entropy of the plaque algebra is the growth integral
    have h2 : Work.EKLC6Core.HcondSig μ (Work.EKLC6Core.pastSigSet t S)
            (MeasurableSpace.comap
              (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
              (Work.EKLC6Core.pastSigSet t S))
        = ENNReal.ofReal
            (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) :=
      Work.EKLC6Core.HcondSig_eq_growth_free (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hmp hL
        hcov hX'' hmeas hint hplq hZ (Work.EKLC6Core.comap_pastSigSet_le t S)
    rw [h2] at h1
    exact h1

end Work.EKLC6Core

end
