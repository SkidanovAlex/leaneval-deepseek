import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chCintand_integrable
import Submission.Work.BoseBoxFock.PCFU.chDintand_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chint_integrable`

Integrability of the four channel integrands of the cubic dictionary: the four channel integrals
`chAint … chDint` (`ChWordChains.lean`) are Bochner integrals of

    `chAintand`, …, `chDintand : X n × (E3 × E3) → ℂ`,

and this module proves that each of them is `Integrable` for every measurable, bounded state `Θ`
supported in the `n`-particle box `abox n (ellH v μ)`.

Each of the four channel kernels `ChAU`, `ChBU`, `ChCU`, `ChDU` (`UnivFrames.lean`) is a product of

* the two bounded frames `Ksfr` (`‖Ksfr z‖ ≤ Σ_s |f_L(s)|`, `norm_Ksfr_le`),
  `KfrU` / `KχfrU` (`norm_KfrU_le`, `norm_KχfrU_le`) — finite sums of plane waves; for the
  `(C)`,`(D)` channels there is also a `w`-integral of `χ_Λ(w)·Ksfr(x+w)·{KfrU,KχfrU}(…)`, which is
  uniformly bounded because it is supported in the finite-volume box `boxL ℓ`
  (`ch_norm_integral_le_of_support_boxL`, `volume_boxL`),
* the corpus localisation `χ_Λ = corpusBox.chiLam ℓ` (modulus `≤ (√chiNormSq)⁻¹`, support in
  `boxL ℓ`, `BoxData.chiLam_supp`),
* the sharp box indicator `θ_Λ = corpusBox.thetaFun ℓ` (modulus `≤ 1`, support `boxL ℓ`),

so the general lemma `chChannelIntegrable` applies verbatim with `K := ChAU` (resp. `ChBU`,
`ChCU`, `ChDU`): the kernel is measurable, uniformly bounded, and vanishes when its first slot
leaves `boxL ℓ` (`(A)`,`(B)` via `χ_Λ(y)`; `(C)`,`(D)` via `θ_Λ(y)`) and when its last slot leaves
`boxL ℓ` (`(A)`,`(C)` via `χ_Λ(u)`; `(B)`,`(D)` via `θ_Λ(u)`).  The `(A)`,`(B)` channels are
instantiated here; the two channels whose kernel carries an inner `w`-integral, `(C)` and `(D)`,
are proved in the sibling modules `PCFU/chCintand_integrable` and `PCFU/chDintand_integrable`
(same statement, same namespace, so that the declaration exists only once in the workspace).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

open Work.BoseB4 Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The `(A)` channel -/

/-- The `(A)`-channel integrand is integrable. -/
theorem chAintand_integrable {n : ℕ} (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    MeasureTheory.Integrable (chAintand v h fc fu μ N i j Θ) := by
  have hℓ : 0 < ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hKm : Measurable (fun p : E3 × (E3 × E3) => ChAU v h fc fu μ N p.1 p.2.1 p.2.2) := by
    have hKs : Measurable (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr.measurable
    have hKf : Measurable (fun z : E3 => KfrU v h μ fu N z) :=
      (continuous_KfrU v h μ fu N).measurable
    have hχ : Measurable (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)).measurable
    have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
      ch_measurable_thetaFun _
    unfold ChAU
    refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · refine Measurable.mul ?_ ?_
          · exact hKs.comp (by fun_prop)
          · exact hχ.comp (by fun_prop)
        · exact hθ.comp (by fun_prop)
      · exact hχ.comp (by fun_prop)
    · exact hKf.comp (by fun_prop)
  have hKb : ∃ CK : ℝ, ∀ p : E3 × (E3 × E3),
      ‖ChAU v h fc fu μ N p.1 p.2.1 p.2.2‖ ≤ CK := by
    refine ⟨(∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
        * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * 1
        * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
        * (∑ k : Lab N, |W1h v h μ fu N k|), fun p => ?_⟩
    rw [ChAU, norm_mul, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact norm_Ksfr_le (p.2.1 - p.1)
    · exact norm_chiLam_le (ellH v μ) p.1
    · exact ch_thetaFun_norm_le (ellH v μ) p.2.1
    · exact norm_chiLam_le (ellH v μ) p.2.2
    · exact norm_KfrU_le v h μ fu N (p.1 - p.2.2)
  obtain ⟨CK, hCK⟩ := hKb
  have hKs1 : ∀ y x u : E3, y ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
      ChAU v h fc fu μ N y x u = 0 := by
    intro y x u hy
    have hz : Work.BoseK15.corpusBox.chiLam (ellH v μ) y = 0 :=
      ch_chiLam_eq_zero_of_notMem hℓ hy
    rw [ChAU, hz]; simp
  have hKs2 : ∀ y x u : E3, u ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
      ChAU v h fc fu μ N y x u = 0 := by
    intro y x u hu
    have hz : Work.BoseK15.corpusBox.chiLam (ellH v μ) u = 0 :=
      ch_chiLam_eq_zero_of_notMem hℓ hu
    rw [ChAU, hz]; simp
  exact chChannelIntegrable hℓ Θ hΘm hΘb hΘs i j
    (fun p : E3 × (E3 × E3) => ChAU v h fc fu μ N p.1 p.2.1 p.2.2) hKm CK hCK hKs1 hKs2

/-! ## The `(B)` channel -/

/-- The `(B)`-channel integrand is integrable. -/
theorem chBintand_integrable {n : ℕ} (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    MeasureTheory.Integrable (chBintand v h fc fu μ N i j Θ) := by
  have hℓ : 0 < ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hKm : Measurable (fun p : E3 × (E3 × E3) => ChBU v h fc fu μ N p.1 p.2.1 p.2.2) := by
    have hKs : Measurable (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr.measurable
    have hKf : Measurable (fun z : E3 => KχfrU v h μ fu N z) :=
      (continuous_KχfrU v h μ fu N).measurable
    have hχ : Measurable (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)).measurable
    have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
      ch_measurable_thetaFun _
    unfold ChBU
    refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · refine Measurable.mul ?_ ?_
          · exact hKs.comp (by fun_prop)
          · exact hχ.comp (by fun_prop)
        · exact hθ.comp (by fun_prop)
      · exact hθ.comp (by fun_prop)
    · exact hKf.comp (by fun_prop)
  have hKb : ∃ CK : ℝ, ∀ p : E3 × (E3 × E3),
      ‖ChBU v h fc fu μ N p.1 p.2.1 p.2.2‖ ≤ CK := by
    refine ⟨(∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
        * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * 1 * 1
        * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|), fun p => ?_⟩
    rw [ChBU, norm_mul, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact norm_Ksfr_le (p.2.1 - p.1)
    · exact norm_chiLam_le (ellH v μ) p.1
    · exact ch_thetaFun_norm_le (ellH v μ) p.2.1
    · exact ch_thetaFun_norm_le (ellH v μ) p.2.2
    · exact norm_KχfrU_le v h μ fu N p.1
  obtain ⟨CK, hCK⟩ := hKb
  have hKs1 : ∀ y x u : E3, y ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
      ChBU v h fc fu μ N y x u = 0 := by
    intro y x u hy
    have hz : Work.BoseK15.corpusBox.chiLam (ellH v μ) y = 0 :=
      ch_chiLam_eq_zero_of_notMem hℓ hy
    rw [ChBU, hz]; simp
  have hKs2 : ∀ y x u : E3, u ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
      ChBU v h fc fu μ N y x u = 0 := by
    intro y x u hu
    have hz : Work.BoseK15.corpusBox.thetaFun (ellH v μ) u = 0 :=
      ch_thetaFun_eq_zero_of_notMem hu
    rw [ChBU, hz]; simp
  exact chChannelIntegrable hℓ Θ hΘm hΘb hΘs i j
    (fun p : E3 × (E3 × E3) => ChBU v h fc fu μ N p.1 p.2.1 p.2.2) hKm CK hCK hKs1 hKs2

/-! ## The four channel integrands are integrable -/

theorem chint_integrable {n : ℕ} (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    MeasureTheory.Integrable (Work.BoseBoxFock.PCFU.chAintand v h fc fu μ N i j Θ)
      ∧ MeasureTheory.Integrable (Work.BoseBoxFock.PCFU.chBintand v h fc fu μ N i j Θ)
      ∧ MeasureTheory.Integrable (Work.BoseBoxFock.PCFU.chCintand v h fc fu μ N i j Θ)
      ∧ MeasureTheory.Integrable (Work.BoseBoxFock.PCFU.chDintand v h fc fu μ N i j Θ) :=
  ⟨chAintand_integrable v h fc fu μ N i j Θ hΘm hΘb hΘs,
   chBintand_integrable v h fc fu μ N i j Θ hΘm hΘb hΘs,
   chCintand_integrable v h fc fu μ N i j Θ hΘm hΘb hΘs,
   chDintand_integrable v h fc fu μ N i j Θ hΘm hΘb hΘs⟩

end Work.BoseBoxFock.PCFU
