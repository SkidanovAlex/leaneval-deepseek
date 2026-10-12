import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BSKinetic.integral_bsWin_deriv_sq
import Submission.Work.BSKinetic.locKinEnWordBox_of_familyBound
import Submission.Work.BlockBound4.chiScale_grad_bound
import Submission.Work.BoseKinLoc.Gap.gapBare_eq_expand
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.fsT_bound_abs` — the one-body localised kinetic word is `H¹`-bounded

FS `lem:LocKinEn`'s left-hand side is the *one-body* localised kinetic word

`fsT ℓ d s ε_T b u ψ = neuWord + gapWord + momWord + mainWord`

(FS `eq:DefT`, `Submission/Work/BoseKinLoc/Defs.lean`).  This file proves that for fixed
parameters (`ℓ > 0`, `d > 0`, and **any** reals `s, ε_T, b`) and under the single hypothesis
`hmom` that the large-momentum form is dominated by the mean-free box mass (FS `eq:Q1Qslide`),

`momForm ℓ d u ψ ≤ ∫_{Λ(u)}(Q_uψ)²`,

the word is bounded in absolute value by a constant times the free `H¹`-norm of `ψ`,

`|fsT ℓ d s ε_T b u ψ| ≤ C·(∫ψ² + Σ_k∫(∂_kψ)²)`,

where `C` depends only on `(ℓ, d, s, ε_T, b)` — in particular **uniformly in the translation
parameter `u`** and uniformly in the state `ψ`.

## The four pieces and their bounds

For `ψ ∈ C_c^∞` and every `u`, with `Λ(u) = lamBox ℓ u`, `Q_uψ = Qfree ℓ u ψ` and
`gapBare ℓ u ψ = ∫_{Λ(u)}(Q_uψ)²`:

| piece | bound | ingredient |
|---|---|---|
| `neuWord = ½ε_T(dℓ)⁻²·neuFrac(Q_uψ)` | `≤ |½ε_T(dℓ)⁻²|·gapBare` | `0 ≤ neuFrac ≤ gapBare` (`g = 0` trial, `neuFrac_le_gapBare`) |
| `gapWord = bℓ⁻²·gapBare` | `≤ |bℓ⁻²|·gapBare` | `gapBare_nonneg` |
| `momWord = bε_T(dℓ)⁻²·momForm` | `≤ |bε_T(dℓ)⁻²|·gapBare` | `hmom`, `momForm_nonneg` |
| `mainWord` | `≤ (|1-ε_T|·2(1+c₁²) + |ε_T|·2(1+c₂²))·W` | `bsOneBody_le_weighted` |

where `c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`, and `W = ∫(χ_uQ_uψ)² + Σ_k∫(∂_k(χ_uQ_uψ))²` is the
`H¹`-norm of the windowed mean-free state.  The mean-free box mass is controlled by the free
mass,

`gapBare ℓ u ψ = ∫_Λψ² − ℓ³m_u² ≤ ∫ψ²`   (`gapBare_eq_expand`),

and the windowed state satisfies the uniform `H¹`-bound `W ≤ K·(∫ψ² + Σ_k∫(∂_kψ)²)` with `K`
depending on `ℓ` only (`windowed_L2_le`, `windowed_dir_le`).  The latter is the only analytic
content: `χ_u` and `∂_kχ_u` are the fixed bump `χ` and `ℓ⁻¹∂_kχ` up to translation, so
`‖χ_u‖_∞ ≤ chiSupAbs` (`chiScale_abs_le_sup`) and
`Σ_k(∂_kχ_u)² ≤ Kg/ℓ²` (`chiScale_grad_bound`), while the box mean is dominated by the box mass,
`ℓ³m_u² ≤ ∫_Λψ²` (the case `gapBare ≥ 0` of `gapBare_eq_expand` together with
`∫_Λψ² ≤ ∫ψ²`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic
open Submission.BoseGases
open Work.BSKinetic
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

private lemma sq_fun_eq (ψ : ℝ³ → ℝ) : (fun z : ℝ³ => (ψ z) ^ 2) = fun z : ℝ³ => ψ z * ψ z := by
  funext z; ring

private lemma psi_sq_integrable {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) : Integrable (fun z : ℝ³ => (ψ z) ^ 2) := by
  rw [sq_fun_eq]
  exact (hψ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcs.mul_right

private lemma psi_sq_cs {ψ : ℝ³ → ℝ} (hcs : HasCompactSupport ψ) :
    HasCompactSupport (fun z : ℝ³ => (ψ z) ^ 2) := by
  rw [sq_fun_eq]
  exact hcs.mul_right

private lemma boxIntegral_le (ℓ : ℝ) (u : ℝ³) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2) ≤ ∫ z : ℝ³, (ψ z) ^ 2 :=
  MeasureTheory.setIntegral_le_integral (psi_sq_integrable hψ hcs)
    (Filter.Eventually.of_forall fun z => sq_nonneg (ψ z))

private lemma gapBare_le_integral_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BoseKinLoc.gapBare ℓ u ψ ≤ ∫ z : ℝ³, (ψ z) ^ 2 := by
  have hexp := Work.BoseKinLoc.Gap.gapBare_eq_expand ℓ hℓ ψ hψ u
  have hle := boxIntegral_le ℓ u hψ hcs
  have hb : 0 ≤ ℓ ^ 3 * (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 :=
    mul_nonneg (pow_nonneg hℓ.le 3) (sq_nonneg _)
  rw [hexp]; linarith

private lemma mean_sq_mul_le {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 * ℓ ^ 3 ≤ ∫ z : ℝ³, (ψ z) ^ 2 := by
  have hexp := Work.BoseKinLoc.Gap.gapBare_eq_expand ℓ hℓ ψ hψ u
  have hnn := Work.BoseKinLoc.gapBare_nonneg ℓ u ψ
  have hA := boxIntegral_le ℓ u hψ hcs
  rw [hexp] at hnn
  have hC : ℓ ^ 3 * (Work.BSKinetic.bsMean ℓ u ψ) ^ 2
      ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 := by linarith
  rw [mul_comm]
  linarith

private lemma bddBelow_trialSet_lamBox {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : Integrable (fun z : ℝ³ => (φ z) ^ 2)
      (volume.restrict (Work.BoseKinLoc.lamBox ℓ u))) :
    BddBelow {c : ℝ | ∃ g : ℝ³ → ℝ,
      ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
      c = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2)
          - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, φ z * g z)
          + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                    (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                  + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2))} := by
  refine ⟨0, ?_⟩
  rintro c ⟨g, hg, hgs, hcval⟩
  rw [hcval]
  set Λ := Work.BoseKinLoc.lamBox ℓ u with hΛdef
  have hAint : Integrable (fun z : ℝ³ => (φ z) ^ 2) (volume.restrict Λ) := by
    simpa only [hΛdef] using hφ
  have hDint : Integrable (fun z : ℝ³ => (g z) ^ 2) (volume.restrict Λ) :=
    Work.BoseKinLoc.NeuFrac.integrableOn_sq_of_contDiff hg hgs u
  have hA_nn : 0 ≤ ∫ z in Λ, (φ z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hD_nn : 0 ≤ ∫ z in Λ, (g z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hK_nn : 0 ≤ ∑ k : Fin 3, ∫ z in Λ,
      (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => sq_nonneg _))
  have htail : 0 ≤ a2 * ((∑ k : Fin 3, ∫ z in Λ,
        (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2) + a2 * (∫ z in Λ, (g z) ^ 2)) :=
    mul_nonneg ha2 (add_nonneg hK_nn (mul_nonneg ha2 hD_nn))
  have key : 0 ≤ (∫ z in Λ, (φ z) ^ 2) - 2 * a2 * (∫ z in Λ, φ z * g z)
      + a2 ^ 2 * (∫ z in Λ, (g z) ^ 2) := by
    by_cases hint : Integrable (fun z : ℝ³ => φ z * g z) (volume.restrict Λ)
    · rw [Work.BoseKinLoc.NeuFrac.integral_sq_sub_sq hAint hint hDint]
      exact integral_nonneg (fun z => sq_nonneg _)
    · rw [integral_undef hint]
      nlinarith [hA_nn, hD_nn, ha2, sq_nonneg a2]
  have hle : a2 ^ 2 * (∫ z in Λ, (g z) ^ 2)
      ≤ a2 * ((∑ k : Fin 3, ∫ z in Λ,
            (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Λ, (g z) ^ 2)) := by
    have hmul : a2 * ((∑ k : Fin 3, ∫ z in Λ,
            (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Λ, (g z) ^ 2))
        = a2 * (∑ k : Fin 3, ∫ z in Λ,
              (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (a2 * (∫ z in Λ, (g z) ^ 2)) := by ring
    rw [hmul]
    nlinarith [mul_nonneg ha2 hK_nn]
  linarith [key, hle]

private lemma neuFrac_le_gapBare {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : Integrable (fun z : ℝ³ => (φ z) ^ 2) (volume.restrict (Work.BoseKinLoc.lamBox ℓ u))) :
    Work.BoseKinLoc.neuFrac ℓ a2 u φ ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2 := by
  refine csInf_le (bddBelow_trialSet_lamBox ha2 u hφ)
    ⟨(fun _ : ℝ³ => (0 : ℝ)), contDiff_const, HasCompactSupport.zero, ?_⟩
  simp

private lemma neuFrac_Qfree_bounds {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2)
    (u : ℝ³) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    0 ≤ Work.BoseKinLoc.neuFrac ℓ a2 u (Work.BoseKinLoc.Qfree ℓ u ψ) ∧
      Work.BoseKinLoc.neuFrac ℓ a2 u (Work.BoseKinLoc.Qfree ℓ u ψ)
        ≤ Work.BoseKinLoc.gapBare ℓ u ψ := by
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := hψ.continuous.sub continuous_const
  have hI : Integrable (fun z : ℝ³ => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
      (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    ContinuousOn.integrableOn_compact (Work.BoseKinLoc.Gap.isCompact_lamBox hℓ u)
      (hcont.pow 2).continuousOn
  exact ⟨Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2 ℓ a2 ha2 u _ hI, neuFrac_le_gapBare ha2 u hI⟩

private lemma windowed_L2_le {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ z : ℝ³, (Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) ^ 2)
      ≤ (2 * chiSupAbs ^ 2 + 2) * (∫ z : ℝ³, (ψ z) ^ 2) := by
  change (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u) * (ψ z - bsMean ℓ u ψ)) ^ 2)
      ≤ (2 * chiSupAbs ^ 2 + 2) * (∫ z : ℝ³, (ψ z) ^ 2)
  set m : ℝ := bsMean ℓ u ψ with hm
  have hψc : Continuous (fun z : ℝ³ => (ψ z) ^ 2) := hψ.continuous.pow 2
  have hIψ2 : Integrable (fun z : ℝ³ => (ψ z) ^ 2) := psi_sq_integrable hψ hcs
  have hχc : Continuous (fun z : ℝ³ => chiScale ℓ (z - ℓ • u) * chiScale ℓ (z - ℓ • u)) := by
    have hcont : Continuous (fun z : ℝ³ => chiScale ℓ (z - ℓ • u)) :=
      (chiScale_contDiff (ne_of_gt hℓ)).continuous.comp (by fun_prop)
    exact hcont.mul hcont
  have hχcs : HasCompactSupport (fun z : ℝ³ => chiScale ℓ (z - ℓ • u) * chiScale ℓ (z - ℓ • u)) :=
    (Work.BSKinetic.bsWin_hasCompactSupport hℓ u).mul_right
  have hIχ2 : Integrable (fun z : ℝ³ => (chiScale ℓ (z - ℓ • u)) ^ 2) := by
    simpa [pow_two] using hχc.integrable_of_hasCompactSupport hχcs
  have hIprod : Integrable (fun z : ℝ³ => (chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2) := by
    have h1 : Integrable (fun z : ℝ³ => (chiScale ℓ (z - ℓ • u) * chiScale ℓ (z - ℓ • u))
        * (ψ z * ψ z)) :=
      (hχc.mul (hψ.continuous.mul hψ.continuous)).integrable_of_hasCompactSupport
        (hχcs.mul_right)
    simpa [pow_two] using h1
  have hpt : ∀ z : ℝ³, (chiScale ℓ (z - ℓ • u) * (ψ z - m)) ^ 2
      ≤ 2 * ((chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)
        + 2 * (m ^ 2 * (chiScale ℓ (z - ℓ • u)) ^ 2) := by
    intro z
    have h1 : (ψ z - m) ^ 2 ≤ 2 * (ψ z) ^ 2 + 2 * m ^ 2 := by
      nlinarith [sq_nonneg (ψ z + m)]
    calc (chiScale ℓ (z - ℓ • u) * (ψ z - m)) ^ 2
        = (chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z - m) ^ 2 := by ring
      _ ≤ (chiScale ℓ (z - ℓ • u)) ^ 2 * (2 * (ψ z) ^ 2 + 2 * m ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = 2 * ((chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)
        + 2 * (m ^ 2 * (chiScale ℓ (z - ℓ • u)) ^ 2) := by ring
  have hmaj1 : Integrable (fun z : ℝ³ => 2 * ((chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)) :=
    hIprod.const_mul 2
  have hmaj2 : Integrable (fun z : ℝ³ => 2 * (m ^ 2 * (chiScale ℓ (z - ℓ • u)) ^ 2)) :=
    (hIχ2.const_mul (m ^ 2)).const_mul 2
  have hmain := integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _)
    (hmaj1.add hmaj2) (Eventually.of_forall hpt)
  have hsplit : (∫ z : ℝ³, (2 * ((chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)
        + 2 * (m ^ 2 * (chiScale ℓ (z - ℓ • u)) ^ 2)))
      = 2 * (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)
        + 2 * m ^ 2 * (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2) := by
    rw [integral_add hmaj1 hmaj2, integral_const_mul, integral_const_mul, integral_const_mul]
    ring
  have hP : (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)
      ≤ chiSupAbs ^ 2 * (∫ z : ℝ³, (ψ z) ^ 2) := by
    have hpt2 : ∀ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2
        ≤ chiSupAbs ^ 2 * (ψ z) ^ 2 := by
      intro z
      have h2 : (chiScale ℓ (z - ℓ • u)) ^ 2 ≤ chiSupAbs ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg chiSupAbs_nonneg]
        exact chiScale_abs_le_sup ℓ (z - ℓ • u)
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have h := integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (hIψ2.const_mul (chiSupAbs ^ 2)) (Eventually.of_forall hpt2)
    rwa [integral_const_mul] at h
  have hQ : (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2) = ℓ ^ 3 := by
    rw [MeasureTheory.integral_sub_right_eq_self (fun w : ℝ³ => (chiScale ℓ w) ^ 2) (ℓ • u)]
    exact integral_chiScale_sq hℓ
  have hm2 : m ^ 2 * ℓ ^ 3 ≤ ∫ z : ℝ³, (ψ z) ^ 2 := by
    rw [hm]; exact mean_sq_mul_le hℓ u hψ hcs
  calc (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u) * (ψ z - m)) ^ 2)
      ≤ ∫ z : ℝ³, (2 * ((chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)
          + 2 * (m ^ 2 * (chiScale ℓ (z - ℓ • u)) ^ 2)) := hmain
    _ = 2 * (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2 * (ψ z) ^ 2)
          + 2 * m ^ 2 * (∫ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2) := hsplit
    _ ≤ 2 * (chiSupAbs ^ 2 * (∫ z : ℝ³, (ψ z) ^ 2)) + 2 * m ^ 2 * ℓ ^ 3 := by
        rw [hQ]; gcongr
    _ ≤ 2 * (chiSupAbs ^ 2 * (∫ z : ℝ³, (ψ z) ^ 2)) + 2 * (∫ z : ℝ³, (ψ z) ^ 2) := by
        linarith [hm2]
    _ = (2 * chiSupAbs ^ 2 + 2) * (∫ z : ℝ³, (ψ z) ^ 2) := by ring

private lemma fderiv_windowed_apply {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (u z : ℝ³) (k : Fin 3) :
    fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u) * (ψ y - bsMean ℓ u ψ)) z
        (Submission.BoseGases.kcStdBasis k)
      = chiScale ℓ (z - ℓ • u) * fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)
        + (ψ z - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) (z - ℓ • u)
            (Submission.BoseGases.kcStdBasis k) := by
  have hd : DifferentiableAt ℝ (fun y : ℝ³ => ψ y - bsMean ℓ u ψ) z :=
    (hψ.differentiable (by norm_num) z).sub_const _
  have h := Work.BSKinetic.fderiv_bsWin_mul_apply (ℓ := ℓ) u z
    (Submission.BoseGases.kcStdBasis k) hd
  rw [show (fun y : ℝ³ => Work.BSKinetic.bsWin ℓ u y * (ψ y - bsMean ℓ u ψ))
      = (fun y : ℝ³ => chiScale ℓ (y - ℓ • u) * (ψ y - bsMean ℓ u ψ)) from rfl] at h
  rw [h, fderiv_sub_const]

private lemma dk_sq_integrable {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (k : Fin 3) :
    Integrable (fun z : ℝ³ => (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  have hcont : Continuous (fun z : ℝ³ => fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) :=
    (hψ.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have hcs1 : HasCompactSupport (fun z : ℝ³ => fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) :=
    (hcs.fderiv ℝ).comp_left (g := fun L : ℝ³ →L[ℝ] ℝ => L (Submission.BoseGases.kcStdBasis k))
      (by simp)
  have h := (hcont.mul hcont).integrable_of_hasCompactSupport (μ := volume) hcs1.mul_right
  exact h.congr (Filter.Eventually.of_forall fun z => by simp [Pi.mul_apply, pow_two])

private lemma dchi_sq_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) (k : Fin 3) :
    Integrable (fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
      (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  have hcont : Continuous (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) (z - ℓ • u)
      (Submission.BoseGases.kcStdBasis k)) :=
    (((chiScale_contDiff (ne_of_gt hℓ)).continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).comp (continuous_id.sub continuous_const)
  have hcs1 : HasCompactSupport (fun w : ℝ³ => fderiv ℝ (chiScale ℓ) w
      (Submission.BoseGases.kcStdBasis k)) :=
    ((chiScale_hasCompactSupport (ne_of_gt hℓ)).fderiv ℝ).comp_left
      (g := fun L : ℝ³ →L[ℝ] ℝ => L (Submission.BoseGases.kcStdBasis k)) (by simp)
  have hcs2 : HasCompactSupport (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) (z - ℓ • u)
      (Submission.BoseGases.kcStdBasis k)) :=
    hcs1.comp_homeomorph (Homeomorph.subRight (ℓ • u))
  have h := (hcont.mul hcont).integrable_of_hasCompactSupport (μ := volume) hcs2.mul_right
  exact h.congr (Filter.Eventually.of_forall fun z => by simp [Pi.mul_apply, pow_two])

private lemma windowed_dir_le {ℓ : ℝ} (hℓ : 0 < ℓ) (Kg : ℝ)
    (hKgb : ∀ x : ℝ³, ∑ k : Fin 3, (fderiv ℝ (chiScale ℓ) x (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ Kg / ℓ ^ 2)
    (u : ℝ³) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)
        * (ψ y - bsMean ℓ u ψ)) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      ≤ (12 * Kg / ℓ ^ 2 + 4 * (∑ k : Fin 3, ∫ z : ℝ³,
            (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2)
          * (∫ z : ℝ³, (ψ z) ^ 2)
        + 2 * chiSupAbs ^ 2 * (∑ k : Fin 3, ∫ z : ℝ³,
            (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  set m : ℝ := bsMean ℓ u ψ with hm
  have hm2v : m ^ 2 * ℓ ^ 3 ≤ ∫ z : ℝ³, (ψ z) ^ 2 := by
    rw [hm]; exact mean_sq_mul_le hℓ u hψ hcs
  have hψsq_int : Integrable (fun z : ℝ³ => (ψ z) ^ 2) := psi_sq_integrable hψ hcs
  have hGsum : 0 ≤ ∑ k : Fin 3, ∫ z : ℝ³,
      (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _
  have hper : ∀ k : Fin 3,
      (∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u) * (ψ y - m)) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
        ≤ 2 * chiSupAbs ^ 2 * (∫ z : ℝ³,
              (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + 4 * (Kg / ℓ ^ 2) * (∫ z : ℝ³, (ψ z) ^ 2)
          + 4 * m ^ 2 * (ℓ * (∫ z : ℝ³,
              (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by
    intro k
    have hχb : ∀ z : ℝ³, (chiScale ℓ (z - ℓ • u)) ^ 2 ≤ chiSupAbs ^ 2 := by
      intro z
      rw [sq_le_sq, abs_of_nonneg chiSupAbs_nonneg]
      exact chiScale_abs_le_sup ℓ (z - ℓ • u)
    have hkb : ∀ z : ℝ³, (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
        (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ Kg / ℓ ^ 2 := by
      intro z
      exact (Finset.single_le_sum (f := fun j : Fin 3 => (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
        (Submission.BoseGases.kcStdBasis j)) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)).trans (hKgb (z - ℓ • u))
    have hKg0 : 0 ≤ Kg / ℓ ^ 2 := by
      have h : 0 ≤ ∑ j : Fin 3, (fderiv ℝ (chiScale ℓ) (0 : ℝ³)
          (Submission.BoseGases.kcStdBasis j)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith [hKgb (0 : ℝ³)]
    have hpt : ∀ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u) * (ψ y - m)) z
        (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ 2 * chiSupAbs ^ 2 * (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
          + 4 * (Kg / ℓ ^ 2) * (ψ z) ^ 2
          + 4 * m ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
              (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
      intro z
      rw [fderiv_windowed_apply hψ u z k, ← hm]
      have ha2 : (chiScale ℓ (z - ℓ • u) * fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
          ≤ chiSupAbs ^ 2 * (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (hχb z) (sq_nonneg _)
      have hb2 : ((ψ z - m) * fderiv ℝ (chiScale ℓ) (z - ℓ • u)
          (Submission.BoseGases.kcStdBasis k)) ^ 2
          ≤ 2 * (ψ z) ^ 2 * (Kg / ℓ ^ 2) + 2 * m ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
              (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        rw [mul_pow]
        have h1 : (ψ z - m) ^ 2 ≤ 2 * (ψ z) ^ 2 + 2 * m ^ 2 := by
          nlinarith [sq_nonneg (ψ z + m)]
        have hA := mul_le_mul_of_nonneg_right h1
          (sq_nonneg (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k)))
        have hB := mul_le_mul (hkb z) (le_refl ((ψ z) ^ 2)) (sq_nonneg _) hKg0
        nlinarith [hA, hB]
      nlinarith [sq_nonneg (chiScale ℓ (z - ℓ • u) * fderiv ℝ ψ z
          (Submission.BoseGases.kcStdBasis k)
          - (ψ z - m) * fderiv ℝ (chiScale ℓ) (z - ℓ • u)
              (Submission.BoseGases.kcStdBasis k)), ha2, hb2]
    have h1 : Integrable (fun z : ℝ³ => 2 * chiSupAbs ^ 2 *
        (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
      (dk_sq_integrable hψ hcs k).const_mul (2 * chiSupAbs ^ 2)
    have h2 : Integrable (fun z : ℝ³ => 4 * (Kg / ℓ ^ 2) * (ψ z) ^ 2) :=
      hψsq_int.const_mul (4 * (Kg / ℓ ^ 2))
    have h3 : Integrable (fun z : ℝ³ => 4 * m ^ 2 *
        (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
      (dchi_sq_integrable hℓ u k).const_mul (4 * m ^ 2)
    have hmono := integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _)
      ((h1.add h2).add h3) (Eventually.of_forall hpt)
    have hGk : (∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ℓ * (∫ z : ℝ³, (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
      rw [MeasureTheory.integral_sub_right_eq_self
        (fun w : ℝ³ => (fderiv ℝ (chiScale ℓ) w (Submission.BoseGases.kcStdBasis k)) ^ 2) (ℓ • u)]
      exact Work.UBBInputs9.B.integral_fderiv_chiScale_sq ℓ hℓ (Submission.BoseGases.kcStdBasis k)
    calc (∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u) * (ψ y - m)) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
        ≤ ∫ z : ℝ³, (2 * chiSupAbs ^ 2 * (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
            + 4 * (Kg / ℓ ^ 2) * (ψ z) ^ 2
            + 4 * m ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
                (Submission.BoseGases.kcStdBasis k)) ^ 2) := hmono
      _ = 2 * chiSupAbs ^ 2 * (∫ z : ℝ³, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
            + 4 * (Kg / ℓ ^ 2) * (∫ z : ℝ³, (ψ z) ^ 2)
            + 4 * m ^ 2 * (∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
                (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
          rw [integral_add (f := fun z : ℝ³ => 2 * chiSupAbs ^ 2 *
                (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
                + 4 * (Kg / ℓ ^ 2) * (ψ z) ^ 2)
              (g := fun z : ℝ³ => 4 * m ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
                    (Submission.BoseGases.kcStdBasis k)) ^ 2) (h1.add h2) h3,
            integral_add (f := fun z : ℝ³ => 2 * chiSupAbs ^ 2 *
                (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
              (g := fun z : ℝ³ => 4 * (Kg / ℓ ^ 2) * (ψ z) ^ 2) h1 h2,
            integral_const_mul, integral_const_mul, integral_const_mul]
      _ = 2 * chiSupAbs ^ 2 * (∫ z : ℝ³, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
            + 4 * (Kg / ℓ ^ 2) * (∫ z : ℝ³, (ψ z) ^ 2)
            + 4 * m ^ 2 * (ℓ * (∫ z : ℝ³,
                (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by rw [hGk]
  calc (∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)
        * (ψ y - m)) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      ≤ ∑ k : Fin 3, (2 * chiSupAbs ^ 2 * (∫ z : ℝ³,
            (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + 4 * (Kg / ℓ ^ 2) * (∫ z : ℝ³, (ψ z) ^ 2)
          + 4 * m ^ 2 * (ℓ * (∫ z : ℝ³,
              (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2))) :=
        Finset.sum_le_sum fun k _ => hper k
    _ = 2 * chiSupAbs ^ 2 * (∑ k : Fin 3, ∫ z : ℝ³,
            (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + 12 * (Kg / ℓ ^ 2) * (∫ z : ℝ³, (ψ z) ^ 2)
          + 4 * m ^ 2 * ℓ * (∑ k : Fin 3, ∫ z : ℝ³,
              (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum (s := (Finset.univ : Finset (Fin 3))),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum (s := (Finset.univ : Finset (Fin 3))),
          ← Finset.mul_sum (s := (Finset.univ : Finset (Fin 3)))]
        ring
    _ ≤ 2 * chiSupAbs ^ 2 * (∑ k : Fin 3, ∫ z : ℝ³,
            (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + 12 * (Kg / ℓ ^ 2) * (∫ z : ℝ³, (ψ z) ^ 2)
          + 4 * (∑ k : Fin 3, ∫ z : ℝ³,
              (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2
            * (∫ z : ℝ³, (ψ z) ^ 2) := by
        have hlast : 4 * m ^ 2 * ℓ * (∑ k : Fin 3, ∫ z : ℝ³,
              (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2)
            ≤ 4 * (∑ k : Fin 3, ∫ z : ℝ³,
              (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2
              * (∫ z : ℝ³, (ψ z) ^ 2) := by
          rw [div_eq_mul_inv]
          have h4S : (0 : ℝ) ≤ 4 * (∑ k : Fin 3, ∫ z : ℝ³,
              (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) * (ℓ ^ 2)⁻¹ :=
            mul_nonneg (by positivity) (by positivity)
          have key := mul_le_mul_of_nonneg_right hm2v h4S
          have e1 : m ^ 2 * ℓ ^ 3 * (4 * (∑ k : Fin 3, ∫ z : ℝ³,
                (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) * (ℓ ^ 2)⁻¹)
              = 4 * m ^ 2 * ℓ * (∑ k : Fin 3, ∫ z : ℝ³,
                (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
            field_simp
          rw [e1] at key
          linarith [key]
        linarith
    _ = (12 * Kg / ℓ ^ 2 + 4 * (∑ k : Fin 3, ∫ z : ℝ³,
            (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2)
          * (∫ z : ℝ³, (ψ z) ^ 2)
        + 2 * chiSupAbs ^ 2 * (∑ k : Fin 3, ∫ z : ℝ³,
            (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by ring


private lemma dir_sum_eq (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    (∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => Work.BSKinetic.bsWin ℓ u y
        * Work.BSKinetic.bsQ ℓ u ψ y) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = (∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)
          * (ψ y - bsMean ℓ u ψ)) z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  simp only [Work.BSKinetic.bsWin, Work.BSKinetic.bsQ]

theorem fsT_bound_abs {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hmom : ∀ (u : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ENat) ψ → HasCompactSupport ψ →
        Work.BoseKinLoc.momForm ℓ d u ψ
          ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ENat) ψ → HasCompactSupport ψ →
      |Work.BoseKinLoc.fsT ℓ d s εT b u ψ|
        ≤ C * ((∫ z : EuclideanSpace ℝ (Fin 3), (ψ z) ^ 2)
            + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
                (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  obtain ⟨Kg, hKg0, hKgb⟩ := Work.BlockBound4.chiScale_grad_bound
  have hGsum : 0 ≤ ∑ k : Fin 3, ∫ z : ℝ³,
      (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _
  set Kwv : ℝ := (2 * chiSupAbs ^ 2 + 2)
    + (12 * Kg / ℓ ^ 2 + 4 * (∑ k : Fin 3, ∫ z : ℝ³,
        (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2)
    + 2 * chiSupAbs ^ 2 with hKwv
  set C4 : ℝ := |(1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ)| + |b * ℓ ^ (-2 : ℤ)|
    + |b * εT * (d * ℓ) ^ (-2 : ℤ)| with hC4
  set C5 : ℝ := |1 - εT| * (2 * (1 + ((2 * (s * ℓ))⁻¹) ^ 2))
    + |εT| * (2 * (1 + ((2 * (d * s * ℓ))⁻¹) ^ 2)) with hC5
  have hKwv0 : 0 ≤ Kwv := by
    rw [hKwv]
    have hK2 : 0 ≤ 12 * Kg / ℓ ^ 2 + 4 * (∑ k : Fin 3, ∫ z : ℝ³,
        (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2 := by
      have ha : 0 ≤ 12 * Kg / ℓ ^ 2 := by
        rw [div_eq_mul_inv]; exact mul_nonneg (by linarith) (by positivity)
      have hb : 0 ≤ 4 * (∑ k : Fin 3, ∫ z : ℝ³,
          (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2 := by
        rw [div_eq_mul_inv]; exact mul_nonneg (by linarith) (by positivity)
      linarith
    nlinarith [hK2, sq_nonneg chiSupAbs]
  have hC40 : 0 ≤ C4 := by rw [hC4]; positivity
  have hC50 : 0 ≤ C5 := by rw [hC5]; positivity
  refine ⟨3 * C4 + Kwv * C5, by positivity, ?_⟩
  intro u ψ hψ hcs
  set E0 : ℝ := ∫ z : ℝ³, (ψ z) ^ 2 with hE0def
  set Dsp : ℝ := ∑ k : Fin 3, ∫ z : ℝ³,
    (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2 with hDspdef
  have hE0 : 0 ≤ E0 := by rw [hE0def]; exact integral_nonneg fun z => sq_nonneg _
  have hDsp : 0 ≤ Dsp := by
    rw [hDspdef]; exact Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _
  have hgap : Work.BoseKinLoc.gapBare ℓ u ψ ≤ E0 := by
    rw [hE0def]; exact gapBare_le_integral_sq hℓ u hψ hcs
  have hgap0 : 0 ≤ Work.BoseKinLoc.gapBare ℓ u ψ := Work.BoseKinLoc.gapBare_nonneg ℓ u ψ
  -- the windowed state bound
  have hW : (∫ z : ℝ³, (Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) ^ 2)
      + ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => Work.BSKinetic.bsWin ℓ u y
          * Work.BSKinetic.bsQ ℓ u ψ y) z (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ Kwv * (E0 + Dsp) := by
    have hL2 := windowed_L2_le hℓ u hψ hcs
    have hDir := windowed_dir_le hℓ Kg (hKgb ℓ hℓ) u hψ hcs
    rw [← dir_sum_eq ℓ u ψ] at hDir
    have hK1 : 0 ≤ 2 * chiSupAbs ^ 2 + 2 := by positivity
    have hK2 : 0 ≤ 12 * Kg / ℓ ^ 2 + 4 * (∑ k : Fin 3, ∫ z : ℝ³,
        (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2 := by
      have ha : 0 ≤ 12 * Kg / ℓ ^ 2 := by
        rw [div_eq_mul_inv]; exact mul_nonneg (by linarith) (by positivity)
      have hb : 0 ≤ 4 * (∑ k : Fin 3, ∫ z : ℝ³,
          (fderiv ℝ chi z (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 2 := by
        rw [div_eq_mul_inv]; exact mul_nonneg (by linarith) (by positivity)
      linarith
    have hK3 : 0 ≤ 2 * chiSupAbs ^ 2 := by positivity
    rw [hKwv]
    nlinarith [hL2, hDir, hE0, hDsp, hK1, hK2, hK3]
  -- the four word bounds
  have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (by positivity) _
  have hneu := neuFrac_Qfree_bounds hℓ ha2 u hψ hcs
  have hw1 : |Work.BoseKinLoc.neuWord ℓ d εT u ψ|
      ≤ |(1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ)| * E0 := by
    rw [show Work.BoseKinLoc.neuWord ℓ d εT u ψ
        = (1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ))
            u (Work.BoseKinLoc.Qfree ℓ u ψ) from rfl, abs_mul, abs_of_nonneg hneu.1]
    exact mul_le_mul_of_nonneg_left (hneu.2.trans hgap) (abs_nonneg _)
  have hw2 : |Work.BoseKinLoc.gapWord ℓ b u ψ| ≤ |b * ℓ ^ (-2 : ℤ)| * E0 := by
    rw [show Work.BoseKinLoc.gapWord ℓ b u ψ
        = b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ u ψ from rfl, abs_mul,
      abs_of_nonneg hgap0]
    exact mul_le_mul_of_nonneg_left hgap (abs_nonneg _)
  have hmf0 : 0 ≤ Work.BoseKinLoc.momForm ℓ d u ψ := Work.BoseKinLoc.momForm_nonneg u ψ
  have hmfg : Work.BoseKinLoc.momForm ℓ d u ψ ≤ Work.BoseKinLoc.gapBare ℓ u ψ := hmom u ψ hψ hcs
  have hw3 : |Work.BoseKinLoc.momWord ℓ d εT b u ψ| ≤ |b * εT * (d * ℓ) ^ (-2 : ℤ)| * E0 := by
    rw [show Work.BoseKinLoc.momWord ℓ d εT b u ψ
        = b * εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d u ψ from rfl, abs_mul,
      abs_of_nonneg hmf0]
    exact mul_le_mul_of_nonneg_left (hmfg.trans hgap) (abs_nonneg _)
  -- the main word
  have hB1 := Work.BSKinetic.bsOneBody_le_weighted (ℓ := ℓ) (c := (2 * (s * ℓ))⁻¹) hℓ u hψ hcs
  have hB2 := Work.BSKinetic.bsOneBody_le_weighted (ℓ := ℓ) (c := (2 * (d * s * ℓ))⁻¹) hℓ u hψ hcs
  have hB10 : 0 ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ :=
    Work.BSKinetic.bsOneBody_nonneg (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ _) u ψ
  have hB20 : 0 ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ :=
    Work.BSKinetic.bsOneBody_nonneg (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ _) u ψ
  have hB1' : Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
      ≤ 2 * (1 + ((2 * (s * ℓ))⁻¹) ^ 2) * (Kwv * (E0 + Dsp)) :=
    hB1.trans (mul_le_mul_of_nonneg_left hW (by positivity))
  have hB2' : Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ
      ≤ 2 * (1 + ((2 * (d * s * ℓ))⁻¹) ^ 2) * (Kwv * (E0 + Dsp)) :=
    hB2.trans (mul_le_mul_of_nonneg_left hW (by positivity))
  have hw4 : |Work.BoseKinLoc.mainWord ℓ d s εT u ψ| ≤ C5 * (Kwv * (E0 + Dsp)) := by
    rw [show Work.BoseKinLoc.mainWord ℓ d s εT u ψ
        = (1 - εT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
          + εT * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ from rfl,
      hC5]
    calc |(1 - εT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
          + εT * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ|
        ≤ |(1 - εT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ|
          + |εT * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ| :=
          abs_add_le _ _
      _ = |1 - εT| * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
          + |εT| * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ := by
          rw [abs_mul, abs_mul, abs_of_nonneg hB10, abs_of_nonneg hB20]
      _ ≤ |1 - εT| * (2 * (1 + ((2 * (s * ℓ))⁻¹) ^ 2) * (Kwv * (E0 + Dsp)))
          + |εT| * (2 * (1 + ((2 * (d * s * ℓ))⁻¹) ^ 2) * (Kwv * (E0 + Dsp))) :=
          add_le_add (mul_le_mul_of_nonneg_left hB1' (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hB2' (abs_nonneg _))
      _ = (|1 - εT| * (2 * (1 + ((2 * (s * ℓ))⁻¹) ^ 2))
            + |εT| * (2 * (1 + ((2 * (d * s * ℓ))⁻¹) ^ 2))) * (Kwv * (E0 + Dsp)) := by ring
  -- assemble
  have htri : |Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ
        + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ|
      ≤ |Work.BoseKinLoc.neuWord ℓ d εT u ψ| + |Work.BoseKinLoc.gapWord ℓ b u ψ|
        + |Work.BoseKinLoc.momWord ℓ d εT b u ψ| + |Work.BoseKinLoc.mainWord ℓ d s εT u ψ| := by
    have h1 := abs_add_le (Work.BoseKinLoc.neuWord ℓ d εT u ψ) (Work.BoseKinLoc.gapWord ℓ b u ψ)
    have h2 := abs_add_le (Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ)
      (Work.BoseKinLoc.momWord ℓ d εT b u ψ)
    have h3 := abs_add_le (Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ
      + Work.BoseKinLoc.momWord ℓ d εT b u ψ) (Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
    linarith
  rw [Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u ψ]
  calc |Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ
        + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ|
      ≤ |Work.BoseKinLoc.neuWord ℓ d εT u ψ| + |Work.BoseKinLoc.gapWord ℓ b u ψ|
        + |Work.BoseKinLoc.momWord ℓ d εT b u ψ| + |Work.BoseKinLoc.mainWord ℓ d s εT u ψ| := htri
    _ ≤ C4 * E0 + C5 * (Kwv * (E0 + Dsp)) := by
        rw [hC4]
        nlinarith [hw1, hw2, hw3, hw4, abs_nonneg (Work.BoseKinLoc.neuWord ℓ d εT u ψ),
          abs_nonneg (Work.BoseKinLoc.gapWord ℓ b u ψ), abs_nonneg (Work.BoseKinLoc.momWord ℓ d εT b u ψ),
          abs_nonneg (Work.BoseKinLoc.mainWord ℓ d s εT u ψ), hE0]
    _ ≤ (3 * C4 + Kwv * C5) * (E0 + Dsp) := by
        rw [hC4] at hC40
        rw [hC5] at hC50
        nlinarith [hC40, hC50, hKwv0, hE0, hDsp]

end Work.BoseKinLoc.Kinetic
