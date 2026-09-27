import Mathlib
import Submission.Work.EKLRelCross.PeriodDefs

/-!
# Covariance of the period set under the diagonal flow

For a family `ν : X₃ → Measure SL₃(ℝ)` satisfying the EKL covariance relation

`ν (α^t • x) = c • (ν x).map (g ↦ α^t g α^{-t})`

for some scalar `c ≠ 0, ⊤`, the period set of `ν` inside the root group `U_ij` transforms by
the scalar `e^{t i - t j}`:

`PerSet ν i j hij (α^t • x) = image (τ ↦ e^{t i - t j} τ) (PerSet ν i j hij x)`.

The mathematical content is the conjugation identity `α^t u_ij(s) α^{-t} = u_ij(e^{t i - t j} s)`
together with the fact that pushing a measure forward along the conjugation `g ↦ α^t g α^{-t}`
commutes with right translation by the conjugated root element.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

noncomputable section

/-- The conjugation-by-`aDiag t` map `g ↦ aDiag t * g * (aDiag t)⁻¹`. -/
abbrev aConj (t : Fin 3 → ℝ) : SL3 → SL3 := fun g => aDiag t * g * (aDiag t)⁻¹

/-- The inverse of `aConj t`, namely `g ↦ (aDiag t)⁻¹ * g * aDiag t`. -/
abbrev aConjInv (t : Fin 3 → ℝ) : SL3 → SL3 := fun g => (aDiag t)⁻¹ * g * aDiag t

lemma measurable_aConj (t : Fin 3 → ℝ) : Measurable (aConj t) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

lemma measurable_aConjInv (t : Fin 3 → ℝ) : Measurable (aConjInv t) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

lemma aConjInv_comp_aConj (t : Fin 3 → ℝ) : aConjInv t ∘ aConj t = id := by
  funext g
  simp only [Function.comp_apply, aConj, aConjInv, id_eq]
  group

/-- `(aDiag t)⁻¹ * u_ij(e^{t i - t j} s) = u_ij(s) * (aDiag t)⁻¹`. -/
lemma inv_mul_uij_conj (t : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    (aDiag t)⁻¹ * uij hij (Real.exp (t i - t j) * s) = uij hij s * (aDiag t)⁻¹ := by
  have h := Work.EKLContract.Lemmas.aDiag_conj_uij t hij s
  have h2 : uij hij s * (aDiag t)⁻¹
      = (aDiag t)⁻¹ * uij hij (Real.exp (t i - t j) * s) := by
    calc uij hij s * (aDiag t)⁻¹
        = (aDiag t)⁻¹ * ((aDiag t) * uij hij s * (aDiag t)⁻¹) := by group
      _ = (aDiag t)⁻¹ * uij hij (Real.exp (t i - t j) * s) := by rw [h]
  exact h2.symm

/-- `aDiag t * u_ij(s) = u_ij(e^{t i - t j} s) * aDiag t`. -/
lemma aDiag_mul_uij (t : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    aDiag t * uij hij s = uij hij (Real.exp (t i - t j) * s) * aDiag t := by
  have h := Work.EKLContract.Lemmas.aDiag_conj_uij t hij s
  rw [← h]; group

/-- Conjugating the right-translation by `u_ij(e^{t i - t j} s)` is the same as right-translating
by `u_ij(s)` and then conjugating. -/
lemma aConj_comp_mulRight (t : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    (fun g : SL3 => g * uij hij (Real.exp (t i - t j) * s)) ∘ (aConj t)
      = (aConj t) ∘ (fun g : SL3 => g * uij hij s) := by
  funext g
  simp only [Function.comp_apply]
  calc aConj t g * uij hij (Real.exp (t i - t j) * s)
      = (aDiag t * g) * ((aDiag t)⁻¹ * uij hij (Real.exp (t i - t j) * s)) := by
        simp only [aConj]; group
    _ = (aDiag t * g) * (uij hij s * (aDiag t)⁻¹) := by rw [inv_mul_uij_conj]
    _ = aConj t (g * uij hij s) := by simp only [aConj]; group

/-- Pushing a measure forward along `aConj t` commutes with right translation by the conjugated
root element: `(ν.map (aConj t)).map (· * u_ij(e^{t i - t j} s))
= ((ν.map (· * u_ij s)).map (aConj t))`. -/
lemma map_aConj_mulRight (t : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j)
    (ν' : Measure SL3) (s : ℝ) :
    (ν'.map (aConj t)).map (fun g => g * uij hij (Real.exp (t i - t j) * s))
      = (ν'.map (fun g => g * uij hij s)).map (aConj t) := by
  have h1 : Measurable (aConj t) := measurable_aConj t
  have h2 : Measurable (fun g : SL3 => g * uij hij (Real.exp (t i - t j) * s)) :=
    (continuous_id.mul continuous_const).measurable
  have h3 : Measurable (fun g : SL3 => g * uij hij s) :=
    (continuous_id.mul continuous_const).measurable
  rw [Measure.map_map h2 h1, Measure.map_map h1 h3, aConj_comp_mulRight]

/-- Cancellation of a nonzero, finite `ENNReal` scalar on measures. -/
lemma smul_measure_eq_cancel {μ μ' : Measure SL3} {c : ENNReal} (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (h : c • μ = c • μ') : μ = μ' := by
  ext s
  have hs : c * μ s = c * μ' s := by
    have hh := congrArg (fun m : Measure SL3 => m s) h
    simpa [Measure.smul_apply, smul_eq_mul] using hh
  have hs' : μ s * c = μ' s * c := by
    rw [mul_comm (μ s) c, mul_comm (μ' s) c]; exact hs
  exact (ENNReal.mul_left_inj hc0 hcT).mp hs'

/-- Pushing measures forward along the conjugation `aConj t` is injective. -/
lemma map_aConj_injective (t : Fin 3 → ℝ) :
    Function.Injective (fun μ : Measure SL3 => μ.map (aConj t)) := by
  intro μ μ' h
  have h' := congrArg (fun ν : Measure SL3 => ν.map (aConjInv t)) h
  simpa [Measure.map_map (measurable_aConjInv t) (measurable_aConj t), aConjInv_comp_aConj]
    using h'

theorem perSet_aDiag_conj (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (x : Work.EKLContract.X3) (c : ENNReal)
    (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hcov : ν (Work.EKLContract.aDiag t • x)
      = c • (ν x).map (fun g => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹)) :
    Work.EKLRelCross.PerSet ν i j hij (Work.EKLContract.aDiag t • x)
      = Set.image (fun τ : ℝ => Real.exp (t i - t j) * τ) (Work.EKLRelCross.PerSet ν i j hij x) := by
  -- The covariance, rewritten in terms of `aConj t`.
  have e1gen : ∀ s : ℝ,
      (ν (aDiag t • x)).map (fun g => g * uij hij (Real.exp (t i - t j) * s))
        = c • ((ν x).map (fun g => g * uij hij s)).map (aConj t) := by
    intro s
    rw [hcov, Measure.map_smul, map_aConj_mulRight] <;> try fun_prop
  ext σ
  simp only [PerSet, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hσ
    refine ⟨Real.exp (-(t i - t j)) * σ, ?_, ?_⟩
    · -- `exp (-(t i - t j)) * σ` is a period for `ν x`.
      have hb : Real.exp (t i - t j) * (Real.exp (-(t i - t j)) * σ) = σ := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      have hσ' : (ν (aDiag t • x)).map
          (fun g => g * uij hij (Real.exp (t i - t j) * (Real.exp (-(t i - t j)) * σ)))
          = ν (aDiag t • x) := by rw [hb]; exact hσ
      have hkey : c • ((ν x).map (fun g => g * uij hij (Real.exp (-(t i - t j)) * σ))).map (aConj t)
          = c • (ν x).map (aConj t) := by
        rw [← e1gen (Real.exp (-(t i - t j)) * σ), hσ', hcov]
      exact map_aConj_injective t (smul_measure_eq_cancel hc0 hcT hkey)
    · rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  · -- Converse: push a period of `ν x` forward.
    rintro ⟨τ, hτ, rfl⟩
    rw [e1gen τ, hτ, hcov]

end

end Work.EKLRelCross
