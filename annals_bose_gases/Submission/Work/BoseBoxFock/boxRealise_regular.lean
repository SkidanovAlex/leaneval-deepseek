import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BoxFockDefs
import Submission.Work.BoseDict.bomb_dGamma_slot

/-!
# `Work.BoseBoxFock.boxRealise_regular` — regularity of the box realisation

The realisation `Work.BoseDict.boxRealise e d Ψ = Σ_α Ψ_α (α!/√d!) M_α` of a model Fock
vector on the `d`-particle box (BF3b) is a *finite* linear combination of the symmetric
mode products `M_α = modeProd e d α`.  If every mode function `e l` is in `L^∞` and
supported in the box `Λ(ℓ) = corpusBox.boxL ℓ = acube ℓ` (the centred cube), then

* every mode factor `x ↦ e l (x i)` vanishes off the cube, so `M_α` — and hence
  `boxRealise e d Ψ` — is supported in the `d`-particle box `abox d ℓ`;
* `x ↦ e l (x i)` is a.e. strongly measurable (pullback of `e l` along the
  quasi-measure-preserving coordinate projection, `Measure.quasiMeasurePreserving_eval`),
  hence so is every finite sum/product of them;
* from `MemLp (e l) ⊤` one gets an a.e. bound `‖e l z‖ ≤ M l`; pushing it to the product
  space (`Measure.tendsto_eval_ae_ae`) gives `‖e l (x i)‖ ≤ M l` for a.e. `x`, and then
  `‖boxRealise e d Ψ x‖ ≤ Σ_{α ∈ Ψ.support} ‖Ψ_α α!/√d!‖ · Σ_σ ∏_i M (σ i)`
  for a.e. `x`.

This is the regularity interface used by the dictionary (`uSlot_regular`,
`bomb_n0_eq_cS1C`, …): support in the box, a.e. strong measurability, essential
boundedness.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The coordinate pullback of an a.e. strongly measurable one-particle function. -/
lemma aestronglyMeasurable_comp_apply {d : ℕ} {e : Work.BoseDict.Sp → ℂ}
    (he : AEStronglyMeasurable e (volume : Measure Work.BoseDict.Sp)) (i : Fin d) :
    AEStronglyMeasurable (fun x : Work.BoseDict.Xn d => e (x i))
      (volume : Measure (Work.BoseDict.Xn d)) :=
  he.comp_quasiMeasurePreserving
    (MeasureTheory.Measure.quasiMeasurePreserving_eval
      (fun _ : Fin d => (volume : Measure Work.BoseDict.Sp)) i)

/-- An `L^∞` one-particle function is a.e. bounded by a nonnegative constant. -/
lemma exists_ae_bound_of_memLp_top {e : Work.BoseDict.Sp → ℂ}
    (he : MemLp e ⊤ (volume : Measure Work.BoseDict.Sp)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ z ∂(volume : Measure Work.BoseDict.Sp), ‖e z‖ ≤ M := by
  have hlt : eLpNormEssSup e (volume : Measure Work.BoseDict.Sp) < ⊤ := by
    rw [← eLpNorm_exponent_top he.aestronglyMeasurable]
    exact he.eLpNorm_lt_top
  obtain ⟨C, hC⟩ :=
    (eLpNormEssSup_lt_top_iff_isBoundedUnder (f := e) (μ := volume)).mp hlt
  refine ⟨max (C : ℝ) 0, le_max_right _ _, ?_⟩
  filter_upwards [hC] with z hz
  have hz' : (‖e z‖₊ : ℝ) ≤ (C : ℝ) := by exact_mod_cast hz
  exact le_trans (by simpa using hz') (le_max_left _ _)

/-- The a.e. bound on the model's mode products: if every mode function is a.e. bounded by
`M`, then `modeProd e d α` is a.e. bounded by the sum over the labellings of `∏ i, M (σ i)`. -/
lemma modeProd_norm_ae_le {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (M : Fin m → ℝ)
    (hM : ∀ l, 0 ≤ M l) (x : Work.BoseDict.Xn d)
    (hx : ∀ (l : Fin m) (i : Fin d), ‖e l (x i)‖ ≤ M l) (α : Fin m →₀ ℕ) :
    ‖Work.BoseDict.modeProd e d α x‖ ≤ ∑ σ : Fin d → Fin m, ∏ i : Fin d, M (σ i) := by
  rw [Work.BoseDict.modeProd]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  by_cases hσ : Work.BoseDict.modeMult σ = α
  · rw [if_pos hσ, one_mul, norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hx (σ i) i)
  · rw [if_neg hσ, zero_mul, norm_zero]
    exact Finset.prod_nonneg fun i _ => hM (σ i)

theorem boxRealise_regular {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤ MeasureTheory.volume)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : Work.BoseB4.RealFock m) :
    Function.support (Work.BoseDict.boxRealise e d Ψ) ⊆ Submission.BoseGases.abox d ℓ
    ∧ MeasureTheory.AEStronglyMeasurable (Work.BoseDict.boxRealise e d Ψ)
        (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d))
    ∧ (∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
        ‖Work.BoseDict.boxRealise e d Ψ x‖ ≤ C) := by
  classical
  -- the two descriptions of the box agree
  have hbox : Work.BoseK15.corpusBox.boxL ℓ = Submission.BoseGases.acube ℓ :=
    Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ
  -- every mode function vanishes outside the centred cube
  have hez : ∀ (l : Fin m) (z : Work.BoseDict.Sp),
      z ∉ Submission.BoseGases.acube ℓ → e l z = 0 := by
    intro l z hz
    by_contra hne
    exact hz (hbox ▸ hsupp l (Function.mem_support.mpr hne))
  -- hence the mode products too
  have hmode_zero : ∀ (α : Fin m →₀ ℕ) (x : Work.BoseDict.Xn d),
      (∃ i : Fin d, x i ∉ Submission.BoseGases.acube ℓ) →
        Work.BoseDict.modeProd e d α x = 0 := by
    rintro α x ⟨i, hi⟩
    rw [Work.BoseDict.modeProd]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hez (σ i) (x i) hi), mul_zero]
  -- the realisation expanded on the support of `Ψ`
  have hfun : Work.BoseDict.boxRealise e d Ψ
      = ∑ α ∈ Ψ.support, (fun x : Work.BoseDict.Xn d =>
          ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * Work.BoseDict.modeProd e d α x) := by
    rw [Work.BoseDict.boxRealise_eq_sum_gen e Ψ]
    funext x
    rw [Finset.sum_apply]
  -- the support conjunct
  have hsupp_abox : Function.support (Work.BoseDict.boxRealise e d Ψ)
      ⊆ Submission.BoseGases.abox d ℓ := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxab
    refine hx ?_
    have hnotall : ¬ (∀ i : Fin d, x i ∈ Submission.BoseGases.acube ℓ) :=
      fun h => hxab ((Submission.BoseGases.mem_abox_iff d ℓ x).mpr h)
    obtain ⟨i, hi⟩ := not_forall.mp hnotall
    rw [Work.BoseDict.boxRealise_eq_sum_gen e Ψ]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [hmode_zero α x ⟨i, hi⟩, mul_zero]
  -- a.e. strong measurability
  have hpull : ∀ (l : Fin m) (i : Fin d),
      AEStronglyMeasurable (fun x : Work.BoseDict.Xn d => e l (x i))
        (volume : Measure (Work.BoseDict.Xn d)) :=
    fun l i => aestronglyMeasurable_comp_apply (hbdd l).aestronglyMeasurable i
  have hmode_aesm : ∀ α : Fin m →₀ ℕ,
      AEStronglyMeasurable (fun x : Work.BoseDict.Xn d => Work.BoseDict.modeProd e d α x)
        (volume : Measure (Work.BoseDict.Xn d)) := by
    intro α
    have hα : (fun x : Work.BoseDict.Xn d => Work.BoseDict.modeProd e d α x)
        = ∑ σ : Fin d → Fin m, (fun x : Work.BoseDict.Xn d =>
            (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ∏ i : Fin d, e (σ i) (x i)) := by
      funext x
      rw [Finset.sum_apply, Work.BoseDict.modeProd]
    rw [hα]
    refine Finset.aestronglyMeasurable_sum _ fun σ _ => ?_
    refine AEStronglyMeasurable.const_mul ?_ _
    rw [show (fun x : Work.BoseDict.Xn d => ∏ i : Fin d, e (σ i) (x i))
        = ∏ i : Fin d, (fun x : Work.BoseDict.Xn d => e (σ i) (x i)) from by
      funext x
      rw [Finset.prod_apply]]
    exact Finset.aestronglyMeasurable_prod _ fun i _ => hpull (σ i) i
  have hAESM : AEStronglyMeasurable (Work.BoseDict.boxRealise e d Ψ)
      (volume : Measure (Work.BoseDict.Xn d)) := by
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum _ fun α _ => (hmode_aesm α).const_mul _
  -- a.e. bounds on the mode functions
  obtain ⟨M, hMnonneg, hMb⟩ : ∃ M : Fin m → ℝ, (∀ l, 0 ≤ M l) ∧
      (∀ l, ∀ᵐ z ∂(volume : Measure Work.BoseDict.Sp), ‖e l z‖ ≤ M l) := by
    choose M hM' using fun l => exists_ae_bound_of_memLp_top (hbdd l)
    exact ⟨M, fun l => (hM' l).1, fun l => (hM' l).2⟩
  have hall : ∀ᵐ x ∂(MeasureTheory.Measure.pi
        (fun _ : Fin d => (volume : Measure Work.BoseDict.Sp))),
      ∀ (l : Fin m) (i : Fin d), ‖e l (x i)‖ ≤ M l := by
    rw [Filter.eventually_all]
    intro l
    rw [Filter.eventually_all]
    intro i
    exact (MeasureTheory.Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin d => (volume : Measure Work.BoseDict.Sp)) (i := i)).eventually (hMb l)
  -- the a.e. bound
  refine ⟨hsupp_abox, hAESM, ?_⟩
  refine ⟨∑ α ∈ Ψ.support,
      ‖((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)‖
        * (∑ σ : Fin d → Fin m, ∏ i : Fin d, M (σ i)), ?_⟩
  filter_upwards [hall] with x hx
  rw [Work.BoseDict.boxRealise_eq_sum_gen e Ψ]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun α _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (modeProd_norm_ae_le M hMnonneg x hx α) (norm_nonneg _)

end Work.BoseBoxFock
