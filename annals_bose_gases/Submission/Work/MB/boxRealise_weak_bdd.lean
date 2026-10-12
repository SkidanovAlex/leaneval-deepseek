import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.boxRealise_regular
import Submission.Work.MB.SlotWeakDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open scoped BigOperators

/-! ## Auxiliary lemmas about the mode products

`boxRealise e d Ψ = Σ_{α ∈ Ψ.support} Ψ_α (α!/√d!) M_α` is a *finite* combination of the
symmetric mode products `M_α = modeProd e d α`, each of which is a finite sum of finite
products of the one-particle modes `x ↦ e l (x i)`.  The three lemmas below are the
pointwise ingredients: measurability, the pointwise norm bound, and the vanishing of the
mode product on any configuration with a coordinate outside the box. -/

/-- A symmetric mode product is measurable as soon as every mode function is. -/
lemma measurable_modeProd {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (α : Fin m →₀ ℕ) :
    Measurable (fun x : Work.BoseDict.Xn d => Work.BoseDict.modeProd e d α x) := by
  have hα : (fun x : Work.BoseDict.Xn d => Work.BoseDict.modeProd e d α x)
      = fun x : Work.BoseDict.Xn d => ∑ σ : Fin d → Fin m,
          (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
            * ∏ i : Fin d, e (σ i) (x i) := by
    funext x
    rw [Work.BoseDict.modeProd]
  rw [hα]
  refine Finset.measurable_sum _ fun σ _ => ?_
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_prod _ fun i _ => (hmeas (σ i)).comp (measurable_pi_apply i)

/-- The pointwise bound on a mode product in terms of the pointwise bounds `B` on the
mode functions. -/
lemma norm_modeProd_le {m d : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ) (B : Fin m → ℝ)
    (hB : ∀ l x, ‖e l x‖ ≤ B l) (hBnn : ∀ l, 0 ≤ B l) (α : Fin m →₀ ℕ)
    (x : Work.BoseDict.Xn d) :
    ‖Work.BoseDict.modeProd e d α x‖ ≤ ∑ σ : Fin d → Fin m, ∏ i : Fin d, B (σ i) := by
  rw [Work.BoseDict.modeProd]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  by_cases hσ : Work.BoseDict.modeMult σ = α
  · rw [if_pos hσ, one_mul, norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hB (σ i) (x i))
  · rw [if_neg hσ, zero_mul, norm_zero]
    exact Finset.prod_nonneg fun i _ => hBnn (σ i)

theorem boxRealise_weak_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : Work.BoseB4.RealFock m) :
    Measurable (Work.BoseDict.boxRealise e d Ψ)
      ∧ (∃ C : ℝ, ∀ x : Work.BoseDict.Xn d, ‖Work.BoseDict.boxRealise e d Ψ x‖ ≤ C)
      ∧ Function.support (Work.BoseDict.boxRealise e d Ψ) ⊆ Work.MB.boxPow d ℓ := by
  classical
  -- pointwise bounds on the mode functions
  choose B hB using hbdE
  have hBnn : ∀ l, 0 ≤ B l := fun l => le_trans (norm_nonneg (e l 0)) (hB l 0)
  -- the finite expansion of the realisation on the support of `Ψ`
  have hfun : Work.BoseDict.boxRealise e d Ψ
      = ∑ α ∈ Ψ.support, (fun x : Work.BoseDict.Xn d =>
          ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * Work.BoseDict.modeProd e d α x) := by
    rw [Work.BoseDict.boxRealise_eq_sum_gen (e := e) (d := d) Ψ]
    funext x
    rw [Finset.sum_apply]
  -- the same expansion, evaluated at a point
  have happ : ∀ x : Work.BoseDict.Xn d, Work.BoseDict.boxRealise e d Ψ x
      = ∑ α ∈ Ψ.support,
          ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * Work.BoseDict.modeProd e d α x := by
    intro x
    rw [hfun, Finset.sum_apply]
  -- every mode function vanishes off the box
  have hez : ∀ (l : Fin m) (z : Work.BoseDict.Sp),
      z ∉ Work.BoseK15.corpusBox.boxL ℓ → e l z = 0 := by
    intro l z hz
    by_contra hne
    exact hz (hsupp l (Function.mem_support.mpr hne))
  -- hence so does every mode product, as soon as one coordinate is outside the box
  have hmode_zero : ∀ (α : Fin m →₀ ℕ) (x : Work.BoseDict.Xn d),
      (∃ i : Fin d, x i ∉ Work.BoseK15.corpusBox.boxL ℓ) →
        Work.BoseDict.modeProd e d α x = 0 := by
    rintro α x ⟨i, hi⟩
    rw [Work.BoseDict.modeProd]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hez (σ i) (x i) hi), mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · -- measurability
    rw [hfun]
    have hlam : (∑ α ∈ Ψ.support, (fun x : Work.BoseDict.Xn d =>
          ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * Work.BoseDict.modeProd e d α x))
        = fun x : Work.BoseDict.Xn d => ∑ α ∈ Ψ.support,
            ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
              * Work.BoseDict.modeProd e d α x := by
      funext x
      rw [Finset.sum_apply]
    rw [hlam]
    exact Finset.measurable_sum _ fun α _ => (measurable_modeProd hmeas α).const_mul _
  · -- the pointwise bound
    refine ⟨∑ α ∈ Ψ.support,
        ‖((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)‖
          * (∑ σ : Fin d → Fin m, ∏ i : Fin d, B (σ i)), ?_⟩
    intro x
    rw [happ x]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_modeProd_le e B hB hBnn α x) (norm_nonneg _)
  · -- the support
    intro x hx
    rw [Function.mem_support] at hx
    rw [boxPow, Set.mem_univ_pi]
    by_contra hcon
    obtain ⟨i, hi⟩ := not_forall.mp hcon
    exact hx (by
      rw [happ x]
      exact Finset.sum_eq_zero fun α _ => by
        rw [hmode_zero α x ⟨i, hi⟩, mul_zero])

end Work.MB
