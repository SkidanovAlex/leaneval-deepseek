import Submission.Work.VolterraLong.Weighted.Basic

/-!
# The long-interval Volterra operator

This file defines the Volterra operator `longOp` on
`BoundedContinuousFunction (Set.Icc a b) E` and proves that it is well defined
(i.e. that it maps continuous functions to continuous functions), together with
the two structural lemmas relating its fixed points to solutions of `(★)`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The underlying function of the Volterra operator is continuous on `[a,b]`
whenever the data is. -/
lemma continuous_longOpFunOn {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E ≃L[ℝ] E) (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z₀ : ℝ → E)
    (W : BoundedContinuousFunction (Set.Icc a b) E)
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b)) :
    Continuous (longOpFunOn hab A G Θ Ξ Z₀ W) := by
  change Continuous (fun s : Set.Icc a b =>
    bcfExt hab W (s : ℝ) - ((A s).symm : E →L[ℝ] E)
      (G (s : ℝ) (zExt hab Z₀ (s : ℝ) + bcfExt hab W (s : ℝ)) -
        (∫ σ in (s : ℝ)..b, Θ (s : ℝ) σ (zExt hab Z₀ σ + bcfExt hab W σ)) - Ξ (s : ℝ)))
  have hZ₀e : Continuous fun s : Set.Icc a b => zExt hab Z₀ (s : ℝ) :=
    (zExt_continuous hab hZ₀_cont).comp continuous_subtype_val
  have hWe : Continuous fun s : Set.Icc a b => bcfExt hab W (s : ℝ) :=
    (bcfExt_continuous hab W).comp continuous_subtype_val
  -- the parametric integral term
  have hI : Continuous (fun s : Set.Icc a b =>
      ∫ σ in (s : ℝ)..b, Θ (s : ℝ) σ (zExt hab Z₀ σ + bcfExt hab W σ)) := by
    set f : ℝ → ℝ → E := fun s σ => Θ s σ (zExt hab Z₀ σ + bcfExt hab W σ) with hf
    have hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
      have hpair : Continuous (fun p : ℝ × ℝ =>
          (p.1, p.2, zExt hab Z₀ p.2 + bcfExt hab W p.2)) := by fun_prop
      exact hΘ_cont.comp hpair
    have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := f) (a₀ := b) (s := fun s : ℝ => s) hf_cont continuous_id
    have heq : (fun s : ℝ => -∫ σ in b..s, f s σ) = (fun s : ℝ => ∫ σ in s..b, f s σ) := by
      funext s
      rw [intervalIntegral.integral_symm]
      exact neg_neg _
    have hneg : Continuous (fun s : ℝ => -∫ σ in b..s, f s σ) := hcont.neg
    rw [heq] at hneg
    have hfin : Continuous (fun s : Set.Icc a b => ∫ σ in (s : ℝ)..b, f (s : ℝ) σ) :=
      hneg.comp continuous_subtype_val
    simpa only [hf] using hfin
  have hG : Continuous (fun s : Set.Icc a b =>
      G (s : ℝ) (zExt hab Z₀ (s : ℝ) + bcfExt hab W (s : ℝ))) :=
    hG_cont.comp (continuous_subtype_val.prodMk (hZ₀e.add hWe))
  have hΞ : Continuous (fun s : Set.Icc a b => Ξ (s : ℝ)) :=
    hΞ_cont.comp continuous_subtype_val
  have hbr : Continuous (fun s : Set.Icc a b =>
      G (s : ℝ) (zExt hab Z₀ (s : ℝ) + bcfExt hab W (s : ℝ)) -
        (∫ σ in (s : ℝ)..b, Θ (s : ℝ) σ (zExt hab Z₀ σ + bcfExt hab W σ)) - Ξ (s : ℝ)) :=
    (hG.sub hI).sub hΞ
  have hA : Continuous (fun s : Set.Icc a b => ((A s).symm : E →L[ℝ] E)) :=
    continuousOn_iff_continuous_domRestrict.mp hA_cont
  exact hWe.sub (hA.clm_apply hbr)

/-- The long-interval Volterra operator on `C([a,b], E)`. -/
def longOp {a b : ℝ} (hab : a ≤ b) (A : ℝ → E ≃L[ℝ] E) (G : ℝ → E → E)
    (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z₀ : ℝ → E)
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b)) :
    BoundedContinuousFunction (Set.Icc a b) E → BoundedContinuousFunction (Set.Icc a b) E :=
  fun W => BoundedContinuousFunction.mkOfCompact
    { toFun := longOpFunOn hab A G Θ Ξ Z₀ W
      continuous_toFun :=
        continuous_longOpFunOn hab A G Θ Ξ Z₀ W hA_cont hG_cont hΘ_cont hΞ_cont hZ₀_cont }

lemma longOp_apply {a b : ℝ} (hab : a ≤ b) (A : ℝ → E ≃L[ℝ] E) (G : ℝ → E → E)
    (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z₀ : ℝ → E)
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (W : BoundedContinuousFunction (Set.Icc a b) E) (s : Set.Icc a b) :
    longOp hab A G Θ Ξ Z₀ hA_cont hG_cont hΘ_cont hΞ_cont hZ₀_cont W s =
      longOpFun A G Θ Ξ (zExt hab Z₀) (bcfExt hab W) b (s : ℝ) := rfl

/-- The values of the extension `zExt` inside `[a,b]` may be replaced by the
original function inside any integral over a subinterval of `[a,b]`. -/
lemma integral_zExt_eq {a b : ℝ} (hab : a ≤ b) (Θ : ℝ → ℝ → E → E) (Z₀ W : ℝ → E)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ σ in s..b, Θ s σ (zExt hab Z₀ σ + W σ)) =
      (∫ σ in s..b, Θ s σ (Z₀ σ + W σ)) := by
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [Set.uIcc_of_le hs.2] at hσ
  have hσmem : σ ∈ Set.Icc a b := ⟨le_trans hs.1 hσ.1, hσ.2⟩
  change Θ s σ (zExt hab Z₀ σ + W σ) = Θ s σ (Z₀ σ + W σ)
  rw [zExt_of_mem hab (Z := Z₀) hσmem]

/-- A fixed point of the Volterra operator gives a solution of `(★)` with
`Z = Z₀ + W`. -/
lemma solvesOn_of_longOp_fixedPoint {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E ≃L[ℝ] E) (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z₀ : ℝ → E)
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (W : BoundedContinuousFunction (Set.Icc a b) E)
    (hfix : longOp hab A G Θ Ξ Z₀ hA_cont hG_cont hΘ_cont hΞ_cont hZ₀_cont W = W) :
    SolvesOn a b G Θ Ξ (fun s => Z₀ s + bcfExt hab W s) := by
  intro s hs
  have hval : longOp hab A G Θ Ξ Z₀ hA_cont hG_cont hΘ_cont hΞ_cont hZ₀_cont W
      ⟨s, hs⟩ = W ⟨s, hs⟩ := by rw [hfix]
  rw [longOp_apply] at hval
  simp only [longOpFun, bcfExt_of_mem hab (Z := W) hs, zExt_of_mem hab (Z := Z₀) hs] at hval
  rw [integral_zExt_eq hab Θ Z₀ (bcfExt hab W) hs] at hval
  set B : E := G s (Z₀ s + W ⟨s, hs⟩) -
      (∫ σ in s..b, Θ s σ (Z₀ σ + bcfExt hab W σ)) - Ξ s with hB
  have hzero : ((A s).symm : E →L[ℝ] E) B = 0 := by
    have h1 : W ⟨s, hs⟩ - ((A s).symm : E →L[ℝ] E) B = W ⟨s, hs⟩ := hval
    have h4 : W ⟨s, hs⟩ - ((A s).symm : E →L[ℝ] E) B - W ⟨s, hs⟩ = 0 := sub_eq_zero.mpr h1
    have h5 : -(((A s).symm : E →L[ℝ] E) B) = 0 := by
      have he : W ⟨s, hs⟩ - ((A s).symm : E →L[ℝ] E) B - W ⟨s, hs⟩ =
          -(((A s).symm : E →L[ℝ] E) B) := by abel
      rw [he] at h4
      exact h4
    simpa using h5
  have hB0 : B = 0 := EquivLike.injective (A s).symm (hzero.trans (map_zero _).symm)
  rw [hB] at hB0
  rw [← bcfExt_of_mem hab (Z := W) hs] at hB0
  have h1 : G s (Z₀ s + bcfExt hab W s) -
      (∫ σ in s..b, Θ s σ (Z₀ σ + bcfExt hab W σ)) = Ξ s := sub_eq_zero.mp hB0
  have h2 : G s (Z₀ s + bcfExt hab W s) =
      (∫ σ in s..b, Θ s σ (Z₀ σ + bcfExt hab W σ)) + Ξ s := by
    rw [← h1]
    abel
  simpa only using h2

end Work.VolterraLong
