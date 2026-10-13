/-
  WilG5 / Face — raising the source dimension of a chart.

  Given a chart `f : ℝ^{μ'} → ℝ^{n'}` which is `C^r` on the open cube and all of whose
  iterated derivative norms are `≤ 1`, the same is true of its pullback
  `t ↦ f (projCoord h t)` along the coordinate projection `projCoord h : ℝ^μ → ℝ^{μ'}`
  (`μ' ≤ μ`), which keeps the first `μ'` coordinates.

  The projection is packaged as a continuous linear map `projCLM h` of operator norm `≤ 1`;
  the pullback is then the composition `f ∘ projCLM h` with a linear map on the right, so
  - `ContDiffOn` is `ContDiffOn.comp_continuousLinearMap` restricted (via `mono`) to the
    open cube `openCube μ ⊆ projCLM h ⁻¹' openCube μ'`, and
  - the iterated derivatives are
    `iteratedFDeriv k (f ∘ P) t = (iteratedFDerivWithin k f (openCube μ') (P t)).compContinuousLinearMap (fun _ => P)`
    (`ContinuousLinearMap.iteratedFDerivWithin_comp_right`), whose norm is at most
    `1 * ‖P‖^k ≤ 1` since `‖P‖ ≤ 1` (`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`).
-/
import Mathlib
import Submission.Work.WilG5.Face.Defs

set_option autoImplicit false
noncomputable section

namespace Work.WilG5.Face

open WilkiesDesign

/-! ## The coordinate projection as a continuous linear map -/

/-- The first `μ'` coordinates, as a linear map. -/
def projLM {μ μ' : ℕ} (h : μ' ≤ μ) : (Fin μ → ℝ) →ₗ[ℝ] (Fin μ' → ℝ) where
  toFun := projCoord h
  map_add' := by intro v w; funext j; rfl
  map_smul' := by intro a v; funext j; rfl

/-- The coordinate projection does not increase the sup norm. -/
lemma norm_projCoord_le {μ μ' : ℕ} (h : μ' ≤ μ) (v : Fin μ → ℝ) :
    ‖projCoord h v‖ ≤ ‖v‖ := by
  by_cases hne : Nonempty (Fin μ')
  · have hI := hne
    rw [pi_norm_le_iff_of_nonempty]
    intro j
    exact norm_le_pi_norm v (Fin.castLE h j)
  · have hI : IsEmpty (Fin μ') := not_nonempty_iff.mp hne
    have hS : Subsingleton (Fin μ' → ℝ) := inferInstance
    rw [Subsingleton.eq_zero (projCoord h v), norm_zero]
    exact norm_nonneg v

/-- The first `μ'` coordinates, as a continuous linear map. -/
def projCLM {μ μ' : ℕ} (h : μ' ≤ μ) : (Fin μ → ℝ) →L[ℝ] (Fin μ' → ℝ) :=
  (projLM h).mkContinuous 1 fun v => by rw [one_mul]; exact norm_projCoord_le h v

@[simp] lemma projCLM_apply {μ μ' : ℕ} (h : μ' ≤ μ) (v : Fin μ → ℝ) :
    projCLM h v = projCoord h v := rfl

/-- The coordinate projection has operator norm at most `1`. -/
lemma norm_projCLM_le_one {μ μ' : ℕ} (h : μ' ≤ μ) : ‖projCLM h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]; exact norm_projCoord_le h v

/-! ## The pullback of a chart -/

theorem proj_charts {μ μ' n' r : ℕ} (h : μ' ≤ μ) (f : (Fin μ' → ℝ) → (Fin n' → ℝ))
    (hf : ContDiffOn ℝ r f (WilkiesDesign.openCube μ'))
    (hbd : ∀ k ≤ r, ∀ t ∈ WilkiesDesign.openCube μ', ‖iteratedFDeriv ℝ k f t‖ ≤ 1) :
    ContDiffOn ℝ r (fun t => f (Work.WilG5.Face.projCoord h t)) (WilkiesDesign.openCube μ) ∧
      ∀ k ≤ r, ∀ t ∈ WilkiesDesign.openCube μ,
        ‖iteratedFDeriv ℝ k (fun t => f (Work.WilG5.Face.projCoord h t)) t‖ ≤ 1 := by
  have hU' : IsOpen (WilkiesDesign.openCube μ') := by
    have h : WilkiesDesign.openCube μ' =
        ⋂ i : Fin μ', {x : Fin μ' → ℝ | x i ∈ Set.Ioo (0:ℝ) 1} := by
      ext x; simp [WilkiesDesign.openCube]
    rw [h]
    exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))
  have hpreopen : IsOpen ((projCLM h) ⁻¹' WilkiesDesign.openCube μ') :=
    hU'.preimage (projCLM h).continuous
  have hPle : ‖projCLM h‖ ≤ 1 := norm_projCLM_le_one h
  constructor
  · -- `t ↦ f (projCoord h t)` is `f ∘ projCLM h`, restricted to the open cube of `ℝ^μ`.
    have hcomp : ContDiffOn ℝ r (f ∘ ⇑(projCLM h))
        (⇑(projCLM h) ⁻¹' WilkiesDesign.openCube μ') := hf.comp_continuousLinearMap (projCLM h)
    have hsub : WilkiesDesign.openCube μ ⊆ ⇑(projCLM h) ⁻¹' WilkiesDesign.openCube μ' :=
      fun x hx => projCoord_mem_openCube h hx
    exact (hcomp.mono hsub).congr (fun x _ => rfl)
  · intro k hk t ht
    have hpt : (projCLM h) t ∈ WilkiesDesign.openCube μ' := projCoord_mem_openCube h ht
    have htpre : t ∈ (⇑(projCLM h) ⁻¹' WilkiesDesign.openCube μ') := hpt
    -- the iterated derivative of the composition with a linear map on the right
    have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (projCLM h) hf
      hU'.uniqueDiffOn hpreopen.uniqueDiffOn (x := t) hpt (i := k) (by exact_mod_cast hk)
    have hfun : (fun t => f (Work.WilG5.Face.projCoord h t)) = f ∘ ⇑(projCLM h) := rfl
    rw [hfun]
    -- the preimage of the open cube is a neighbourhood of `t`, so the derivative within it
    -- is the honest iterated derivative
    have h1 : iteratedFDerivWithin ℝ k (f ∘ ⇑(projCLM h))
        (⇑(projCLM h) ⁻¹' WilkiesDesign.openCube μ') t
        = iteratedFDeriv ℝ k (f ∘ ⇑(projCLM h)) t :=
      iteratedFDerivWithin_of_isOpen k hpreopen htpre
    rw [← h1, hcomp]
    calc ‖(iteratedFDerivWithin ℝ k f (WilkiesDesign.openCube μ') ((projCLM h) t)).compContinuousLinearMap
            (fun _ : Fin k => (projCLM h : (Fin μ → ℝ) →L[ℝ] (Fin μ' → ℝ)))‖
        ≤ ‖iteratedFDerivWithin ℝ k f (WilkiesDesign.openCube μ') ((projCLM h) t)‖ *
            ∏ _ : Fin k, ‖(projCLM h : (Fin μ → ℝ) →L[ℝ] (Fin μ' → ℝ))‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDerivWithin ℝ k f (WilkiesDesign.openCube μ') ((projCLM h) t)‖ *
            ‖projCLM h‖ ^ k := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ 1 * 1 := by
          refine mul_le_mul ?_ (pow_le_one₀ (norm_nonneg _) hPle)
            (pow_nonneg (norm_nonneg _) k) zero_le_one
          rw [iteratedFDerivWithin_of_isOpen k hU' hpt]
          exact hbd k hk ((projCLM h) t) hpt
      _ = 1 := one_mul 1

end Work.WilG5.Face
