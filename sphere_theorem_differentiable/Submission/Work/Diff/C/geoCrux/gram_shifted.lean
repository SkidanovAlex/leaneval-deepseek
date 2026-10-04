import Mathlib
import Submission.Work.Diff.C.geoCrux.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shifted Gram comparison (`Work.Diff.C.GeoCrux.GramShiftedProp`)

This file proves the *shifted* version of the "Gram matrix is almost constant along a unit-speed
ray" estimate of the classical high-pinching sphere theorem.  The unshifted version is
`Work.Diff.C.gram_along` (`Submission/Work/Diff/C/gram_along.lean`), which compares
`gp f₁ f₂ (GExp q (s • u))` with the value at the *base point* `q`; here the comparison is between
two points `GExp q (a • u)` and `GExp q (s • u)` of the ray (`0 ≤ a ≤ s`) and no value at `q` is
needed.  This is the form used to *restart* the comparison at a dip exit (see
`Submission/Work/Diff/C/gram_bad_case.lean`).

* `Work.Diff.C.geoCrux.abs_sub_le_of_derivWithin_bound` — the one-sided mean value inequality on an
  arbitrary interval `[a,s]`;
* `Work.Diff.C.geoCrux.gram_along_Icc` — the shifted `gram_along`;
* `Work.Diff.C.geoCrux.gram_shifted` — the target, obtained from `gram_along_Icc` by transferring the
  hypotheses of the cutoff family (`psi_comp_eq_self'`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.C.geoCrux

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

/-! ## The mean value inequality on an arbitrary interval -/

/-- **The one-sided mean value inequality** on an interval `[a,s]`: a continuous real function on
`[a,s]` whose right derivative on `(a,s)` is bounded by `C` in absolute value satisfies
`|g s - g a| ≤ C (s - a)`. -/
theorem abs_sub_le_of_derivWithin_bound {g h : ℝ → ℝ} {a s C : ℝ} (has : a ≤ s)
    (hcont : ContinuousOn g (Set.Icc a s))
    (hder : ∀ t ∈ Set.Ico a s, HasDerivWithinAt g (h t) (Set.Ici t) t)
    (hbd : ∀ t ∈ Set.Ico a s, ‖h t‖ ≤ C) :
    |g s - g a| ≤ C * (s - a) := by
  have key : ‖g s - g a‖ ≤ C * (s - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment (f := g) (f' := h) (a := a) (b := s)
      (C := C) hcont hder hbd s ⟨has, le_rfl⟩
  rwa [Real.norm_eq_abs] at key

section Shifted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The Gram pairing of two almost-`-f g` functions is `2ε`-Lipschitz along a geodesic ray, on an
arbitrary sub-interval.**  If `f₁, f₂` satisfy `|Hess fᵢ + fᵢ·g| ≤ ε·g` at every point of the
unit-speed ray `t ↦ GExp q (t • u)` and `|∇fᵢ| ≤ 1` there, and `0 ≤ a ≤ s`, then

`|gp f₁ f₂ (GExp q (s • u)) − gp f₁ f₂ (GExp q (a • u))| ≤ 2ε(s − a)`.

This is `Work.Diff.C.gram_along` with the interval `[0,s]` replaced by `[a,s]` (and without the
comparison with the value at the base point, which is not available when the hypotheses only hold
starting at `a`). -/
theorem gram_along_Icc
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {f₁ f₂ : M → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    {u : TangentSpace I q} (hu : Inner.inner ℝ u u = 1) {a s : ℝ} (ha0 : 0 ≤ a) (has : a ≤ s)
    (hsm₁ : ∀ t ∈ Set.Icc a s,
      CMDiffAt ∞ f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
    (hsm₂ : ∀ t ∈ Set.Icc a s,
      CMDiffAt ∞ f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
    (hH₁ : ∀ t ∈ Set.Icc a s,
      ∀ V W : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)),
        |rhess cov f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) V W
          + f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
            * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖)
    (hH₂ : ∀ t ∈ Set.Icc a s,
      ∀ V W : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)),
        |rhess cov f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) V W
          + f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
            * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖)
    (hg₁ : ∀ t ∈ Set.Icc a s,
      Inner.inner ℝ (rgrad (I := I) (M := M) f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
        (rgrad (I := I) (M := M) f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))) ≤ 1)
    (hg₂ : ∀ t ∈ Set.Icc a s,
      Inner.inner ℝ (rgrad (I := I) (M := M) f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
        (rgrad (I := I) (M := M) f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))) ≤ 1) :
    |gp (I := I) (M := M) f₁ f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (s • u))
        - gp (I := I) (M := M) f₁ f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (a • u))|
      ≤ 2 * ε * (s - a) := by
  classical
  let γ : ℝ → M := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (τ • u)
  have hu_ne : u ≠ 0 := by
    intro h0
    have h1 : (0 : ℝ) = 1 := by
      rw [h0] at hu
      simpa using hu
    exact one_ne_zero h1.symm
  have hu_norm : ‖u‖ = 1 := by
    have h2 : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hu]
    nlinarith [norm_nonneg u]
  have hmd_pos : ∀ t : ℝ, 0 < t → MDifferentiableAt 𝓘(ℝ) I γ t := fun t ht =>
    Submission.GExpTwoSided.mdifferentiableAt_GExp_smul (cov := cov) hmet q hu_ne ht
  have hmd_zero : MDifferentiableAt 𝓘(ℝ) I γ 0 := by
    have hG : ContMDiffAt 𝓘(ℝ, E) I ∞
        (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q (show TangentSpace I q from w))
        (0 : E) := Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet q 0
    have hlin : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun τ : ℝ => τ • (show E from u)) 0 :=
      (ContinuousLinearMap.toSpanSingleton ℝ (show E from u)).contMDiffAt
    have hG' : ContMDiffAt 𝓘(ℝ, E) I ∞
        (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q (show TangentSpace I q from w))
        ((0 : ℝ) • (show E from u)) := by
      rw [zero_smul]
      exact hG
    have hcomp := ContMDiffAt.comp 0 hG' hlin
    simpa only [Function.comp_def] using hcomp.mdifferentiableAt (by simp)
  have hγ0 : γ 0 = q := by
    show Submission.GlobalExp.GExp (cov := cov) hmet q ((0 : ℝ) • u) = q
    rw [zero_smul]
    exact Submission.GlobalExp.GExp_zero hmet q
  have hvel_pos : ∀ t : ℝ, 0 < t → ‖curveVelocity (I := I) γ t‖ = 1 := fun t ht => by
    have h1 : ‖curveVelocity (I := I)
        (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (τ • u)) t‖ = ‖u‖ :=
      Submission.GlobalExp.norm_curveVelocity_GExp_smul (cov := cov) hmet q hu_ne ht
    exact h1.trans hu_norm
  have hvel_zero : ‖curveVelocity (I := I) γ 0‖ = 1 := by
    rw [hγ0]
    have h2 : curveVelocity (I := I) γ 0 = u :=
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hu_ne
    rw [h2, hu_norm]
  have ht_nonneg : ∀ t ∈ Set.Icc a s, 0 ≤ t := fun t ht => le_trans ha0 ht.1
  have ht_nonneg' : ∀ t ∈ Set.Ico a s, 0 ≤ t := fun t ht =>
    ht_nonneg t ⟨ht.1, le_of_lt ht.2⟩
  have hderiv : ∀ t ∈ Set.Ico a s,
      HasDerivWithinAt (fun τ => gp (I := I) (M := M) f₁ f₂ (γ τ)) (gval cov f₁ f₂ γ t)
        (Set.Ici t) t := by
    intro t ht
    have hts : t ∈ Set.Icc a s := ⟨ht.1, le_of_lt ht.2⟩
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ t := by
      rcases eq_or_lt_of_le (ht_nonneg' t ht) with h | h
      · subst h; exact hmd_zero
      · exact hmd_pos t h
    have hvel : ‖curveVelocity (I := I) γ t‖ = 1 := by
      rcases eq_or_lt_of_le (ht_nonneg' t ht) with h | h
      · subst h; exact hvel_zero
      · exact hvel_pos t h
    exact (gram_deriv_along (cov := cov) (hmet := hmet) (f₁ := f₁) (f₂ := f₂) (ε := ε)
      (γ := γ) (t := t) hmd hvel (hsm₁ t hts) (hsm₂ t hts) (hH₁ t hts) (hH₂ t hts)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico a s, ‖gval cov f₁ f₂ γ t‖ ≤ 2 * ε := by
    intro t ht
    have hts : t ∈ Set.Icc a s := ⟨ht.1, le_of_lt ht.2⟩
    have hvel : ‖curveVelocity (I := I) γ t‖ = 1 := by
      rcases eq_or_lt_of_le (ht_nonneg' t ht) with h | h
      · subst h; exact hvel_zero
      · exact hvel_pos t h
    exact gram_deriv_bound (cov := cov) hε hvel
      (hH₁ t hts) (hH₂ t hts) (hg₁ t hts) (hg₂ t hts)
  have hcont : ContinuousOn (fun τ => gp (I := I) (M := M) f₁ f₂ (γ τ))
      (Set.Icc a s) := by
    intro t ht
    have hγc : ContinuousAt γ t := by
      rcases eq_or_lt_of_le (ht_nonneg t ht) with h | h
      · subst h; exact hmd_zero.continuousAt
      · exact (hmd_pos t h).continuousAt
    have hW₁ : CMDiffAt ∞ (T% (rgrad (I := I) f₁)) (γ t) := rgrad_contMDiffAt (hsm₁ t ht)
    have hW₂ : CMDiffAt ∞ (T% (rgrad (I := I) f₂)) (γ t) := rgrad_contMDiffAt (hsm₂ t ht)
    have hinner : CMDiffAt ∞
        (fun y : M => Inner.inner ℝ (rgrad (I := I) f₁ y) (rgrad (I := I) f₂ y)) (γ t) :=
      ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hW₁ hW₂
    have hprod : CMDiffAt ∞ (fun y : M => f₁ y * f₂ y) (γ t) := (hsm₁ t ht).mul (hsm₂ t ht)
    have hgp : ContinuousAt (fun x : M => gp (I := I) (M := M) f₁ f₂ x) (γ t) := by
      have h : ContinuousAt
          ((fun y : M => Inner.inner ℝ (rgrad (I := I) f₁ y) (rgrad (I := I) f₂ y))
            + fun y : M => f₁ y * f₂ y) (γ t) := (hinner.add hprod).continuousAt
      refine h.congr ?_
      filter_upwards with y
      simp only [Pi.add_apply, gp]
    exact (hgp.comp hγc).continuousWithinAt
  have key := abs_sub_le_of_derivWithin_bound (g := fun τ => gp (I := I) (M := M) f₁ f₂ (γ τ))
    (h := fun t => gval cov f₁ f₂ γ t) (a := a) (s := s) (C := 2 * ε) has hcont hderiv hbound
  simpa only [γ] using key

end Shifted

theorem gram_shifted : Work.Diff.C.GeoCrux.GramShiftedProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ p e hON hsmC hHess hcont hgrad hinit ψ hψ u s a hu ha0 has i j hstay
  obtain ⟨hψC, hψmono, hψder, hψid, hψconst⟩ := hψ
  obtain ⟨hderiv1, hderiv2⟩ := psi_deriv_good (c := c) hψC hψid
  have hgt_i : ∀ σ ∈ Set.Icc a s,
      -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    have h := (hstay σ hσ).1
    linarith
  have hgt_j : ∀ σ ∈ Set.Icc a s,
      -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e j
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    have h := (hstay σ hσ).2
    linarith
  have hsm_i : ∀ σ ∈ Set.Icc a s,
      CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e i)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
    fun σ hσ => hsmC _ _ (le_of_lt (hgt_i σ hσ))
  have hsm_j : ∀ σ ∈ Set.Icc a s,
      CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e j)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
    fun σ hσ => hsmC _ _ (le_of_lt (hgt_j σ hσ))
  have hsmF_i : ∀ σ ∈ Set.Icc a s,
      CMDiffAt ∞ (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
    fun σ hσ => ContMDiffAt.comp _ hψC.contDiffAt.contMDiffAt (hsm_i σ hσ)
  have hsmF_j : ∀ σ ∈ Set.Icc a s,
      CMDiffAt ∞ (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
    fun σ hσ => ContMDiffAt.comp _ hψC.contDiffAt.contMDiffAt (hsm_j σ hσ)
  have hHessF_i : ∀ σ ∈ Set.Icc a s,
      ∀ V W : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)),
      |rhess cov (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) V W
        + ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) * Inner.inner ℝ V W|
        ≤ ε₁ * ‖V‖ * ‖W‖ := by
    intro σ hσ V W
    obtain ⟨hv, _, hhe⟩ := psi_comp_eq_self' (I := I) (M := M) (cov := cov)
      (c := c) (ψ := ψ) (f := fFam (I := I) (M := M) (cov := cov) hmet p e i)
      (x := Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      hψC hψid hderiv1 hderiv2 (hstay σ hσ).1 (hsm_i σ hσ)
    rw [hv, hhe]
    simp only [fFam]
    exact hHess (qpt (I := I) (M := M) (cov := cov) hmet p e i) _ V W (hgt_i σ hσ)
  have hHessF_j : ∀ σ ∈ Set.Icc a s,
      ∀ V W : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)),
      |rhess cov (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) V W
        + ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) * Inner.inner ℝ V W|
        ≤ ε₁ * ‖V‖ * ‖W‖ := by
    intro σ hσ V W
    obtain ⟨hv, _, hhe⟩ := psi_comp_eq_self' (I := I) (M := M) (cov := cov)
      (c := c) (ψ := ψ) (f := fFam (I := I) (M := M) (cov := cov) hmet p e j)
      (x := Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      hψC hψid hderiv1 hderiv2 (hstay σ hσ).2 (hsm_j σ hσ)
    rw [hv, hhe]
    simp only [fFam]
    exact hHess (qpt (I := I) (M := M) (cov := cov) hmet p e j) _ V W (hgt_j σ hσ)
  have hgradF_i : ∀ σ ∈ Set.Icc a s,
      Inner.inner ℝ
        (rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)))
        (rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ 1 := by
    intro σ hσ
    obtain ⟨_, hgr, _⟩ := psi_comp_eq_self' (I := I) (M := M) (cov := cov)
      (c := c) (ψ := ψ) (f := fFam (I := I) (M := M) (cov := cov) hmet p e i)
      (x := Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      hψC hψid hderiv1 hderiv2 (hstay σ hσ).1 (hsm_i σ hσ)
    rw [hgr]
    simp only [fFam]
    rw [hgrad (qpt (I := I) (M := M) (cov := cov) hmet p e i) _ (hgt_i σ hσ)]
    nlinarith [sq_nonneg (fFam (I := I) (M := M) (cov := cov) hmet p e i
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)))]
  have hgradF_j : ∀ σ ∈ Set.Icc a s,
      Inner.inner ℝ
        (rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)))
        (rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ 1 := by
    intro σ hσ
    obtain ⟨_, hgr, _⟩ := psi_comp_eq_self' (I := I) (M := M) (cov := cov)
      (c := c) (ψ := ψ) (f := fFam (I := I) (M := M) (cov := cov) hmet p e j)
      (x := Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      hψC hψid hderiv1 hderiv2 (hstay σ hσ).2 (hsm_j σ hσ)
    rw [hgr]
    simp only [fFam]
    rw [hgrad (qpt (I := I) (M := M) (cov := cov) hmet p e j) _ (hgt_j σ hσ)]
    nlinarith [sq_nonneg (fFam (I := I) (M := M) (cov := cov) hmet p e j
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)))]
  exact gram_along_Icc (cov := cov) hmet htor (q := p)
    (f₁ := fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
    (f₂ := fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
    (ε := ε₁) hε₁ hu ha0 has hsmF_i hsmF_j hHessF_i hHessF_j hgradF_i hgradF_j



end Work.Diff.C.geoCrux
