import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.gram_along
import Submission.Work.Diff.C.psi_estimates
import Submission.Work.Diff.C.psi_deriv_good
import Submission.Work.Diff.C.rhess_comp
import Submission.Work.Diff.C.gp_helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The pointwise package at a point of the good region.**  On the region `{f ≥ -1 + 2c}` the
cutoff `ψ` acts as the identity *together with* its first two derivatives, so the composite
`ψ ∘ f` has the same value, the same gradient and the same Hessian as `f` itself.  (This is
`Work.Diff.C.psi_comp_eq_self` of `gram_good_ray`, restated here so that this file does not depend
on a module that is still under construction.) -/
theorem psi_comp_eq_self'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {c : ℝ} {ψ : ℝ → ℝ} {f : M → ℝ} {x : M}
    (hψC : ContDiff ℝ ∞ ψ)
    (hval : ∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s)
    (hd1 : ∀ s : ℝ, -1 + 2 * c ≤ s → deriv ψ s = 1)
    (hd2 : ∀ s : ℝ, -1 + 2 * c ≤ s → iteratedDeriv 2 ψ s = 0)
    (hfx : -1 + 2 * c ≤ f x) (hsm : CMDiffAt ∞ f x) :
    ψ (f x) = f x ∧
      rgrad (I := I) (M := M) (fun y : M => ψ (f y)) x = rgrad (I := I) (M := M) f x ∧
      ∀ V W : TangentSpace I x,
        rhess cov (fun y : M => ψ (f y)) x V W = rhess cov f x V W := by
  have hfm : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := hsm.mdifferentiableAt (by simp)
  have hderiv : HasDerivAt ψ (deriv ψ (f x)) (f x) :=
    (hψC.contDiffAt.differentiableAt (by simp)).hasDerivAt
  refine ⟨hval (f x) hfx, ?_, ?_⟩
  · rw [rgrad_comp_hasDerivAt (I := I) hfm hderiv, hd1 (f x) hfx, one_smul]
  · intro V W
    rw [rhess_comp (cov := cov) ψ f x V W hψC.contDiffAt hsm, hd2 (f x) hfx, hd1 (f x) hfx]
    ring

/-- **The Gram matrix is nearly constant along a ray, for a single pair of indices.**
`qᵢ := qpt hmet p e i`, `fᵢ := fFam hmet p e i`, `Fᵢ := ψ ∘ fᵢ`, and `x = GExp p (s • u)` on a
unit-speed ray from `p`.  If the two functions of the pair `(i,j)` stay above `-1+2c` all along the
ray (so that `ψ` acts as the identity and the Hessian/gradient hypotheses of `HessBoundRegion` and
the eikonal identity apply there), then `A_ij = gp Fᵢ Fⱼ` is within `2ε₁s` of its value at `p`,
which is `δ_ij` (`Work.Diff.C.init_gram`).  Unlike `Work.Diff.C.gram_good_ray` this only requires
*the two functions of the pair* to stay in the smooth region, so it also applies when a third index
dips below `-1+c`. -/
theorem gram_along_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    {p x : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p} {u : TangentSpace I p} {s : ℝ}
    (hu : Inner.inner ℝ u u = 1) (hs0 : 0 ≤ s)
    (hx : Submission.GlobalExp.GExp (cov := cov) hmet p (s • u) = x)
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ t : ℝ, 0 ≤ deriv ψ t ∧ deriv ψ t ≤ 2) ∧
      (∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t) ∧ (∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c))
    (i j : Fin (Module.finrank ℝ E + 1))
    (hstay : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ∧
      -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e j
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) :
    |gp (I := I) (M := M)
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y)) x
      - (if i = j then 1 else 0)| ≤ 2 * ε₁ * s := by
  classical
  obtain ⟨hψC, hψmono, hψder, hψid, hψconst⟩ := hψ
  obtain ⟨hderiv1, hderiv2⟩ := psi_deriv_good (c := c) hψC hψid
  -- the two `f`s stay strictly above `-1 + c` along the ray
  have hgt_i : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    have h := (hstay σ hσ).1
    linarith
  have hgt_j : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e j
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    have h := (hstay σ hσ).2
    linarith
  -- smoothness of the `f`s and of their `ψ`-composites along the ray
  have hsm_i : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e i)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    exact hsmC _ _ (le_of_lt (hgt_i σ hσ))
  have hsm_j : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e j)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    exact hsmC _ _ (le_of_lt (hgt_j σ hσ))
  have hsmF_i : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      CMDiffAt ∞ (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    exact ContMDiffAt.comp _ hψC.contDiffAt.contMDiffAt (hsm_i σ hσ)
  have hsmF_j : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      CMDiffAt ∞ (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ hσ
    exact ContMDiffAt.comp _ hψC.contDiffAt.contMDiffAt (hsm_j σ hσ)
  -- the Hessian bound for the `ψ`-composites along the ray
  have hHessF_i : ∀ σ ∈ Set.Icc (0 : ℝ) s,
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
  have hHessF_j : ∀ σ ∈ Set.Icc (0 : ℝ) s,
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
  -- the gradient bound for the `ψ`-composites along the ray
  have hgradF_i : ∀ σ ∈ Set.Icc (0 : ℝ) s,
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
  have hgradF_j : ∀ σ ∈ Set.Icc (0 : ℝ) s,
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
  -- integrate the derivative bound along the ray
  have hmain := gram_along (I := I) (M := M) (cov := cov) hmet htor (q := p)
    (f₁ := fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
    (f₂ := fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
    (ε := ε₁) hε₁ hu hs0 hsmF_i hsmF_j hHessF_i hHessF_j hgradF_i hgradF_j
  -- the value of the Gram matrix at the base point
  have hgp0 : gp (I := I) (M := M)
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y)) p
      = (if i = j then 1 else 0) :=
    (init_gram (I := I) (M := M) (cov := cov) hmet hc hc1 hsmC hON hinit
      ⟨hψC, hψmono, hψder, hψid, hψconst⟩).2 i j
  rw [hx, hgp0] at hmain
  exact hmain

end Work.Diff.C
