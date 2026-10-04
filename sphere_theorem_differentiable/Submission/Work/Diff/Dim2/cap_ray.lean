import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.C.init_data
import Submission.GExpLocalInj
import Submission.LensLoop
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

/-!
# Area `d = 2`: the exponential map at a cap centre is the inverse of `Φp` on a small ball

`cap_ray` collects the elementary facts about the pair `(GExp p, Φp)` that the smooth-Reeb
construction at a pole `p` uses:

* `Φp` is a two-sided inverse of `GExp p` on a (fibre) ball of radius `ρ`;
* the rays of `GExp p` are minimising unit-speed geodesics up to time `ρ`;
* the velocity of such a ray at time `t ∈ (0,ρ)` is the gradient of the distance `rdist p`.

The proof is a small-radius restriction of the hypotheses: `exists_pos_riemannianEDist_GExp_eq`
gives a radius `ρ₁` on which `d(p, GExp p w) = ‖w‖`; `GExp p` is a local diffeomorphism at `0`
(inverse function theorem, `mfderiv_GExp_zero`), whence injective on a ball of radius `ε`; and on
the resulting ball `Φp` is the two-sided inverse.  The last conjunct is the eikonal equation
`rgrad_rdist_eikonal` combined with the chain rule `mvfderiv_comp_curve` along the ray.
-/

theorem cap_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {Φp : M → TangentSpace I p} {v : ℝ} (hv : 0 < v)
    (hsm : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y)
    (hnorm : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
      Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖)
    (hinv : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
      Submission.GlobalExp.GExp (cov := cov) hmet p (Φp y) = y) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < v ∧
      (∀ w : TangentSpace I p, ‖w‖ < ρ →
        Φp (Submission.GlobalExp.GExp (cov := cov) hmet p w) = w) ∧
      (∀ (w : TangentSpace I p) (t : ℝ), ‖w‖ = 1 → 0 ≤ t → t < ρ →
        Work.Diff.C.rdist (I := I) (M := M) p
            (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) = t) ∧
      (∀ (w : TangentSpace I p) (t : ℝ), ‖w‖ = 1 → 0 < t → t < ρ →
        curveVelocity (I := I) (fun s : ℝ =>
            Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t =
          Work.Diff.C.rgrad (I := I) (M := M)
            (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w))) := by
  classical
  -- ## Step 1: a radius on which `GExp p` realises the fibre norm as the distance.
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ :=
    Submission.GlobalExp.exists_pos_riemannianEDist_GExp_eq (cov := cov) hmet htor p
  -- ## Step 2: `GExp p` is injective on a ball around the origin.
  have hLinj : Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p (0 : TangentSpace I p) := by
    refine Submission.GExpLocalInj.locallyInjectiveAtGExp_of_injective_mfderiv (cov := cov) hmet
      (p := p) (v := 0) ?_
    intro a b hab
    have h0 := Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet p
    have h1 : (ContinuousLinearMap.id ℝ E) a = (ContinuousLinearMap.id ℝ E) b := h0 ▸ hab
    exact h1
  obtain ⟨S, hS, hSinj⟩ := hLinj
  obtain ⟨ε, hεpos, hεS⟩ := Metric.mem_nhds_iff.mp hS
  -- ## Step 3: the radius of the conclusion.
  set ρ : ℝ := min (min ρ₁ ε) v / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact div_pos (lt_min (lt_min hρ₁pos hεpos) hv) (by norm_num)
  have hρv : ρ < v := by
    rw [hρdef]
    have h : min (min ρ₁ ε) v ≤ v := min_le_right _ _
    linarith
  have hρρ₁ : ρ < ρ₁ := by
    rw [hρdef]
    have h : min (min ρ₁ ε) v ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hρε : ρ < ε := by
    rw [hρdef]
    have h : min (min ρ₁ ε) v ≤ ε := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  -- ## Step 4: the distance to a ray is the length of its velocity.
  have hdist_ray : ∀ w : TangentSpace I p, ‖w‖ < ρ →
      Work.Diff.C.rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p w) = ‖w‖ := by
    intro w hw
    rw [Work.Diff.C.rdist, hρ₁ w (lt_trans hw hρρ₁),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact Submission.GlobalExp.sqrt_chartGram_self (I := I) (x := p) w
  -- ## Step 5: injectivity of `GExp p` on the ball of radius `ρ`.
  have hinj_ball : ∀ u w : TangentSpace I p, ‖u‖ < ρ → ‖w‖ < ρ →
      Submission.GlobalExp.GExp (cov := cov) hmet p u =
        Submission.GlobalExp.GExp (cov := cov) hmet p w → u = w := by
    intro u w hu hw heq
    refine hSinj u (hεS ?_) w (hεS ?_) heq
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact lt_trans hu hρε
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact lt_trans hw hρε
  -- ## Step 6: the second conjunct.
  have hray : ∀ (w : TangentSpace I p) (t : ℝ), ‖w‖ = 1 → 0 ≤ t → t < ρ →
      Work.Diff.C.rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) = t := by
    intro w t hw ht0 htρ
    have hnormt : ‖t • w‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hw, mul_one]
    rw [hdist_ray (t • w) (by rw [hnormt]; exact htρ), hnormt]
  -- ## Step 7: the third conjunct.
  have hvel : ∀ (w : TangentSpace I p) (t : ℝ), ‖w‖ = 1 → 0 < t → t < ρ →
      curveVelocity (I := I) (fun s : ℝ =>
          Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t =
        Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) := by
    intro w t hw ht0 htρ
    have hwne : w ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hw
      norm_num at hw
    -- smoothness of the ray
    have hGsm : ContMDiffOn 𝓘(ℝ) I ∞
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) Set.univ :=
      Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hwne
    have hGmd : MDifferentiableAt 𝓘(ℝ) I
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t :=
      (hGsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
    -- the point is in the annulus of smoothness of `rdist p`
    have hxt : 0 < Work.Diff.C.rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) := by
      rw [hray w t hw ht0.le htρ]
      exact ht0
    have hltv : Work.Diff.C.rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) < v := by
      rw [hray w t hw ht0.le htρ]
      exact lt_trans htρ hρv
    have hgsm : CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) := hsm _ hxt hltv
    have hgmd : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) :=
      hgsm.mdifferentiableAt (by simp)
    -- the chain rule along the ray
    have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
      (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) (t := t)
      hgmd hGmd
    have hder : deriv ((fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) ∘
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w))) t = 1 := by
      have hev : ((fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) ∘
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)))
            =ᶠ[𝓝 t] id := by
        have hmem : t ∈ Set.Ioo (t / 2) ((t + ρ) / 2) :=
          ⟨by linarith, by linarith⟩
        filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
        show Work.Diff.C.rdist (I := I) (M := M) p
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) = s
        exact hray w s hw (by linarith [hs.1, ht0]) (by linarith [hs.2, htρ])
      calc deriv ((fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) ∘
            (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w))) t
          = deriv id t := hev.deriv_eq
        _ = 1 := deriv_id t
    -- the eikonal equation and the chain rule together give the inner product
    have hinner : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)))
        (curveVelocity (I := I) (fun s : ℝ =>
          Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t) = 1 := by
      rw [Work.Diff.C.inner_rgrad, Submission.Geodesic.curveVelocity_apply]
      exact hchain.trans hder
    have hunit : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)))
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w))) = 1 :=
      Work.Diff.C.rgrad_rdist_eikonal (cov := cov) hmet htor (q := p)
        (x := Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) (ne_of_gt hxt) hgsm
    have hgnorm : ‖Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w))‖ = 1 := by
      have h : ‖Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w))‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq]
        exact hunit
      nlinarith [norm_nonneg (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)))]
    have hvnorm : ‖curveVelocity (I := I) (fun s : ℝ =>
        Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t‖ = 1 := by
      rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hwne
        (ne_of_gt ht0), hw]
    have hvv : Inner.inner ℝ (curveVelocity (I := I) (fun s : ℝ =>
          Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t)
        (curveVelocity (I := I) (fun s : ℝ =>
          Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t) = 1 := by
      rw [real_inner_self_eq_norm_sq, hvnorm]
      norm_num
    have hinner' : Inner.inner ℝ (curveVelocity (I := I) (fun s : ℝ =>
          Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t)
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w))) = 1 := by
      rw [real_inner_comm]
      exact hinner
    have hzero : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M)
            (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) -
          curveVelocity (I := I) (fun s : ℝ =>
            Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t)
        (Work.Diff.C.rgrad (I := I) (M := M)
            (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) -
          curveVelocity (I := I) (fun s : ℝ =>
            Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t) = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, hunit, hinner, hinner', hvv]
      ring
    exact (sub_eq_zero.mp (inner_self_eq_zero.mp hzero)).symm
  -- ## Step 8: the first conjunct (⟸ of `hinv`), and assembly.
  refine ⟨ρ, hρpos, hρv, ?_, hray, hvel⟩
  intro w hw
  have hrd : Work.Diff.C.rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p w) = ‖w‖ := hdist_ray w hw
  have hltv : Work.Diff.C.rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p w) < v := by
    rw [hrd]
    exact lt_trans hw hρv
  have hinv' : Submission.GlobalExp.GExp (cov := cov) hmet p
      (Φp (Submission.GlobalExp.GExp (cov := cov) hmet p w))
      = Submission.GlobalExp.GExp (cov := cov) hmet p w := hinv _ hltv
  have hnrm : ‖Φp (Submission.GlobalExp.GExp (cov := cov) hmet p w)‖ = ‖w‖ := by
    rw [← hnorm _ hltv, hrd]
  exact hinj_ball _ w (by rw [hnrm]; exact hw) hw hinv'

end Work.Diff.Dim2
