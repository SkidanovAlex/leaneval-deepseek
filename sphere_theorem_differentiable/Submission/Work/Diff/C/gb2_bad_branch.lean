import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.gb2_dip_aux
import Submission.Work.Diff.C.gb2_dip_branch
import Submission.Work.Diff.C.geoCrux.gram_shifted
import Submission.Work.Diff.C.geoCrux.far_ball_diam
import Submission.Work.Diff.C.geoCrux.bad_index_model
import Submission.Work.Diff.C.geoCrux.Defs
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.rgrad_fcos_eikonal
import Submission.Work.Diff.C.psi_estimates
import Submission.Work.Diff.C.sum_rule_good_ray
import Submission.Work.Diff.C.gram_along_pair
import Submission.Work.Diff.C.ray_cap_algebra
import Submission.Work.Diff.C.dip_equator_crux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The whole "bad index" branch of `Work.Diff.C.gram_pointwise2`

This module proves `Work.Diff.C.gb2_bad_branch`: the complete bad-index branch of the classical
high-pinching endgame at a ray point `x = GExp p (s • u)`, given the geometric hypotheses of
`Work.Diff.C.gram_pointwise2` (NO global diameter bound, NO perimeter bound) together with

* `hmodel` — the ODE model comparison along the ray for every index whose trigonometric bound
  `-1+3c ≤ mᵢ` holds on `[0,s]` (this is what `Work.Diff.C.gram_ray_data` produces);
* `hbad` — the failure of the trigonometric bound for some index and some time.

The internal case analysis is

* **dip case** (`∃ j σ, β_j sin σ < -1+3c`): `Work.Diff.C.gb2_dip_branch` applies;
* **equator case** (no such `j`): every `Fin.succ`-index is trig-good, hence the failure of the
  trigonometric bound is at index `0`, and everything is controlled by the model of the
  `Fin.succ`-indices and by the explicit eikonal identities for `cos`.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic

set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section BadBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The bad-index branch.**  See the module docstring. -/
theorem gb2_bad_branch
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ t : ℝ, 0 ≤ deriv ψ t ∧ deriv ψ t ≤ 2) ∧
      (∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t) ∧ (∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c))
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi)
    (hrs : rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s)
    {x : M} (hxs : Submission.GlobalExp.GExp (cov := cov) hmet p (s • u) = x)
    (hmodel : ∀ (i : Fin (Module.finrank ℝ E + 1)),
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos σ
          + Inner.inner ℝ (rgrad (I := I) (M := M)
              (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin σ) →
      (∀ τ ∈ Set.Icc (0 : ℝ) s, -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) s,
        |fFam (I := I) (M := M) (cov := cov) hmet p e i
            (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
          - (fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos τ
            + Inner.inner ℝ (rgrad (I := I) (M := M)
                (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin τ)|
          ≤ 2 * ε₁ * s))
    (hbad : ∃ (i : Fin (Module.finrank ℝ E + 1)) (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) s ∧
      fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos σ
        + Inner.inner ℝ (rgrad (I := I) (M := M)
            (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin σ < -1 + 3 * c)
    {K : ℝ} (hKn : 300 * (Real.sqrt c + ε₁ * Real.pi) ≤ K)
    (hKn2 : 125 * ((Module.finrank ℝ E : ℝ) + 1) * (Real.sqrt c + ε₁ * Real.pi) ≤ K) :
    |(∑ k : Fin (Module.finrank ℝ E + 1),
        (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)) ^ 2) - 1| ≤ K ∧
    (∀ k l : Fin (Module.finrank ℝ E + 1),
      |gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e l y)) x
        - (if k = l then 1 else 0)| ≤ K) := by
  classical
  -- ## elementary facts about `ψ`
  have hψC : ContDiff ℝ ∞ ψ := hψ.1
  have hψid : ∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t := hψ.2.2.2.1
  have hψconst : ∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c := hψ.2.2.2.2
  have hψ0 : deriv ψ (-1 + c) = 0 := deriv_eq_zero_of_le_const hψC hψconst
  have hψest := psi_estimates hc hψ
  have hψder1 : ∀ t : ℝ, -1 + 2 * c < t → deriv ψ t = 1 := hψest.2.2.2.2.2.1
  have hψsub : ∀ t : ℝ, -1 ≤ t → |ψ t - t| ≤ 2 * c := fun t ht => gb2_psi_abs_sub_le hc hψ ht
  have hψone : ∀ t : ℝ, t ≤ 1 → |ψ t| ≤ 1 := fun t ht => gb2_psi_abs_le_one hc hc1 hψ ht
  have hψd2 : ∀ t : ℝ, |deriv ψ t| ≤ 2 := by
    intro t
    rw [abs_of_nonneg (hψ.2.2.1 t).1]
    exact (hψ.2.2.1 t).2
  -- ## arithmetic of `lam = √c + ε₁π`
  set lam : ℝ := Real.sqrt c + ε₁ * Real.pi with hlam
  have hsqrtc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hε₁π0 : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact add_nonneg hsqrtc hε₁π0
  have hc_le_sqrtc : c ≤ Real.sqrt c := by
    have hsq : Real.sqrt c * Real.sqrt c = c := by rw [← sq]; exact Real.sq_sqrt hc.le
    have hle1 : Real.sqrt c ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    calc c = Real.sqrt c * Real.sqrt c := hsq.symm
      _ ≤ Real.sqrt c * 1 := mul_le_mul_of_nonneg_left hle1 hsqrtc
      _ = Real.sqrt c := mul_one _
  have hc_le_lam : c ≤ lam := by rw [hlam]; linarith
  have hsqrtc_le_lam : Real.sqrt c ≤ lam := by rw [hlam]; linarith
  have hε₁π_le_lam : ε₁ * Real.pi ≤ lam := by rw [hlam]; linarith
  have hc_le_96 : c ≤ 1 / 96 := by
    have h1 : 1 - Real.cos α ≤ α ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := α)
      linarith
    have h2 : α ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith [hα.le, hα1]
    nlinarith [hnum1, h1, h2]
  have h6c_le_one : 6 * c ≤ 1 := by linarith
  have hsqrt6c_le_one : Real.sqrt (6 * c) ≤ 1 := by
    calc Real.sqrt (6 * c) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h6c_le_one
      _ = 1 := Real.sqrt_one
  have hsqrt6_le : Real.sqrt (6 * c) ≤ 3 * lam := by
    have h1 : Real.sqrt (6 * c) = Real.sqrt 6 * Real.sqrt c := Real.sqrt_mul (by norm_num) c
    have h2 : Real.sqrt 6 ≤ 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg 6]
    rw [h1]
    have h3 : Real.sqrt 6 * Real.sqrt c ≤ 3 * Real.sqrt c :=
      mul_le_mul_of_nonneg_right h2 hsqrtc
    nlinarith [h3, hsqrtc_le_lam, hsqrtc]
  have h2ε₁s : 2 * ε₁ * s ≤ 2 * lam := by
    have h1 : 2 * ε₁ * s ≤ 2 * ε₁ * Real.pi :=
      mul_le_mul_of_nonneg_left hsπ (by linarith)
    have h2 : 2 * (ε₁ * Real.pi) ≤ 2 * lam := by linarith [hε₁π_le_lam]
    linarith
  have hsin_lt : ∀ t : ℝ, Real.cos t < -1 + 2 * c → |Real.sin t| ≤ 2 * Real.sqrt c := by
    intro t ht
    have h1 : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq t]
    have h2 : (1 - 2 * c) ^ 2 ≤ Real.cos t ^ 2 := by nlinarith [Real.neg_one_le_cos t, hc]
    have h3 : Real.sin t ^ 2 ≤ 4 * c := by nlinarith [h1, h2, hc]
    have h4 : |Real.sin t| ≤ Real.sqrt (4 * c) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h3
    have h5 : Real.sqrt (4 * c) = 2 * Real.sqrt c := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt 4 = (2 : ℝ) by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    linarith [h4, h5.le, h5.ge]
  -- ## the ray
  have hu_ne : u ≠ 0 := by intro h0; rw [h0] at hu; simp at hu
  have hray := rdist_GExp_ray_eq (I := I) (M := M) (cov := cov) hmet htor hu hs0 hrs
  have hray_pt : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) = σ :=
    hray.1
  -- ## the model at `p`
  have hmod0 : ∀ τ : ℝ, fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) p * Real.cos τ
      + Inner.inner ℝ (rgrad (I := I) (M := M)
          (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1))) p) u * Real.sin τ = Real.cos τ := by
    intro τ
    obtain ⟨h0v, h0g, -⟩ := hinit
    have hq0 : qpt (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)) = p := by
      rw [qpt, dirv, Fin.cases_zero, smul_zero]
      exact Submission.GlobalExp.GExp_zero hmet p
    have hv : fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) p = 1 := by
      show fcos (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e 0) p = 1
      rw [hq0]; exact h0v
    have hg : rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1))) p = 0 := by
      show rgrad (I := I) (M := M) (fcos (I := I) (M := M)
        (qpt (I := I) (M := M) (cov := cov) hmet p e 0)) p = 0
      rw [hq0]; exact h0g
    rw [hv, hg]
    simp
  have hmodS : ∀ (j : Fin (Module.finrank ℝ E)) (τ : ℝ),
      fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) p * Real.cos τ
      + Inner.inner ℝ (rgrad (I := I) (M := M)
          (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)) p) u * Real.sin τ
      = Inner.inner ℝ (e j) u * Real.sin τ := by
    intro j τ
    obtain ⟨-, -, hrest⟩ := hinit
    have hv : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) p = 0 := by
      show fcos (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)) p = 0
      exact (hrest j).1
    have hg : rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
        (Fin.succ j)) p = e j := by
      show rgrad (I := I) (M := M) (fcos (I := I) (M := M)
        (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j))) p = e j
      exact (hrest j).2
    rw [hv, hg]
    ring
  -- ## basic facts about the family
  have hf0ray : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
        = Real.cos τ := by
    intro τ hτ
    show Real.cos (rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e
      (0 : Fin (Module.finrank ℝ E + 1)))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) = Real.cos τ
    rw [show qpt (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)) = p from by
      rw [qpt, dirv, Fin.cases_zero, smul_zero]
      exact Submission.GlobalExp.GExp_zero hmet p]
    rw [hray_pt τ hτ]
  have hf0x : fFam (I := I) (M := M) (cov := cov) hmet p e
      (0 : Fin (Module.finrank ℝ E + 1)) x = Real.cos s := by
    rw [← hxs]; exact hf0ray s ⟨hs0, le_rfl⟩
  have hF0x : ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
      (0 : Fin (Module.finrank ℝ E + 1)) x) = ψ (Real.cos s) := by rw [hf0x]
  have hpsile1 : ∀ k : Fin (Module.finrank ℝ E + 1),
      |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)| ≤ 1 :=
    fun k => hψone _ (Real.cos_le_one _)
  -- the gradient bound `‖∇(ψ ∘ f_k)‖ ≤ 2`
  have hgradbd : ∀ (k : Fin (Module.finrank ℝ E + 1)) (y : M),
      ‖rgrad (I := I) (M := M)
        (fun z : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k z)) y‖ ≤ 2 := by
    intro k y
    by_cases hlt : fFam (I := I) (M := M) (cov := cov) hmet p e k y < -1 + c
    · have hz : rgrad (I := I) (M := M)
          (fun z : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k z)) y = 0 := by
        apply rgrad_eq_zero_of_eventuallyEq_const (I := I) (F := fun z : M =>
          ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k z))
        filter_upwards [(isOpen_lt (hcont _) continuous_const).mem_nhds hlt] with z hz
        exact hψconst _ (le_of_lt hz)
      rw [hz, norm_zero]; norm_num
    · push_neg at hlt
      have hsm : CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e k) y :=
        hsmC _ y hlt
      rw [rgrad_psi_comp (I := I) hψC (f := fFam (I := I) (M := M) (cov := cov) hmet p e k) hsm,
        norm_smul, Real.norm_eq_abs]
      rcases lt_or_eq_of_le hlt with hgt | heq
      · have h1 : |deriv ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k y)| ≤ 2 := hψd2 _
        have h2 : ‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e k) y‖ ≤ 1 := by
          have he := hgrad (qpt (I := I) (M := M) (cov := cov) hmet p e k) y hgt
          have h3 : ‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e k) y‖ ^ 2
              = 1 - (fFam (I := I) (M := M) (cov := cov) hmet p e k y) ^ 2 := by
            rw [← real_inner_self_eq_norm_sq]; exact he
          have h4 : ‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e k) y‖ ^ 2 ≤ 1 := by
            rw [h3]; nlinarith [sq_nonneg (fFam (I := I) (M := M) (cov := cov) hmet p e k y)]
          have h5 := Real.sqrt_le_sqrt h4
          rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] at h5
        calc |deriv ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k y)|
              * ‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e k) y‖
            ≤ 2 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
          _ = 2 := by norm_num
      · rw [show fFam (I := I) (M := M) (cov := cov) hmet p e k y = -1 + c from heq.symm, hψ0]
        simp
  have hcont0 : Continuous (fFam (I := I) (M := M) (cov := cov) hmet p e
      (0 : Fin (Module.finrank ℝ E + 1))) :=
    hcont (qpt (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)))
  have hgrad0 : ∀ y : M, -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1))) y)
        (rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1))) y) = 1 - (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1)) y) ^ 2 :=
    fun y hy => hgrad (qpt (I := I) (M := M) (cov := cov) hmet p e
      (0 : Fin (Module.finrank ℝ E + 1))) y hy
  have hsmC0 : ∀ y : M, -1 + c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) y →
      CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1))) y :=
    fun y hy => hsmC (qpt (I := I) (M := M) (cov := cov) hmet p e
      (0 : Fin (Module.finrank ℝ E + 1))) y hy
  have hle_or_lt : ∀ a b : ℝ, a ≤ b ∨ b < a := fun a b => (lt_or_ge b a).symm
  -- ## Parseval and the at-most-one facts
  obtain ⟨hpar, hAtMost, hSin, hTrigOf⟩ :=
    ray_cap_algebra (I := I) (M := M) (p := p) (e := e) hON hα hα1 hu
  -- ## the model comparison for the trig-good indices
  have hgood_model : ∀ (j : Fin (Module.finrank ℝ E)),
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Inner.inner ℝ (e j) u * Real.sin σ) →
      (∀ τ ∈ Set.Icc (0 : ℝ) s, -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) s,
          |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
            - Inner.inner ℝ (e j) u * Real.sin τ| ≤ 2 * ε₁ * s) := by
    intro j hj
    obtain ⟨h1, h2⟩ := hmodel (Fin.succ j) (fun σ hσ => by rw [hmodS j σ]; exact hj σ hσ)
    exact ⟨h1, fun τ hτ => by
      have h3 := h2 τ hτ
      rwa [hmodS j τ] at h3⟩
  have htrig_of_pos : ∀ (j : Fin (Module.finrank ℝ E)), -Real.cos α < Inner.inner ℝ (e j) u →
      ∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Inner.inner ℝ (e j) u * Real.sin σ := by
    intro j hj σ hσ
    have h1 : -Real.cos α ≤ Inner.inner ℝ (e j) u * Real.sin σ :=
      hTrigOf j hj σ ⟨hσ.1, le_trans hσ.2 hsπ⟩
    have h2 : -1 + 3 * c ≤ -Real.cos α := by linarith [hnum1]
    linarith
  -- ## the value bound for the trig-good indices at `x`
  have hβ_parseval : ∀ (j : Fin (Module.finrank ℝ E)), |Inner.inner ℝ (e j) u| ≤ 1 := by
    intro j
    have hsingle : (Inner.inner ℝ (e j) u) ^ 2
        ≤ ∑ k : Fin (Module.finrank ℝ E), (Inner.inner ℝ (e k) u) ^ 2 :=
      Finset.single_le_sum (f := fun k => (Inner.inner ℝ (e k) u) ^ 2) (fun k _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h := Real.sqrt_le_sqrt (le_trans hsingle (le_of_eq hpar))
    rwa [Real.sqrt_one, Real.sqrt_sq_eq_abs] at h
  have hvalS : ∀ (j : Fin (Module.finrank ℝ E)),
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Inner.inner ℝ (e j) u * Real.sin σ) →
      (|Real.sin s| ≤ Real.sqrt (6 * c) ∨ |Inner.inner ℝ (e j) u| ≤ Real.sqrt (6 * c)) →
      |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x)| ≤ 5 * lam := by
    intro j hj hb
    have h1 : -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x := by
      have h := (hgood_model j hj).1 s ⟨hs0, le_rfl⟩
      rwa [hxs] at h
    rw [hψid _ h1]
    have h2 : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
        - Inner.inner ℝ (e j) u * Real.sin s| ≤ 2 * ε₁ * s := by
      have h := (hgood_model j hj).2 s ⟨hs0, le_rfl⟩
      rwa [hxs] at h
    have hs1 : |Real.sin s| ≤ 1 := by
      rw [abs_le]; exact ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩
    have h3 : |Inner.inner ℝ (e j) u * Real.sin s| ≤ Real.sqrt (6 * c) := by
      rw [abs_mul]
      rcases hb with hb | hb
      · calc |Inner.inner ℝ (e j) u| * |Real.sin s| ≤ 1 * Real.sqrt (6 * c) :=
              mul_le_mul (hβ_parseval j) hb (abs_nonneg _) (by positivity)
          _ = Real.sqrt (6 * c) := one_mul _
      · calc |Inner.inner ℝ (e j) u| * |Real.sin s| ≤ Real.sqrt (6 * c) * 1 :=
              mul_le_mul hb hs1 (abs_nonneg _) (by positivity)
          _ = Real.sqrt (6 * c) := mul_one _
    have h4 := abs_add_le (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
      - Inner.inner ℝ (e j) u * Real.sin s) (Inner.inner ℝ (e j) u * Real.sin s)
    rw [sub_add_cancel] at h4
    linarith [h2, h3, h4, hsqrt6_le, h2ε₁s]
  -- ## the entry `(0,0)`
  have hpair00 : |gp (I := I) (M := M)
      (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) y))
      (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) y)) x - 1| ≤ 20 * c := by
    by_cases hcs : Real.cos s ≤ -1 + c
    · have hz : rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y)) x = 0 := by
        rcases lt_or_eq_of_le hcs with hcs' | hcs'
        · apply rgrad_eq_zero_of_eventuallyEq_const (I := I) (F := fun y : M =>
            ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1)) y))
          filter_upwards [(isOpen_lt hcont0 continuous_const).mem_nhds (by
            show fFam (I := I) (M := M) (cov := cov) hmet p e
                (0 : Fin (Module.finrank ℝ E + 1)) x < -1 + c
            rw [hf0x]; exact hcs')] with z hz
          exact hψconst _ (le_of_lt hz)
        · have hsm : CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1))) x :=
            hsmC0 x (by rw [hf0x]; exact le_of_eq hcs'.symm)
          rw [rgrad_psi_comp (I := I) hψC (f := fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1))) hsm]
          rw [show fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) x = -1 + c from by rw [hf0x]; exact hcs',
            hψ0, zero_smul]
      have hv : ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1)) x) = -1 + c := hψconst _ (by rw [hf0x]; exact hcs)
      simp only [gp]
      rw [hz, hv]
      simp only [inner_zero_left, zero_add]
      have h2 : |(-1 + c) * (-1 + c) - 1| ≤ 20 * c := by
        rw [abs_le]; constructor <;> nlinarith [hc]
      linarith
    · push_neg at hcs
      have hsm : CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1))) x := hsmC0 x (by rw [hf0x]; exact le_of_lt hcs)
      have heik := hgrad0 x (by rw [hf0x]; exact hcs)
      have hgr : rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y)) x
          = deriv ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1)) x)
            • rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1))) x :=
        rgrad_psi_comp (I := I) hψC (f := fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1))) hsm
      have hnf : Inner.inner ℝ (rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1))) x)
          (rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1))) x) = 1 - Real.cos s ^ 2 := by
        rw [← hf0x]; exact heik
      have hgoal : gp (I := I) (M := M)
            (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1)) y))
            (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1)) y)) x - 1
          = (deriv ψ (Real.cos s) ^ 2 - 1) * (1 - Real.cos s ^ 2)
            + (ψ (Real.cos s) ^ 2 - Real.cos s ^ 2) := by
        rw [gp, hgr, real_inner_smul_left, real_inner_smul_right, hnf, hf0x]
        ring
      rw [hgoal]
      rcases hle_or_lt (Real.cos s) (-1 + 2 * c) with h2c | h2c
      · have hB : 1 - Real.cos s ^ 2 ≤ 4 * c := by
          have h1 : -1 ≤ Real.cos s := Real.neg_one_le_cos s
          nlinarith [h2c, hc, h1]
        have hB0 : 0 ≤ 1 - Real.cos s ^ 2 := by
          have h1 : Real.cos s ≤ 1 := Real.cos_le_one s
          nlinarith [h1]
        have hBabs : |1 - Real.cos s ^ 2| ≤ 4 * c := by rw [abs_of_nonneg hB0]; exact hB
        have hA : |deriv ψ (Real.cos s) ^ 2 - 1| ≤ 3 := by
          rw [abs_le]
          have h0 := (hψ.2.2.1 (Real.cos s)).1
          have h0' := (hψ.2.2.1 (Real.cos s)).2
          constructor <;> nlinarith
        have hC : |ψ (Real.cos s) ^ 2 - Real.cos s ^ 2| ≤ 4 * c := by
          have hle1 : -1 ≤ Real.cos s := Real.neg_one_le_cos s
          have ha : |ψ (Real.cos s) - Real.cos s| ≤ 2 * c := hψsub _ hle1
          have hb : |ψ (Real.cos s) + Real.cos s| ≤ 2 := by
            have h0 : |ψ (Real.cos s)| ≤ 1 := hψone _ (Real.cos_le_one s)
            have h1 : |Real.cos s| ≤ 1 := by
              rw [abs_le]; exact ⟨Real.neg_one_le_cos s, Real.cos_le_one s⟩
            calc |ψ (Real.cos s) + Real.cos s| ≤ |ψ (Real.cos s)| + |Real.cos s| := abs_add_le _ _
              _ ≤ 1 + 1 := by linarith
              _ = 2 := by norm_num
          have he : ψ (Real.cos s) ^ 2 - Real.cos s ^ 2
              = (ψ (Real.cos s) - Real.cos s) * (ψ (Real.cos s) + Real.cos s) := by ring
          rw [he, abs_mul]
          have h9 : |ψ (Real.cos s) - Real.cos s| * |ψ (Real.cos s) + Real.cos s| ≤ (2 * c) * 2 :=
            mul_le_mul ha hb (abs_nonneg _) (by linarith [hc])
          linarith [h9, hc]
        have h3 := abs_add_le ((deriv ψ (Real.cos s) ^ 2 - 1) * (1 - Real.cos s ^ 2))
          (ψ (Real.cos s) ^ 2 - Real.cos s ^ 2)
        have h4 : |(deriv ψ (Real.cos s) ^ 2 - 1) * (1 - Real.cos s ^ 2)| ≤ 3 * (4 * c) := by
          rw [abs_mul]
          exact mul_le_mul hA hBabs (abs_nonneg _) (by norm_num)
        linarith
      · have hψf : ψ (Real.cos s) = Real.cos s := hψid _ (le_of_lt h2c)
        have hder : deriv ψ (Real.cos s) = 1 := hψder1 _ h2c
        rw [hψf, hder]
        ring_nf
        simp only [abs_zero]
        positivity
  -- ## the gradient of `F_0` at `x` in the clamp region
  have hgradF0_le : Real.cos s < -1 + 2 * c →
      ‖rgrad (I := I) (M := M)
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1)) y)) x‖ ≤ 4 * lam := by
    intro hcs
    have hsin : |Real.sin s| ≤ 2 * Real.sqrt c := hsin_lt s hcs
    rcases hle_or_lt (Real.cos s) (-1 + c) with hlt | hlt
    · have hz : rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y)) x = 0 := by
        rcases lt_or_eq_of_le hlt with hlt' | hlt'
        · apply rgrad_eq_zero_of_eventuallyEq_const (I := I) (F := fun y : M =>
            ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1)) y))
          filter_upwards [(isOpen_lt hcont0 continuous_const).mem_nhds (by
            show fFam (I := I) (M := M) (cov := cov) hmet p e
                (0 : Fin (Module.finrank ℝ E + 1)) x < -1 + c
            rw [hf0x]; exact hlt')] with z hz
          exact hψconst _ (le_of_lt hz)
        · have hsm : CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1))) x :=
            hsmC0 x (by rw [hf0x]; exact le_of_eq hlt'.symm)
          rw [rgrad_psi_comp (I := I) hψC (f := fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1))) hsm]
          rw [show fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) x = -1 + c from by rw [hf0x]; exact hlt',
            hψ0, zero_smul]
      rw [hz, norm_zero]; linarith [hlam0]
    · have hsm : CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1))) x := hsmC0 x (by rw [hf0x]; exact le_of_lt hlt)
      rw [rgrad_psi_comp (I := I) hψC (f := fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1))) hsm, norm_smul, Real.norm_eq_abs]
      have hnorm : ‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1))) x‖ = |Real.sin s| := by
        have hs : ‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1))) x‖
            = Real.sqrt (‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
                (0 : Fin (Module.finrank ℝ E + 1))) x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
        rw [hs, ← real_inner_self_eq_norm_sq, hgrad0 x (by rw [hf0x]; exact hlt), hf0x]
        rw [show 1 - Real.cos s ^ 2 = Real.sin s ^ 2 by linarith [Real.sin_sq_add_cos_sq s]]
        exact Real.sqrt_sq_eq_abs _
      calc |deriv ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1)) x)|
            * ‖rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e
              (0 : Fin (Module.finrank ℝ E + 1))) x‖
          ≤ 2 * (2 * Real.sqrt c) := by
            rw [hnorm]; exact mul_le_mul (hψd2 _) hsin (abs_nonneg _) (by norm_num)
        _ ≤ 4 * lam := by nlinarith [hsqrtc_le_lam]
  -- ## the generic two-factor bound
  have hgp_le_gp : ∀ (A B : M → ℝ) (C1 C2 C3 C4 : ℝ), ‖rgrad (I := I) (M := M) A x‖ ≤ C1 →
      ‖rgrad (I := I) (M := M) B x‖ ≤ C2 → |A x| ≤ C3 → |B x| ≤ C4 →
      |gp (I := I) (M := M) A B x| ≤ C1 * C2 + C3 * C4 := by
    intro A B C1 C2 C3 C4 h1 h2 h3 h4
    simp only [gp]
    have h5 : |Inner.inner ℝ (rgrad (I := I) (M := M) A x) (rgrad (I := I) (M := M) B x)| ≤ C1 * C2 := by
      have h := abs_real_inner_le_norm (rgrad (I := I) (M := M) A x) (rgrad (I := I) (M := M) B x)
      have h6 : ‖rgrad (I := I) (M := M) A x‖ * ‖rgrad (I := I) (M := M) B x‖ ≤ C1 * C2 :=
        mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      linarith
    have h7 : |A x * B x| ≤ C3 * C4 := by
      rw [abs_mul]
      exact mul_le_mul h3 h4 (abs_nonneg _) (le_trans (abs_nonneg _) h3)
    linarith [abs_add_le (Inner.inner ℝ (rgrad (I := I) (M := M) A x) (rgrad (I := I) (M := M) B x))
      (A x * B x), h5, h7]
  -- ## the entries between index `0` and a trig-good `Fin.succ` index
  have hpair0 : ∀ (j : Fin (Module.finrank ℝ E)),
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Inner.inner ℝ (e j) u * Real.sin σ) →
      (|Real.sin s| ≤ Real.sqrt (6 * c) ∨ |Inner.inner ℝ (e j) u| ≤ Real.sqrt (6 * c)) →
      |gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x|
        ≤ 14 * lam := by
    intro j hj hb
    by_cases hcs : -1 + 2 * c ≤ Real.cos s
    · have hstay : ∀ σ ∈ Set.Icc (0 : ℝ) s,
          -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ∧
          -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
        intro σ hσ
        refine ⟨?_, (hgood_model j hj).1 σ hσ⟩
        rw [hf0ray σ hσ]
        rcases lt_or_eq_of_le hσ.2 with hlt | heq
        · exact le_trans hcs (le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi hσ.1 hsπ hlt))
        · rw [heq]; exact hcs
      have hpair := gram_along_pair (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hu hs0 hxs
        hON hsmC hHess hcont hgrad hinit hψ (0 : Fin (Module.finrank ℝ E + 1)) (Fin.succ j) hstay
      have hδ : (if (0 : Fin (Module.finrank ℝ E + 1)) = Fin.succ j then (1:ℝ) else 0) = 0 :=
        if_neg (Ne.symm (Fin.succ_ne_zero j))
      rw [hδ, sub_zero] at hpair
      refine le_trans hpair ?_
      linarith [h2ε₁s]
    · push_neg at hcs
      have h1 : ‖rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y)) x‖ ≤ 4 * lam := hgradF0_le hcs
      have h2 : ‖rgrad (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x‖ ≤ 2 :=
        hgradbd (Fin.succ j) x
      have h3 : |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
          (0 : Fin (Module.finrank ℝ E + 1)) x)| ≤ 1 := hpsile1 0
      have h4 : |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x)| ≤ 5 * lam :=
        hvalS j hj hb
      have h5 := hgp_le_gp _ _ (4 * lam) 2 1 (5 * lam) h1 h2 h3 h4
      nlinarith [h5, hlam0]
  -- ## the entries between two trig-good `Fin.succ` indices
  have hgram_ss : ∀ (j j' : Fin (Module.finrank ℝ E)),
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Inner.inner ℝ (e j) u * Real.sin σ) →
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Inner.inner ℝ (e j') u * Real.sin σ) →
      |gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j') y)) x
        - (if (Fin.succ j : Fin (Module.finrank ℝ E + 1)) = Fin.succ j' then 1 else 0)|
        ≤ 2 * ε₁ * s := by
    intro j j' hj hj'
    have hstay : ∀ σ ∈ Set.Icc (0 : ℝ) s,
        -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ∧
        -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j')
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
      fun σ hσ => ⟨(hgood_model j hj).1 σ hσ, (hgood_model j' hj').1 σ hσ⟩
    exact gram_along_pair (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hu hs0 hxs
      hON hsmC hHess hcont hgrad hinit hψ (Fin.succ j) (Fin.succ j') hstay
  -- ## the two cases
  by_cases hD : ∃ (j : Fin (Module.finrank ℝ E)) (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) s ∧
      Inner.inner ℝ (e j) u * Real.sin σ < -1 + 3 * c
  · obtain ⟨j0, σ0, hσ0, hlt0⟩ := hD
    have hsin_pos : 0 < Real.sin σ0 := by
      have h1 : 0 ≤ Real.sin σ0 := Real.sin_nonneg_of_nonneg_of_le_pi hσ0.1 (le_trans hσ0.2 hsπ)
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exfalso
        rw [← h, mul_zero] at hlt0
        linarith
    have hβneg : Inner.inner ℝ (e j0) u < 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hlt0, hsin_pos]
    have hj0 : Inner.inner ℝ (e j0) u ≤ -(1 - 3 * c) := by
      have hsin1 : Real.sin σ0 ≤ 1 := Real.sin_le_one _
      nlinarith [hlt0, hsin1, hβneg]
    have hbad' : ∃ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) s ∧
        Inner.inner ℝ (e j0) u * Real.sin σ < -1 + 3 * c := ⟨σ0, hσ0, hlt0⟩
    have hj0cos : Inner.inner ℝ (e j0) u ≤ -Real.cos α := by linarith [hnum1]
    have huniq : ∀ j : Fin (Module.finrank ℝ E), Inner.inner ℝ (e j) u ≤ -(1 - 3 * c) → j = j0 := by
      intro j hj
      by_contra hne
      exact hAtMost j j0 hne (by linarith [hnum1]) hj0cos
    have hpos : ∀ j : Fin (Module.finrank ℝ E), j ≠ j0 → -Real.cos α < Inner.inner ℝ (e j) u := by
      intro j hj
      by_contra hcon
      push_neg at hcon
      exact hAtMost j j0 hj hcon hj0cos
    have hmod : ∀ j : Fin (Module.finrank ℝ E), j ≠ j0 →
        (∀ τ ∈ Set.Icc (0 : ℝ) s,
            -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) s,
            |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
                (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
              - Inner.inner ℝ (e j) u * Real.sin τ| ≤ 2 * ε₁ * s) :=
      fun j hj => hgood_model j (htrig_of_pos j (hpos j hj))
    have hbetaj : ∀ j : Fin (Module.finrank ℝ E), j ≠ j0 →
        |Inner.inner ℝ (e j) u| ≤ Real.sqrt (6 * c) := by
      intro j hj
      have hsingle : (Inner.inner ℝ (e j) u) ^ 2
          ≤ ∑ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))).erase j0,
              (Inner.inner ℝ (e k) u) ^ 2 :=
        Finset.single_le_sum (f := fun k => (Inner.inner ℝ (e k) u) ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      have hsum_erase : ∑ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))).erase j0,
            (Inner.inner ℝ (e k) u) ^ 2
          = 1 - (Inner.inner ℝ (e j0) u) ^ 2 := by
        have h1 := Finset.sum_erase_add (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k => (Inner.inner ℝ (e k) u) ^ 2) (Finset.mem_univ j0)
        rw [hpar] at h1
        linarith
      have hle : (Inner.inner ℝ (e j) u) ^ 2 ≤ 6 * c := by
        have h1 : (1 - 3 * c) ^ 2 ≤ (Inner.inner ℝ (e j0) u) ^ 2 := by nlinarith [hj0, hβneg]
        rw [hsum_erase] at hsingle
        nlinarith [hsingle, h1]
      have h2 := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq_eq_abs] at h2
    exact gb2_dip_branch (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1 hε₁ hnum1 hnum2
      hON hdiam hsmC hHess hcont hgrad hinit hψ (u := u) (s := s) (x := x) hu hs0 hsπ hrs hxs
      (j0 := j0) hj0 huniq hbad' hpar hmod hbetaj
      (fun j hj => hpair0 j (htrig_of_pos j (hpos j hj)) (Or.inr (hbetaj j hj))) hpair00
      (fun j j' hj hj' => hgram_ss j j' (htrig_of_pos j (hpos j hj)) (htrig_of_pos j' (hpos j' hj')))
      hf0ray hF0x hray_pt hgradbd hpsile1 (K := K) hKn hKn2
  · -- the equator case: every `Fin.succ` index is trig-good and index `0` is bad
    have hall : ∀ (j : Fin (Module.finrank ℝ E)), ∀ σ ∈ Set.Icc (0 : ℝ) s,
        -1 + 3 * c ≤ Inner.inner ℝ (e j) u * Real.sin σ := by
      intro j σ hσ
      by_contra hcon
      push_neg at hcon
      exact hD ⟨j, σ, hσ, hcon⟩
    -- index `0` is bad, hence `sin s` is small
    have hbad0 : Real.cos s < -1 + 3 * c := by
      obtain ⟨i₁, σ₁, hσ₁, hlt₁⟩ := hbad
      rcases Fin.eq_zero_or_eq_succ i₁ with hz | ⟨j₁, hs₁⟩
      · rw [hz, hmod0 σ₁] at hlt₁
        rcases lt_or_eq_of_le hσ₁.2 with hlt | heq
        · exact lt_trans (Real.cos_lt_cos_of_nonneg_of_le_pi hσ₁.1 hsπ hlt) hlt₁
        · rw [heq] at hlt₁; exact hlt₁
      · rw [hs₁, hmodS j₁ σ₁] at hlt₁
        exact absurd (hall j₁ σ₁ hσ₁) (not_le.mpr hlt₁)
    have hsin_small : |Real.sin s| ≤ Real.sqrt (6 * c) := by
      have h1 : Real.sin s ^ 2 = 1 - Real.cos s ^ 2 := by linarith [Real.sin_sq_add_cos_sq s]
      have h2 : (1 - 3 * c) ^ 2 < Real.cos s ^ 2 := by nlinarith [hbad0, hc, hc1]
      have h3 : Real.sin s ^ 2 ≤ 6 * c := by nlinarith [h1, h2]
      have h4 := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq_eq_abs] at h4
    -- the sum rule
    have hsumB : |(∑ k : Fin (Module.finrank ℝ E + 1),
        (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)) ^ 2) - 1| ≤ K := by
      obtain ⟨hmle, hmsum⟩ :=
        model_sum_eq_one (I := I) (M := M) (cov := cov) hmet hinit hON hu hpar
      have hdec : (∑ k : Fin (Module.finrank ℝ E + 1),
            (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)) ^ 2) - 1
          = ∑ k : Fin (Module.finrank ℝ E + 1),
              ((ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)) ^ 2
                - (fFam (I := I) (M := M) (cov := cov) hmet p e k p * Real.cos s
                  + Inner.inner ℝ (rgrad (I := I) (M := M)
                      (fFam (I := I) (M := M) (cov := cov) hmet p e k) p) u
                    * Real.sin s) ^ 2) := by
        rw [Finset.sum_sub_distrib, hmsum]
      rw [hdec]
      have hterm : ∀ k : Fin (Module.finrank ℝ E + 1),
          |(ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)) ^ 2
            - (fFam (I := I) (M := M) (cov := cov) hmet p e k p * Real.cos s
              + Inner.inner ℝ (rgrad (I := I) (M := M)
                  (fFam (I := I) (M := M) (cov := cov) hmet p e k) p) u
                * Real.sin s) ^ 2| ≤ 124 * lam := by
        intro k
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
        · rw [hmod0 s, hF0x]
          have h1 : |ψ (Real.cos s) - Real.cos s| ≤ 2 * c := hψsub _ (Real.neg_one_le_cos s)
          have h2 : |ψ (Real.cos s) + Real.cos s| ≤ 2 := by
            have hb : |Real.cos s| ≤ 1 := by
              rw [abs_le]; exact ⟨Real.neg_one_le_cos s, Real.cos_le_one s⟩
            calc |ψ (Real.cos s) + Real.cos s| ≤ |ψ (Real.cos s)| + |Real.cos s| := abs_add_le _ _
              _ ≤ 1 + 1 := add_le_add (hψone _ (Real.cos_le_one s)) hb
              _ = 2 := by norm_num
          have h3 : ψ (Real.cos s) ^ 2 - Real.cos s ^ 2
              = (ψ (Real.cos s) - Real.cos s) * (ψ (Real.cos s) + Real.cos s) := by ring
          rw [h3, abs_mul]
          have h4 : |ψ (Real.cos s) - Real.cos s| * |ψ (Real.cos s) + Real.cos s| ≤ (2 * c) * 2 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by linarith [hc])
          have h5 : (4 : ℝ) * c ≤ 124 * lam := by nlinarith [hc_le_lam, hlam0]
          linarith
        · rw [hmodS j s]
          have h1 : -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x := by
            have h := (hgood_model j (hall j)).1 s ⟨hs0, le_rfl⟩
            rwa [hxs] at h
          rw [hψid _ h1]
          have h2 : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
              - Inner.inner ℝ (e j) u * Real.sin s| ≤ 2 * ε₁ * s := by
            have h := (hgood_model j (hall j)).2 s ⟨hs0, le_rfl⟩
            rwa [hxs] at h
          have h3 : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
              + Inner.inner ℝ (e j) u * Real.sin s| ≤ 2 := by
            have hb : |Inner.inner ℝ (e j) u * Real.sin s| ≤ 1 := by
              rw [abs_mul]
              have hs1 : |Real.sin s| ≤ 1 := by
                rw [abs_le]; exact ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩
              calc |Inner.inner ℝ (e j) u| * |Real.sin s| ≤ 1 * 1 :=
                    mul_le_mul (hβ_parseval j) hs1 (abs_nonneg _) (by norm_num)
                _ = 1 := by norm_num
            have hfx : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x| ≤ 1 :=
              Real.abs_cos_le_one _
            calc |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
                  + Inner.inner ℝ (e j) u * Real.sin s|
                ≤ |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x|
                  + |Inner.inner ℝ (e j) u * Real.sin s| := abs_add_le _ _
              _ ≤ 1 + 1 := by linarith
              _ = 2 := by norm_num
          have h4 : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x ^ 2
                - (Inner.inner ℝ (e j) u * Real.sin s) ^ 2| ≤ (2 * ε₁ * s) * 2 := by
            have he : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x ^ 2
                - (Inner.inner ℝ (e j) u * Real.sin s) ^ 2
                = (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
                    - Inner.inner ℝ (e j) u * Real.sin s)
                  * (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
                    + Inner.inner ℝ (e j) u * Real.sin s) := by ring
            rw [he, abs_mul]
            have hb : (0 : ℝ) ≤ 2 * ε₁ * s := by positivity
            exact mul_le_mul h2 h3 (abs_nonneg _) hb
          have h5 : (2 * ε₁ * s) * 2 ≤ 124 * lam := by linarith [h2ε₁s, hlam0]
          linarith
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun k _ => hterm k)) ?_
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hcast : ((Module.finrank ℝ E + 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) + 1 := by
        push_cast; ring
      rw [hcast]
      have hnn : 0 ≤ ((Module.finrank ℝ E : ℝ) + 1) * lam := by positivity
      nlinarith [hnn, hKn2, hlam0]
    -- the Gram matrix
    refine ⟨hsumB, ?_⟩
    have hsymm : ∀ A B : M → ℝ, gp (I := I) (M := M) A B x = gp (I := I) (M := M) B A x := by
      intro A B
      simp only [gp, real_inner_comm]
      ring
    have hKsmall : 20 * c ≤ K := by nlinarith [hKn, hlam0, hc_le_lam]
    have hK14 : 14 * lam ≤ K := by nlinarith [hKn, hlam0]
    have hK2e : 2 * ε₁ * s ≤ K := by nlinarith [hKn, hlam0, h2ε₁s]
    intro k l
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨j, rfl⟩
      · rw [if_pos rfl]
        exact le_trans hpair00 hKsmall
      · rw [if_neg (Ne.symm (Fin.succ_ne_zero j)), sub_zero]
        exact le_trans (hpair0 j (hall j) (Or.inl hsin_small)) hK14
    · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨j, rfl⟩
      · rw [if_neg (Fin.succ_ne_zero i), sub_zero, hsymm]
        exact le_trans (hpair0 i (hall i) (Or.inl hsin_small)) hK14
      · by_cases hij : i = j
        · rw [hij, if_pos rfl]
          have hss := hgram_ss j j (hall j) (hall j)
          rw [if_pos rfl] at hss
          exact le_trans hss hK2e
        · rw [if_neg (fun h => hij (Fin.succ_injective _ h))]
          have hss := hgram_ss i j (hall i) (hall j)
          rw [if_neg (fun h => hij (Fin.succ_injective _ h))] at hss
          exact le_trans hss hK2e

end BadBranch

end Work.Diff.C
