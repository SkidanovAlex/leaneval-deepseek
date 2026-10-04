import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.gb2_dip_aux
import Submission.Work.Diff.C.geoCrux.gram_shifted
import Submission.Work.Diff.C.geoCrux.far_ball_diam
import Submission.Work.Diff.C.geoCrux.bad_index_model
import Submission.Work.Diff.C.geoCrux.Defs
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.rgrad_fcos_eikonal
import Submission.Work.Diff.C.psi_estimates
import Submission.Work.Diff.C.sum_rule_good_ray

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dip branch of `Work.Diff.C.gram_bad_case2`

This module proves `Work.Diff.C.gb2_dip_branch`: the whole "there is a dip index" branch of the
bad-index case of the classical high-pinching endgame, stated with the geometric hypotheses of
`Work.Diff.C.gram_pointwise2` / `gram_bad_case2` (NO global diameter bound `hdiam2` and NO perimeter
bound `hper` are needed), plus the good-index facts already established inside
`Work.Diff.C.gram_bad_case2` (the model comparison and Gram estimates for the indices `j ≠ j0`,
Parseval, the ray data).

The two analytic inputs are imported:
* `Work.Diff.C.geoCrux.far_ball_diam` — the far ball of `q_{j0}` has diameter `≤ 50 (√c + ε₁π)`;
* `Work.Diff.C.geoCrux.bad_index_model` — for the dip index `i0 = Fin.succ j0`, the model
  comparison `|f_{i0}(γτ) - β sin τ| ≤ 60 (√c + ε₁π)`, the location of the clamp times
  (`f_{i0}(γτ) ≤ -1+2c → |cos τ| ≤ 60 (√c + ε₁π)`) and the smallness of `f_{i0}` on the far part of
  the ray.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic

set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- `ψ` is within `2c` of the identity on `[-1, ∞)` (a local copy of `Work.Diff.C.psi_abs_sub_le`). -/
theorem gb2_psi_abs_sub_le {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ t : ℝ, 0 ≤ deriv ψ t ∧ deriv ψ t ≤ 2) ∧
      (∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t) ∧ (∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c))
    {t : ℝ} (ht : -1 ≤ t) : |ψ t - t| ≤ 2 * c := by
  obtain ⟨h1, -, -, -, h5, -, -, -, -, -⟩ := psi_estimates hc hψ
  by_cases h : -1 + c ≤ t
  · exact h5 t h
  · rw [h1 t (le_of_lt (lt_of_not_ge h)), abs_le]
    constructor <;> linarith

/-- `ψ` takes values in `[-1, 1]` on `(-∞, 1]` (a local copy of `Work.Diff.C.psi_abs_le_one`). -/
theorem gb2_psi_abs_le_one {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ t : ℝ, 0 ≤ deriv ψ t ∧ deriv ψ t ≤ 2) ∧
      (∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t) ∧ (∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c))
    {t : ℝ} (ht : t ≤ 1) : |ψ t| ≤ 1 := by
  obtain ⟨-, -, h3, h4, -, -, -, -, -, -⟩ := psi_estimates hc hψ
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have := h3 t
    linarith
  · have hle : ψ t ≤ max t (-1 + 2 * c) := h4 t
    have h2 : max t (-1 + 2 * c) ≤ 1 := max_le ht (by linarith)
    linarith

/-- **The dip branch.**  See the module docstring. -/
theorem gb2_dip_branch
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
    {j0 : Fin (Module.finrank ℝ E)}
    (hj0 : Inner.inner ℝ (e j0) u ≤ -(1 - 3 * c))
    (huniq : ∀ j : Fin (Module.finrank ℝ E), Inner.inner ℝ (e j) u ≤ -(1 - 3 * c) → j = j0)
    (hbad' : ∃ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) s ∧
      Inner.inner ℝ (e j0) u * Real.sin σ < -1 + 3 * c)
    (hpar : ∑ j : Fin (Module.finrank ℝ E), (Inner.inner ℝ (e j) u) ^ 2 = 1)
    (hmod : ∀ j : Fin (Module.finrank ℝ E), j ≠ j0 →
      (∀ τ ∈ Set.Icc (0 : ℝ) s,
          -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) s,
          |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
            - Inner.inner ℝ (e j) u * Real.sin τ| ≤ 2 * ε₁ * s))
    (hbetaj : ∀ j : Fin (Module.finrank ℝ E), j ≠ j0 →
      |Inner.inner ℝ (e j) u| ≤ Real.sqrt (6 * c))
    (hpair0 : ∀ j : Fin (Module.finrank ℝ E), j ≠ j0 →
      |gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x|
        ≤ 14 * (Real.sqrt c + ε₁ * Real.pi))
    (hpair00 : |gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1)) y)) x - 1| ≤ 20 * c)
    (hgram_ss : ∀ j j' : Fin (Module.finrank ℝ E), j ≠ j0 → j' ≠ j0 →
      |gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j') y)) x
        - (if (Fin.succ j : Fin (Module.finrank ℝ E + 1)) = Fin.succ j' then 1 else 0)|
        ≤ 2 * ε₁ * s)
    (hf0ray : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = Real.cos τ)
    (hF0x : ψ (fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) x) = ψ (Real.cos s))
    (hray_pt : ∀ σ ∈ Set.Icc (0 : ℝ) s, rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) = σ)
    (hgradbd : ∀ (k : Fin (Module.finrank ℝ E + 1)) (y : M),
      ‖rgrad (I := I) (M := M)
        (fun z : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k z)) y‖ ≤ 2)
    (hpsile1 : ∀ k : Fin (Module.finrank ℝ E + 1),
      |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)| ≤ 1)
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
  -- ## the two analytic inputs (both proved elsewhere, and axiom-clean)
  have hfar : ∀ (k : Fin (Module.finrank ℝ E)) (z z' : M),
      Real.pi - Real.arccos (1 - c) ≤
          rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      Real.pi - Real.arccos (1 - c) ≤
          rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z' →
      rdist (I := I) (M := M) z z' ≤ 50 * (Real.sqrt c + ε₁ * Real.pi) :=
    fun k => geoCrux.far_ball_diam (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1
      hε₁ hnum1 hnum2 hON hsmC hHess hcont hgrad hinit hdiam k
  obtain ⟨hclamp, hfarval, hmodel⟩ :=
    geoCrux.bad_index_model (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1 hε₁ hnum1
      hnum2 hON hsmC hHess hcont hgrad hinit hdiam hfar hu hs0 hsπ hray_pt j0 hbad'
  -- ## notation
  have hψC : ContDiff ℝ ∞ ψ := hψ.1
  have hψid : ∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t := hψ.2.2.2.1
  have hψconst : ∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c := hψ.2.2.2.2
  have hψder_le : ∀ t : ℝ, deriv ψ t ≤ 2 := fun t => (hψ.2.2.1 t).2
  have hψ0 : deriv ψ (-1 + c) = 0 := deriv_eq_zero_of_le_const hψC hψconst
  have hψest := psi_estimates hc hψ
  have hψder1 : ∀ t : ℝ, -1 + 2 * c < t → deriv ψ t = 1 := hψest.2.2.2.2.2.1
  have hψsub : ∀ t : ℝ, -1 ≤ t → |ψ t - t| ≤ 2 * c := fun t ht => gb2_psi_abs_sub_le hc hψ ht
  have hψone : ∀ t : ℝ, t ≤ 1 → |ψ t| ≤ 1 := fun t ht => gb2_psi_abs_le_one hc hc1 hψ ht
  -- ## the numeric content of `lam = √c + ε₁π`
  set lam : ℝ := Real.sqrt c + ε₁ * Real.pi with hlam
  have hsqrtc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hε₁π0 : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
  have hlam0 : 0 ≤ lam := by
    rw [hlam]; exact add_nonneg hsqrtc hε₁π0
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
  have hlam_le_one : lam ≤ 1 := by
    rw [hlam]
    have h1 : Real.sqrt c ≤ 1 / 2 := by
      have h2 : c ≤ (1 / 2 : ℝ) ^ 2 := by linarith
      calc Real.sqrt c ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
        _ = 1 / 2 := Real.sqrt_sq (by norm_num)
    have h3 : ε₁ * Real.pi ≤ 1 / 4 := by nlinarith [hnum2, hc, Real.pi_pos]
    linarith
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
  -- far-case sine bound
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
  -- ## the model at `p` (this is the Parseval identity `Σ m_k(s)² = 1`)
  obtain ⟨hmle, hmsum⟩ :=
    model_sum_eq_one (I := I) (M := M) (cov := cov) hmet hinit hON hu hpar
  have hm0 : fFam (I := I) (M := M) (cov := cov) hmet p e
        (0 : Fin (Module.finrank ℝ E + 1)) p * Real.cos s
      + Inner.inner ℝ (rgrad (I := I) (M := M)
          (fFam (I := I) (M := M) (cov := cov) hmet p e
            (0 : Fin (Module.finrank ℝ E + 1))) p) u * Real.sin s = Real.cos s := by
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
  have hmS : ∀ j : Fin (Module.finrank ℝ E),
      fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) p * Real.cos s
      + Inner.inner ℝ (rgrad (I := I) (M := M)
          (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)) p) u * Real.sin s
      = Inner.inner ℝ (e j) u * Real.sin s := by
    intro j
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
  have hf0x : fFam (I := I) (M := M) (cov := cov) hmet p e
      (0 : Fin (Module.finrank ℝ E + 1)) x = Real.cos s := by
    rw [← hxs]; exact hf0ray s ⟨hs0, le_rfl⟩
  have hcos_le_one : Real.cos s ≤ 1 := Real.cos_le_one s
  have hFix : |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
      - Inner.inner ℝ (e j0) u * Real.sin s| ≤ 60 * lam + 2 * c := by
    have hm := hmodel s ⟨hs0, le_rfl⟩
    rw [hxs] at hm
    have hp : |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
        - fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x| ≤ 2 * c :=
      hψsub _ (Real.neg_one_le_cos _)
    have h := abs_sub_le (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x))
      (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
      (Inner.inner ℝ (e j0) u * Real.sin s)
    linarith
  -- the clamp bound at `s`, in the cases where the dip index is clamped at the endpoint
  have hcos_s : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x ≤ -1 + 2 * c →
      |Real.cos s| ≤ 60 * lam := by
    intro hle
    have h := hclamp s ⟨hs0, le_rfl⟩ (by rw [hxs]; exact hle)
    exact h
  -- ## the sum rule
  have hsum : |(∑ k : Fin (Module.finrank ℝ E + 1),
      (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e k x)) ^ 2) - 1| ≤ K := by
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
      · rw [hm0, hf0x]
        have h1 : |ψ (Real.cos s) - Real.cos s| ≤ 2 * c := hψsub _ (Real.neg_one_le_cos s)
        have h2 : |ψ (Real.cos s) + Real.cos s| ≤ 2 := by
          have hb : |Real.cos s| ≤ 1 := by
            rw [abs_le]; exact ⟨Real.neg_one_le_cos s, Real.cos_le_one s⟩
          calc |ψ (Real.cos s) + Real.cos s| ≤ |ψ (Real.cos s)| + |Real.cos s| := abs_add_le _ _
            _ ≤ 1 + 1 := add_le_add (hψone _ hcos_le_one) hb
            _ = 2 := by norm_num
        have h3 : ψ (Real.cos s) ^ 2 - Real.cos s ^ 2
            = (ψ (Real.cos s) - Real.cos s) * (ψ (Real.cos s) + Real.cos s) := by ring
        rw [h3, abs_mul]
        have h4 : |ψ (Real.cos s) - Real.cos s| * |ψ (Real.cos s) + Real.cos s| ≤ 2 * c * 2 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by linarith [hc])
        have h5 : (4 : ℝ) * c ≤ 124 * lam := by nlinarith [hc_le_lam, hlam0]
        linarith
      · by_cases hj : j = j0
        · rw [hj]
          rw [hmS j0]
          have hle1 := hpsile1 (Fin.succ j0)
          have hm1 : |Inner.inner ℝ (e j0) u * Real.sin s| ≤ 1 := by
            have hβ : |Inner.inner ℝ (e j0) u| ≤ 1 := by
              have h := abs_real_inner_le_norm (e j0) u
              have he : ‖e j0‖ = 1 := by
                have hh := hON j0 j0
                rw [if_pos rfl, real_inner_self_eq_norm_sq] at hh
                nlinarith [norm_nonneg (e j0)]
              have hu1 : ‖u‖ = 1 := by
                have hh := real_inner_self_eq_norm_sq u
                rw [hu] at hh
                nlinarith [norm_nonneg u]
              rwa [he, hu1, mul_one] at h
            rw [abs_mul]
            have hs1 : |Real.sin s| ≤ 1 := by
              rw [abs_le]; exact ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩
            calc |Inner.inner ℝ (e j0) u| * |Real.sin s| ≤ 1 * 1 :=
                  mul_le_mul hβ hs1 (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          have hsum2 : |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
              + Inner.inner ℝ (e j0) u * Real.sin s| ≤ 2 := by
            calc _ ≤ |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)|
                  + |Inner.inner ℝ (e j0) u * Real.sin s| := abs_add_le _ _
              _ ≤ 1 + 1 := add_le_add hle1 hm1
              _ = 2 := by norm_num
          have h3 : ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x) ^ 2
              - (Inner.inner ℝ (e j0) u * Real.sin s) ^ 2
              = (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
                  - Inner.inner ℝ (e j0) u * Real.sin s)
                * (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
                  + Inner.inner ℝ (e j0) u * Real.sin s) := by ring
          rw [h3, abs_mul]
          have h4 : |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
                - Inner.inner ℝ (e j0) u * Real.sin s|
              * |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x)
                + Inner.inner ℝ (e j0) u * Real.sin s|
              ≤ (60 * lam + 2 * c) * 2 :=
            mul_le_mul hFix hsum2 (abs_nonneg _) (by linarith [hlam0, hc])
          have h5 : (60 * lam + 2 * c) * 2 ≤ 124 * lam := by
            nlinarith [hc_le_lam, hlam0]
          linarith
        · have hcl := (hmod j hj).1 s ⟨hs0, le_rfl⟩
          have hdev := (hmod j hj).2 s ⟨hs0, le_rfl⟩
          rw [hxs] at hcl hdev
          have hF : ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x)
              = fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x :=
            hψid _ hcl
          rw [hF, hmS j]
          have h2 : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
              + Inner.inner ℝ (e j) u * Real.sin s| ≤ 2 := by
            have hb : |Inner.inner ℝ (e j) u * Real.sin s| ≤ 1 := by
              rw [abs_mul]
              have hβ := hbetaj j hj
              have hs1 : |Real.sin s| ≤ 1 := by
                rw [abs_le]; exact ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩
              have hβ1 : |Inner.inner ℝ (e j) u| ≤ 1 := le_trans hβ hsqrt6c_le_one
              calc |Inner.inner ℝ (e j) u| * |Real.sin s| ≤ 1 * 1 :=
                    mul_le_mul hβ1 hs1 (abs_nonneg _) (by norm_num)
                _ = 1 := by norm_num
            calc _ ≤ |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x|
                  + |Inner.inner ℝ (e j) u * Real.sin s| := abs_add_le _ _
              _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) hb
              _ = 2 := by norm_num
          have h3 : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x ^ 2
              - (Inner.inner ℝ (e j) u * Real.sin s) ^ 2
              = (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
                  - Inner.inner ℝ (e j) u * Real.sin s)
                * (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
                  + Inner.inner ℝ (e j) u * Real.sin s) := by ring
          rw [h3, abs_mul]
          have h4 : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
                - Inner.inner ℝ (e j) u * Real.sin s|
              * |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x
                + Inner.inner ℝ (e j) u * Real.sin s| ≤ (2 * ε₁ * s) * 2 :=
            mul_le_mul hdev h2 (abs_nonneg _) (by positivity)
          have h5 : (2 * ε₁ * s) * 2 ≤ 124 * lam := by linarith [h2ε₁s, hlam0]
          linarith
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun k _ => hterm k)) ?_
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hc1' : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have := Module.finrank_pos (R := ℝ) (M := E)
      exact_mod_cast this
    have hcast : ((Module.finrank ℝ E + 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) + 1 := by
      push_cast; ring
    rw [hcast]
    have hnn : 0 ≤ ((Module.finrank ℝ E : ℝ) + 1) * lam := by positivity
    nlinarith [hnn, hKn2]
  -- ## the Gram entries
  refine ⟨hsum, ?_⟩
  -- ## the Gram entries
  let fi : M → ℝ := fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0)
  let Fi : M → ℝ := fun y : M => ψ (fi y)
  let f0 : M → ℝ := fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1))
  let F0 : M → ℝ := fun y : M => ψ (f0 y)
  have hfi : fi = fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) := rfl
  have hFi : Fi = (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) y)) := rfl
  have hf0 : f0 = fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)) := rfl
  have hF0 : F0 = (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)) y)) := rfl
  have hfiv : ∀ y : M, fi y = fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) y :=
    fun y => by simp only [hfi]
  have hf0v : ∀ y : M, f0 y = fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)) y :=
    fun y => by simp only [hf0]
  have hFiv : ∀ y : M, Fi y = ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) y) :=
    fun y => by simp only [hFi]
  have hF0v : ∀ y : M, F0 y = ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)) y) :=
    fun y => by simp only [hF0]
  have hK0 : 0 ≤ K := le_trans (by positivity : (0:ℝ) ≤ 300 * lam) hKn
  have hfi_cont : Continuous fi :=
    hcont (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0))
  have hf0_cont : Continuous f0 :=
    hcont (qpt (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1)))
  have hu_ne : u ≠ 0 := by intro h0; rw [h0] at hu; simp at hu
  have hγ_cont : Continuous (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hu_ne).continuous
  have hfig_cont : Continuous (fun τ : ℝ => fi (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) :=
    hfi_cont.comp hγ_cont
  have hsymm : ∀ A B : M → ℝ, gp (I := I) (M := M) A B x = gp (I := I) (M := M) B A x := by
    intro A B
    simp only [gp, real_inner_comm]
    ring
  have hle_or_lt : ∀ a b : ℝ, a ≤ b ∨ b < a := fun a b => (lt_or_ge b a).symm
  have heik : ∀ y : M, -1 + c < fi y →
      Inner.inner ℝ (rgrad (I := I) (M := M) fi y) (rgrad (I := I) (M := M) fi y) = 1 - (fi y) ^ 2 :=
    fun y hy => hgrad (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0)) y hy
  have heik0 : ∀ y : M, -1 + c < f0 y →
      Inner.inner ℝ (rgrad (I := I) (M := M) f0 y) (rgrad (I := I) (M := M) f0 y) = 1 - (f0 y) ^ 2 :=
    fun y hy => hgrad (qpt (I := I) (M := M) (cov := cov) hmet p e 0) y hy
  have hpsi_abs : ∀ t : ℝ, -1 ≤ t → |ψ t| ≤ |t| + 2 * c := by
    intro t ht
    have h1 : |ψ t| - |t| ≤ 2 * c :=
      le_trans (le_abs_self _)
        (le_trans (abs_abs_sub_abs_le_abs_sub (ψ t) t) (hψsub t ht))
    linarith
  have hψd2 : ∀ t : ℝ, |deriv ψ t| ≤ 2 := by
    intro t
    rw [abs_of_nonneg (hψ.2.2.1 t).1]
    exact (hψ.2.2.1 t).2
  have hFixb : |ψ (fi x) - Inner.inner ℝ (e j0) u * Real.sin s| ≤ 60 * lam + 2 * c := by
    simpa only [hfi] using hFix
  have hf0xb : f0 x = Real.cos s := by rw [hf0v]; exact hf0x
  have hF0xb : F0 x = ψ (Real.cos s) := by rw [hF0v]; exact hF0x
  -- ### the value / gradient dichotomy of the dip index
  have hFi_lep : ∀ y : M, fi y ≤ -1 + c → Fi y = -1 + c ∧ rgrad (I := I) (M := M) Fi y = 0 := by
    intro y hle
    refine ⟨hψconst _ hle, ?_⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · apply rgrad_eq_zero_of_eventuallyEq_const (I := I) (F := Fi)
      filter_upwards [(isOpen_lt hfi_cont continuous_const).mem_nhds hlt] with z hz
      exact hψconst _ (le_of_lt hz)
    · have hsm : CMDiffAt ∞ fi y :=
        hsmC (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0)) y (le_of_eq heq.symm)
      rw [rgrad_psi_comp (I := I) hψC (f := fi) hsm, heq, hψ0, zero_smul]
  have hFi_gtp : ∀ y : M, -1 + c < fi y →
      rgrad (I := I) (M := M) Fi y = deriv ψ (fi y) • rgrad (I := I) (M := M) fi y :=
    fun y hgt => rgrad_psi_comp (I := I) hψC (f := fi)
      (hsmC (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0)) y (le_of_lt hgt))
  -- the gradient of `Fi` where `fi ≤ -1 + 2c`
  have hgradFi_of : ∀ y : M, fi y ≤ -1 + 2 * c → ‖rgrad (I := I) (M := M) Fi y‖ ≤ 4 * lam := by
    intro y hle
    rcases hle_or_lt (fi y) (-1 + c) with h1 | h1
    · rw [(hFi_lep y h1).2, norm_zero]; linarith [hlam0]
    · rw [hFi_gtp y h1, norm_smul, Real.norm_eq_abs]
      have hsq : ‖rgrad (I := I) (M := M) fi y‖ ^ 2 ≤ 4 * c := by
        rw [← real_inner_self_eq_norm_sq, heik y h1]
        nlinarith [hle, hc, h1]
      have hnorm : ‖rgrad (I := I) (M := M) fi y‖ ≤ 2 * Real.sqrt c := by
        have h := Real.sqrt_le_sqrt hsq
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
          show Real.sqrt 4 = (2 : ℝ) by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
        exact h
      calc |deriv ψ (fi y)| * ‖rgrad (I := I) (M := M) fi y‖ ≤ 2 * (2 * Real.sqrt c) :=
            mul_le_mul (hψd2 _) hnorm (norm_nonneg _) (by norm_num)
        _ ≤ 4 * lam := by nlinarith [hsqrtc_le_lam]
  -- the value bound for the good indices on the ray
  have hFS_le_at : ∀ (j : Fin (Module.finrank ℝ E)), j ≠ j0 → ∀ z ∈ Set.Icc (0 : ℝ) s,
      |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (z • u)))| ≤ 5 * lam := by
    intro j hj z hz
    have h1 := (hmod j hj).1 z hz
    have hid := hψid _ h1
    rw [hid]
    have h2 := (hmod j hj).2 z hz
    have h3 : |Inner.inner ℝ (e j) u * Real.sin z| ≤ Real.sqrt (6 * c) := by
      rw [abs_mul]
      have hs1 : |Real.sin z| ≤ 1 := by
        rw [abs_le]; exact ⟨Real.neg_one_le_sin z, Real.sin_le_one z⟩
      calc |Inner.inner ℝ (e j) u| * |Real.sin z| ≤ Real.sqrt (6 * c) * 1 :=
            mul_le_mul (hbetaj j hj) hs1 (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = Real.sqrt (6 * c) := mul_one _
    have h4 := abs_add_le (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (z • u)) - Inner.inner ℝ (e j) u * Real.sin z)
      (Inner.inner ℝ (e j) u * Real.sin z)
    rw [sub_add_cancel] at h4
    linarith [h2, h3, h4, hsqrt6_le, h2ε₁s]
  have hFS_le : ∀ (j : Fin (Module.finrank ℝ E)), j ≠ j0 →
      |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x)| ≤ 5 * lam := by
    intro j hj
    have h := hFS_le_at j hj s ⟨hs0, le_rfl⟩
    rwa [hxs] at h
  -- the value bound for index `0` where the dip index is clamped at `x`
  have hF0x_le : fi x ≤ -1 + 2 * c → |F0 x| ≤ 62 * lam := by
    intro hle
    have hle' : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0) x ≤ -1 + 2 * c := by
      rw [← hfi]; exact hle
    have h60 := hcos_s hle'
    have h1 : |F0 x| ≤ |Real.cos s| + 2 * c := by
      rw [hF0xb]
      exact hpsi_abs _ (Real.neg_one_le_cos s)
    linarith [h60, h1, hc_le_lam]
  -- the value bound for index `0` at a far point
  have hF0far_le : ∀ z ∈ Set.Icc (0 : ℝ) s,
      fi (Submission.GlobalExp.GExp (cov := cov) hmet p (z • u)) ≤ -1 + 2 * c →
      |F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (z • u))| ≤ 62 * lam := by
    intro z hz hcl
    have h60 : |Real.cos z| ≤ 60 * lam := by
      have h' : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (z • u)) ≤ -1 + 2 * c := by
        rw [← hfi]; exact hcl
      exact hclamp z hz h'
    have h1 : |F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (z • u))|
        ≤ |Real.cos z| + 2 * c := by
      have h2 : F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (z • u)) = ψ (Real.cos z) := by
        rw [hF0v]
        exact congrArg ψ (hf0ray z hz)
      rw [h2]
      exact hpsi_abs _ (Real.neg_one_le_cos z)
    linarith [h60, h1, hc_le_lam]
  -- the value bound for the dip index at a far point
  have hFix_far : |Real.sin s| ≤ 2 * Real.sqrt c → |Fi x| ≤ 66 * lam := by
    intro hsin
    have h1 : |Fi x| ≤ |Inner.inner ℝ (e j0) u * Real.sin s| + (60 * lam + 2 * c) := by
      have h5 : |Fi x - Inner.inner ℝ (e j0) u * Real.sin s| ≤ 60 * lam + 2 * c := by
        simpa only [hFi] using hFixb
      have h3 := abs_add_le (Fi x - Inner.inner ℝ (e j0) u * Real.sin s)
        (Inner.inner ℝ (e j0) u * Real.sin s)
      rw [sub_add_cancel] at h3
      linarith
    have hβ : |Inner.inner ℝ (e j0) u| ≤ 1 := by
      have h := abs_real_inner_le_norm (e j0) u
      have he : ‖e j0‖ = 1 := by
        have hh := hON j0 j0
        rw [if_pos rfl, real_inner_self_eq_norm_sq] at hh
        nlinarith [norm_nonneg (e j0)]
      have hu1 : ‖u‖ = 1 := by
        have hh := real_inner_self_eq_norm_sq u
        rw [hu] at hh
        nlinarith [norm_nonneg u]
      rwa [he, hu1, mul_one] at h
    have h4 : |Inner.inner ℝ (e j0) u * Real.sin s| ≤ 2 * Real.sqrt c := by
      rw [abs_mul]
      calc |Inner.inner ℝ (e j0) u| * |Real.sin s| ≤ 1 * (2 * Real.sqrt c) :=
            mul_le_mul hβ hsin (abs_nonneg _) (by norm_num)
        _ = 2 * Real.sqrt c := one_mul _
    linarith [h1, h4, hlam0, hc_le_lam, hsqrtc_le_lam]
  -- the generic two-factor bound
  have hgp_le : ∀ (A B : M → ℝ) (z : M) (C1 C2 C3 C4 : ℝ), ‖rgrad (I := I) (M := M) A z‖ ≤ C1 →
      ‖rgrad (I := I) (M := M) B z‖ ≤ C2 →
      |A z| ≤ C3 → |B z| ≤ C4 → |gp (I := I) (M := M) A B z| ≤ C1 * C2 + C3 * C4 := by
    intro A B z C1 C2 C3 C4 h1 h2 h3 h4
    simp only [gp]
    have h5 : |Inner.inner ℝ (rgrad (I := I) (M := M) A z) (rgrad (I := I) (M := M) B z)| ≤ C1 * C2 := by
      have h := abs_real_inner_le_norm (rgrad (I := I) (M := M) A z) (rgrad (I := I) (M := M) B z)
      have h6 : ‖rgrad (I := I) (M := M) A z‖ * ‖rgrad (I := I) (M := M) B z‖ ≤ C1 * C2 :=
        mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      linarith
    have h7 : |A z * B z| ≤ C3 * C4 := by
      rw [abs_mul]
      exact mul_le_mul h3 h4 (abs_nonneg _) (le_trans (abs_nonneg _) h3)
    linarith [abs_add_le (Inner.inner ℝ (rgrad (I := I) (M := M) A z) (rgrad (I := I) (M := M) B z)) (A z * B z), h5, h7]
  -- ### the anchor
  have hanchor : -1 + 2 * c < fi x → ∃ a : ℝ, a ∈ Set.Icc (0 : ℝ) s ∧
      (∀ τ ∈ Set.Icc a s, -1 + 2 * c ≤ fi (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) ∧
      (a = 0 ∨ (fi (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) = -1 + 2 * c ∧
        |Real.cos a| ≤ 60 * lam)) := by
    intro hx
    by_cases hemp : ∃ τ ∈ Set.Icc (0 : ℝ) s,
        fi (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) ≤ -1 + 2 * c
    · obtain ⟨a, haIcc, hale, hmax⟩ := exists_isGreatest_of_Icc_le hfig_cont hemp
      have has : a < s := by
        rcases lt_or_eq_of_le haIcc.2 with h | h
        · exact h
        · exfalso
          have hs_eq : fi (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ -1 + 2 * c := by
            rw [← h]; exact hale
          rw [hxs] at hs_eq
          linarith
      have haeq : fi (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) = -1 + 2 * c := by
        rcases lt_or_eq_of_le hale with hlt | heq
        · exfalso
          have hop : {τ : ℝ | fi (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) < -1 + 2 * c}
              ∈ 𝓝 a :=
            (isOpen_lt hfig_cont continuous_const).mem_nhds hlt
          obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hop
          have hspos : 0 < 2 * (s - a) := by linarith
          set τ : ℝ := a + min ε (2 * (s - a)) / 2 with hτdef
          have hminpos : 0 < min ε (2 * (s - a)) := lt_min hεpos hspos
          have hτball : τ ∈ Metric.ball a ε := by
            rw [Metric.mem_ball, Real.dist_eq, hτdef, add_sub_cancel_left, abs_lt]
            exact ⟨by nlinarith [hεpos, hminpos],
                   by nlinarith [min_le_left ε (2 * (s - a)), hminpos]⟩
          have hτs : τ ≤ s := by rw [hτdef]; nlinarith [min_le_right ε (2 * (s - a))]
          have hτ0 : 0 ≤ τ := by rw [hτdef]; linarith [haIcc.1, hminpos]
          have h1 : fi (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) ≤ -1 + 2 * c :=
            le_of_lt (hε hτball)
          have h2 : τ ≤ a := hmax τ ⟨hτ0, hτs⟩ h1
          rw [hτdef] at h2
          nlinarith [hminpos]
        · exact heq
      have hclampa : |Real.cos a| ≤ 60 * lam := by
        have h' : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) ≤ -1 + 2 * c := by
          have h2t : fi (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) ≤ -1 + 2 * c :=
            haeq.le
          simpa only [hfi] using h2t
        exact hclamp a haIcc h'
      refine ⟨a, haIcc, ?_, Or.inr ⟨haeq, hclampa⟩⟩
      intro τ hτ
      rcases lt_or_eq_of_le hτ.1 with h1 | h1
      · by_contra hcon
        push_neg at hcon
        have := hmax τ ⟨le_trans haIcc.1 (le_of_lt h1), hτ.2⟩ (le_of_lt hcon)
        linarith
      · rw [← h1]; exact haeq.ge
    · push_neg at hemp
      exact ⟨0, ⟨le_rfl, hs0⟩, fun τ hτ => le_of_lt (hemp τ hτ), Or.inl rfl⟩
  -- ### the diagonal entry of the dip index
  have hdiag : |gp (I := I) (M := M) Fi Fi x - 1| ≤ K := by
    rcases hle_or_lt (fi x) (-1 + c) with h1 | h1
    · obtain ⟨hv, hg⟩ := hFi_lep x h1
      simp only [gp]
      rw [hg, hv]
      simp only [inner_zero_left, zero_add]
      have h2 : |(-1 + c) * (-1 + c) - 1| ≤ 20 * c := by
        rw [abs_le]; constructor <;> nlinarith [hc]
      nlinarith [h2, hK0, hKn, hlam0, hc_le_lam]
    · rcases hle_or_lt (fi x) (-1 + 2 * c) with h2 | h2
      · have hgoal : gp (I := I) (M := M) Fi Fi x - 1
            = (deriv ψ (fi x) ^ 2 - 1) * (1 - (fi x) ^ 2) + (ψ (fi x) ^ 2 - (fi x) ^ 2) := by
          have hFi_x : Fi x = ψ (fi x) := hFiv x
          simp only [gp]
          rw [hFi_gtp x h1, real_inner_smul_left, real_inner_smul_right, heik x h1, hFi_x]
          ring
        rw [hgoal]
        have hA : |deriv ψ (fi x) ^ 2 - 1| ≤ 3 := by
          rw [abs_le]
          have h0 := (hψ.2.2.1 (fi x)).1
          have h0' := (hψ.2.2.1 (fi x)).2
          constructor <;> nlinarith
        have hB : 1 - (fi x) ^ 2 ≤ 4 * c := by
          have hle1 : -1 ≤ fi x := Real.neg_one_le_cos _
          nlinarith [h2, hc, hle1]
        have hB0 : 0 ≤ 1 - (fi x) ^ 2 := by
          have hle1 : fi x ≤ 1 := Real.cos_le_one _
          nlinarith [hle1]
        have hBabs : |1 - (fi x) ^ 2| ≤ 4 * c := by
          rw [abs_of_nonneg hB0]; exact hB
        have hC : |ψ (fi x) ^ 2 - (fi x) ^ 2| ≤ 4 * c := by
          have hle1 : -1 ≤ fi x := Real.neg_one_le_cos _
          have ha : |ψ (fi x) - fi x| ≤ 2 * c := hψsub _ hle1
          have hb : |ψ (fi x) + fi x| ≤ 2 := by
            have h0 : |ψ (fi x)| ≤ 1 := hpsile1 (Fin.succ j0)
            have h1 : |fi x| ≤ 1 := by
              rw [hfi]
              show |Real.cos (rdist (I := I) (M := M)
                (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j0)) x)| ≤ 1
              exact Real.abs_cos_le_one _
            calc |ψ (fi x) + fi x| ≤ |ψ (fi x)| + |fi x| := abs_add_le _ _
              _ ≤ 1 + 1 := by linarith
              _ = 2 := by norm_num
          have he : ψ (fi x) ^ 2 - (fi x) ^ 2 = (ψ (fi x) - fi x) * (ψ (fi x) + fi x) := by ring
          rw [he, abs_mul]
          have h9 : |ψ (fi x) - fi x| * |ψ (fi x) + fi x| ≤ (2 * c) * 2 :=
            mul_le_mul ha hb (abs_nonneg (ψ (fi x) + fi x)) (by linarith [hc])
          linarith [h9, hc]
        have hsum : |(deriv ψ (fi x) ^ 2 - 1) * (1 - (fi x) ^ 2)
            + (ψ (fi x) ^ 2 - (fi x) ^ 2)| ≤ 20 * c := by
          have h3 := abs_add_le ((deriv ψ (fi x) ^ 2 - 1) * (1 - (fi x) ^ 2))
            (ψ (fi x) ^ 2 - (fi x) ^ 2)
          have h4 : |(deriv ψ (fi x) ^ 2 - 1) * (1 - (fi x) ^ 2)| ≤ 3 * (4 * c) := by
            rw [abs_mul]
            exact mul_le_mul hA hBabs (abs_nonneg _) (by norm_num)
          linarith
        nlinarith [hsum, hKn, hlam0, hc_le_lam, hK0]
      · have hgoal : gp (I := I) (M := M) Fi Fi x - 1 = 0 := by
          have hψf : ψ (fi x) = fi x := hψid _ (le_of_lt h2)
          have hder : deriv ψ (fi x) = 1 := hψder1 _ h2
          have hFi_x : Fi x = ψ (fi x) := hFiv x
          simp only [gp]
          rw [hFi_gtp x h1, real_inner_smul_left, real_inner_smul_right, heik x h1, hFi_x, hder, hψf]
          ring
        rw [hgoal, abs_zero]
        exact hK0
  -- ### the entry of the dip index with index `0`
  have hwith0 : |gp (I := I) (M := M) Fi F0 x| ≤ K := by
    rcases hle_or_lt (fi x) (-1 + c) with h1 | h1
    · obtain ⟨hv, hg⟩ := hFi_lep x h1
      have h2 : fi x ≤ -1 + 2 * c := by linarith
      have h0b := hF0x_le h2
      simp only [gp]
      rw [hg, hv]
      simp only [inner_zero_left, zero_add]
      have h3 : |(-1 + c) * F0 x| ≤ 1 * (62 * lam) := by
        rw [abs_mul]
        refine mul_le_mul ?_ h0b (abs_nonneg _) (by norm_num)
        rw [abs_le]; constructor <;> linarith [hc, hc1]
      nlinarith [h3, hKn, hlam0, hK0]
    · rcases hle_or_lt (fi x) (-1 + 2 * c) with h2 | h2
      · have hC1 := hgradFi_of x h2
        have hC2 : ‖rgrad (I := I) (M := M) F0 x‖ ≤ 2 := hgradbd 0 x
        have hC3 : |Fi x| ≤ 1 := hpsile1 (Fin.succ j0)
        have hC4 := hF0x_le h2
        have h := hgp_le Fi F0 x (4 * lam) 2 1 (62 * lam) hC1 hC2 hC3 hC4
        nlinarith [h, hKn, hlam0, hK0]
      · by_cases hcos : -1 + 2 * c ≤ Real.cos s
        · obtain ⟨a, haIcc, hastay, ha0or⟩ := hanchor h2
          have hstay0 : ∀ τ ∈ Set.Icc a s, -1 + 2 * c ≤
              fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (Module.finrank ℝ E + 1))
                (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) := by
            intro τ hτ
            rw [hf0ray τ ⟨le_trans haIcc.1 hτ.1, hτ.2⟩]
            rcases lt_or_eq_of_le hτ.2 with hlt | heq
            · exact le_trans hcos (le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi
                (le_trans haIcc.1 hτ.1) hsπ hlt))
            · rw [heq]; exact hcos
          have hshift := geoCrux.gram_shifted (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁
            hON hsmC hHess hcont hgrad hinit hψ (u := u) (s := s) (a := a) hu haIcc.1 haIcc.2
            (Fin.succ j0) (0 : Fin (Module.finrank ℝ E + 1))
            (fun τ hτ => ⟨hastay τ hτ, hstay0 τ hτ⟩)
          rw [hxs] at hshift
          have hAa : |gp (I := I) (M := M) Fi F0
              (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| ≤ 71 * lam := by
            rcases ha0or with ha0 | ⟨haeq, hcosa⟩
            · have h0u : Submission.GlobalExp.GExp (cov := cov) hmet p (a • u) = p := by
                rw [ha0, zero_smul]
                exact Submission.GlobalExp.GExp_zero hmet p
              rw [h0u, hFi, hF0]
              have hig := (init_gram (I := I) (M := M) (cov := cov) hmet hc hc1 hsmC hON hinit hψ).2
                (Fin.succ j0) (0 : Fin (Module.finrank ℝ E + 1))
              rw [hig, if_neg (Fin.succ_ne_zero j0), abs_zero]
              linarith [hlam0]
            · have h1 : ‖rgrad (I := I) (M := M) Fi
                  (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))‖ ≤ 4 * lam :=
                hgradFi_of _ (le_of_eq haeq)
              have h2 : ‖rgrad (I := I) (M := M) F0
                  (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))‖ ≤ 2 := hgradbd 0 _
              have h3 : |Fi (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| ≤ 1 := by
                rw [hFiv]; exact hψone _ (Real.cos_le_one _)
              have h4 : |F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| ≤ 62 * lam :=
                hF0far_le a haIcc haeq.le
              have h := hgp_le Fi F0 _ (4 * lam) 2 1 (62 * lam) h1 h2 h3 h4
              nlinarith [h, hlam0, hK0]
          have h2e : 2 * ε₁ * (s - a) ≤ 2 * lam := by
            have h1 : 2 * ε₁ * (s - a) ≤ 2 * ε₁ * s :=
              mul_le_mul_of_nonneg_left (by linarith [haIcc.1]) (by linarith)
            linarith [h1, h2ε₁s]
          have hshift' : |gp (I := I) (M := M) Fi F0 x
              - gp (I := I) (M := M) Fi F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))|
              ≤ 2 * ε₁ * (s - a) := by
            simpa only [hFi, hF0] using hshift
          have htri : |gp (I := I) (M := M) Fi F0 x| ≤
              |gp (I := I) (M := M) Fi F0 x
                - gp (I := I) (M := M) Fi F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))|
              + |gp (I := I) (M := M) Fi F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| := by
            have h := abs_add_le
              (gp (I := I) (M := M) Fi F0 x - gp (I := I) (M := M) Fi F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)))
              (gp (I := I) (M := M) Fi F0 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)))
            rwa [sub_add_cancel] at h
          linarith [hshift', hAa, h2e, htri, hKn, hlam0, hK0]
        · have hcos' : Real.cos s < -1 + 2 * c := lt_of_not_ge hcos
          have hsin : |Real.sin s| ≤ 2 * Real.sqrt c := hsin_lt s hcos'
          have h1 : ‖rgrad (I := I) (M := M) Fi x‖ ≤ 1 := by
            rcases hle_or_lt (fi x) (-1 + c) with hle | hle
            · rw [(hFi_lep x hle).2, norm_zero]; linarith [hlam0]
            · have hder : deriv ψ (fi x) = 1 := hψder1 _ h2
              rw [hFi_gtp x hle, norm_smul, Real.norm_eq_abs, hder]
              rw [show |(1:ℝ)| = 1 by norm_num, one_mul]
              have hsq : ‖rgrad (I := I) (M := M) fi x‖ ^ 2 ≤ 1 := by
                rw [← real_inner_self_eq_norm_sq, heik x hle]
                nlinarith [sq_nonneg (fi x)]
              have hnorm : ‖rgrad (I := I) (M := M) fi x‖ ≤ 1 := by
                have h := Real.sqrt_le_sqrt hsq
                rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] at h
              exact hnorm
          have h2 : ‖rgrad (I := I) (M := M) F0 x‖ ≤ 4 * lam := by
            rcases hle_or_lt (Real.cos s) (-1 + c) with hle | hle
            · rcases lt_or_eq_of_le hle with hlt | heq
              · have hz : rgrad (I := I) (M := M) F0 x = 0 := by
                  apply rgrad_eq_zero_of_eventuallyEq_const (I := I) (F := F0)
                  filter_upwards [(isOpen_lt hf0_cont continuous_const).mem_nhds
                    (show f0 x < -1 + c by rw [hf0v, hf0x]; exact hlt)] with y hy
                  exact hψconst _ (le_of_lt hy)
                rw [hz, norm_zero]; linarith [hlam0]
              · have hsm : CMDiffAt ∞ f0 x := by
                  refine hsmC (qpt (I := I) (M := M) (cov := cov) hmet p e 0) x ?_
                  change -1 + c ≤ f0 x
                  rw [hf0v, hf0x, ← heq]
                rw [rgrad_psi_comp (I := I) hψC (f := f0) hsm]
                rw [show f0 x = -1 + c by rw [hf0v, hf0x]; exact heq]
                rw [hψ0, zero_smul, norm_zero]
                linarith [hlam0]
            · have hsm : CMDiffAt ∞ f0 x := by
                refine hsmC (qpt (I := I) (M := M) (cov := cov) hmet p e 0) x ?_
                change -1 + c ≤ f0 x
                rw [hf0v, hf0x]
                exact le_of_lt hle
              rw [rgrad_psi_comp (I := I) hψC (f := f0) hsm, norm_smul, Real.norm_eq_abs]
              have hle' : -1 + c < f0 x := by rw [hf0v, hf0x]; exact hle
              have hnorm : ‖rgrad (I := I) (M := M) f0 x‖ = |Real.sin s| := by
                have hs : ‖rgrad (I := I) (M := M) f0 x‖
                    = Real.sqrt (‖rgrad (I := I) (M := M) f0 x‖ ^ 2) :=
                  (Real.sqrt_sq (norm_nonneg _)).symm
                rw [hs, ← real_inner_self_eq_norm_sq, heik0 x hle', hf0v, hf0x]
                rw [show 1 - Real.cos s ^ 2 = Real.sin s ^ 2 by
                  linarith [Real.sin_sq_add_cos_sq s]]
                exact Real.sqrt_sq_eq_abs _
              calc |deriv ψ (f0 x)| * ‖rgrad (I := I) (M := M) f0 x‖ ≤ 2 * (2 * Real.sqrt c) := by
                    rw [hnorm]
                    exact mul_le_mul (hψd2 _) hsin (abs_nonneg _) (by norm_num)
                _ ≤ 4 * lam := by nlinarith [hsqrtc_le_lam]
          have h3 : |Fi x| ≤ 66 * lam := hFix_far hsin
          have h4 : |F0 x| ≤ 1 := hpsile1 0
          have h := hgp_le Fi F0 x 1 (4 * lam) (66 * lam) 1 h1 h2 h3 h4
          nlinarith [h, hKn, hlam0, hK0]
  -- ### the entry of the dip index with a good `succ` index
  have hwithS : ∀ j : Fin (Module.finrank ℝ E), j ≠ j0 →
      |gp (I := I) (M := M) Fi
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x| ≤ K := by
    intro j hj
    rcases hle_or_lt (fi x) (-1 + c) with h1 | h1
    · obtain ⟨hv, hg⟩ := hFi_lep x h1
      have h2 : fi x ≤ -1 + 2 * c := by linarith
      have h0b := hFS_le j hj
      simp only [gp]
      rw [hg, hv]
      simp only [inner_zero_left, zero_add]
      have h3 : |(-1 + c) * ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) x)|
          ≤ 1 * (5 * lam) := by
        rw [abs_mul]
        refine mul_le_mul ?_ h0b (abs_nonneg _) (by norm_num)
        rw [abs_le]; constructor <;> linarith [hc, hc1]
      nlinarith [h3, hKn, hlam0, hK0]
    · rcases hle_or_lt (fi x) (-1 + 2 * c) with h2 | h2
      · have hC1 := hgradFi_of x h2
        have hC2 : ‖rgrad (I := I) (M := M)
            (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x‖ ≤ 2 :=
          hgradbd (Fin.succ j) x
        have hC3 : |Fi x| ≤ 1 := hpsile1 (Fin.succ j0)
        have hC4 := hFS_le j hj
        have h := hgp_le Fi _ x (4 * lam) 2 1 (5 * lam) hC1 hC2 hC3 hC4
        nlinarith [h, hKn, hlam0, hK0]
      · obtain ⟨a, haIcc, hastay, ha0or⟩ := hanchor h2
        have hstayS : ∀ τ ∈ Set.Icc a s, -1 + 2 * c ≤
            fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) :=
          fun τ hτ => (hmod j hj).1 τ ⟨le_trans haIcc.1 hτ.1, hτ.2⟩
        have hshift := geoCrux.gram_shifted (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁
          hON hsmC hHess hcont hgrad hinit hψ (u := u) (s := s) (a := a) hu haIcc.1 haIcc.2
          (Fin.succ j0) (Fin.succ j)
          (fun τ hτ => ⟨hastay τ hτ, hstayS τ hτ⟩)
        rw [hxs] at hshift
        have hAa : |gp (I := I) (M := M) Fi
            (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
            (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| ≤ 14 * lam := by
          rcases ha0or with ha0 | ⟨haeq, hcosa⟩
          · have h0u : Submission.GlobalExp.GExp (cov := cov) hmet p (a • u) = p := by
              rw [ha0, zero_smul]
              exact Submission.GlobalExp.GExp_zero hmet p
            rw [h0u, hFi]
            have hig := (init_gram (I := I) (M := M) (cov := cov) hmet hc hc1 hsmC hON hinit hψ).2
              (Fin.succ j0) (Fin.succ j)
            rw [hig, if_neg (fun h => hj (Fin.succ_injective _ h).symm), abs_zero]
            linarith [hlam0]
          · have h1 : ‖rgrad (I := I) (M := M) Fi
                (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))‖ ≤ 4 * lam :=
              hgradFi_of _ (le_of_eq haeq)
            have h2 : ‖rgrad (I := I) (M := M)
                (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
                (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))‖ ≤ 2 :=
              hgradbd (Fin.succ j) _
            have h3 : |Fi (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| ≤ 1 := by
              rw [hFiv]; exact hψone _ (Real.cos_le_one _)
            have h4 : |ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j)
                (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)))| ≤ 5 * lam :=
              hFS_le_at j hj a haIcc
            have h := hgp_le Fi _ _ (4 * lam) 2 1 (5 * lam) h1 h2 h3 h4
            nlinarith [h, hlam0, hK0]
        have h2e : 2 * ε₁ * (s - a) ≤ 2 * lam := by
          have h1 : 2 * ε₁ * (s - a) ≤ 2 * ε₁ * s :=
            mul_le_mul_of_nonneg_left (by linarith [haIcc.1]) (by linarith)
          linarith [h1, h2ε₁s]
        have hshift' : |gp (I := I) (M := M) Fi
              (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x
              - gp (I := I) (M := M) Fi
                (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
                (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| ≤ 2 * ε₁ * (s - a) := by
          simpa only [hFi] using hshift
        have htri : |gp (I := I) (M := M) Fi
              (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x| ≤
            |gp (I := I) (M := M) Fi
              (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x
              - gp (I := I) (M := M) Fi
                (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
                (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))|
            + |gp (I := I) (M := M) Fi
                (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
                (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))| := by
          have h := abs_add_le
            (gp (I := I) (M := M) Fi
              (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y)) x
              - gp (I := I) (M := M) Fi
                (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
                (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)))
            (gp (I := I) (M := M) Fi
              (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ j) y))
              (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)))
          rwa [sub_add_cancel] at h
        linarith [hshift', hAa, h2e, htri, hKn, hlam0, hK0]
  -- ### assembly
  intro k l
  have hKsmall : 20 * c ≤ K := by nlinarith [hKn, hlam0, hc_le_lam]
  have hKq : 14 * lam ≤ K := by nlinarith [hKn, hlam0]
  have hK2e : 2 * ε₁ * s ≤ K := by nlinarith [hKn, hlam0, h2ε₁s]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨j, rfl⟩
    · rw [if_pos rfl]
      exact le_trans hpair00 hKsmall
    · by_cases hj : j = j0
      · rw [hj, if_neg (Ne.symm (Fin.succ_ne_zero j0)), sub_zero, hsymm]
        exact hwith0
      · rw [if_neg (Ne.symm (Fin.succ_ne_zero j)), sub_zero]
        exact le_trans (hpair0 j hj) hKq
  · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨j, rfl⟩
    · by_cases hi : i = j0
      · rw [hi, if_neg (Fin.succ_ne_zero j0), sub_zero]
        exact hwith0
      · rw [if_neg (Fin.succ_ne_zero i), sub_zero, hsymm]
        exact le_trans (hpair0 i hi) hKq
    · by_cases hi : i = j0
      · by_cases hj : j = j0
        · rw [hi, hj, if_pos rfl]
          exact hdiag
        · rw [hi, if_neg (fun h => hj (Fin.succ_injective _ h).symm), sub_zero]
          exact hwithS j hj
      · by_cases hj : j = j0
        · rw [hj, if_neg (fun h => hi (Fin.succ_injective _ h)), sub_zero, hsymm]
          exact hwithS i hi
        · exact le_trans (hgram_ss i j hi hj) hK2e
end Branch

end Work.Diff.C
