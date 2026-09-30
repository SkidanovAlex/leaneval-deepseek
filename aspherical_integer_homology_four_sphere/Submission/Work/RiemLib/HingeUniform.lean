import Submission.Work.RiemLib.ChartFlowModel
import Submission.Work.RiemLib.ModelPath

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Route (M) for a parameter map, and the uniform comparison radius of a chart piece

`Submission.ModelPath.edist_expMap_le_model_ind` proves the local hinge comparison for the
exponential map `expMap cov x₀` in the chart at `x₀`, but its radius may depend on `x₀` (the chart
at `x₀` is arbitrary atlas data, see `Submission/Roadmap.lean` §38).  For the globalisation one
needs a *uniform* radius over a compact chart piece; the correct parameter map is the chart-flow
exponential `Submission.GExpFlow.chartFlowExp D q` of a fixed chart.

This file provides:

* `pointwise_bound_gen` — the pointwise differential bound along the great-circle model path, for an
  *arbitrary* map `F : E → M` and base point `q` (transcription of
  `Submission.ModelPath.pointwise_bound`, whose proof only ever uses the model bound `hbound`);
* `edist_le_model_gen` — the local hinge comparison for `F` (transcription of
  `Submission.ModelPath.edist_expMap_le_model_ind`);
* `exists_uniform_chartFlow_comparison` — the uniform comparison radius of a compact chart piece.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Curvature
open Submission.Rauch
open Submission.JacobiTensor
open Submission.Gauss
open Submission.GlobalExp
open Submission.ChartGeoAt
open Submission.FlowJacobi
open Submission.GExpFlow
open Submission.ChartFlowVar
open Submission.ChartFlowModel
open Submission.ModelBound
open Submission.ModelPath
open Submission.ChartBounds

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeUniform

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M}

/-- **The pointwise differential bound along the model path** (general parameter map `F`).
`hbound` is the polar model differential bound for `F` at the base point `q`, phrased with the
chart metric at `z₀` based at `q`; the path in the model space `E` is the coordinate image of the
great-circle path in the fibre `T_qM` under the chart trivialisation. -/
theorem pointwise_bound_gen [Nontrivial E]
    {F : E → M} {q : M} (hqs : q ∈ (extChartAt I z₀).source)
    {ρ Φ r₁ r₂ : ℝ} {U V : TangentSpace I q}
    (hbound : ∀ (r r' : ℝ) (e e' : E), 0 < r → r < ρ →
      chartGram (I := I) z₀ q e e = 1 → chartGram (I := I) z₀ q e e' = 0 →
      ‖(mfderiv 𝓘(ℝ, E) I F (r • e)) (r' • e + r • e')‖ ^ 2
        ≤ r' ^ 2 + (Real.sin r) ^ 2 * chartGram (I := I) z₀ q e' e')
    (hr1 : 0 < r₁) (hr1ρ : r₁ < ρ) (hr2 : 0 < r₂) (hr2ρ : r₂ < ρ)
    (hr1π : r₁ < Real.pi / 3) (hr2π : r₂ < Real.pi / 3)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi)
    (hcos : Real.cos Φ = Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)
    (hind : ∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(mfderiv 𝓘(ℝ, E) I F
          ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q
            (show TangentSpace I q from
              pσ (gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ)
                (gcC (Real.cos r₁) (Real.cos r₂) Φ) s)))
        ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q
          (show TangentSpace I q from
            pσ' (gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ)
              (gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ)
              (gcC (Real.cos r₁) (Real.cos r₂) Φ) (gcC' (Real.cos r₁) (Real.cos r₂) Φ) s))‖ ≤ Φ := by
  intro s hs
  set L : TangentSpace I q →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q with hLdef
  set A : ℝ → TangentSpace I q := gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hA
  set C : ℝ → ℝ := gcC (Real.cos r₁) (Real.cos r₂) Φ with hC
  set A' : ℝ → TangentSpace I q := gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hA'
  set C' : ℝ → ℝ := gcC' (Real.cos r₁) (Real.cos r₂) Φ with hC'
  have hAA₁ : ‖Real.sin r₁ • U‖ ^ 2 + (Real.cos r₁) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hU, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₁
  have hAA₂ : ‖Real.sin r₂ • V‖ ^ 2 + (Real.cos r₂) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hV, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₂
  have hcosAA : inner ℝ (Real.sin r₁ • U) (Real.sin r₂ • V)
      + Real.cos r₁ * Real.cos r₂ = Real.cos Φ := by
    rw [real_inner_smul_left, real_inner_smul_right, hcos]
    ring
  have hunit : ‖A s‖ ^ 2 + (C s) ^ 2 = 1 := by
    rw [hA, hC]
    exact gc_unit _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
  have hspeed : ‖A' s‖ ^ 2 + (C' s) ^ 2 = Φ ^ 2 := by
    rw [hA', hC']
    exact gc_speed _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
  have hne : A s ≠ 0 := by
    rw [hA]
    exact gcA_ne_zero r₁ r₂ Φ hr1 hr2 (by linarith [hr1π, Real.pi_pos])
      (by linarith [hr2π, Real.pi_pos]) hΦ0 hΦπ hind hs
  have hderA : HasDerivAt A (gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ s) s := by
    rw [hA]; exact hasDerivAt_gcA _ _ _ s
  have hderC : HasDerivAt C (gcC' (Real.cos r₁) (Real.cos r₂) Φ s) s := by
    rw [hC]; exact hasDerivAt_gcC _ _ _ s
  have htan : inner ℝ (A' s) (A s) + (C' s) * (C s) = 0 := by
    have hder : HasDerivAt (fun u : ℝ => ‖A u‖ ^ 2 + (C u) ^ 2) 0 s := by
      have hconst : (fun u : ℝ => ‖A u‖ ^ 2 + (C u) ^ 2) = fun _ => (1 : ℝ) := by
        funext u
        rw [hA, hC]
        exact gc_unit _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
      rw [hconst]
      exact hasDerivAt_const _ _
    have hder2 : HasDerivAt (fun u : ℝ => ‖A u‖ ^ 2 + (C u) ^ 2)
        (2 * inner ℝ (A s) (A' s) + 2 * (C s * C' s)) s := by
      have hA'eq : gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ = A' := hA'.symm
      have hC'eq : gcC' (Real.cos r₁) (Real.cos r₂) Φ = C' := hC'.symm
      have h1 : HasDerivAt (fun u : ℝ => ‖A u‖ ^ 2) (2 * inner ℝ (A s) (A' s)) s := by
        have := hderA.norm_sq
        rw [hA'eq] at this
        exact this
      have h2 : HasDerivAt (fun u : ℝ => (C u) ^ 2) (2 * (C s * C' s)) s := by
        have hm := hderC.mul hderC
        rw [hC'eq] at hm
        have hfun : (C * C) = fun u : ℝ => (C u) ^ 2 := by
          funext u; rw [Pi.mul_apply, sq]
        rw [hfun] at hm
        have hval : C' s * C s + C s * C' s = 2 * (C s * C' s) := by ring
        rw [hval] at hm
        exact hm
      exact h1.add h2
    have huniq := hder.unique hder2
    have hsym : inner ℝ (A' s) (A s) = inner ℝ (A s) (A' s) := real_inner_comm _ _
    linarith
  have hrp : 0 < pRadius C s := by
    have hcle : C s ≤ 1 := by
      have h2 : C s ^ 2 ≤ 1 := by nlinarith [hunit, sq_nonneg (‖A s‖)]
      nlinarith [h2, sq_nonneg (C s - 1)]
    have hclt : C s < 1 := by
      rcases lt_or_eq_of_le hcle with h' | h'
      · exact h'
      · exfalso
        have h0 : ‖A s‖ = 0 := by nlinarith [hunit, h', norm_nonneg (A s)]
        exact hne (norm_eq_zero.mp h0)
    rw [pRadius]
    exact Real.arccos_pos.mpr hclt
  have hrmaxlt : max r₁ r₂ < Real.pi / 3 := max_lt hr1π hr2π
  have hrmax : max r₁ r₂ ≤ Real.pi / 2 := by linarith [hrmaxlt, Real.pi_pos]
  have hrle : pRadius C s ≤ max r₁ r₂ := by
    have hge : Real.cos (max r₁ r₂) ≤ C s := by
      rw [hC]
      exact gcC_ge r₁ r₂ Φ hr1.le hr2.le hrmax hΦ0 hΦπ hs
    rw [pRadius]
    calc Real.arccos (C s) ≤ Real.arccos (Real.cos (max r₁ r₂)) := Real.arccos_le_arccos hge
      _ = max r₁ r₂ := Real.arccos_cos (le_trans hr1.le (le_max_left _ _))
          (le_trans hrmax (by linarith [Real.pi_pos]))
  have hrlt : pRadius C s < ρ := lt_of_le_of_lt hrle (max_lt hr1ρ hr2ρ)
  set e : TangentSpace I q := pE A C s with he
  set e' : TangentSpace I q := pE' A A' C C' s with he'
  have he1 : ‖e‖ = 1 := by rw [he]; exact pE_norm A C s hunit hne
  have hee' : inner ℝ e e' = 0 := by
    rw [he, he']; exact inner_pE_pE' A A' C C' s hunit hne htan
  have hcg1 : chartGram (I := I) z₀ q (L e) (L e) = 1 := by
    rw [hLdef, chartGram_clm (I := I) hqs e e, real_inner_self_eq_norm_sq, he1]
    norm_num
  have hcg2 : chartGram (I := I) z₀ q (L e) (L e') = 0 := by
    rw [hLdef, chartGram_clm (I := I) hqs e e']
    exact hee'
  have hb := hbound (pRadius C s) (pR C C' s) (L e) (L e') hrp hrlt hcg1 hcg2
  have hLe' : chartGram (I := I) z₀ q (L e') (L e') = ‖e'‖ ^ 2 := by
    rw [hLdef, chartGram_clm (I := I) hqs e' e', real_inner_self_eq_norm_sq]
  rw [hLe'] at hb
  have hpolar := polar_identity A A' C C' s Φ hunit hne htan hspeed
  rw [← he'] at hpolar
  have hσs : L (show TangentSpace I q from pσ A C s) = (pRadius C s) • L e := by
    rw [show (show TangentSpace I q from pσ A C s) = (pRadius C s) • e from by
      simp only [pσ, he]]
    rw [map_smul]
  have hσs' : L (show TangentSpace I q from pσ' A A' C C' s)
      = (pR C C' s) • L e + (pRadius C s) • L e' := by
    rw [show (show TangentSpace I q from pσ' A A' C C' s)
        = (pR C C' s) • e + (pRadius C s) • e' from by simp only [pσ', he, he']]
    rw [map_add, map_smul, map_smul]
  have hfinal : ‖(mfderiv 𝓘(ℝ, E) I F (L (show TangentSpace I q from pσ A C s)))
      (L (show TangentSpace I q from pσ' A A' C C' s))‖ ^ 2 ≤ Φ ^ 2 := by
    rw [hσs, hσs']
    exact hb.trans_eq hpolar
  exact (sq_le_sq₀ (norm_nonneg _) hΦ0.le).mp hfinal

/-- **The local hinge comparison for a parameter map `F`** (abstract form).  All the analytic
ingredients are supplied as hypotheses: the polar model differential bound `hbound`, the smoothness
`hsm` of `F` on a ball, and the lower bound `hgram_q` of the chart metric at `q`. -/
theorem edist_le_model_gen [Nontrivial E]
    {F : E → M} {q : M} (hqs : q ∈ (extChartAt I z₀).source)
    {ρ ρsm : ℝ} (hρsm : 0 < ρsm) {r₁ r₂ : ℝ} {U V : TangentSpace I q}
    (hbound : ∀ (r r' : ℝ) (e e' : E), 0 < r → r < ρ →
      chartGram (I := I) z₀ q e e = 1 → chartGram (I := I) z₀ q e e' = 0 →
      ‖(mfderiv 𝓘(ℝ, E) I F (r • e)) (r' • e + r • e')‖ ^ 2
        ≤ r' ^ 2 + (Real.sin r) ^ 2 * chartGram (I := I) z₀ q e' e')
    (hsm : ∀ u : E, ‖u‖ < ρsm → ContMDiffAt 𝓘(ℝ, E) I ∞ F u)
    {lam : ℝ} (hlam : 0 < lam)
    (hgram_q : ∀ w : E, lam * ‖w‖ ^ 2 ≤ chartGram (I := I) z₀ q w w)
    (hr1 : 0 < r₁) (hr1ρ : r₁ < ρ) (hr2 : 0 < r₂) (hr2ρ : r₂ < ρ)
    (hr1π : r₁ < Real.pi / 3) (hr2π : r₂ < Real.pi / 3)
    (hr1sm : r₁ < Real.sqrt lam * ρsm) (hr2sm : r₂ < Real.sqrt lam * ρsm)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1)
    (hind : ∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0) :
    Manifold.riemannianEDist I
        (F ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q (r₁ • U)))
        (F ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q (r₂ • V)))
      ≤ ENNReal.ofReal (Real.arccos (Real.cos r₁ * Real.cos r₂
          + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)) := by
  classical
  have hslpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  set Φ : ℝ := Real.arccos (Real.cos r₁ * Real.cos r₂
    + Real.sin r₁ * Real.sin r₂ * inner ℝ U V) with hΦdef
  have hΦcos : Real.cos Φ = Real.cos r₁ * Real.cos r₂
      + Real.sin r₁ * Real.sin r₂ * inner ℝ U V := by
    rw [hΦdef]
    exact (model_cos_range q r₁ r₂ U V hU hV).1
  have hΦlt : Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V < 1 :=
    modelDist_lt_one q hr1 hr2 hr1π hr2π hU hV hind
  have hΦgt : -1 < Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V :=
    modelDist_gt_neg_one q hr1 hr2 hr1π hr2π hU hV
  have hΦ0 : 0 < Φ := by rw [hΦdef]; exact Real.arccos_pos.mpr hΦlt
  have hΦπ : Φ < Real.pi := by rw [hΦdef]; exact Real.arccos_lt_pi.mpr hΦgt
  set L : TangentSpace I q →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q with hLdef
  set A : ℝ → TangentSpace I q := gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hA
  set A' : ℝ → TangentSpace I q := gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hA'
  set C : ℝ → ℝ := gcC (Real.cos r₁) (Real.cos r₂) Φ with hC
  set C' : ℝ → ℝ := gcC' (Real.cos r₁) (Real.cos r₂) Φ with hC'
  set σ : ℝ → TangentSpace I q := fun s => (pRadius C s) • ((pSin C s)⁻¹ • A s) with hσ
  set σ' : ℝ → TangentSpace I q := fun s => (pR C C' s) • ((pSin C s)⁻¹ • A s)
      + (pRadius C s) • ((pSin C s)⁻¹ • A' s
          + (((C s) * (C' s)) / (pSin C s) ^ 3) • A s) with hσ'
  set Γ : ℝ → M := fun s => F (L (σ s)) with hΓ
  have hAA₁ : ‖Real.sin r₁ • U‖ ^ 2 + (Real.cos r₁) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hU, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₁
  have hAA₂ : ‖Real.sin r₂ • V‖ ^ 2 + (Real.cos r₂) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hV, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₂
  have hcosAA : inner ℝ (Real.sin r₁ • U) (Real.sin r₂ • V)
      + Real.cos r₁ * Real.cos r₂ = Real.cos Φ := by
    rw [real_inner_smul_left, real_inner_smul_right, hΦcos]
    ring
  have hunit : ∀ s, ‖A s‖ ^ 2 + (C s) ^ 2 = 1 := by
    intro s
    rw [hA, hC]
    exact gc_unit _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
  have hneF : ∀ s ∈ Set.Icc (0 : ℝ) 1, A s ≠ 0 := by
    intro s hs
    rw [hA]
    exact gcA_ne_zero r₁ r₂ Φ hr1 hr2 (by linarith [hr1π, Real.pi_pos])
      (by linarith [hr2π, Real.pi_pos]) hΦ0 hΦπ hind hs
  have hrmaxlt : max r₁ r₂ < Real.pi / 3 := max_lt hr1π hr2π
  have hrmax : max r₁ r₂ ≤ Real.pi / 2 := by linarith [hrmaxlt, Real.pi_pos]
  have hrle : ∀ s ∈ Set.Icc (0 : ℝ) 1, pRadius C s ≤ max r₁ r₂ := by
    intro s hs
    have hge : Real.cos (max r₁ r₂) ≤ C s := by
      rw [hC]
      exact gcC_ge r₁ r₂ Φ hr1.le hr2.le hrmax hΦ0 hΦπ hs
    rw [pRadius]
    calc Real.arccos (C s) ≤ Real.arccos (Real.cos (max r₁ r₂)) := Real.arccos_le_arccos hge
      _ = max r₁ r₂ := Real.arccos_cos (le_trans hr1.le (le_max_left _ _))
          (le_trans hrmax (by linarith [Real.pi_pos]))
  -- the pointwise bound for the differential
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(mfderiv 𝓘(ℝ, E) I F (L (σ t))) (L (σ' t))‖ ≤ Φ := by
    intro t ht
    exact pointwise_bound_gen (z₀ := z₀) (F := F) (q := q) hqs (ρ := ρ) (Φ := Φ)
      (r₁ := r₁) (r₂ := r₂) (U := U) (V := V) hbound hr1 hr1ρ hr2 hr2ρ hr1π hr2π hU hV
      hΦ0 hΦπ hΦcos hind t ht
  -- smoothness of the model path
  have hAsm : ContDiff ℝ ∞ A := by
    rw [hA]
    show ContDiff ℝ ∞ (fun s : ℝ => (Real.sin ((1 - s) * Φ) / Real.sin Φ) • (Real.sin r₁ • U)
      + (Real.sin (s * Φ) / Real.sin Φ) • (Real.sin r₂ • V))
    exact (((Real.contDiff_sin.comp ((contDiff_const.sub contDiff_id).mul contDiff_const)).div_const
      _).smul_const _).add
      (((Real.contDiff_sin.comp (contDiff_id.mul contDiff_const)).div_const _).smul_const _)
  have hCsm : ContDiff ℝ ∞ C := by
    rw [hC]
    show ContDiff ℝ ∞ (fun s : ℝ => (Real.sin ((1 - s) * Φ) / Real.sin Φ) * Real.cos r₁
      + (Real.sin (s * Φ) / Real.sin Φ) * Real.cos r₂)
    exact (((Real.contDiff_sin.comp ((contDiff_const.sub contDiff_id).mul contDiff_const)).div_const
      _).mul contDiff_const).add
      ((((Real.contDiff_sin.comp (contDiff_id.mul contDiff_const)).div_const _).mul contDiff_const))
  -- the endpoints
  have hσ0 : σ 0 = r₁ • U := by
    show (Real.arccos (C 0)) • ((Real.sqrt (1 - (C 0) ^ 2))⁻¹ • (A 0)) = r₁ • U
    have hA0 : A 0 = Real.sin r₁ • U := by
      rw [hA]
      show (Real.sin ((1 - 0) * Φ) / Real.sin Φ) • (Real.sin r₁ • U)
        + (Real.sin (0 * Φ) / Real.sin Φ) • (Real.sin r₂ • V) = Real.sin r₁ • U
      rw [sub_zero, one_mul, zero_mul, Real.sin_zero, zero_div, zero_smul, add_zero,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_smul]
    have hC0 : C 0 = Real.cos r₁ := by
      rw [hC]
      show (Real.sin ((1 - 0) * Φ) / Real.sin Φ) * Real.cos r₁
        + (Real.sin (0 * Φ) / Real.sin Φ) * Real.cos r₂ = Real.cos r₁
      rw [sub_zero, one_mul, zero_mul, Real.sin_zero, zero_div, zero_mul, add_zero,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_mul]
    rw [hA0, hC0]
    have hsin1 : 0 < Real.sin r₁ :=
      Real.sin_pos_of_pos_of_lt_pi hr1 (by linarith [hr1π, Real.pi_pos])
    have hs : Real.sqrt (1 - Real.cos r₁ ^ 2) = Real.sin r₁ := by
      rw [← Real.sin_sq, Real.sqrt_sq hsin1.le]
    rw [hs, Real.arccos_cos hr1.le (le_of_lt (by linarith [hr1π, Real.pi_pos])),
      inv_smul_smul₀ (ne_of_gt hsin1)]
  have hσ1 : σ 1 = r₂ • V := by
    show (Real.arccos (C 1)) • ((Real.sqrt (1 - (C 1) ^ 2))⁻¹ • (A 1)) = r₂ • V
    have hA1 : A 1 = Real.sin r₂ • V := by
      rw [hA]
      show (Real.sin ((1 - 1) * Φ) / Real.sin Φ) • (Real.sin r₁ • U)
        + (Real.sin (1 * Φ) / Real.sin Φ) • (Real.sin r₂ • V) = Real.sin r₂ • V
      rw [sub_self, zero_mul, Real.sin_zero, zero_div, zero_smul, zero_add, one_mul,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_smul]
    have hC1 : C 1 = Real.cos r₂ := by
      rw [hC]
      show (Real.sin ((1 - 1) * Φ) / Real.sin Φ) * Real.cos r₁
        + (Real.sin (1 * Φ) / Real.sin Φ) * Real.cos r₂ = Real.cos r₂
      rw [sub_self, zero_mul, Real.sin_zero, zero_div, zero_mul, zero_add, one_mul,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_mul]
    rw [hA1, hC1]
    have hsin2 : 0 < Real.sin r₂ :=
      Real.sin_pos_of_pos_of_lt_pi hr2 (by linarith [hr2π, Real.pi_pos])
    have hs : Real.sqrt (1 - Real.cos r₂ ^ 2) = Real.sin r₂ := by
      rw [← Real.sin_sq, Real.sqrt_sq hsin2.le]
    rw [hs, Real.arccos_cos hr2.le (le_of_lt (by linarith [hr2π, Real.pi_pos])),
      inv_smul_smul₀ (ne_of_gt hsin2)]
  -- the fibre norm of the path
  have hfnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖σ t‖ = pRadius C t := by
    intro t ht
    have hS : 0 < pSin C t := pSin_pos A C t (hunit t) (hneF t ht)
    show ‖(pRadius C t) • ((pSin C t)⁻¹ • A t)‖ = pRadius C t
    have hAN : ‖A t‖ = pSin C t := (pSin_eq_norm A C t (hunit t)).symm
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ pRadius C t from Real.arccos_nonneg (C t)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hS), hAN,
      inv_mul_cancel₀ (ne_of_gt hS), mul_one]
  -- smallness in the model norm
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖L (σ t)‖ < ρsm := by
    intro t ht
    have hlem := hgram_q (L (σ t))
    have hchart : chartGram (I := I) z₀ q (L (σ t)) (L (σ t)) = ‖σ t‖ ^ 2 := by
      rw [hLdef, chartGram_clm (I := I) hqs (σ t) (σ t), real_inner_self_eq_norm_sq]
    rw [hchart, hfnorm t ht] at hlem
    have hr : pRadius C t < Real.sqrt lam * ρsm :=
      lt_of_le_of_lt (hrle t ht) (max_lt hr1sm hr2sm)
    have h2 : (pRadius C t) ^ 2 < lam * ρsm ^ 2 := by
      have h3 := mul_self_lt_mul_self (show 0 ≤ pRadius C t from Real.arccos_nonneg (C t)) hr
      calc (pRadius C t) ^ 2 = pRadius C t * pRadius C t := by rw [pow_two]
        _ < (Real.sqrt lam * ρsm) * (Real.sqrt lam * ρsm) := h3
        _ = lam * ρsm ^ 2 := by
            rw [mul_mul_mul_comm, Real.mul_self_sqrt hlam.le]
            ring
    have h4 : lam * ‖L (σ t)‖ ^ 2 < lam * ρsm ^ 2 := lt_of_le_of_lt hlem h2
    have h5 := lt_of_mul_lt_mul_left h4 hlam.le
    nlinarith [h5, norm_nonneg (L (σ t)), hρsm]
  -- the derivative of the path
  have hσd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt σ (σ' t) t := by
    intro t ht
    have hS : 0 < pSin C t := pSin_pos A C t (hunit t) (hneF t ht)
    have hAd : HasDerivAt A (A' t) t := by
      rw [hA, hA']
      exact hasDerivAt_gcA_normed _ _ _ t
    have hCd : HasDerivAt C (C' t) t := by
      rw [hC, hC']
      exact hasDerivAt_gcC _ _ _ t
    show HasDerivAt (fun u : ℝ => (pRadius C u) • ((pSin C u)⁻¹ • A u))
      ((pR C C' t) • ((pSin C t)⁻¹ • A t)
        + (pRadius C t) • ((pSin C t)⁻¹ • A' t
            + (((C t) * (C' t)) / (pSin C t) ^ 3) • A t)) t
    exact hasDerivAt_modelPath A A' C C' t hAd hCd hS
  -- smoothness of the path
  have hσsm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ σ t := by
    intro t ht
    have hCs : C t ∈ Set.Ioo (-1 : ℝ) 1 := by
      have h := hunit t
      constructor
      · by_contra hcon
        rw [not_lt] at hcon
        have h0 : ‖A t‖ = 0 := by nlinarith [h, hcon, norm_nonneg (A t)]
        exact hneF t ht (norm_eq_zero.mp h0)
      · by_contra hcon
        rw [not_lt] at hcon
        have h0 : ‖A t‖ = 0 := by nlinarith [h, hcon, norm_nonneg (A t)]
        exact hneF t ht (norm_eq_zero.mp h0)
    show ContDiffAt ℝ ∞ (fun u : ℝ => (pRadius C u) • ((pSin C u)⁻¹ • A u)) t
    exact contDiffAt_modelPath A C t hAsm.contDiffAt hCsm.contDiffAt hCs.1 hCs.2
  -- smoothness of the curve in `M`
  have hσLsm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (fun s => L (σ s)) t := by
    intro t ht
    have h := L.contDiff.contDiffAt.comp t (hσsm t ht)
    simpa [Function.comp_def] using h
  have hΓsm : CMDiff[Set.Icc (0 : ℝ) 1] 1 Γ := by
    have h1 : ContMDiffOn 𝓘(ℝ) I ∞ Γ (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hσc : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s => L (σ s)) t :=
        contMDiffAt_iff_contDiffAt.mpr (hσLsm t ht)
      have hF : ContMDiffAt 𝓘(ℝ, E) I ∞ F (L (σ t)) := hsm (L (σ t)) (hsmall t ht)
      exact (hF.comp t hσc).contMDiffWithinAt.mono (Set.subset_univ _)
    exact h1.of_le (WithTop.coe_le_coe.mpr le_top)
  -- the velocity identity
  have hvel : ∀ t ∈ Set.Icc (0 : ℝ) 1, curveVelocity (I := I) Γ t
      = (mfderiv 𝓘(ℝ, E) I F (L (σ t))) (L (σ' t)) := by
    intro t ht
    have hσdL : HasDerivAt (fun s => L (σ s)) (L (σ' t)) t := by
      have h := (L.hasFDerivAt (x := σ t)).comp t (hσd t ht).hasFDerivAt
      have h2 := h.hasDerivAt
      simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using h2
    have hmd : MDifferentiableAt 𝓘(ℝ, E) I F (L (σ t)) :=
      (hsm (L (σ t)) (hsmall t ht)).mdifferentiableAt (by norm_num)
    have hev : Γ =ᶠ[𝓝 t] (fun r => F (L (σ r))) := Filter.EventuallyEq.of_eq rfl
    exact curveVelocity_eq_mfderiv_comp (f := F) (σ := fun s => L (σ s))
      (σ' := fun _ => L (σ' t)) (γ := Γ) hσdL hmd hev
  -- the length integral
  haveI hcontR : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  have hdist : Manifold.riemannianEDist I (Γ 0) (Γ 1) ≤ Manifold.pathELength I Γ 0 1 :=
    Submission.EDist.riemannianEDist_le_pathELength (I := I) hΓsm rfl rfl zero_le_one
  have hlen : Manifold.pathELength I Γ 0 1
      = ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ :=
    Manifold.pathELength_eq_lintegral_mfderiv_Icc
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ ≤ ENNReal.ofReal Φ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    have h1 : ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ
        = ENNReal.ofReal ‖curveVelocity (I := I) Γ t‖ := by
      change ‖curveVelocity (I := I) Γ t‖ₑ = _
      rw [Submission.Minimal.enorm_eq_ofReal_norm]
    rw [h1, hvel t ht]
    exact ENNReal.ofReal_le_ofReal (hpoint t ht)
  have hmain : Manifold.riemannianEDist I (Γ 0) (Γ 1) ≤ ENNReal.ofReal Φ :=
    calc Manifold.riemannianEDist I (Γ 0) (Γ 1) ≤ Manifold.pathELength I Γ 0 1 := hdist
      _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ := hlen
      _ ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal Φ := MeasureTheory.lintegral_mono_ae hae
      _ = ENNReal.ofReal Φ := by
          rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
          norm_num
  calc Manifold.riemannianEDist I
        (F ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q (r₁ • U)))
        (F ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q (r₂ • V)))
      = Manifold.riemannianEDist I (Γ 0) (Γ 1) := by
        congr 1
        · simp only [hΓ, hσ0, hLdef]
        · simp only [hΓ, hσ1, hLdef]
    _ ≤ ENNReal.ofReal Φ := hmain
    _ = ENNReal.ofReal (Real.arccos (Real.cos r₁ * Real.cos r₂
          + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)) := by rw [hΦdef]

/-- **The uniform comparison radius of a compact chart piece** (linearly independent case).
There is `ρ > 0`, independent of `q ∈ Z`, such that for all unit `U V ∈ T_qM` spanning a plane and all
`r₁ r₂ ∈ (0,ρ)` the chart-flow exponential points satisfy the model comparison. -/
theorem exists_uniform_chartFlow_comparison_ind [Nontrivial E] [CompactSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {Z : Set M} (hZsrc : Z ⊆ (chartAt H z₀).source)
    {lam : ℝ} (hlam : 0 < lam)
    (hgram : ∀ q ∈ Z, ∀ w : E, lam * ‖w‖ ^ 2 ≤ chartGram (I := I) z₀ q w w)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ Real.sqrt lam * (1 / (2 * flowScale D)) ∧
      ∀ q ∈ Z, ∀ (r₁ r₂ : ℝ) (U V : TangentSpace I q),
      0 < r₁ → r₁ < ρ → 0 < r₂ → r₂ < ρ → ‖U‖ = 1 → ‖V‖ = 1 →
      (∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0) →
      Manifold.riemannianEDist I
          (chartFlowExp (cov := cov) D q
            ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q (r₁ • U)))
          (chartFlowExp (cov := cov) D q
            ((trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q (r₂ • V)))
        ≤ ENNReal.ofReal (Real.arccos (Real.cos r₁ * Real.cos r₂
            + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)) := by
  classical
  obtain ⟨ρb, hρb, hbound₀⟩ := chartFlow_model_bound_polar (cov := cov) (z₀ := z₀) (Z := Z)
    hmet htor hpinch hZsrc hlam hgram D
  have hcpos : 0 < flowScale D := flowScale_pos D
  have hρsm : 0 < 1 / (2 * flowScale D) := div_pos one_pos (mul_pos two_pos hcpos)
  have hslpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨min (min ρb (Real.pi / 3)) (Real.sqrt lam * (1 / (2 * flowScale D))),
    lt_min (lt_min hρb (by linarith [Real.pi_pos])) (mul_pos hslpos hρsm), min_le_right _ _, ?_⟩
  intro q hq r₁ r₂ U V hr1 hr1ρ hr2 hr2ρ hU hV hind
  have hqs : q ∈ (extChartAt I z₀).source := by simpa using hZsrc hq
  have hsm : ∀ u : E, ‖u‖ < 1 / (2 * flowScale D) →
      ContMDiffAt 𝓘(ℝ, E) I ∞ (chartFlowExp (cov := cov) D q) u := by
    intro u hu
    refine chartFlowExp_contMDiffAt (cov := cov) D ?_
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [lt_div_iff₀ (mul_pos two_pos hcpos)] at hu
    linarith
  refine edist_le_model_gen (z₀ := z₀) (F := chartFlowExp (cov := cov) D q)
    (q := q) hqs (ρ := ρb) (ρsm := 1 / (2 * flowScale D)) hρsm
    (fun r r' e e' hr hrρ he hee' => hbound₀ q hq r r' e e' hr hrρ he hee')
    hsm hlam (fun w => hgram q hq w)
    hr1 (lt_of_lt_of_le hr1ρ (le_trans (min_le_left _ _) (min_le_left _ _)))
    hr2 (lt_of_lt_of_le hr2ρ (le_trans (min_le_left _ _) (min_le_left _ _)))
    (lt_of_lt_of_le hr1ρ (le_trans (min_le_left _ _) (min_le_right _ _)))
    (lt_of_lt_of_le hr2ρ (le_trans (min_le_left _ _) (min_le_right _ _)))
    (lt_of_lt_of_le hr1ρ (min_le_right _ _))
    (lt_of_lt_of_le hr2ρ (min_le_right _ _))
    hU hV hind

end

end Submission.HingeUniform
