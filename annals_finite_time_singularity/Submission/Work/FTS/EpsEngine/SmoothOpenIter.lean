/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/SmoothOpenIter.lean` — the *lead's ruling* on finding (XXIII),
# installed: one Picard step preserves `SmoothOpen` (no differentiation under `∫ ds`)

The obstruction of `EpsEngine/NOTES_LocalStep.md` §5 (finding (XXIII)) came from differentiating
`∫₀^τ F (w_s) ds` in `(z,θ)`, which would need all-order pointwise bounds on the derivative slots of
the integrand, uniformly in `s` — not available from the class data.  The ruling
(`sources/ftsV2/fts_e4_smoothopen_ruling.md`) shows the route is the wrong one: **Fubini moves the
time integral inside the mollifier**,

    h₀ + ∫₀^τ Feps(w_s) ds  =  h₀ + J_ε(Ψ) − (∫₀^τ c_s ds)·bump      on `Q0`,
    Ψ := ∫₀^τ profRHS(Pz J_ε w_s) ds,     c_s := L12(J_ε Φ_s)(0)/pzNorm,

and `J_ε` of any locally integrable function is `C^∞` on `Q0` (the proved `Jeps_contDiffOn`).  So `Ψ`
only has to be *continuous*, which needs merely the order-0 bound `(C)`
(`profRHS_pre_sub_pt_le_Sq`: the pre-mollified right-hand side is pointwise Lipschitz in the profile,
uniformly on the quadrant, hence — along a curve that is `EpsSq`-Lipschitz in the fake time —
jointly continuous in log coordinates).

This file is the lead's companion `.lean` (axiom-clean, copied verbatim except for this header and
the removed `#print axioms` line).  Contents:

* `Work.FTS.StrongEps.EpsLocalPStar.profRHS_pre_sub_pt_le_Sq` — the (C) bound;
* `Work.FTS.EpsEngine.SORuling.smoothOpen_of_mollForm` — mollified form ⟹ `SmoothOpen`;
* `Work.FTS.EpsEngine.SORuling.conv_intervalIntegral_swap` — the Fubini step;
* `Work.FTS.EpsEngine.SORuling.continuous_logPull_family` — joint continuity in log coordinates;
* `Work.FTS.EpsEngine.SORuling.smoothOpen_picard_slice` — the generic Picard step;
* `Work.FTS.EpsEngine.SORuling.smoothOpen_iter_succ_XBall` — **the concrete `hkeepIter`
  `SmoothOpen` clause** for the `XBall` class.

The two remaining inputs of `smoothOpen_iter_succ_XBall` are supplied by the engine:
`hEq` (the time-Minkowski bound `EpsSq (w_s − w_t) ≤ L (s−t)²`, from `IterContMeas`'s induction) and
`hFint` (pointwise interval integrability, from the `cont(n)` component of `iter_cont_meas`, or
directly from `hpt` + `hEq`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Convolution
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsLocalPStar
set_option maxHeartbeats 1600000 in
/-- (C) **pointwise Lipschitz bound of the PRE-mollified right-hand side** on the `X`-ball:
`|profRHS(Wp u) − profRHS(Wp v)|(z,θ) ≤ C √EpsSq(u−v)`, uniformly on the open quadrant.
(Same hypotheses as `profRHS_sub_sup_le_Sq`; the proof is its first half.) -/
theorem profRHS_pre_sub_pt_le_Sq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (_hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Fn},
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      Work.FTS.StrongEps.EpsMem α u → Work.FTS.StrongEps.EpsSq α u ≤ R →
      Work.FTS.StrongEps.EpsMem α v → Work.FTS.StrongEps.EpsSq α v ≤ R →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ C₀ * α ^ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
          - profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨K₁, hK₁pos, hK₁⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨CD, hCDpos, hCD⟩ := HkSq_Wp_sub_le_weak (α := α) hρ hα hε hε1
  obtain ⟨Cpt, hCpt0, hCpt⟩ := pointwise_le_HkNorm (α := α) hα0 hα1
  set BS : ℝ := Real.sqrt (CH * (CH / ε) ^ 10 * R) + 1 with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]; have := Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R); linarith
  have hWp5 : ∀ {w : Fn}, Work.FTS.EllipticEst.SmoothOpen w → Work.FTS.StrongEps.EpsMem α w →
      Work.FTS.StrongEps.EpsSq α w ≤ R →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w) ≤ BS := by
    intro w hsw hmw hrw
    have hfac : 0 ≤ CH * (CH / ε) ^ 10 := by positivity
    have hle : Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w)
        ≤ CH * (CH / ε) ^ 10 * R :=
      le_trans (hCH α hα ε hε hε1 5 (by norm_num) w hsw hmw)
        (mul_le_mul_of_nonneg_left hrw hfac)
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hle) ?_
    rw [hBSdef]; linarith
  set Q : ℝ := Real.sqrt CD with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  set M₀ : ℝ := 1 + 2 * BS with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; linarith
  have hM₀0 : 0 ≤ M₀ := le_trans zero_le_one hM₀1
  refine ⟨max 1 (Cpt * K₁ * M₀ ^ 2 * Q), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hsu hsv hmu hru hmv hrv hclu hclv hxnu hxnv z θ hz hθ0 hθ1
  set d : Fn := fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
      - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ with hddef
  obtain ⟨hΔsm, hΔmem4, hΔxn⟩ := hK₁
    (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
    (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclu hclv hxnu hxnv
  have hDd : Work.Spaces.HkSq α 5 d
      ≤ CD * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    rw [hddef]; exact hCD hsu hsv hmu hmv hclu hclv
  have hQbd : Work.Spaces.HkNorm α 5 d
      ≤ Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    rw [Work.Spaces.HkNorm, hQdef, ← Real.sqrt_mul hCDpos.le]
    exact Real.sqrt_le_sqrt hDd
  have hWu := hWp5 hsu hmu hru
  have hWv := hWp5 hsv hmv hrv
  have h1 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have h2 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have hM2 : (1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2 ≤ M₀ ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by rw [hM₀def]; linarith) 2
  have hZ : 0 ≤ Work.Spaces.HkNorm α 5 d := Work.Spaces.HkNorm_nonneg α 5 d
  have hKM : 0 ≤ K₁ * M₀ ^ 2 := mul_nonneg hK₁pos.le (pow_nonneg hM₀0 2)
  have hpt := hCpt hΔsm hΔmem4 hz hθ0 hθ1
  have hfinal : |profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
          - profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ|
      ≤ (Cpt * K₁ * M₀ ^ 2 * Q)
        * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    calc _ ≤ Cpt * Work.Spaces.HkNorm α 4 (fun z θ =>
            profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
              - profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ) := hpt
      _ ≤ Cpt * (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d) := by
          refine mul_le_mul_of_nonneg_left (le_trans hΔxn ?_) hCpt0
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hK₁pos.le) hZ
      _ ≤ Cpt * (K₁ * M₀ ^ 2
            * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQbd hKM) hCpt0
      _ = _ := by ring
  exact le_trans hfinal (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

end Work.FTS.StrongEps.EpsLocalPStar

namespace Work.FTS.EpsEngine.SORuling

open Work.FTS.StrongEps

set_option autoImplicit false

/-- (A) mollified form ⟹ `SmoothOpen`. -/
theorem smoothOpen_of_mollForm {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    {h₀ Ψ u : Fn} {c : ℝ} (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hΨ : Continuous (logPull Ψ))
    (hu : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      u z θ = h₀ z θ + Jeps ρ ε Ψ z θ - c * bump z θ) :
    Work.FTS.EllipticEst.SmoothOpen u := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have hJ : ContDiffOn ℝ n (Function.uncurry (Jeps ρ ε Ψ)) Work.FTS.EllipticEst.Q0 :=
    Jeps_contDiffOn ρ hρ hε hΨ.locallyIntegrable n
  have h0n := h0.forall n
  have hb := Work.FTS.StrongEps.smoothOpen_bump.forall n
  have hsum : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Function.uncurry h₀ p + Function.uncurry (Jeps ρ ε Ψ) p - c * Function.uncurry bump p)
      Work.FTS.EllipticEst.Q0 :=
    (h0n.add hJ).sub (contDiffOn_const.mul hb)
  refine hsum.congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
  simp only [Function.uncurry_apply_pair]
  exact hu z θ hp'.1 ⟨hp'.2.1, hp'.2.2⟩

/-- (B) Fubini: the time integral commutes with a compactly supported continuous kernel. -/
theorem conv_intervalIntegral_swap {k : ℝ × ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {H : ℝ → ℝ × ℝ → ℝ}
    (hH : Continuous (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2)) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : ℝ × ℝ) :
    IntervalIntegrable (fun s => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H s) x)
        volume 0 τ ∧
      (∫ s in (0 : ℝ)..τ, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H s) x)
        = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (fun y => ∫ s in (0 : ℝ)..τ, H s y)) x := by
  set f : ℝ → ℝ × ℝ → ℝ := fun s t => k t * H s (x - t) with hfdef
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hfdef]
    exact (hk.comp continuous_snd).mul
      (hH.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd)))
  set K := tsupport k with hK
  have hKc : IsCompact K := hks
  have hon : IntegrableOn (Function.uncurry f) (Icc 0 τ ×ˢ K) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hfc.continuousOn.integrableOn_compact (isCompact_Icc.prod hKc)
  have hon2 : IntegrableOn (Function.uncurry f) (Ioc 0 τ ×ˢ (univ : Set (ℝ × ℝ)))
      (volume.prod volume) := by
    refine (hon.mono_set (prod_mono Ioc_subset_Icc_self le_rfl)).of_forall_sdiff_eq_zero
      (measurableSet_Ioc.prod MeasurableSet.univ) ?_
    rintro ⟨s, t⟩ ⟨⟨hs, -⟩, hnot⟩
    have ht : t ∉ K := fun ht => hnot ⟨hs, ht⟩
    simp only [Function.uncurry_apply_pair, hfdef, image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioc 0 τ)).prod volume) := by
    have := hon2
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at this
    exact this
  have hswap := MeasureTheory.integral_integral_swap hint
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ]
    have h1 := hint.integral_prod_left
    refine h1.congr (Eventually.of_forall fun s => ?_)
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hfdef,
      Function.uncurry_apply_pair]
  · rw [intervalIntegral.integral_of_le hτ]
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    simp only [hfdef] at hswap
    rw [hswap]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [intervalIntegral.integral_of_le hτ, integral_const_mul]

/-- (D) joint continuity, in log coordinates, of a family that is continuous on `Q0` slice-wise and
uniformly Lipschitz in the time parameter (time clamped to `[0,τ]`). -/
theorem continuous_logPull_family {G : ℝ → Fn} {τ : ℝ} (hτ : 0 ≤ τ) {K : NNReal}
    (hcont : ∀ s ∈ Icc 0 τ, ContinuousOn (Function.uncurry (G s)) Work.FTS.EllipticEst.Q0)
    (hlip : ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |G s z θ - G t z θ| ≤ K * |s - t|) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (G (projIcc 0 τ hτ q.1 : ℝ)) q.2) := by
  refine continuous_prod_of_continuous_lipschitzWith _ K (fun a => ?_) (fun x => ?_)
  · have hc := hcont _ (projIcc 0 τ hτ a).2
    exact ContinuousOn.comp_continuous hc continuous_logMap_quad.1 continuous_logMap_quad.2
  · refine LipschitzWith.of_dist_le_mul (fun s t => ?_)
    have hmem := continuous_logMap_quad.2 x
    have h1 := hlip _ (projIcc 0 τ hτ s).2 _ (projIcc 0 τ hτ t).2 _ _ hmem.1 ⟨hmem.2.1, hmem.2.2⟩
    have h2 : dist (projIcc 0 τ hτ s) (projIcc 0 τ hτ t) ≤ 1 * dist s t :=
      (LipschitzWith.projIcc hτ).dist_le_mul s t
    rw [Real.dist_eq]
    rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq, one_mul] at h2
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 K.2)

/-- (E) **one Picard step preserves `SmoothOpen`** (generic form): if the integrand has the mollified
form `F (slice W s) = J_ε (G s) − c s · bump` on `Q0` with `G` jointly continuous (log coordinates,
time clamped), and the integrand is interval-integrable in `s` at every point (the `cont(n)` component
of the proved `iter_cont_meas`), then `h₀ + ∫₀^τ F (slice W s) ds` is `SmoothOpen`. -/
theorem smoothOpen_picard_slice {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    {h₀ : Fn} {F : Fn → Fn} {W : Fam} {G : ℝ → Fn} {c : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hF : ∀ s ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      F (slice W s) z θ = Jeps ρ ε (G s) z θ - c s * bump z θ)
    (hG : Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (G (projIcc 0 τ hτ q.1 : ℝ)) q.2))
    (hFint : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun s => F (slice W s) z θ) volume 0 τ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice W s) z θ) := by
  set Gp : ℝ → Fn := fun s => G (projIcc 0 τ hτ s : ℝ) with hGp
  set Ψ : Fn := fun z θ => ∫ s in (0 : ℝ)..τ, Gp s z θ with hΨdef
  have hlogΨ : logPull Ψ = fun x => ∫ s in (0 : ℝ)..τ, logPull (Gp s) x := rfl
  have hΨ : Continuous (logPull Ψ) := by
    rw [hlogΨ]
    have hc : Continuous (Function.uncurry (fun (x : ℝ × ℝ) (s : ℝ) => logPull (Gp s) x)) :=
      hG.comp continuous_swap
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 τ
  refine smoothOpen_of_mollForm hρ hε (c := ∫ s in (0 : ℝ)..τ, c s) h0 hΨ ?_
  intro z θ hz hθ
  have hB := conv_intervalIntegral_swap (k := Jker ρ ε) (contDiff_Jker ρ hρ ε 0).continuous
    (hasCompactSupport_Jker ρ hρ hε) (H := fun s => logPull (Gp s)) hG hτ (sOf z, zetaOf θ)
  have hJs : (fun s => Jeps ρ ε (Gp s) z θ) = fun s =>
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull (Gp s)) (sOf z, zetaOf θ) :=
    funext fun s => Jeps_eq_conv ρ ε _ hz hθ
  have hJΨ : Jeps ρ ε Ψ z θ = (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => ∫ s in (0 : ℝ)..τ, logPull (Gp s) y)) (sOf z, zetaOf θ) := by
    rw [Jeps_eq_conv ρ ε Ψ hz hθ, hlogΨ]
  have hA : IntervalIntegrable (fun s => Jeps ρ ε (Gp s) z θ) volume 0 τ := by
    rw [hJs]; exact hB.1
  have hAint : ∫ s in (0 : ℝ)..τ, Jeps ρ ε (Gp s) z θ = Jeps ρ ε Ψ z θ := by
    rw [hJs, hB.2, hJΨ]
  have hFeq : ∀ s ∈ Set.uIcc (0 : ℝ) τ,
      F (slice W s) z θ = Jeps ρ ε (Gp s) z θ - c s * bump z θ := by
    intro s hs
    rw [Set.uIcc_of_le hτ] at hs
    have hp : (projIcc 0 τ hτ s : ℝ) = s := by rw [projIcc_of_mem hτ hs]
    simp only [hGp, hp]
    exact hF s hs z θ hz hθ
  have hcb : ∫ s in (0 : ℝ)..τ, c s * bump z θ
      = ∫ s in (0 : ℝ)..τ, (Jeps ρ ε (Gp s) z θ - F (slice W s) z θ) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    show c s * bump z θ = Jeps ρ ε (Gp s) z θ - F (slice W s) z θ
    rw [hFeq s hs]; ring
  have hsub := intervalIntegral.integral_sub hA (hFint z θ hz hθ)
  have hmc : ∫ s in (0 : ℝ)..τ, c s * bump z θ = (∫ s in (0 : ℝ)..τ, c s) * bump z θ :=
    intervalIntegral.integral_mul_const _ _
  show h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice W s) z θ
    = h₀ z θ + Jeps ρ ε Ψ z θ - (∫ s in (0 : ℝ)..τ, c s) * bump z θ
  linarith [hcb, hsub, hmc, hAint]

/-- (F) **`hkeepIter`'s `SmoothOpen` clause, concretely** (the `XBall` class): if the `n`-th Picard
iterate stays in `XBall` on `[0,δ]`, is `EpsSq`-Lipschitz in time (the Minkowski bound of the engine,
`EpsSq (w_s − w_t) ≤ L (s−t)²`), and its integrand is interval-integrable at each point (the `cont(n)`
component of `iter_cont_meas`), then every slice of the `(n+1)`-st iterate is `SmoothOpen`. -/
theorem smoothOpen_iter_succ_XBall {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (n : ℕ)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hP : ∀ s ∈ Icc 0 δ, XBall α ρ ε R C₀
      (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))
    (hEq : ∀ s ∈ Icc 0 δ, ∀ t ∈ Icc 0 δ, EpsSq α (fun z θ =>
      slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s z θ
        - slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hFint : ∀ τ ∈ Icc 0 δ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun s => Feps α ρ ε Φs E
        (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s) z θ) volume 0 τ)
    {τ : ℝ} (hτ : τ ∈ Icc 0 δ) :
    Work.FTS.EllipticEst.SmoothOpen
      (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) := by
  set w : ℝ → Fn := fun s =>
    slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s with hw
  set G : ℝ → Fn := fun s =>
    Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε (w s))) with hGdef
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.EpsLocalPStar.profRHS_pre_sub_pt_le_Sq
    (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hEll hstar hml hR
  have hsub : ∀ s ∈ Icc 0 τ, s ∈ Icc 0 δ := fun s hs => ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hcont : ∀ s ∈ Icc 0 τ, ContinuousOn (Function.uncurry (G s)) Work.FTS.EllipticEst.Q0 :=
    fun s hs => ((smoothOpen_profRHS_of_classC hα hEll hstar
      (hP s (hsub s hs)).classC).forall 0).continuousOn
  set K : NNReal := ⟨C * Real.sqrt Lw, mul_nonneg hCpos.le (Real.sqrt_nonneg _)⟩ with hK
  have hlip : ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |G s z θ - G t z θ| ≤ K * |s - t| := by
    intro s hs t ht z θ hz hθ
    have hPs := hP s (hsub s hs)
    have hPt := hP t (hsub t ht)
    have h1 := hC hPs.smoothOpen hPt.smoothOpen hPs.mem hPs.sq_le hPt.mem hPt.sq_le
      hPs.classC hPt.classC hPs.ball hPt.ball z θ hz hθ.1 hθ.2
    have h2 : Real.sqrt (EpsSq α (fun z θ => w s z θ - w t z θ)) ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq s (hsub s hs) t (hsub t ht))
    calc |G s z θ - G t z θ| ≤ C * Real.sqrt (EpsSq α (fun z θ => w s z θ - w t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (K : ℝ) * |s - t| := by
          show C * (Real.sqrt Lw * |s - t|) = (C * Real.sqrt Lw) * |s - t|; ring
  have hG := continuous_logPull_family hτ.1 hcont hlip
  have hF : ∀ s ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Feps α ρ ε Φs E (w s) z θ = Jeps ρ ε (G s) z θ
        - (Work.Construction.L12 (Jeps ρ ε (G s)) 0 / pzNorm) * bump z θ := by
    intro s _ z θ _ _
    show Pz (Jeps ρ ε (G s)) z θ = _
    rw [Pz_apply]
  exact smoothOpen_picard_slice (W := Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n)
    hρ hε hτ.1 h0 hF hG (hFint τ hτ)

end Work.FTS.EpsEngine.SORuling


