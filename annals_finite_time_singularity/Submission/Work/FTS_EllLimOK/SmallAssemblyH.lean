import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Metrizable.Uniformity
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH
import Submission.Work.FTS_EllLimOK.Closed
import Submission.Work.FTS_EllLimOK.ClosedCompact3H_of_bounds_fatou
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS_EllLimOK.PkgJets.pinBase
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Slice
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_RegExport.Vz7Eslot
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.limEpsSq_lipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter iter_zero limFam epsL2 DomM)
open Work.FTS.EpsEngine (Feps XBall iter_bounds_v4 tendsto_slice_iter_limFam
  EpsMem_and_EpsSq_le_of_ae_tendsto_mem EpsMem_congr_pt iter_cont_meas_prefix
  aesm_weighted_uIoc_of_restrict continuousOn_Feps_of_XBall EpsSq_iter_sub_sq_le)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `limEpsSq_lipschitz` — the time-Lipschitz clause (in the weighted `L²`-metric) of the limit
family of the Volterra–Picard iteration of the projected `ε`-scheme

Given the `X`-ball hypotheses of the local step (the iterate ball clause `hiter`, the gates
`hbd`/`hlip`/`hpt` of `Feps` on the ball, and the datum's ball clauses), every pair of slices of
the limit family `limFam (Feps α ρ ε Φs E) h₀` at fake times `σ, τ ∈ [0,δ]` has a difference
which is a member of the weighted space, with size bounded by `L (σ − τ)²`.

The proof is the Fatou step `EpsMem_and_EpsSq_le_of_ae_tendsto_mem` applied to the sequence

  `A m := slice (iter … m) σ − slice (iter … m) τ  ⟶  slice (limFam) σ − slice (limFam) τ`,

whose members are in the weighted space with the *same* size bound: the bound
`EpsSq α (A m) ≤ L (σ − τ)²` is `EpsEngine.EpsSq_iter_sub_sq_le` (Minkowski for the parametric
integral), while the membership `EpsMem α (A m)` is the private lemma `iter_pair_mem_aux` below
(the level-`m` iterate is `h₀ + ∫₀^t F(level m−1)`, so a difference of two of its slices is a
difference of two parametric interval integrals; the two copies of `h₀` cancel).  The a.e.
convergence of `A m` is `tendsto_slice_iter_limFam`, whose geometric increment bound is the fifth
component of `iter_bounds_v4`.
-/

private abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- **Membership of the difference of two slices of the same Picard iterate** (at two fake times).
The `(k+1)`-st iterate is `h₀ + ∫₀^t F(level k)`; the two copies of `h₀` cancel, so the difference
is the difference of two parametric interval integrals, each of which is in the weighted space by
`EpsMem_and_EpsSq_intervalIntegral_le` (whose a.e.-strong-measurability input is the weighted
Carathéodory measurability of the level-`k` curve, from `iter_cont_meas_prefix`). -/
private theorem iter_pair_mem_aux {α Cpt L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (k : ℕ)
    (hδ : 0 < δ) (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (hP : ∀ n : ℕ, n ≤ k → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2) Qd)
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ, q ∉ Qd → F u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ))) :
    ∀ σ ∈ Set.Icc 0 δ, ∀ τ ∈ Set.Icc 0 δ,
      EpsMem α (fun z θ => slice (iter F h₀ (k + 1)) σ z θ
        - slice (iter F h₀ (k + 1)) τ z θ) := by
  obtain ⟨_hcontAll, haesmAll⟩ :=
    iter_cont_meas_prefix (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := F) (h₀ := h₀) (P := P) k hδ hL hCpt hP hcontP hzeroP hbd hpt
  intro σ hσ τ hτ
  -- each of the two interval integrals is a member of the weighted space and `AK2`
  have key : ∀ t ∈ Set.Icc 0 δ,
      EpsMem α (fun z θ => ∫ s in (0 : ℝ)..t, F (slice (iter F h₀ k) s) z θ)
      ∧ Work.FTS.StrongEps.EpsLocalPStar.AK2 α
          (fun z θ => ∫ s in (0 : ℝ)..t, F (slice (iter F h₀ k) s) z θ) := by
    intro t ht
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ k) p.1) p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
        ((volume.restrict (Set.uIoc 0 t)).prod DomM) :=
      aesm_weighted_uIoc_of_restrict (α := α) (δ := δ) (τ := t)
        (Φ := fun s => F (slice (iter F h₀ k) s)) ht (haesmAll k le_rfl)
    have hGbd : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
        epsL2 α (F (slice (iter F h₀ k) s)) ≤ ENNReal.ofReal L := by
      rw [MeasureTheory.ae_restrict_iff' (measurableSet_uIoc (a := (0 : ℝ)) (b := t))]
      refine Filter.Eventually.of_forall (fun s hs => ?_)
      have hsδ : s ∈ Set.Icc 0 δ := by
        rw [Set.uIoc_of_le ht.1] at hs
        exact ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
      exact Work.FTS.StrongEps.EpsLocalPStar.epsL2_le_ofReal_of_mem
        (hbd _ (hP k le_rfl s hsδ)).1 (hbd _ (hP k le_rfl s hsδ)).2
    exact ⟨(Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le
        (α := α) (τ := t) (B := L) ht.1 hL hmeas hGbd).1,
      Work.FTS.StrongEps.EpsLocalPStar.AK2_intervalIntegral (α := α) ht.1 hmeas⟩
  have hpair := Work.FTS.StrongEps.EpsLocalPStar.EpsMem_sub2 (key σ hσ).2 (key τ hτ).2
    (key σ hσ).1 (key τ hτ).1
  refine EpsMem_congr_pt (fun z θ => ?_) hpair
  have h1 : slice (iter F h₀ (k + 1)) σ z θ
      = h₀ z θ + ∫ s in (0 : ℝ)..σ, F (slice (iter F h₀ k) s) z θ := by
    simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
  have h2 : slice (iter F h₀ (k + 1)) τ z θ
      = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ k) s) z θ := by
    simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
  simp only [h1, h2]
  ring

/-- **The iterate ball clause and the pointwise convergence of the Picard curves**, produced from
the scheme's hypotheses: the numerical set-up of the contraction, the five a-priori bounds
`iter_bounds_v4`, and `tendsto_slice_iter_limFam`. -/
private theorem iter_ball_and_conv {α C₀ Ce Cs Cpt L δ R : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hC₀ : 0 ≤ C₀) (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hL : 0 < L) (hδ : 0 < δ) (hδL : δ * Real.sqrt L < 1) (hR : 0 < R)
    (hbd : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        ≤ L * EpsSq α (fun z θ => u z θ - v z θ))
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)))
    (hsmo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hcl : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)))
    (hball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
      ≤ C₀ * α ^ 2)
    (hdatmem : EpsMem α h₀) (hdatsq : EpsSq α h₀ ≤ R)
    (hiter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀)
        (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ)) :
    (∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
        XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ n) τ)) ∧
      (∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Filter.Tendsto (fun N : ℕ => slice (iter (Feps α ρ ε Φs E) h₀ N) τ z θ)
          Filter.atTop (nhds (slice (limFam (Feps α ρ ε Φs E) h₀) τ z θ))) := by
  -- ## the numerical set-up of the contraction
  set q : ℝ := δ ^ 2 * L with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq]
    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hp : (δ * Real.sqrt L) ^ 2 = δ ^ 2 * L := by rw [mul_pow, Real.sq_sqrt hL.le]
    have h1 : (δ * Real.sqrt L) ^ 2 < 1 := by nlinarith [hδL, mul_nonneg hδ.le hsL]
    rwa [hp] at h1
  set r : ℝ := Real.sqrt q with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Real.sqrt_mul hq0, ← hr, ih, pow_succ']
  have hr1 : r < 1 := by
    have h2 : r ^ 2 = q := by rw [hr]; exact Real.sq_sqrt hq0
    nlinarith [hr0, h2, hq1]
  -- ## the datum in the ball, and the two gates of `Feps` on the ball
  have hP₀ : XBall α ρ ε R (2 * C₀) h₀ :=
    ⟨hsmo, hdatmem, hdatsq, hcl,
      le_trans hball (by nlinarith [hC₀, sq_nonneg α])⟩
  have hcontF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2) Qd :=
    fun u hu => (continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).1
  have hzeroF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u → ∀ q : ℝ × ℝ, q ∉ Qd →
      Feps α ρ ε Φs E u q.1 q.2 = 0 :=
    fun u hu => (continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).2
  have hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀)
        (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
          Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s) z θ) := by
    intro n τ hτ
    have h : slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ
        = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
          Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s) z θ := by
      funext z θ
      simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
    rw [← h]
    exact hiter n τ hτ
  -- ## the five a-priori bounds of the engine
  obtain ⟨hP, _hB0, _hBK, _hwsq, hwpt⟩ :=
    iter_bounds_v4 (α := α) (F := Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => XBall α ρ ε R (2 * C₀) u)
      (Cpt := Cpt) (L := L) (δ := δ) (q := q) (r := r)
      hδ hL hδL hq hr hq0 hq1 hr0 hrpow hCpt hP₀ hbd hlip hpt hcontF hzeroF hkeepIter
  refine ⟨hP, fun τ hτ z θ hz hθ0 hθ1 => ?_⟩
  exact tendsto_slice_iter_limFam (F := Feps α ρ ε Φs E) (h₀ := h₀) (δ := δ)
    (Cpt := Cpt) (r := r) hCpt hr0 hr1
    (fun n τ hτ hn z θ hz hθ0 hθ1 => hwpt n τ hτ hn z θ hz hθ0 hθ1) τ hτ z θ hz hθ0 hθ1

theorem limEpsSq_lipschitz {α C₀ Ce Cs M' Cpt L δ R : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hC₀ : 0 < C₀) (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hM' : 0 ≤ M')
    (hL : 0 < L) (hδ : 0 < δ) (hδL : δ * Real.sqrt L < 1) (hR : 0 < R)
    (hbd : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
        Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hsmo : Work.FTS.EllipticEst.SmoothOpen h₀) (hmem : Work.Spaces.HkMem α 6 h₀)
    (hM6 : Work.Spaces.HkSq α 6 h₀ ≤ M')
    (hcl : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)))
    (hball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
      ≤ C₀ * α ^ 2)
    (hdatmem : Work.FTS.StrongEps.EpsMem α h₀) (hdatsq : Work.FTS.StrongEps.EpsSq α h₀ ≤ R)
    (hiter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ)) :
    ∃ L' : ℝ, 0 < L' ∧ ∀ σ ∈ Set.Icc 0 δ, ∀ τ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice
            (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice
            (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice
            (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice
            (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ)
        ≤ L' * (σ - τ) ^ 2 := by
  classical
  obtain ⟨hP, hconv⟩ :=
    iter_ball_and_conv (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Cpt := Cpt) (L := L)
      (δ := δ) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
      hC₀.le hα hρ hε hEll hstar hL hδ hδL hR hbd hlip hCpt hpt hsmo hcl hball hdatmem hdatsq
      hiter
  have hcontF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2) Qd :=
    fun u hu => (continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).1
  have hzeroF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u → ∀ q : ℝ × ℝ, q ∉ Qd →
      Feps α ρ ε Φs E u q.1 q.2 = 0 :=
    fun u hu => (continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).2
  refine ⟨L, hL, ?_⟩
  intro σ hσ τ hτ
  have hBnn : 0 ≤ L * (σ - τ) ^ 2 := mul_nonneg hL.le (sq_nonneg _)
  refine EpsMem_and_EpsSq_le_of_ae_tendsto_mem (α := α) (B := L * (σ - τ) ^ 2) hBnn
    (A := fun m : ℕ => fun z θ => slice (iter (Feps α ρ ε Φs E) h₀ m) σ z θ
      - slice (iter (Feps α ρ ε Φs E) h₀ m) τ z θ)
    (Alim := fun z θ => slice (limFam (Feps α ρ ε Φs E) h₀) σ z θ
      - slice (limFam (Feps α ρ ε Φs E) h₀) τ z θ) ?_ ?_ ?_
  · -- membership of every member of the sequence
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      refine EpsMem_congr_pt (fun z θ => ?_) (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_zero2 α)
      simp only [iter_zero, Work.FTS.Galerkin.slice_apply, sub_self]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      exact iter_pair_mem_aux (α := α) (Cpt := Cpt) (L := L) (δ := δ)
        (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R (2 * C₀) u) k
        hδ hL.le hCpt (fun n _ => hP n) hcontF hzeroF hbd hpt σ hσ τ hτ
  · -- the uniform size bound of the sequence
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hz : (fun z θ => slice (iter (Feps α ρ ε Φs E) h₀ 0) σ z θ
          - slice (iter (Feps α ρ ε Φs E) h₀ 0) τ z θ) = fun _ _ => (0 : ℝ) := by
        funext z θ
        simp only [iter_zero, Work.FTS.Galerkin.slice_apply, sub_self]
      rw [hz, Work.FTS.StrongEps.EpsSq_zero]
      exact hBnn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      exact EpsSq_iter_sub_sq_le (α := α) (Cpt := Cpt) (L := L) (δ := δ)
        (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R (2 * C₀) u) (k + 1)
        hδ hL.le hCpt (fun n _ => hP n) hcontF hzeroF hbd hpt σ hσ τ hτ
  · -- a.e. convergence on the domain
    filter_upwards [Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    exact ((hconv σ hσ p.1 p.2 hz hθ0 hθ1).sub (hconv τ hτ p.1 p.2 hz hθ0 hθ1))

end Work.FTS.StrongEps.EpsE4Thr.LeafD2
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.VolterraLimFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (Feps XBall)
open Work.FTS.StrongEps (EpsMem EpsSq)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option maxHeartbeats 1600000

/-!
# `Submission/Work/FTS/StrongEps/EpsE4Thr/VolterraLimFam.lean`

The **Volterra identity of the limit family** of the projected `ε`-scheme:

  `limFam (Feps α ρ ε Φs E) h₀ z θ τ = h₀ z θ + ∫₀^τ Feps α ρ ε Φs E (slice (limFam …) s) z θ ds`

The task here is to prove the *integral* form (the derivative form is
`Work.FTS.EpsEngine.exists_volterra_v4`'s conclusion, whose hypotheses are exactly the ones at
hand: the limit slices are in the `X`-ball by `EpsE4Thr.XBallLimExists`, and the iterate clause
`hiter` is the engine's `hkeepIter`).  The integral form follows from the derivative form by the
fundamental theorem of calculus, since the integrand is bounded (a geometric telescope of the
Picard increments via the pointwise gate `hpt`) and is a pointwise limit of the continuous
functions `s ↦ Feps … (slice (iter … N) s) z θ` (the Picard convergence `EpsSq → 0` together
with `hpt`).  The three auxiliary lemmas below (`abs_F_iter_le`,
`integrableOn_of_tendsto_bounded`, `tendsto_F_iter_limFam`) carry that analytic content and are
proved in place.

Namespace `Work.FTS.StrongEps.EpsE4Thr.VLF` holds the helpers.
-/

namespace Work.FTS.StrongEps.EpsE4Thr.VLF

/-- **A uniform bound on the `F`-images of the Picard iterates**, from the pointwise gate `hpt`
and the geometric size bounds on the increments: the increments telescope, so
`|F (slice (iter N) τ) z θ| ≤ |F h₀ z θ| + Cpt ∑_{k<N} r^{k+1} ≤ |F h₀ z θ| + Cpt (1-r)⁻¹`. -/
theorem abs_F_iter_le {α : ℝ} {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {P : Work.FTS.Galerkin.Fn → Prop}
    {Cpt δ q r : ℝ} (hδ : 0 ≤ δ) (hCpt : 0 ≤ Cpt)
    (hP₀ : P h₀)
    (hkeep : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ))
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α
        (fun z θ => u z θ - v z θ)))
    (hwsq : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ n τ) ≤ q ^ (n + 1))
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n) :
    ∀ N : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ) z θ|
        ≤ |F h₀ z θ| + Cpt * (1 - r)⁻¹ := by
  have hPall : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) τ) := by
    intro n
    induction n with
    | zero =>
      intro τ _
      have h0 : Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ 0) τ = h₀ := rfl
      rw [h0]; exact hP₀
    | succ m _ => intro τ hτ; exact hkeep m τ hτ
  have hinv : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith)
  -- the per-increment bound
  have hincr : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ) z θ
        - F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) τ) z θ|
        ≤ Cpt * r ^ (n + 1) := by
    intro n τ hτ z θ hz hθ0 hθ1
    have h := hpt (slice (iter F h₀ (n + 1)) τ) (slice (iter F h₀ n) τ)
      (hPall (n + 1) τ hτ) (hPall n τ hτ) z θ hz hθ0 hθ1
    refine le_trans h ?_
    have hw : (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - slice (iter F h₀ n) τ z θ)
        = Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ n τ := rfl
    rw [hw, ← hrpow (n + 1)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hwsq n τ hτ)) hCpt
  -- the partial-sum telescoping bound
  have hmain : ∀ N : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ) z θ|
        ≤ |F h₀ z θ| + Cpt * (∑ k ∈ Finset.range N, r ^ (k + 1)) := by
    intro N
    induction N with
    | zero =>
      intro τ _ z θ _ _ _
      have h0 : Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ 0) τ = h₀ := rfl
      rw [h0, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    | succ m ih =>
      intro τ hτ z θ hz hθ0 hθ1
      have h1 := ih τ hτ z θ hz hθ0 hθ1
      have h2 := hincr m τ hτ z θ hz hθ0 hθ1
      rw [Finset.sum_range_succ]
      have habs : |F (slice (iter F h₀ (m + 1)) τ) z θ|
          ≤ |F (slice (iter F h₀ m) τ) z θ|
            + |F (slice (iter F h₀ (m + 1)) τ) z θ - F (slice (iter F h₀ m) τ) z θ| := by
        have hkey := abs_add_le (F (slice (iter F h₀ m) τ) z θ)
          (F (slice (iter F h₀ (m + 1)) τ) z θ - F (slice (iter F h₀ m) τ) z θ)
        have heq : F (slice (iter F h₀ m) τ) z θ
            + (F (slice (iter F h₀ (m + 1)) τ) z θ - F (slice (iter F h₀ m) τ) z θ)
            = F (slice (iter F h₀ (m + 1)) τ) z θ := by ring
        rw [heq] at hkey
        exact hkey
      calc |F (slice (iter F h₀ (m + 1)) τ) z θ|
          ≤ |F (slice (iter F h₀ m) τ) z θ|
            + |F (slice (iter F h₀ (m + 1)) τ) z θ - F (slice (iter F h₀ m) τ) z θ| := habs
        _ ≤ (|F h₀ z θ| + Cpt * (∑ k ∈ Finset.range m, r ^ (k + 1))) + Cpt * r ^ (m + 1) := by
            linarith [h1, h2]
        _ = |F h₀ z θ| + Cpt * (∑ k ∈ Finset.range m, r ^ (k + 1) + r ^ (m + 1)) := by ring
  -- the geometric bound on the partial sums
  intro N τ hτ z θ hz hθ0 hθ1
  have h1 := hmain N τ hτ z θ hz hθ0 hθ1
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hgeo : (∑ k ∈ Finset.range N, r ^ (k + 1)) ≤ (1 - r)⁻¹ := by
    have hsumm : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_norm_lt_one hnorm
    have hpart : (∑ k ∈ Finset.range N, r ^ k) ≤ (1 - r)⁻¹ := by
      rw [← tsum_geometric_of_norm_lt_one hnorm]
      exact hsumm.sum_le_tsum _ (fun k _ => pow_nonneg hr0 k)
    have hfac : (∑ k ∈ Finset.range N, r ^ (k + 1)) = r * (∑ k ∈ Finset.range N, r ^ k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
    rw [hfac]
    exact (mul_le_mul_of_nonneg_left hpart hr0).trans (mul_le_of_le_one_left hinv hr1.le)
  have h2 : Cpt * (∑ k ∈ Finset.range N, r ^ (k + 1)) ≤ Cpt * (1 - r)⁻¹ :=
    mul_le_mul_of_nonneg_left hgeo hCpt
  linarith

/-- **A pointwise limit of continuous functions with a uniform bound is integrable** on a
sub-interval of the domain: `g` is a.e. strongly measurable (pointwise limit of measurable
functions) and bounded by `B` on `Icc 0 τ`, whose measure is finite. -/
theorem integrableOn_of_tendsto_bounded {u : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {δ τ B : ℝ}
    (hτ : τ ∈ Set.Icc 0 δ) (hB : 0 ≤ B)
    (hcont : ∀ n : ℕ, ContinuousOn (u n) (Set.Icc 0 δ))
    (htend : ∀ s ∈ Set.Icc 0 δ, Filter.Tendsto (fun n => u n s) Filter.atTop (nhds (g s)))
    (hbdd : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 δ, |u n s| ≤ B) :
    MeasureTheory.IntegrableOn g (Set.Icc 0 τ) := by
  have hsub : Set.Icc 0 τ ⊆ Set.Icc 0 δ := Set.Icc_subset_Icc_right hτ.2
  have hμ : (volume : Measure ℝ) (Set.Icc 0 τ) < (⊤ : ENNReal) := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine MeasureTheory.IntegrableOn.of_bound hμ ?_ B ?_
  · -- `g` is a pointwise limit of the measurable `u n`
    refine aestronglyMeasurable_of_tendsto_ae (ι := ℕ) (f := u) (g := g) Filter.atTop
      (fun n => ?_) ?_
    · exact ((hcont n).mono hsub).aestronglyMeasurable measurableSet_Icc
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_
      exact htend s (hsub hs)
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_
    rw [Real.norm_eq_abs]
    refine le_of_tendsto ((htend s (hsub hs)).abs) (Filter.eventually_atTop.2 ⟨0, ?_⟩)
    intro n _
    exact hbdd n s (hsub hs)

/-- **The `F`-images along the Picard iterates converge to the `F`-image of the limit family**:
the pointwise gate `hpt` together with the geometric tail bound `EpsSq (iter N − limFam) ≤ q ^ N`
(which is `EpsEngine.EpsSq_iter_limFam_le`) and `√(q^N) = r^N → 0`. -/
theorem tendsto_F_iter_limFam {α : ℝ} {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {P : Work.FTS.Galerkin.Fn → Prop}
    {Cpt δ q r : ℝ} (hCpt : 0 ≤ Cpt) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n)
    (hP : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) τ))
    (hlimP : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ))
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α
        (fun z θ => u z θ - v z θ)))
    (hconv : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ)
        Filter.atTop (nhds (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)))
    (hBK : ∀ M K : ℕ, 1 ≤ K → K ≤ M → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ M) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ K) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ M) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ K) τ z θ)
        ≤ q ^ (K + 1)) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => F (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ) z θ)
        Filter.atTop (nhds (F (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ) z θ)) := by
  intro τ hτ z θ hz hθ0 hθ1
  have htail : ∀ N : ℕ, 1 ≤ N → Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)
        ≤ q ^ N :=
    fun N hN => (Work.FTS.EpsEngine.EpsSq_iter_limFam_le (α := α) (q := q) (δ := δ)
      hq0 hq1 hconv hBK N hN τ hτ).2
  have hstep : ∀ N : ℕ, 1 ≤ N →
      |F (slice (iter F h₀ N) τ) z θ - F (slice (limFam F h₀) τ) z θ| ≤ Cpt * r ^ N := by
    intro N hN
    have h := hpt (slice (iter F h₀ N) τ) (slice (limFam F h₀) τ) (hP N τ hτ) (hlimP τ hτ)
      z θ hz hθ0 hθ1
    refine le_trans h ?_
    rw [← hrpow N]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (htail N hN)) hCpt
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      |F (slice (iter F h₀ N) τ) z θ - F (slice (limFam F h₀) τ) z θ| ≤ Cpt * r ^ N :=
    Filter.eventually_atTop.2 ⟨1, fun N hN => hstep N hN⟩
  have hlim : Filter.Tendsto (fun N : ℕ =>
      |F (slice (iter F h₀ N) τ) z θ - F (slice (limFam F h₀) τ) z θ|)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun N => abs_nonneg _)) hev
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul Cpt)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hlim)

end Work.FTS.StrongEps.EpsE4Thr.VLF

namespace Work.FTS.StrongEps.EpsE4Thr

theorem VolterraLimFam {α C₀ Ce Cs M' Cpt L δ R : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hC₀ : 0 < C₀) (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hM : 0 ≤ M') (hL : 0 < L) (hδ : 0 < δ) (hδL : δ * Real.sqrt L < 1) (hR : 0 < R)
    (hbd : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
        Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hsmo : Work.FTS.EllipticEst.SmoothOpen h₀) (hmem : Work.Spaces.HkMem α 6 h₀)
    (hM6 : Work.Spaces.HkSq α 6 h₀ ≤ M')
    (hcl : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)))
    (hball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
      ≤ C₀ * α ^ 2)
    (hdatmem : Work.FTS.StrongEps.EpsMem α h₀) (hdatsq : Work.FTS.StrongEps.EpsSq α h₀ ≤ R)
    (hiter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ)) :
    ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Work.FTS.EpsEngine.Feps α ρ ε Φs E
              (Work.FTS.Galerkin.slice
                (Work.FTS.StrongEps.EpsLocalPStar.limFam
                  (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) s) z θ := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## 0. numerical set-up
  set q : ℝ := δ ^ 2 * L with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq]
    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hp : (δ * Real.sqrt L) ^ 2 = δ ^ 2 * L := by rw [mul_pow, Real.sq_sqrt hL.le]
    have h1 : (δ * Real.sqrt L) ^ 2 < 1 := by nlinarith [hδL, mul_nonneg hδ.le hsL]
    rwa [hp] at h1
  set r : ℝ := Real.sqrt q with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Real.sqrt_mul hq0, ← hr, ih, pow_succ']
  have hr1 : r < 1 := by
    have h2 : r ^ 2 = q := by rw [hr]; exact Real.sq_sqrt hq0
    nlinarith [hr0, h2, hq1]
  -- ## 1. the datum is in the ball, and the iterate clause
  have hP₀ : XBall α ρ ε R (2 * C₀) h₀ :=
    ⟨hsmo, hdatmem, hdatsq, hcl, le_trans hball (by nlinarith [hC₀.le, sq_nonneg α])⟩
  have hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀)
        (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
          Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s) z θ) := by
    intro n τ hτ
    have h : slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ
        = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s) z θ := by
      funext z θ
      simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
    rw [← h]
    exact hiter n τ hτ
  have hkeepP : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀)
        (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) := by
    intro n τ hτ
    rw [show slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ
        = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s) z θ from by
      funext z θ
      simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]]
    exact hkeepIter n τ hτ
  have hP : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ n) τ) := by
    intro n
    induction n with
    | zero =>
      intro τ _
      have h0 : slice (iter (Feps α ρ ε Φs E) h₀ 0) τ = h₀ := rfl
      rw [h0]; exact hP₀
    | succ m ih =>
      intro τ hτ
      exact hkeepP m τ hτ
  -- ## 2. the engine's per-profile data
  have hcontF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).1
  have hzeroF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u → ∀ p : ℝ × ℝ,
      p ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E u p.1 p.2 = 0 :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).2
  -- ## 3. the a-priori bounds of the engine
  obtain ⟨-, hB0, hBK, hwsq, hwpt⟩ :=
    Work.FTS.EpsEngine.iter_bounds_v4 (α := α) (F := Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => XBall α ρ ε R (2 * C₀) u) (Cpt := Cpt) (L := L) (δ := δ) (q := q) (r := r)
      hδ hL hδL hq hr hq0 hq1 hr0 hrpow hCpt hP₀ hbd hlip hpt hcontF hzeroF hkeepIter
  obtain ⟨hcontIter, hmeasIter⟩ :=
    Work.FTS.EpsEngine.iter_cont_meas (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R (2 * C₀) u)
      hδ hL.le hCpt hP hcontF hzeroF hbd hpt
  have hconv : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => slice (iter (Feps α ρ ε Φs E) h₀ N) τ z θ) Filter.atTop
        (nhds (slice (limFam (Feps α ρ ε Φs E) h₀) τ z θ)) :=
    Work.FTS.EpsEngine.tendsto_slice_iter_limFam (F := Feps α ρ ε Φs E) (h₀ := h₀) (δ := δ)
      (Cpt := Cpt) (r := r) hCpt hr0 hr1
      (fun n τ hτ hn z θ hz hθ0 hθ1 => hwpt n τ hτ hn z θ hz hθ0 hθ1)
  -- ## 4. the limit slices are in the ball
  obtain ⟨hlimP, -⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.XBallLimExists (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (M' := M') (Cpt := Cpt) (L := L) (δ := δ) (R := R) (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (h₀ := h₀) hC₀ hα hρ hε hε1 hEll hstar hml hM hL hδ hδL hR hbd hlip hCpt hpt
      hsmo hmem hM6 hcl hball hdatmem hdatsq hiter
  -- ## 5. the Volterra derivative of the limit family
  obtain ⟨-, hder⟩ :=
    Work.FTS.EpsEngine.exists_volterra_v4 (α := α) (F := Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => XBall α ρ ε R (2 * C₀) u) (Cpt := Cpt) (L := L) (δ := δ)
      hδ hL hδL hCpt hP₀ hbd hlip hpt hcontF hzeroF hkeepIter hlimP
  -- ## 6. pointwise convergence of the `F`-images, and a uniform bound
  intro z θ τ hz hθ hτ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hFpt : ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      Filter.Tendsto (fun N : ℕ => Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ N) s) z θ)
        Filter.atTop
        (nhds (Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) s) z θ)) :=
    fun s hs => VLF.tendsto_F_iter_limFam (α := α)
      (Cpt := Cpt) (δ := δ) (q := q) (r := r) hCpt hq0 hq1 hr0 hr1 hrpow hP hlimP hpt hconv hBK
      s hs z θ hz hθ0 hθ1
  have hbdd : ∀ N : ℕ, ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      |Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ N) s) z θ|
        ≤ |Feps α ρ ε Φs E h₀ z θ| + Cpt * (1 - r)⁻¹ :=
    fun N s hs => VLF.abs_F_iter_le (α := α)
      (Cpt := Cpt) (δ := δ) (q := q) (r := r) hδ.le hCpt hP₀ hkeepP hpt hwsq hr0 hr1 hrpow
      N s hs z θ hz hθ0 hθ1
  have hφbdd : ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      |Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) s) z θ|
        ≤ |Feps α ρ ε Φs E h₀ z θ| + Cpt * (1 - r)⁻¹ := by
    intro s hs
    refine le_of_tendsto (hFpt s hs).abs (Filter.eventually_atTop.2 ⟨0, fun N _ => hbdd N s hs⟩)
  -- ## 7. integrability of the integrand on `[0,τ]`
  have hBnn : 0 ≤ |Feps α ρ ε Φs E h₀ z θ| + Cpt * (1 - r)⁻¹ := by
    have h1 : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith)
    have h2 : 0 ≤ Cpt * (1 - r)⁻¹ := mul_nonneg hCpt h1
    linarith [abs_nonneg (Feps α ρ ε Φs E h₀ z θ)]
  have hIntOn : MeasureTheory.IntegrableOn
      (fun s : ℝ => Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) s) z θ)
      (Set.Icc 0 τ) :=
    VLF.integrableOn_of_tendsto_bounded
      (u := fun N s => Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ N) s) z θ)
      (g := fun s => Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) s) z θ)
      (δ := δ) (τ := τ) (B := |Feps α ρ ε Φs E h₀ z θ| + Cpt * (1 - r)⁻¹)
      hτ hBnn (fun N => hcontIter N z θ hz hθ0 hθ1) hFpt hbdd
  have hInt : IntervalIntegrable
      (fun s : ℝ => Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) s) z θ) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact hIntOn
  -- ## 8. the fundamental theorem of calculus
  have hcontG : ContinuousOn (fun s : ℝ => limFam (Feps α ρ ε Φs E) h₀ z θ s) (Set.Icc 0 τ) := by
    intro x hx
    have hxδ : x ∈ Set.Icc 0 δ := ⟨hx.1, le_trans hx.2 hτ.2⟩
    exact ((hder z θ x hz hθ hxδ).continuousWithinAt).mono (Set.Icc_subset_Icc_right hτ.2)
  have hderivG : ∀ x ∈ Set.Ioo 0 τ,
      HasDerivWithinAt (fun s : ℝ => limFam (Feps α ρ ε Φs E) h₀ z θ s)
        (Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) x) z θ) (Set.Ioi x) x := by
    intro x hx
    have hxδ : x ∈ Set.Icc 0 δ := ⟨hx.1.le, le_trans hx.2.le hτ.2⟩
    have hmem : Set.Icc 0 δ ∈ 𝓝 x := Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hτ.2)
    exact ((hder z θ x hz hθ hxδ).hasDerivAt hmem).hasDerivWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ.1 hcontG hderivG hInt
  rw [Work.FTS.StrongEps.EpsLocalPStar.limFam_zero (Feps α ρ ε Φs E) h₀ z θ] at hftc
  linarith

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.BoxC2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK/ProducerH/BoxAux/BoxC2` — the closed-box `C²`-regularity of `E g`

The first clause of `RulingELF.PkgBoxH`: `ContDiffOn ℝ 2 (uncurry (E g)) (cbox a₀ b₀)`.

## Route

The function `E g` is `C^∞` on the *open* quadrant (`SmoothOpen`, a field of `EllClassOk`) and
the two boundary lines `θ = 0`, `θ = π/2` carry the prescribed values `E g z 0 = E g z (π/2) = 0`
(`IsBslSol`), which by `BoxAux.Trace` are also the one-sided limits.  The whole content of the
clause is therefore the *one-sided differentiability* of the slices at the two endpoints.

The assembly is the staircase of `BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials`, applied
with the *constant* family `H n = E g` three times (to `E g`, to `∂_z (E g)`, and to the
θ-slope), followed by `BoxDataH.contDiffOn_two_of_fderivWithin_data`.  The two slopes are
`derivWithin`-versions of the partials on the closed intervals, so that their boundary values are
the one-sided derivatives:

* `thSlope W z θ = ∂_θ^{[0,π/2]} W z ·(θ)`, `zSlope a b W z θ = ∂_z^{[a,b]} W · θ(z)`.

The one-sided derivatives at the endpoints exist because the interior derivatives have limits
there: `∂_θ (E g)` is bounded (`second_theta_deriv_DzIter_le_Xn6`, level `0`) and
`∂_θ∂_z (E g)` is bounded (level `1`), so `tendsto_of_deriv_bounded` gives their one-sided limits,
and `hasDerivWithinAt_of_tendsto_deriv` converts those into the within-derivatives.

Everything here is `sorry`-free.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


/-- **The `z`-slope on the closed interval `[a,b]`**. -/
noncomputable def zSlope (a b : ℝ) (W : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  derivWithin (fun z' => W z' θ) (Set.Icc a b) z




/-! ## A uniform `θ`-modulus and the vertical lines give continuity on the box -/

/-- **Continuity on the vertical lines of the box from a uniform `θ`-modulus.** -/
theorem continuousOn_line_of_thetaModulus {F : ℝ → ℝ → ℝ} {C β : ℝ} {a₀ b₀ : ℝ}
    (hβ : 0 < β)
    (hmod : ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      ∀ θ' ∈ Set.Icc 0 (Real.pi / 2), |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β)
    (hint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousOn (fun z => F z θ) (Set.Icc a₀ b₀)) :
    ∀ θ ∈ Set.Icc 0 (Real.pi / 2), ContinuousOn (fun z => F z θ) (Set.Icc a₀ b₀) := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    by_cases hC : C ≤ 0
    · have hconst : ∀ z ∈ Set.Icc a₀ b₀, F z 0 = F z (Real.pi / 4) := by
        intro z hz
        have h1 := hmod z hz 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩ (Real.pi / 4)
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have h2 : C * |(0 : ℝ) - Real.pi / 4| ^ β ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
        have h3 : |F z 0 - F z (Real.pi / 4)| = 0 :=
          le_antisymm (le_trans h1 h2) (abs_nonneg _)
        exact sub_eq_zero.mp (abs_eq_zero.mp h3)
      exact (hint (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).congr
        (fun z hz => hconst z hz)
    · have hCpos : 0 < C := not_le.mp hC
      refine fun z hz => ?_
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hbase : 0 < ε / (8 * C) := by positivity
      set θ₀ : ℝ := min (Real.pi / 4) (min 1 ((ε / (8 * C)) ^ (1 / β))) with hθ₀def
      have hθ₀pos : 0 < θ₀ :=
        lt_min (by linarith [Real.pi_pos]) (lt_min one_pos (Real.rpow_pos_of_pos hbase _))
      have hθ₀lt : θ₀ < Real.pi / 2 :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos])
      have hθ₀le : θ₀ ≤ (ε / (8 * C)) ^ (1 / β) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hpoweq : ((ε / (8 * C)) ^ (1 / β)) ^ β = ε / (8 * C) := by
        rw [← Real.rpow_mul hbase.le]
        have h1 : 1 / β * β = 1 := by field_simp
        rw [h1, Real.rpow_one]
      have hpow : θ₀ ^ β ≤ ε / (8 * C) :=
        calc θ₀ ^ β ≤ ((ε / (8 * C)) ^ (1 / β)) ^ β :=
              Real.rpow_le_rpow (le_of_lt hθ₀pos) hθ₀le hβ.le
          _ = ε / (8 * C) := hpoweq
      have hsmall : C * θ₀ ^ β ≤ ε / 8 := by
        have h1 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
        have h2 : C * (ε / (8 * C)) = ε / 8 := by field_simp
        linarith [h1, h2]
      obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp
        ((hint θ₀ ⟨hθ₀pos, hθ₀lt⟩).continuousWithinAt hz) (ε / 2) (by linarith)
      refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
      have hz0 : |(0 : ℝ) - θ₀| = θ₀ := by rw [abs_sub_comm, sub_zero, abs_of_pos hθ₀pos]
      have h1 : |F z' 0 - F z' θ₀| ≤ C * θ₀ ^ β := by
        have h := hmod z' hz' 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩ θ₀
          ⟨le_of_lt hθ₀pos, le_of_lt hθ₀lt⟩
        rwa [hz0] at h
      have h2 : |F z' θ₀ - F z θ₀| < ε / 2 := by
        have h := hδ hz' hdist
        rwa [Real.dist_eq] at h
      have h3 : |F z θ₀ - F z 0| ≤ C * θ₀ ^ β := by
        have h := hmod z hz 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩ θ₀
          ⟨le_of_lt hθ₀pos, le_of_lt hθ₀lt⟩
        rw [hz0, abs_sub_comm] at h
        exact h
      rw [Real.dist_eq]
      calc |F z' 0 - F z 0|
          ≤ |F z' 0 - F z' θ₀| + |F z' θ₀ - F z θ₀| + |F z θ₀ - F z 0| := by
            rw [show F z' 0 - F z 0
              = (F z' 0 - F z' θ₀) + (F z' θ₀ - F z θ₀) + (F z θ₀ - F z 0) from by ring]
            exact abs_add_three _ _ _
        _ < ε := by linarith [h1, h2, h3, hsmall]
  · rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      by_cases hC : C ≤ 0
      · have hconst : ∀ z ∈ Set.Icc a₀ b₀, F z (Real.pi / 2) = F z (Real.pi / 4) := by
          intro z hz
          have h1 := hmod z hz (Real.pi / 2)
            ⟨by linarith [Real.pi_pos], le_rfl⟩ (Real.pi / 4)
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          have h2 : C * |Real.pi / 2 - Real.pi / 4| ^ β ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
          have h3 : |F z (Real.pi / 2) - F z (Real.pi / 4)| = 0 :=
            le_antisymm (le_trans h1 h2) (abs_nonneg _)
          exact sub_eq_zero.mp (abs_eq_zero.mp h3)
        exact (hint (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).congr
          (fun z hz => hconst z hz)
      · have hCpos : 0 < C := not_le.mp hC
        refine fun z hz => ?_
        rw [Metric.continuousWithinAt_iff]
        intro ε hε
        have hbase : 0 < ε / (8 * C) := by positivity
        set δ₀ : ℝ := min (Real.pi / 4) (min 1 ((ε / (8 * C)) ^ (1 / β))) with hδ₀def
        set θ₀ : ℝ := Real.pi / 2 - δ₀ with hθ₀def
        have hδ₀pos : 0 < δ₀ :=
          lt_min (by linarith [Real.pi_pos]) (lt_min one_pos (Real.rpow_pos_of_pos hbase _))
        have hδ₀le : δ₀ ≤ (ε / (8 * C)) ^ (1 / β) :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        have hpoweq : ((ε / (8 * C)) ^ (1 / β)) ^ β = ε / (8 * C) := by
          rw [← Real.rpow_mul hbase.le]
          have h1 : 1 / β * β = 1 := by field_simp
          rw [h1, Real.rpow_one]
        have hpow : δ₀ ^ β ≤ ε / (8 * C) :=
          calc δ₀ ^ β ≤ ((ε / (8 * C)) ^ (1 / β)) ^ β :=
                Real.rpow_le_rpow (le_of_lt hδ₀pos) hδ₀le hβ.le
            _ = ε / (8 * C) := hpoweq
        have hsmall : C * δ₀ ^ β ≤ ε / 8 := by
          have h1 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
          have h2 : C * (ε / (8 * C)) = ε / 8 := by field_simp
          linarith [h1, h2]
        have hθ₀mem : θ₀ ∈ Set.Ioo 0 (Real.pi / 2) := by
          have h1 : δ₀ ≤ Real.pi / 4 := min_le_left _ _
          constructor <;> simp only [hθ₀def] <;> linarith [Real.pi_pos]
        obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp
          ((hint θ₀ hθ₀mem).continuousWithinAt hz) (ε / 2) (by linarith)
        refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
        have h1 : |F z' (Real.pi / 2) - F z' θ₀| ≤ C * δ₀ ^ β := by
          have h := hmod z' hz' (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩ θ₀
            ⟨le_of_lt hθ₀mem.1, le_of_lt hθ₀mem.2⟩
          have h2 : |Real.pi / 2 - θ₀| = δ₀ := by simp only [hθ₀def]; ring_nf; rw [abs_of_pos hδ₀pos]
          rwa [h2] at h
        have h2 : |F z' θ₀ - F z θ₀| < ε / 2 := by
          have h := hδ hz' hdist
          rwa [Real.dist_eq] at h
        have h3 : |F z θ₀ - F z (Real.pi / 2)| ≤ C * δ₀ ^ β := by
          have h := hmod z hz (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩ θ₀
            ⟨le_of_lt hθ₀mem.1, le_of_lt hθ₀mem.2⟩
          have h2 : |Real.pi / 2 - θ₀| = δ₀ := by simp only [hθ₀def]; ring_nf; rw [abs_of_pos hδ₀pos]
          rw [h2, abs_sub_comm] at h
          exact h
        rw [Real.dist_eq]
        calc |F z' (Real.pi / 2) - F z (Real.pi / 2)|
            ≤ |F z' (Real.pi / 2) - F z' θ₀| + |F z' θ₀ - F z θ₀|
              + |F z θ₀ - F z (Real.pi / 2)| := by
              rw [show F z' (Real.pi / 2) - F z (Real.pi / 2)
                = (F z' (Real.pi / 2) - F z' θ₀) + (F z' θ₀ - F z θ₀)
                  + (F z θ₀ - F z (Real.pi / 2)) from by ring]
              exact abs_add_three _ _ _
          _ < ε := by linarith [h1, h2, h3, hsmall]
    · exact hint θ ⟨h0, hp⟩

/-- **A uniform `θ`-modulus, plus continuity on the interior vertical lines, gives continuity on
the closed box.** -/
theorem continuousOn_of_thetaModulus {F : ℝ → ℝ → ℝ} {C β : ℝ} {a₀ b₀ : ℝ}
    (hβ : 0 < β)
    (hmod : ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      ∀ θ' ∈ Set.Icc 0 (Real.pi / 2), |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β)
    (hint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousOn (fun z => F z θ) (Set.Icc a₀ b₀)) :
    ContinuousOn (Function.uncurry F) (cbox a₀ b₀) := by
  have hline := continuousOn_line_of_thetaModulus (a₀ := a₀) (b₀ := b₀) hβ hmod hint
  intro p hp
  obtain ⟨z, θ⟩ := p
  rw [mem_cbox] at hp
  obtain ⟨hz, hθ⟩ := hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousWithinAt_iff.mp
    ((hline θ hθ).continuousWithinAt hz) (ε / 2) (by linarith)
  have hmodδ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ θ' ∈ Set.Icc 0 (Real.pi / 2),
      |θ' - θ| < δ₁ → C * |θ' - θ| ^ β < ε / 2 := by
    by_cases hC : C ≤ 0
    · refine ⟨1, one_pos, fun θ' _ _ => ?_⟩
      have : C * |θ' - θ| ^ β ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
      linarith
    · have hCpos : 0 < C := not_le.mp hC
      have hbase : 0 < ε / (4 * C) := by positivity
      refine ⟨min 1 ((ε / (4 * C)) ^ (1 / β)), lt_min one_pos (Real.rpow_pos_of_pos hbase _),
        fun θ' _ hlt => ?_⟩
      have hle : |θ' - θ| ≤ (ε / (4 * C)) ^ (1 / β) :=
        le_of_lt (lt_of_lt_of_le hlt (min_le_right _ _))
      have h1 : |θ' - θ| ^ β ≤ (ε / (4 * C)) := by
        calc |θ' - θ| ^ β ≤ ((ε / (4 * C)) ^ (1 / β)) ^ β :=
              Real.rpow_le_rpow (abs_nonneg _) hle hβ.le
          _ = ε / (4 * C) := by
              rw [← Real.rpow_mul hbase.le]
              have h2 : 1 / β * β = 1 := by field_simp
              rw [h2, Real.rpow_one]
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
      have h4 : C * (ε / (4 * C)) = ε / 4 := by field_simp
      linarith [h3, h4]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hmodδ
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun q hq hdist => ?_⟩
  obtain ⟨z', θ'⟩ := q
  rw [mem_cbox] at hq
  obtain ⟨hz', hθ'⟩ := hq
  have hd : dist (z', θ') (z, θ) = max |z' - z| |θ' - θ| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have hzclose : |z' - z| < δ₂ := by
    rw [hd] at hdist
    exact lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdist (min_le_right _ _))
  have hthclose : |θ' - θ| < δ₁ := by
    rw [hd] at hdist
    exact lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdist (min_le_left _ _))
  have h1 : |F z' θ' - F z' θ| < ε / 2 := by
    have h := hmod z' hz' θ hθ θ' hθ'
    have h2 := hδ₁ θ' hθ' hthclose
    have habs : |θ - θ'| ^ β = |θ' - θ| ^ β := by rw [abs_sub_comm]
    rw [habs] at h
    rw [abs_sub_comm (F z' θ) (F z' θ')] at h
    exact lt_of_le_of_lt h h2
  have h2 : |F z' θ - F z θ| < ε / 2 := by
    have h := hδ₂ hz' hzclose
    rwa [Real.dist_eq] at h
  rw [Real.dist_eq, Function.uncurry_apply_pair, Function.uncurry_apply_pair]
  calc |F z' θ' - F z θ| ≤ |F z' θ' - F z' θ| + |F z' θ - F z θ| := by
        rw [show F z' θ' - F z θ = (F z' θ' - F z' θ) + (F z' θ - F z θ) from by ring]
        exact abs_add_le _ _
    _ < ε := by linarith

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SmallAssemblyH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The order-`3` reduction over `HasPkgH`**: obligations 1 and 2 give the order-`3` closure of
every operator carrying `HasPkgH` (same subsequence argument as `Closed3.ClosedE3_of_compact3_uniq3`;
the uniqueness statement `ClosedUniq3G` is package-free). -/
theorem ClosedE3H_of_compact3_uniq3 {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn}
    (hE : HasPkgH α Ce E) (hcomp : ClosedCompact3H α Ce) (huniq : ClosedUniq3G α) :
    ClosedE3G α E := by
  intro fn f hL
  obtain ⟨Ψ, hΨlim⟩ := hcomp E hE fn f hL
  refine ⟨Ψ, hΨlim.1, ?_⟩
  intro j i hji z θ hz
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hL' : LimSeq4 α (fun n => fn (ns (ψ n))) f := limSeq4_comp hL hnsψ.tendsto_atTop
  obtain ⟨Ψ₂, hfat₂, σ, hσ, hJ₂⟩ := hcomp E hE _ f hL'
  have h₂ : IsJetLimit3G α E fn f Ψ₂ :=
    ⟨hfat₂, ⟨fun n => ns (ψ (σ n)), hnsψ.tendsto_atTop.comp hσ, by
      simpa only [Function.comp_apply] using hJ₂⟩⟩
  have hjet := huniq E fn f hL Ψ Ψ₂ hΨlim h₂ j i hji z θ hz
  refine ⟨fun n => ψ (σ n), ?_⟩
  rw [hjet]
  simpa only [Function.comp_apply] using hJ₂ j i hji z θ hz





end Work.FTS_EllLimOK
end
end
