import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimExists
import Submission.Work.FTS.EpsEngine.aesm_weighted_prod_restricted
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le

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
