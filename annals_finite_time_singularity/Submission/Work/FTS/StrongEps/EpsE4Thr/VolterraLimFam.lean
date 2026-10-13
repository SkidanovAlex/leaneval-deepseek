import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimExists
import Submission.Work.FTS.EpsEngine.VolterraV4Main
import Submission.Work.FTS.EpsEngine.H4FepsLim
import Submission.Work.FTS.EpsEngine.LimSmoothOpenEngine
import Submission.Work.FTS.EpsEngine.BallLimFam
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq

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
