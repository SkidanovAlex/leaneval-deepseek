import Mathlib
import Submission.Work.Diff.STE.Lead.coordBound
import Submission.Work.Diff.STE.Lead.mat_jet_bound
import Submission.Work.Diff.STE.Lead.MatJetDefs
import Submission.Work.Diff.STE.Lead.matA_jets
import Submission.Work.Diff.STE.Lead.psi_le_const
import Submission.Work.Diff.STE.Lead.background_jet_bound
import Submission.Work.Diff.STE.Lead.chartMatJet_sharp
import Submission.Work.Diff.STE.Lead.pPhiJetOf_tendsto
import Submission.Work.Diff.STE.Lead.pPhi_entry_bound_v2
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.BNorm_J_le
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.densGood_noT2
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp
import Submission.Work.Diff.STE.D.psi.abs_coord_factor_le
import Submission.Work.Diff.STE.D.psi.JetAffine
import Submission.Work.Diff.STE.commutator_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The DeTurck operator is bounded by the composite norm (Lead layer, STE)

`Work.Diff.STE.Lead.deTurck_bound`: for a section `h : Bil` whose composite norm `D.BNorm k h` is
bounded by `B` and which is pinched between `λ g₀` and `K g₀`, the pointwise value of the DeTurck
operator `P(h) = -2 Ric(h) + L_{W(h)}h` with background `g₀` obeys

  `|P(h)(x)(u,v)| ≤ C (1+B)^2 √(g₀(u,u)) √(g₀(v,v))`

with `C` independent of `B` and `h`; moreover the value is continuous in the section in the
`BNorm k`-topology.

## Route

* `Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp` writes `P(h)(x)(u,v)` as the contraction of the
  jet-level DeTurck operator `pPhiJet` with the coordinates of `u`, `v` in the chart at `x₀ i`.
* The jet components of the chart matrix of `h` in the chart at `x₀ i` are bounded by
  `C √(BNorm k h)/c³` on the part of the `σ i`-ball where the localised weight `ψ i` is `≥ c > 0`
  (`Work.Diff.STE.Lead.chartMatJet_sharp`, fed here with the sharp bound `mat_jet_bound_sqrt` for
  the chart matrix in the orthonormal frame `D.mat` — proved below from the affine bound
  `Work.Diff.STE.Lead.mat_jet_bound` by division by the localised weight).
* At a point `x` one picks the chart `i` for which `ζ i x` is maximal, so that
  `ψ i (coord i x) = ζ i x ≥ 1/√(card ι₀)`; all constants are then uniform in `x`.
* `pPhi` is bounded in terms of the jet norms by `Work.Diff.STE.Lead.pPhi_entry_bound_v2`, and its
  continuity on the nondegenerate locus is `Work.Diff.STE.deTurck.contDiffOn_pPhi`.
-/

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The sharp jet bound for the localised components

`Work.Diff.STE.Lead.pdList_le_sqrt_CSq_fin` bounds the iterated partial derivatives of order `≤ 2`
of a smooth `1`-periodic function by `C √(CSq k (fourierCoeff f))`; on the fundamental cube the
periodisation `D.Rper i h a b` agrees with the complexified component `D.R i h a b`, whose
coefficient norm is a single term of the sum defining `D.BNorm`. -/

theorem R_jet_bound_sharp (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hk : Module.finrank ℝ E + 4 < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E)))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ D.σ i → l.length ≤ 2 →
      |Work.Diff.STE.pdRList l (D.R i h a b) z| ≤ C * Real.sqrt (D.BNorm k h) := by
  obtain ⟨C_R, hC_R_nn, hC_R⟩ :=
    Work.Diff.STE.Lead.pdList_le_sqrt_CSq_fin k (Module.finrank ℝ E) hk
  refine ⟨C_R, hC_R_nn, fun h hsm i a b l z hz hl => ?_⟩
  have hsmR : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm i a b
  obtain ⟨hRper_sm, hRper_per⟩ :=
    Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h a b hsmR
  -- `z` lies strictly inside the centred unit cube
  have hσ8 : D.σ i ≤ 1 / 8 := by have := D.hσ2 i; linarith
  have hzcube : ∀ j : Fin (Module.finrank ℝ E), |z j| < 1 / 2 := by
    intro j
    have h1 : |z j| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j
    linarith
  -- the periodisation agrees with the complexified component near `z`
  have hev : (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b y : ℝ) : ℂ))
      =ᶠ[𝓝 z] D.Rper i h a b := by
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨Metric.ball z (1 / 16), Metric.ball_mem_nhds z (by norm_num), fun y hy => ?_⟩
    have hyc : ∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      intro j
      have h1 : |y j - z j| ≤ ‖y - z‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y - z) j
      have h2 : ‖y - z‖ < 1 / 16 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have h4 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      have h6 : |z j| ≤ D.σ i :=
        le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j) hz
      have h6' : -(D.σ i) ≤ z j := by linarith [neg_abs_le (z j), h6]
      have h6'' : z j ≤ D.σ i := by linarith [le_abs_self (z j), h6]
      rw [Set.mem_Ioo]
      constructor <;> linarith [h4.1, h4.2, h6', h6'', hσ8]
    exact (D.Rper_eq_R i h a b hyc).symm
  have hcongr : Work.Diff.STE.pdList l (fun y => ((D.R i h a b y : ℝ) : ℂ)) z
      = Work.Diff.STE.pdList l (D.Rper i h a b) z :=
    pdList_congr_of_eventuallyEq hev l
  have hle : CSq k (fourierCoeff (D.Rper i h a b)) ≤ D.BNorm k h := by
    simp only [Work.Diff.STE.B3Data.BNorm]
    exact sum3_single_le (fun (i' : ι₀) (a' b' : Fin (Module.finrank ℝ E)) =>
      CSq k (fourierCoeff (D.Rper i' h a' b'))) (fun i' a' b' => CSq_nonneg k _) i a b
  calc |Work.Diff.STE.pdRList l (D.R i h a b) z|
      = ‖(((Work.Diff.STE.pdRList l (D.R i h a b) z : ℝ)) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖Work.Diff.STE.pdList l (fun y => ((D.R i h a b y : ℝ) : ℂ)) z‖ := by
        rw [cm_pdList_ofReal_smooth l (D.R i h a b) hsmR]
    _ = ‖Work.Diff.STE.pdList l (D.Rper i h a b) z‖ := by rw [hcongr]
    _ ≤ C_R * Real.sqrt (CSq k (fourierCoeff (D.Rper i h a b))) :=
        hC_R _ hRper_sm hRper_per l hl z
    _ ≤ C_R * Real.sqrt (D.BNorm k h) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hC_R_nn

/-! ## 2. The sharp jet bound for the chart matrix in the orthonormal frame

`D.R i h a b = matA D i · D.mat i h a b` with `matA D i = ψ i · √(dens i)`.  Near a point where
`ψ i` is `≥ c > 0` the cut-off `χ i` equals `1` (so `D.mat i h a b = D.R i h a b / matA D i`), and
the quotient rule `Work.Diff.STE.Lead.pdRList_div_le`, together with the uniform bounds for `matA`
and its first two derivatives (`Work.Diff.STE.Lead.matA_jets`) and the a priori bound
`ψ i ≤ Mψ` (`Work.Diff.STE.Lead.psi_le_const`), turns the sharp bound for `D.R` into one for
`D.mat`. -/

/-- Near a point where the localised weight is positive, the chart matrix of a section is its
localised component divided by the weight `matA D i = ψ i · √(dens i)`. -/
theorem mat_eventuallyEq_of_psi_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ D.σ i)
    {c : ℝ} (hc : 0 < c) (hcl : c ≤ D.psi i z) :
    D.mat i h a b =ᶠ[𝓝 z] fun y => D.R i h a b y / matA (I := I) (M := M) D i y := by
  have hz2 : ‖z‖ ≤ 2 * D.σ i := by linarith [D.hσ i]
  have hpsi : 0 < D.psi i z := lt_of_lt_of_le hc hcl
  have hζ : D.ζ i (D.pt i z) ≠ 0 := by
    intro h0
    rw [Work.Diff.STE.B3Data.psi, h0, mul_zero] at hpsi
    exact lt_irrefl 0 hpsi
  have hlt : ‖z‖ < D.σ i := by
    have h1 := (D.hζsupp i (D.pt i z) hζ).2
    rwa [D.coord_pt i hz2] at h1
  have hevχ : ∀ᶠ y in 𝓝 z, D.χ i y = 1 := by
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i),
        Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using hlt),
        fun y hy => ?_⟩
    refine D.hχ1 i y ?_
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy)
  have hevψ : ∀ᶠ y in 𝓝 z, 0 < D.psi i y :=
    ((D.psi_contDiff i).continuous.continuousAt).preimage_mem_nhds
      (IsOpen.mem_nhds isOpen_Ioi hpsi)
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
    D.htarget i z hz2
  have hdg := (Work.Diff.STE.B3.densGood (I := I) (M := M) D i) z hzt
  have hevd : ∀ᶠ y in 𝓝 z, 0 < D.dens i y :=
    hdg.2.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi hdg.1)
  filter_upwards [hevχ, hevψ, hevd] with y hyχ hyψ hyd
  have hA : matA (I := I) (M := M) D i y ≠ 0 := by
    simp only [matA]
    exact mul_ne_zero (ne_of_gt hyψ) (Real.sqrt_pos.mpr hyd).ne'
  rw [R_eq_matA_mul_mat D i h a b y]
  exact (mul_div_cancel_left₀ (D.mat i h a b y) hA).symm

/-- **The sharp jet bound for the chart matrix in the `g₀`-orthonormal frame.** -/
theorem mat_jet_bound_sqrt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hk : Module.finrank ℝ E + 4 < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E)))
      (z : Fin (Module.finrank ℝ E) → ℝ) (c : ℝ),
      ‖z‖ ≤ D.σ i → 0 < c → c ≤ D.psi i z → l.length ≤ 2 →
      |Work.Diff.STE.pdRList l (D.mat i h a b) z|
        ≤ C * Real.sqrt (D.BNorm k h) / c ^ 3 := by
  obtain ⟨C_R, hC_R_nn, hC_R⟩ := R_jet_bound_sharp (I := I) (M := M) D k hk
  obtain ⟨Kj, hKj_nn, hKj⟩ := Work.Diff.STE.Lead.matA_jets (I := I) (M := M) D
  obtain ⟨Mψ, hMψ_nn, hMψ⟩ := Work.Diff.STE.Lead.psi_le_const (I := I) (M := M) D
  obtain ⟨d₀, hd₀pos, hd₀⟩ :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  obtain ⟨Cq, hCq_nn, hCq⟩ := Work.Diff.STE.Lead.pdRList_div_le (d := Module.finrank ℝ E)
  set n : ℕ := Module.finrank ℝ E with hn
  set Cδ : ℝ := Mψ ^ 2 / Real.sqrt d₀ + (2 * Kj * Mψ) / d₀ + Kj ^ 2 / (d₀ * Real.sqrt d₀)
    with hCδ
  refine ⟨Cq * (1 + (n : ℝ) + (n : ℝ) ^ 2) * C_R * Cδ + 1, by positivity,
    fun h hsm i a b l z c hz hc hcl hl => ?_⟩
  have hz2 : ‖z‖ ≤ 2 * D.σ i := by linarith [D.hσ i]
  -- the jet bounds for the weight `matA D i`
  have hKj1 := (hKj i z hz).2.1
  have hKj2 := (hKj i z hz).2.2
  -- the weight is bounded below by `c √d₀`
  have hdens := hd₀ i z hz2
  have hsqr_dens : Real.sqrt d₀ ≤ Real.sqrt (D.dens i z) := Real.sqrt_le_sqrt hdens
  have hA_lb : c * Real.sqrt d₀ ≤ |matA (I := I) (M := M) D i z| := by
    have h0 : 0 ≤ Real.sqrt (D.dens i z) := Real.sqrt_nonneg _
    have hmatA_eq : matA (I := I) (M := M) D i z
        = D.psi i z * Real.sqrt (D.dens i z) := rfl
    rw [hmatA_eq, abs_of_nonneg (mul_nonneg (le_trans hc.le hcl) h0)]
    exact mul_le_mul hcl hsqr_dens (Real.sqrt_nonneg _) (le_trans hc.le hcl)
  -- the eventual equality `mat = R / matA`
  have hev := mat_eventuallyEq_of_psi_le (I := I) (M := M) D h i a b z hz hc hcl
  have hcongr := pdRList_congr_of_eventuallyEq hev l
  -- smoothness hypotheses of the quotient rule
  have hsmR : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm i a b
  have hsmA : ContDiff ℝ (⊤ : ℕ∞) (matA (I := I) (M := M) D i) :=
    Work.Diff.STE.Lead.matA_contDiff (I := I) (M := M) D i
  have hdiv := hCq (matA (I := I) (M := M) D i) (D.R i h a b) z (c * Real.sqrt d₀) Kj Kj
    (by positivity) hA_lb hKj_nn hKj_nn hKj1 hKj2 ((hsmA.contDiffAt).of_le (by simp))
    ((hsmR.contDiffAt).of_le (by simp)) l hl
  rw [hcongr]
  -- the sum of the jets of `R`
  have hR_z : |D.R i h a b z| ≤ C_R * Real.sqrt (D.BNorm k h) :=
    hC_R h hsm i a b [] z hz (by simp)
  have hR_1 : ∀ p : Fin (Module.finrank ℝ E), |Work.Diff.STE.pdR p (D.R i h a b) z|
      ≤ C_R * Real.sqrt (D.BNorm k h) := fun p => hC_R h hsm i a b [p] z hz (by simp)
  have hR_2 : ∀ p q : Fin (Module.finrank ℝ E),
      |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (D.R i h a b)) z|
      ≤ C_R * Real.sqrt (D.BNorm k h) := fun p q => hC_R h hsm i a b [q, p] z hz (by simp)
  have hRsum : (|D.R i h a b z| + ∑ p : Fin n, |Work.Diff.STE.pdR p (D.R i h a b) z|
        + ∑ p : Fin n, ∑ q : Fin n,
            |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (D.R i h a b)) z|)
      ≤ (1 + (n : ℝ) + (n : ℝ) ^ 2) * (C_R * Real.sqrt (D.BNorm k h)) := by
    have h2 : (∑ p : Fin n, |Work.Diff.STE.pdR p (D.R i h a b) z|)
        ≤ (n : ℝ) * (C_R * Real.sqrt (D.BNorm k h)) := by
      calc ∑ p : Fin n, |Work.Diff.STE.pdR p (D.R i h a b) z|
          ≤ ∑ _p : Fin n, (C_R * Real.sqrt (D.BNorm k h)) :=
            Finset.sum_le_sum fun p _ => hR_1 p
        _ = (n : ℝ) * (C_R * Real.sqrt (D.BNorm k h)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : (∑ p : Fin n, ∑ q : Fin n,
          |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (D.R i h a b)) z|)
        ≤ (n : ℝ) ^ 2 * (C_R * Real.sqrt (D.BNorm k h)) := by
      calc ∑ p : Fin n, ∑ q : Fin n,
            |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (D.R i h a b)) z|
          ≤ ∑ _p : Fin n, ∑ _q : Fin n, (C_R * Real.sqrt (D.BNorm k h)) :=
            Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hR_2 p q
        _ = (n : ℝ) * ((n : ℝ) * (C_R * Real.sqrt (D.BNorm k h))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (n : ℝ) ^ 2 * (C_R * Real.sqrt (D.BNorm k h)) := by ring
    have hnn : 0 ≤ C_R * Real.sqrt (D.BNorm k h) :=
      mul_nonneg hC_R_nn (Real.sqrt_nonneg _)
    have hn1 : (1 : ℝ) ≤ 1 + (n : ℝ) + (n : ℝ) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
    linarith [hR_z, h2, h3, mul_le_mul_of_nonneg_right hn1 hnn]
  -- the factor produced by the quotient rule
  have hfac : 1 / (c * Real.sqrt d₀) + (Kj + Kj) / (c * Real.sqrt d₀) ^ 2
        + Kj ^ 2 / (c * Real.sqrt d₀) ^ 3 ≤ Cδ / c ^ 3 := by
    have hs : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd₀pos
    have hcMψ : c ≤ Mψ := le_trans hcl (hMψ i z)
    have h1 : 1 / (c * Real.sqrt d₀) ≤ Mψ ^ 2 / (c ^ 3 * Real.sqrt d₀) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : c ^ 2 ≤ Mψ ^ 2 := by nlinarith [hc.le, hcMψ, hMψ_nn]
      have key : c ^ 3 * Real.sqrt d₀ ≤ Mψ ^ 2 * (c * Real.sqrt d₀) := by
        have hb : 0 ≤ c * Real.sqrt d₀ := by positivity
        calc c ^ 3 * Real.sqrt d₀ = c ^ 2 * (c * Real.sqrt d₀) := by ring
          _ ≤ Mψ ^ 2 * (c * Real.sqrt d₀) := mul_le_mul_of_nonneg_right hsq hb
      simpa using key
    have h2 : (Kj + Kj) / (c * Real.sqrt d₀) ^ 2 ≤ (2 * Kj * Mψ) / (c ^ 3 * d₀) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have key : (Kj + Kj) * (c ^ 3 * d₀) ≤ (2 * Kj * Mψ) * (c * Real.sqrt d₀) ^ 2 := by
        have hsq : (c * Real.sqrt d₀) ^ 2 = c ^ 2 * d₀ := by
          rw [mul_pow, Real.sq_sqrt hd₀pos.le]
        rw [hsq]
        have hstep : Kj + Kj ≤ 2 * Kj := by linarith
        have h1 : c ^ 3 * d₀ ≤ Mψ * (c ^ 2 * d₀) := by
          have hc2 : 0 ≤ c ^ 2 * d₀ := by positivity
          calc c ^ 3 * d₀ = c * (c ^ 2 * d₀) := by ring
            _ ≤ Mψ * (c ^ 2 * d₀) := mul_le_mul_of_nonneg_right hcMψ hc2
        calc (Kj + Kj) * (c ^ 3 * d₀) ≤ (2 * Kj) * (c ^ 3 * d₀) :=
              mul_le_mul_of_nonneg_right hstep (by positivity)
          _ ≤ (2 * Kj) * (Mψ * (c ^ 2 * d₀)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (2 * Kj * Mψ) * (c ^ 2 * d₀) := by ring
      simpa using key
    have h3 : Kj ^ 2 / (c * Real.sqrt d₀) ^ 3 ≤ Kj ^ 2 / (c ^ 3 * (d₀ * Real.sqrt d₀)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have key : Kj ^ 2 * (c ^ 3 * (d₀ * Real.sqrt d₀)) ≤ Kj ^ 2 * (c * Real.sqrt d₀) ^ 3 := by
        have hcube : (c * Real.sqrt d₀) ^ 3 = c ^ 3 * (d₀ * Real.sqrt d₀) := by
          have hs2 : (Real.sqrt d₀) ^ 2 = d₀ := Real.sq_sqrt hd₀pos.le
          have hs3 : (Real.sqrt d₀) ^ 3 = d₀ * Real.sqrt d₀ := by
            calc (Real.sqrt d₀) ^ 3 = (Real.sqrt d₀) ^ 2 * Real.sqrt d₀ := by ring
              _ = d₀ * Real.sqrt d₀ := by rw [hs2]
          calc (c * Real.sqrt d₀) ^ 3 = c ^ 3 * (Real.sqrt d₀) ^ 3 := by ring
            _ = c ^ 3 * (d₀ * Real.sqrt d₀) := by rw [hs3]
        rw [hcube]
      simpa using key
    rw [hCδ]
    have e1 : Mψ ^ 2 / (c ^ 3 * Real.sqrt d₀)
        = (Mψ ^ 2 / Real.sqrt d₀) / c ^ 3 := by ring
    have e2 : (2 * Kj * Mψ) / (c ^ 3 * d₀) = ((2 * Kj * Mψ) / d₀) / c ^ 3 := by ring
    have e3 : Kj ^ 2 / (c ^ 3 * (d₀ * Real.sqrt d₀))
        = (Kj ^ 2 / (d₀ * Real.sqrt d₀)) / c ^ 3 := by ring
    calc 1 / (c * Real.sqrt d₀) + (Kj + Kj) / (c * Real.sqrt d₀) ^ 2
          + Kj ^ 2 / (c * Real.sqrt d₀) ^ 3
        ≤ Mψ ^ 2 / (c ^ 3 * Real.sqrt d₀) + (2 * Kj * Mψ) / (c ^ 3 * d₀)
          + Kj ^ 2 / (c ^ 3 * (d₀ * Real.sqrt d₀)) := add_le_add (add_le_add h1 h2) h3
      _ = Mψ ^ 2 / Real.sqrt d₀ / c ^ 3 + (2 * Kj * Mψ) / d₀ / c ^ 3
          + Kj ^ 2 / (d₀ * Real.sqrt d₀) / c ^ 3 := by rw [e1, e2, e3]
      _ = (Mψ ^ 2 / Real.sqrt d₀ + (2 * Kj * Mψ) / d₀
          + Kj ^ 2 / (d₀ * Real.sqrt d₀)) / c ^ 3 := by ring
  -- combine
  have hF_nn : 0 ≤ 1 / (c * Real.sqrt d₀) + (Kj + Kj) / (c * Real.sqrt d₀) ^ 2
      + Kj ^ 2 / (c * Real.sqrt d₀) ^ 3 := by positivity
  have hCδ_nn : 0 ≤ Cδ := by
    rw [hCδ]
    have hs : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd₀pos
    positivity
  have hS'_nn : 0 ≤ (1 + (n : ℝ) + (n : ℝ) ^ 2) * (C_R * Real.sqrt (D.BNorm k h)) :=
    mul_nonneg (by positivity) (mul_nonneg hC_R_nn (Real.sqrt_nonneg _))
  calc |Work.Diff.STE.pdRList l
        (fun y => D.R i h a b y / matA (I := I) (M := M) D i y) z|
      ≤ Cq * (|D.R i h a b z| + ∑ p : Fin n, |Work.Diff.STE.pdR p (D.R i h a b) z|
            + ∑ p : Fin n, ∑ q : Fin n,
                |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (D.R i h a b)) z|)
          * (1 / (c * Real.sqrt d₀) + (Kj + Kj) / (c * Real.sqrt d₀) ^ 2
            + Kj ^ 2 / (c * Real.sqrt d₀) ^ 3) := hdiv
    _ ≤ Cq * ((1 + (n : ℝ) + (n : ℝ) ^ 2) * (C_R * Real.sqrt (D.BNorm k h)))
          * (Cδ / c ^ 3) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hRsum hCq_nn) hfac hF_nn ?_
        exact mul_nonneg hCq_nn hS'_nn
    _ = (Cq * (1 + (n : ℝ) + (n : ℝ) ^ 2) * C_R * Cδ)
          * Real.sqrt (D.BNorm k h) / c ^ 3 := by ring
    _ ≤ (Cq * (1 + (n : ℝ) + (n : ℝ) ^ 2) * C_R * Cδ + 1)
          * Real.sqrt (D.BNorm k h) / c ^ 3 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)


/-! ## 4. Entrywise identification of the chart jets

The chart jet `Work.Diff.STE.DeTurck.chartJet` consists of the value, the first and the second
Fréchet derivative of a matrix-valued function.  The jet bounds proved here (`hBg`, `hChart`) are
stated for the *entries* of those derivatives, so the two identifications below are needed. -/

/-- The `(a,b)`-entry of the Fréchet derivative of a matrix-valued function is the Fréchet
derivative of the entry. -/
lemma fderiv_entry_eq {F : E → Work.Diff.EXT.MatE (E := E)} {y : E} (hF : DifferentiableAt ℝ F y)
    (v : E) (a b : Fin (Module.finrank ℝ E)) :
    ((fderiv ℝ F y) v) a b = (fderiv ℝ (fun y' => F y' a b) y) v := by
  let L : Work.Diff.EXT.MatE (E := E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) => ℝ) b).comp
      (ContinuousLinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) =>
        Fin (Module.finrank ℝ E) → ℝ) a)
  have hL : ∀ M : Work.Diff.EXT.MatE (E := E), L M = M a b := fun M => rfl
  have h1 : fderiv ℝ (fun y' => L (F y')) y = L.comp (fderiv ℝ F y) := by
    have hcomp := fderiv_comp (x := y) (g := L) (f := F) L.differentiableAt hF
    rw [ContinuousLinearMap.fderiv] at hcomp
    simpa [Function.comp_def] using hcomp
  have h2 : (fun y' : E => L (F y')) = fun y' => F y' a b := by
    funext y'
    exact hL _
  calc ((fderiv ℝ F y) v) a b = L ((fderiv ℝ F y) v) := (hL _).symm
    _ = (L.comp (fderiv ℝ F y)) v := rfl
    _ = (fderiv ℝ (fun y' => L (F y')) y) v := by rw [h1]
    _ = (fderiv ℝ (fun y' => F y' a b) y) v := by rw [h2]

/-- The `(a,b)`-entry of a `C^∞` matrix-valued function is `C^∞`. -/
lemma contDiffAt_entry {F : E → Work.Diff.EXT.MatE (E := E)} {y : E}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F y) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y'' => F y'' a b) y := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun M : Work.Diff.EXT.MatE (E := E) => M a b) := by
    fun_prop
  simpa [Function.comp_def] using hL.contDiffAt.comp y hF

/-- The `(a,b)`-entry of the second Fréchet derivative of a matrix-valued function is the second
Fréchet derivative of the entry (in the nesting used by `Work.Diff.STE.DeTurck.chartJet`).  The
hypothesis is the smoothness of `F` in a neighbourhood of `y`, which is what the chart matrix of a
section with `ChartData` provides near a point of the chart target. -/
lemma fderiv_fderiv_entry_eq {F : E → Work.Diff.EXT.MatE (E := E)} {y : E}
    (hF : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ (⊤ : ℕ∞) F y') (v w : E)
    (a b : Fin (Module.finrank ℝ E)) :
    ((fderiv ℝ (fun y' => fderiv ℝ F y') y v) w) a b
      = (fderiv ℝ (fun y' => fderiv ℝ (fun y'' => F y'' a b) y') y v) w := by
  have hFy : ContDiffAt ℝ (⊤ : ℕ∞) F y := hF.self_of_nhds
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hFy.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  have hdG : DifferentiableAt ℝ (fun y' => (fderiv ℝ F y') w) y :=
    hdF.clm_apply (differentiableAt_const w)
  have h2 : (fderiv ℝ (fderiv ℝ F) y).flip w
      = fderiv ℝ (fun y' => (fderiv ℝ F y') w) y := by
    rw [fderiv_clm_apply (c := fderiv ℝ F) (u := fun _ : E => w) hdF
      (differentiableAt_const w)]
    simp
  have h1 : (fderiv ℝ (fun y' => fderiv ℝ F y') y v) w
      = (fderiv ℝ (fun y' => (fderiv ℝ F y') w) y) v := by
    have hflip : ((fderiv ℝ (fderiv ℝ F) y).flip w) v
        = ((fderiv ℝ (fun y' => fderiv ℝ F y') y) v) w :=
      ContinuousLinearMap.flip_apply _ _ _
    rw [← hflip, h2]
  have h3 : (fun y' : E => ((fderiv ℝ F y') w) a b)
      =ᶠ[𝓝 y] fun y' => (fderiv ℝ (fun y'' => F y'' a b) y') w := by
    filter_upwards [hF] with y' hy'
    exact fderiv_entry_eq (y := y') (hy'.differentiableAt (by simp)) w a b
  have h4 : (fderiv ℝ (fun y' => (fderiv ℝ F y') w) y) v a b
      = (fderiv ℝ (fun y' => ((fderiv ℝ F y') w) a b) y) v :=
    fderiv_entry_eq (F := fun y' => (fderiv ℝ F y') w) (y := y) hdG v a b
  have hdG' : DifferentiableAt ℝ (fun y' : E => fderiv ℝ (fun y'' => F y'' a b) y') y :=
    ((contDiffAt_entry hFy a b).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  calc ((fderiv ℝ (fun y' => fderiv ℝ F y') y v) w) a b
      = ((fderiv ℝ (fun y' => (fderiv ℝ F y') w) y) v) a b := by rw [h1]
    _ = (fderiv ℝ (fun y' => ((fderiv ℝ F y') w) a b) y) v := h4
    _ = (fderiv ℝ (fun y' => (fderiv ℝ (fun y'' => F y'' a b) y') w) y) v := by
        rw [h3.fderiv_eq]
    _ = (fderiv ℝ (fun y' => fderiv ℝ (fun y'' => F y'' a b) y') y v) w := by
        have hc := fderiv_clm_apply (c := fun y' => fderiv ℝ (fun y'' => F y'' a b) y')
          (u := fun _ : E => w) hdG' (differentiableAt_const w)
        rw [hc]
        simp [ContinuousLinearMap.flip_apply]

/-- **The chart with the maximal weight at a point.**  For every `x` there is a chart `i` for which
the localised weight `ψ i` at the flat coordinate of `x` is at least `(√(card ι₀))⁻¹`, and for which
all the geometric hypotheses (chart source, smallness of the flat coordinate, orthonormality of the
frame `e i`, membership in `Ky D i`) hold. -/
theorem exists_max_chart (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x : M) :
    ∃ i : ι₀, (Real.sqrt (Fintype.card ι₀))⁻¹ ≤ D.psi i (coord (I := I) (D.x₀ i) x)
      ∧ 0 < D.psi i (coord (I := I) (D.x₀ i) x)
      ∧ x ∈ (extChartAt I (D.x₀ i)).source
      ∧ ‖coord (I := I) (D.x₀ i) x‖ ≤ D.σ i
      ∧ IsONFrame g₀ x (fun a => D.e i a x)
      ∧ coord (I := I) (D.x₀ i) x ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i := by
  haveI hne : Nonempty ι₀ := by
    by_contra hι
    have hsum := D.hζsq x
    have hempty : (Finset.univ : Finset ι₀) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun i _ => hι ⟨i⟩
    rw [hempty, Finset.sum_empty] at hsum
    exact one_ne_zero hsum.symm
  have hNpos : (0 : ℝ) < (Fintype.card ι₀ : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨i, hi⟩ : ∃ i : ι₀, (Fintype.card ι₀ : ℝ)⁻¹ ≤ (D.ζ i x) ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun i _ => hcon i)
    rw [D.hζsq x] at hlt
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
    rw [mul_inv_cancel₀ (ne_of_gt hNpos)] at hlt
    exact lt_irrefl _ hlt
  have hζpos : 0 < D.ζ i x := by
    have hp : 0 < (Fintype.card ι₀ : ℝ)⁻¹ := inv_pos.mpr hNpos
    nlinarith [D.hζnn i x, sq_nonneg (D.ζ i x), hi, hp]
  have hζge : (Real.sqrt (Fintype.card ι₀))⁻¹ ≤ D.ζ i x := by
    rw [← Real.sqrt_inv, ← Real.sqrt_sq hζpos.le]
    exact Real.sqrt_le_sqrt hi
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i x (ne_of_gt hζpos)
  have hle : ‖coord (I := I) (D.x₀ i) x‖ ≤ D.σ i := le_of_lt hlt
  have hON : IsONFrame g₀ x (fun a => D.e i a x) := by
    have h0 := D.heON i (coord (I := I) (D.x₀ i) x) (by linarith [hle, D.hσ i])
    rwa [D.symm_flatToE_coord i hsrc] at h0
  have hψ : D.psi i (coord (I := I) (D.x₀ i) x) = D.ζ i x :=
    D.psi_coord_eq_zeta i (ne_of_gt hζpos)
  refine ⟨i, ?_, ?_, hsrc, hle, hON, ?_⟩
  · rw [hψ]; exact hζge
  · rw [hψ]; exact hζpos
  · exact Work.Diff.STE.D.psi.mem_Ky_of_psi_ne_zero (I := I) (M := M) D
      (by rw [hψ]; exact ne_of_gt hζpos)

/-- **The DeTurck operator as a chart contraction.**  For a section `g` with smooth chart data the
value of the DeTurck operator is the contraction of the jet-level operator `pPhiJetOf` with the
coordinates of the two vectors in the trivialisation at the chart centre. -/
theorem deTurckOp_chart_expansion (hLC : Submission.Diff.LCSmooth I M)
    (g₀ : Submission.Diff.SMet I M) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (g : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), g x u v = g x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < g x v v)
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) g)
    (i : ι₀) {x : M} (hx : x ∈ (extChartAt I (D.x₀ i)).source) (u v : TangentSpace I x) :
    Work.Diff.STE.DeTurck.deTurckOp (Work.Diff.STE.D.smetOf (I := I) g hsym hpos hsm) g₀ x u v
      = ∑ j, ∑ l, Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ g (D.x₀ i)
          ((extChartAt I (D.x₀ i)) x) j l
          * (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j u
            * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x l v) := by
  rw [← Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp (I := I) (M := M) hLC
    (Work.Diff.STE.D.smetOf (I := I) g hsym hpos hsm) g₀ (D.x₀ i)
    (by rw [← extChartAt_source (I := I) (D.x₀ i)]; exact hx) u v]
  rfl

theorem deTurck_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (k : ℕ) (hk : Module.finrank ℝ E + 12 < 2 * k)
    (lam K : ℝ) (hlam : 0 < lam) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h),
      D.BNorm k h ≤ B →
      (∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v) →
      (∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v) →
      ∀ (x : M) (u v : TangentSpace I x),
      |Work.Diff.STE.DeTurck.deTurckOp (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsm) g₀ x u v|
        ≤ C * (1 + B) ^ 2 * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v))
    ∧
    (∀ (B : ℝ) (hseq : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
        (hlim : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym_n : ∀ n, ∀ (x : M) (u v : TangentSpace I x), hseq n x u v = hseq n x v u)
        (hpos_n : ∀ n, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < hseq n x v v)
        (hsm_n : ∀ n, Work.Diff.STE.D.ChartData (I := I) (M := M) (hseq n))
        (hsym_l : ∀ (x : M) (u v : TangentSpace I x), hlim x u v = hlim x v u)
        (hpos_l : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < hlim x v v)
        (hsm_l : Work.Diff.STE.D.ChartData (I := I) (M := M) hlim)
        (hBn : ∀ n, D.BNorm k (hseq n) ≤ B) (hBl : D.BNorm k hlim ≤ B)
        (hell_n : ∀ n, ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ hseq n x v v)
        (hell_l : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ hlim x v v)
        (hub_n : ∀ n, ∀ (x : M) (v : TangentSpace I x), hseq n x v v ≤ K * g₀.inner x v v)
        (hub_l : ∀ (x : M) (v : TangentSpace I x), hlim x v v ≤ K * g₀.inner x v v)
        (hconv : Filter.Tendsto (fun n : ℕ => D.BNorm k (hseq n - hlim)) Filter.atTop (nhds 0)),
        ∀ (x : M) (u v : TangentSpace I x),
        Filter.Tendsto (fun n : ℕ => Work.Diff.STE.DeTurck.deTurckOp
            (Work.Diff.STE.D.smetOf (I := I) (hseq n) (hsym_n n) (hpos_n n) (hsm_n n)) g₀ x u v)
          Filter.atTop (nhds (Work.Diff.STE.DeTurck.deTurckOp
            (Work.Diff.STE.D.smetOf (I := I) hlim hsym_l hpos_l hsm_l) g₀ x u v))) := by
  classical
  obtain ⟨C_M, hC_M_nn, hMatSharp⟩ := mat_jet_bound_sqrt (I := I) (M := M) D k (by omega)
  obtain ⟨C_J, hC_J_nn, hChart⟩ :=
    chartMatJet_sharp (I := I) (M := M) D k (by omega) C_M hC_M_nn hMatSharp
  obtain ⟨Mbg, hMbg_nn, hBg⟩ := background_jet_bound (I := I) (M := M) D
  obtain ⟨C_P, hC_P_nn, hPPhi⟩ := pPhi_entry_bound_v2 (E := E)
  obtain ⟨B₀, hB₀_nn, hB₀⟩ := coord_factor_uniform (I := I) (M := M) D
  have hJet : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) g → ChartJetBound (I := I) (M := M) D k g C :=
    ⟨C_J, hC_J_nn, fun g hsm => hChart g hsm⟩
  constructor
  · -- ================= FIRST CONJUNCT =================
    by_cases hι : Nonempty ι₀
    · haveI : Nonempty ι₀ := hι
      have hNpos : (0 : ℝ) < (Fintype.card ι₀ : ℝ) := by exact_mod_cast Fintype.card_pos
      set c₀ : ℝ := (Real.sqrt (Fintype.card ι₀))⁻¹ with hc₀def
      have hc₀pos : 0 < c₀ := by rw [hc₀def]; positivity
      set q₀ : ℝ := 1 / (((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2) with hq₀def
      have hq₀pos : 0 < q₀ := by rw [hq₀def]; positivity
      set cl : ℝ := min (min 1 (lam * q₀)) q₀ with hcldef
      have hclpos : 0 < cl := by
        rw [hcldef]
        exact lt_min (lt_min one_pos (mul_pos hlam hq₀pos)) hq₀pos
      have hcl_le1 : cl ≤ 1 := by
        rw [hcldef]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      have hcl_lem : cl ≤ lam * q₀ := by
        rw [hcldef]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      have hcl_le_q : cl ≤ q₀ := by rw [hcldef]; exact min_le_right _ _
      set CB : ℝ := C_J / c₀ ^ 3 with hCBdef
      have hCBnn : 0 ≤ CB := by rw [hCBdef]; positivity
      set MA : ℝ := max 1 (2 * (|K| * Mbg)) with hMAdef
      have hMA1 : 1 ≤ MA := by rw [hMAdef]; exact le_max_left _ _
      set MB : ℝ := max 1 Mbg with hMBdef
      have hMB1 : 1 ≤ MB := by rw [hMBdef]; exact le_max_left _ _
      set Cf : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2 * C_P
        * (2 + CB) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5 with hCfdef
      have hCfnn : 0 ≤ Cf := by
        rw [hCfdef]
        refine div_nonneg ?_ (by positivity)
        positivity
      refine ⟨Cf, hCfnn, ?_⟩
      intro B h hsym hpos hsm hBN hlow hup x u v
      have hBnn : 0 ≤ B := by
        refine le_trans ?_ hBN
        simp only [Work.Diff.STE.B3Data.BNorm]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
          Finset.sum_nonneg fun b _ => Work.Diff.STE.CSq_nonneg k _
      -- the chart with the maximal weight
      obtain ⟨i, hψge, hψpos, hsrc, hle_sigma, hON, hKy⟩ :=
        exists_max_chart (I := I) (M := M) D x
      have hc₀_le_ψ : c₀ ≤ D.psi i (coord (I := I) (D.x₀ i) x) := by
        rw [hc₀def]; exact hψge
      let z : Fin (Module.finrank ℝ E) → ℝ := coord (I := I) (D.x₀ i) x
      let y : E := (extChartAt I (D.x₀ i)) x
      have hy : y ∈ (extChartAt I (D.x₀ i)).target := (extChartAt I (D.x₀ i)).map_source hsrc
      have hzy : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z = y :=
        flatToE_coord (I := I) (M := M) D hsrc
      set Md : ℝ := max 1 (CB * (1 + B)) with hMddef
      have hMd1 : 1 ≤ Md := by rw [hMddef]; exact le_max_left _ _
      have hMdnn : 0 ≤ Md := le_trans zero_le_one hMd1
      -- the sharp bound is below `CB * (1 + B)`
      have hKJ : C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3 ≤ CB * (1 + B) := by
        have hs : Real.sqrt (D.BNorm k h) ≤ 1 + B := by
          refine le_trans (Real.sqrt_le_sqrt hBN) ?_
          rw [Real.sqrt_le_iff]
          exact ⟨by linarith, by nlinarith [sq_nonneg B, hBnn]⟩
        have he : C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3
            = (C_J / c₀ ^ 3) * Real.sqrt (D.BNorm k h) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        rw [he, hCBdef]
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      have hKJ_le_Md : C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3 ≤ Md := by
        rw [hMddef]
        exact le_trans hKJ (le_max_right _ _)
      -- the jet bound of the chart matrix of `h`
      have hChartv : ∀ a b : Fin (Module.finrank ℝ E),
          (|Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b|
            ≤ C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3)
          ∧ (∀ p : Fin (Module.finrank ℝ E),
              |(fderiv ℝ (fun y' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
                    y' a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
                  (Work.Diff.EXT.bB (E := E) p)| ≤ C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3)
          ∧ (∀ p q : Fin (Module.finrank ℝ E),
              |(fderiv ℝ (fun y' : E => (fderiv ℝ (fun y'' : E =>
                    Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y'' a b) y'))
                  (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
                  (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|
                ≤ C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3) :=
        fun a b => hChart h hsm i a b z c₀ hle_sigma hc₀pos hc₀_le_ψ
      -- the background jet bounds
      have hBgv : ∀ a b : Fin (Module.finrank ℝ E),
          (|Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b| ≤ Mbg)
          ∧ (∀ p : Fin (Module.finrank ℝ E),
              |(fderiv ℝ (fun y' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner
                    (D.x₀ i) y' a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
                  (Work.Diff.EXT.bB (E := E) p)| ≤ Mbg)
          ∧ (∀ p q : Fin (Module.finrank ℝ E),
              |(fderiv ℝ (fun y' : E => (fderiv ℝ (fun y'' : E =>
                    Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y'' a b) y'))
                  (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
                  (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)| ≤ Mbg) :=
        fun a b => hBg i a b z hle_sigma
      -- differentiability of the two chart matrices
      have hdiff_h : DifferentiableAt ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)) y :=
        ((hsm (D.x₀ i)).contDiffAt
          ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hy)).differentiableAt (by simp)
      have hev_h : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ (⊤ : ℕ∞)
          (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)) y' :=
        Filter.eventually_iff_exists_mem.mpr
          ⟨(extChartAt I (D.x₀ i)).target,
            IsOpen.mem_nhds (isOpen_extChartAt_target (I := I) (D.x₀ i)) hy,
            fun y' hy' => (hsm (D.x₀ i)).contDiffAt
              (IsOpen.mem_nhds (isOpen_extChartAt_target (I := I) (D.x₀ i)) hy')⟩
      have hdiff_g : DifferentiableAt ℝ
          (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)) y :=
        ((Work.Diff.STE.B3.chartMatFun_contDiffAt_of_mem_target (I := I) (M := M) g₀
          (D.x₀ i) hy)).differentiableAt (by simp)
      have hev_g : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ (⊤ : ℕ∞)
          (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)) y' :=
        Filter.eventually_iff_exists_mem.mpr
          ⟨(extChartAt I (D.x₀ i)).target,
            IsOpen.mem_nhds (isOpen_extChartAt_target (I := I) (D.x₀ i)) hy,
            fun y' hy' => Work.Diff.STE.B3.chartMatFun_contDiffAt_of_mem_target (I := I) (M := M)
              g₀ (D.x₀ i) hy'⟩
      -- the entry bound for the chart matrix of the background
      have hABabs : ∀ a b : Fin (Module.finrank ℝ E),
          |g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b))|
            ≤ Mbg := by
        intro a b
        have h1 : Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y a b
            = g₀.inner x
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
          rw [Work.Diff.STE.D.chartMatOf_apply, (extChartAt I (D.x₀ i)).left_inv hsrc]
        have h2 : |Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b| ≤ Mbg := (hBgv a b).1
        rw [hzy, h1] at h2
        exact h2
      have hAB : ∀ a b : Fin (Module.finrank ℝ E),
          g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) ≤ Mbg :=
        fun a b => le_trans (le_abs_self _) (hABabs a b)
      have hABlo : ∀ a b : Fin (Module.finrank ℝ E),
          -Mbg ≤ g₀.inner x
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) :=
        fun a b => by
          have h := hABabs a b
          have h2 := neg_le_abs (g₀.inner x
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)))
          linarith
      -- the quadratic forms of `u ± v`
      have hgg_plus : ∀ k l : Fin (Module.finrank ℝ E),
          g₀.inner x
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
                + Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
                + Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
            ≤ 4 * Mbg := by
        intro k l
        have hexp : g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
              + Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
              + Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
            = g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
              + g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
              + g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
              + g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l)) := by
          simp only [map_add, add_apply]
          ring
        rw [hexp]
        linarith [hAB k k, hAB k l, hAB l k, hAB l l]
      have hgg_minus : ∀ k l : Fin (Module.finrank ℝ E),
          g₀.inner x
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
                - Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
                - Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
            ≤ 4 * Mbg := by
        intro k l
        have hexp : g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
              - Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k)
              - Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
            = g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
              - g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
              - g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
              + g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l)) := by
          simp only [map_sub, sub_apply]
          ring
        rw [hexp]
        linarith [hAB k k, hABlo k l, hABlo l k, hAB l l]
      -- the `h`-quadratic form of a matrix is dominated by `|K|` times the `g₀`-quadratic form
      have hbc : ∀ w : TangentSpace I x, |h x w w| ≤ |K| * g₀.inner x w w := by
        intro w
        have hw1 : 0 ≤ h x w w := by
          rcases eq_or_ne w 0 with hw0 | hw0
          · rw [hw0]; simp
          · exact (hpos x w hw0).le
        have hw2 : 0 ≤ g₀.inner x w w := by
          rcases eq_or_ne w 0 with hw0 | hw0
          · rw [hw0]; simp
          · exact (g₀.pos x w hw0).le
        rw [abs_of_nonneg hw1]
        calc h x w w ≤ K * g₀.inner x w w := hup x w
          _ ≤ |K| * g₀.inner x w w := mul_le_mul_of_nonneg_right (le_abs_self K) hw2
      -- the entry bound for the chart matrix of `h` (from the upper pinching)
      have hA_ent : ∀ k l : Fin (Module.finrank ℝ E),
          |(Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).1 k l| ≤ MA := by
        intro k l
        have hAkl : (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).1 k l
            = h x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k))
                (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l)) := by
          show Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y k l = _
          rw [Work.Diff.STE.D.chartMatOf_apply, (extChartAt I (D.x₀ i)).left_inv hsrc]
        rw [hAkl, hMAdef]
        refine le_max_of_le_right ?_
        set uu : TangentSpace I x :=
          Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) k) with huu
        set vv : TangentSpace I x :=
          Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) l) with hvv
        have hpolar : h x (uu + vv) (uu + vv) - h x (uu - vv) (uu - vv)
            = 2 * (h x uu vv + h x vv uu) := by
          simp only [map_add, map_sub, add_apply, sub_apply]
          ring
        have hsymm : h x vv uu = h x uu vv := (hsym x uu vv).symm
        have h4abs : (4 : ℝ) * |h x uu vv| = |4 * h x uu vv| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        have h4lin : 4 * h x uu vv = h x (uu + vv) (uu + vv) - h x (uu - vv) (uu - vv) := by
          rw [hpolar, hsymm]; ring
        have h2abs : |h x (uu + vv) (uu + vv) - h x (uu - vv) (uu - vv)|
            ≤ |h x (uu + vv) (uu + vv)| + |h x (uu - vv) (uu - vv)| := abs_sub _ _
        have h3abs : |h x (uu + vv) (uu + vv)| ≤ |K| * g₀.inner x (uu + vv) (uu + vv) := hbc _
        have h4abs2 : |h x (uu - vv) (uu - vv)| ≤ |K| * g₀.inner x (uu - vv) (uu - vv) := hbc _
        have h5b : |K| * g₀.inner x (uu + vv) (uu + vv) ≤ 4 * (|K| * Mbg) := by
          calc |K| * g₀.inner x (uu + vv) (uu + vv) ≤ |K| * (4 * Mbg) :=
                mul_le_mul_of_nonneg_left (hgg_plus k l) (abs_nonneg K)
            _ = 4 * (|K| * Mbg) := by ring
        have h6b : |K| * g₀.inner x (uu - vv) (uu - vv) ≤ 4 * (|K| * Mbg) := by
          calc |K| * g₀.inner x (uu - vv) (uu - vv) ≤ |K| * (4 * Mbg) :=
                mul_le_mul_of_nonneg_left (hgg_minus k l) (abs_nonneg K)
            _ = 4 * (|K| * Mbg) := by ring
        have hfinal : 4 * |h x uu vv| ≤ 8 * (|K| * Mbg) := by
          rw [h4abs, h4lin]
          linarith [h2abs, h3abs, h4abs2, h5b, h6b]
        linarith [hfinal]
      -- the operator-norm bounds for the first and second jets of `h`
      have hL_norm : ∀ p : Fin (Module.finrank ℝ E),
          ‖(Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).2.1
            (Work.Diff.EXT.bB (E := E) p)‖ ≤ Md := by
        intro p
        refine (pi_norm_le_iff_of_nonneg hMdnn).mpr fun a =>
          (pi_norm_le_iff_of_nonneg hMdnn).mpr fun b => ?_
        have hraw : |(fderiv ℝ (fun y' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h
              (D.x₀ i) y' a b) y) (Work.Diff.EXT.bB (E := E) p)|
            ≤ C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3 := by
          have h := (hChartv a b).2.1 p
          rwa [hzy] at h
        have hentry : (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).2.1
            (Work.Diff.EXT.bB (E := E) p) a b
            = (fderiv ℝ (fun y' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h
                (D.x₀ i) y' a b) y) (Work.Diff.EXT.bB (E := E) p) := by
          rw [show (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).2.1
              = fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)) y from rfl]
          exact fderiv_entry_eq hdiff_h (Work.Diff.EXT.bB (E := E) p) a b
        rw [hentry]
        exact le_trans hraw hKJ_le_Md
      have hB_norm : ∀ p q : Fin (Module.finrank ℝ E),
          ‖(Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).2.2
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)‖ ≤ Md := by
        intro p q
        refine (pi_norm_le_iff_of_nonneg hMdnn).mpr fun a =>
          (pi_norm_le_iff_of_nonneg hMdnn).mpr fun b => ?_
        have hraw : |(fderiv ℝ (fun y' : E => (fderiv ℝ (fun y'' : E =>
              Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y'' a b) y'))
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
              (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|
            ≤ C_J * Real.sqrt (D.BNorm k h) / c₀ ^ 3 := by
          exact (hChartv a b).2.2 p q
        have hentry : (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).2.2
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q) a b
            = (fderiv ℝ (fun y' : E => (fderiv ℝ (fun y'' : E =>
                Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y'' a b) y'))
                (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
                (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q) := by
          rw [show (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).2.2
              = fderiv ℝ (fun y' : E => fderiv ℝ
                  (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)) y') y from rfl]
          rw [fderiv_fderiv_entry_eq hev_h (Work.Diff.EXT.bB (E := E) p)
            (Work.Diff.EXT.bB (E := E) q) a b]
          rw [← hzy]
        rw [hentry]
        exact le_trans hraw hKJ_le_Md
      -- the operator-norm bounds for the background
      have hLb_norm : ∀ p : Fin (Module.finrank ℝ E),
          ‖(Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).2.1
            (Work.Diff.EXT.bB (E := E) p)‖ ≤ MB := by
        intro p
        refine le_trans ?_ (le_max_right (1 : ℝ) Mbg)
        refine (pi_norm_le_iff_of_nonneg hMbg_nn).mpr fun a =>
          (pi_norm_le_iff_of_nonneg hMbg_nn).mpr fun b => ?_
        have hraw : |(fderiv ℝ (fun y' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M)
              g₀.inner (D.x₀ i) y' a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
              (Work.Diff.EXT.bB (E := E) p)| ≤ Mbg := (hBgv a b).2.1 p
        rw [hzy] at hraw
        have hentry : (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).2.1
            (Work.Diff.EXT.bB (E := E) p) a b
            = (fderiv ℝ (fun y' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner
                (D.x₀ i) y' a b) y) (Work.Diff.EXT.bB (E := E) p) := by
          rw [show (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).2.1
              = fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)) y
              from rfl]
          exact fderiv_entry_eq hdiff_g (Work.Diff.EXT.bB (E := E) p) a b
        rw [hentry]
        exact hraw
      have hBb_norm : ∀ p q : Fin (Module.finrank ℝ E),
          ‖(Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).2.2
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)‖ ≤ MB := by
        intro p q
        refine le_trans ?_ (le_max_right (1 : ℝ) Mbg)
        refine (pi_norm_le_iff_of_nonneg hMbg_nn).mpr fun a =>
          (pi_norm_le_iff_of_nonneg hMbg_nn).mpr fun b => ?_
        have hraw : |(fderiv ℝ (fun y' : E => (fderiv ℝ (fun y'' : E =>
              Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y'' a b) y'))
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
              (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)| ≤ Mbg :=
          (hBgv a b).2.2 p q
        have hentry : (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).2.2
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q) a b
            = (fderiv ℝ (fun y' : E => (fderiv ℝ (fun y'' : E =>
                Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y'' a b) y'))
                (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
                (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q) := by
          rw [show (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).2.2
              = fderiv ℝ (fun y' : E => fderiv ℝ
                  (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)) y') y
              from rfl]
          rw [fderiv_fderiv_entry_eq hev_g (Work.Diff.EXT.bB (E := E) p)
            (Work.Diff.EXT.bB (E := E) q) a b]
          rw [← hzy]
        rw [hentry]
        exact hraw
      have hAb_ent : ∀ a b : Fin (Module.finrank ℝ E),
          |(Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).1 a b| ≤ MB := by
        intro a b
        refine le_trans ?_ (le_max_right (1 : ℝ) Mbg)
        have h := (hBgv a b).1
        rw [hzy] at h
        exact h
      -- the elliptic lower bounds
      have hquadA : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          cl * ∑ a, (ξ a) ^ 2
            ≤ ∑ a, ∑ b, (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).1 a b
                * ξ a * ξ b := by
        intro ξ
        set w : TangentSpace I x := ∑ a, ξ a
          • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a) with hw
        have hbil : ∀ (f : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
            (F : Work.Diff.EXT.MatE (E := E)),
            (∀ a b, F a b = f
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b))) →
            f w w = ∑ a, ∑ b, F a b * ξ a * ξ b := by
          intro f F hF
          have e1 : ∀ a b : Fin (Module.finrank ℝ E),
              f (ξ a • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
                (ξ b • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b))
              = ξ a * ξ b * f (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
                  (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
            intro a b
            simp only [map_smul, smul_apply, smul_eq_mul]
            ring
          calc f w w = ∑ a, f (ξ a • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x
                (Work.Diff.EXT.bB (E := E) a)) w := by
                rw [hw]; simp only [map_sum, sum_apply]; rw [Finset.sum_comm]
            _ = ∑ a, ∑ b, f (ξ a • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x
                  (Work.Diff.EXT.bB (E := E) a))
                  (ξ b • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [hw]; simp only [map_sum]
            _ = ∑ a, ∑ b, ξ a * ξ b * f (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x
                  (Work.Diff.EXT.bB (E := E) a))
                  (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) :=
                Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e1 a b
            _ = ∑ a, ∑ b, F a b * ξ a * ξ b := by
                refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
                rw [hF a b]; ring
        have hAc : ∀ a b : Fin (Module.finrank ℝ E),
            (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ i) y).1 a b
              = h x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
                  (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
          intro a b
          show Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y a b = _
          rw [Work.Diff.STE.D.chartMatOf_apply, (extChartAt I (D.x₀ i)).left_inv hsrc]
        have hAg : ∀ a b : Fin (Module.finrank ℝ E),
            (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).1 a b
              = g₀.inner x (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
                  (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
          intro a b
          show Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y a b = _
          rw [Work.Diff.STE.D.chartMatOf_apply, (extChartAt I (D.x₀ i)).left_inv hsrc]
        have hh : h x w w = ∑ a, ∑ b, (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h
            (D.x₀ i) y).1 a b * ξ a * ξ b := hbil (h x) _ hAc
        have hg : g₀.inner x w w = ∑ a, ∑ b, (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner
            (D.x₀ i) y).1 a b * ξ a * ξ b := hbil (g₀.inner x) _ hAg
        have hgq : q₀ * ∑ a, (ξ a) ^ 2 ≤ g₀.inner x w w := by
          rw [hg, hq₀def]
          exact gmat_qform_lower (I := I) (M := M) D B₀ hB₀_nn hB₀ i hsrc hON hKy ξ
        have hstep : cl * ∑ a, (ξ a) ^ 2 ≤ (lam * q₀) * ∑ a, (ξ a) ^ 2 :=
          mul_le_mul_of_nonneg_right hcl_lem (Finset.sum_nonneg fun a _ => sq_nonneg _)
        have hstep2 : (lam * q₀) * ∑ a, (ξ a) ^ 2 ≤ h x w w := by
          have h2 : lam * (q₀ * ∑ a, (ξ a) ^ 2) ≤ lam * (g₀.inner x w w) :=
            mul_le_mul_of_nonneg_left hgq hlam.le
          have h3 : lam * g₀.inner x w w ≤ h x w w := hlow x w
          have he : (lam * q₀) * ∑ a, (ξ a) ^ 2 = lam * (q₀ * ∑ a, (ξ a) ^ 2) := by ring
          linarith [h2, h3, he.le, he.ge]
        exact (le_trans hstep hstep2).trans hh.le
      have hquadAb : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          cl * ∑ a, (ξ a) ^ 2
            ≤ ∑ a, ∑ b, (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).1 a b
                * ξ a * ξ b := by
        intro ξ
        have h1 : q₀ * ∑ a, (ξ a) ^ 2
            ≤ ∑ a, ∑ b, (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) y).1 a b
                * ξ a * ξ b := by
          rw [hq₀def]
          exact gmat_qform_lower (I := I) (M := M) D B₀ hB₀_nn hB₀ i hsrc hON hKy ξ
        have h2 : cl * ∑ a, (ξ a) ^ 2 ≤ q₀ * ∑ a, (ξ a) ^ 2 :=
          mul_le_mul_of_nonneg_right hcl_le_q (Finset.sum_nonneg fun a _ => sq_nonneg _)
        linarith [h1, h2]
      -- the bound on the jet-level operator
      have hK0 : ∀ j k : Fin (Module.finrank ℝ E),
          |Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i) y j k|
            ≤ C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5 := by
        intro j k
        have hsd : (1 + Md) ^ 2 ≤ (2 + CB) ^ 2 * (1 + B) ^ 2 := by
          have hle : (1 : ℝ) + Md ≤ (2 + CB) * (1 + B) := by
            rw [hMddef]
            have h1B : (1 : ℝ) ≤ 1 + B := by linarith
            have hm : (1 : ℝ) + max 1 (CB * (1 + B)) = max 2 (1 + CB * (1 + B)) := by
              rcases le_total (1 : ℝ) (CB * (1 + B)) with h | h
              · rw [max_eq_right h,
                  max_eq_right (by linarith : (2 : ℝ) ≤ 1 + CB * (1 + B))]
              · rw [max_eq_left h,
                  max_eq_left (by linarith : (1 : ℝ) + CB * (1 + B) ≤ 2)]
                norm_num
            rw [hm]
            exact max_le (by nlinarith [h1B, hCBnn]) (by nlinarith [h1B, hCBnn])
          calc (1 + Md) ^ 2 ≤ ((2 + CB) * (1 + B)) ^ 2 :=
                pow_le_pow_left₀ (by linarith) hle 2
            _ = (2 + CB) ^ 2 * (1 + B) ^ 2 := by rw [mul_pow]
        have hraw := hPPhi _ _ _ _ _ _ MA MB Md cl j k hMA1 hMB1 hMd1 hclpos hcl_le1
          hquadA hquadAb hA_ent hAb_ent hL_norm hLb_norm hB_norm hBb_norm
        have hmono : C_P * (1 + Md) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5
            ≤ C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5 := by
          have hstep : C_P * (1 + Md) ^ 2 ≤ C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 := by
            calc C_P * (1 + Md) ^ 2 ≤ C_P * ((2 + CB) ^ 2 * (1 + B) ^ 2) :=
                  mul_le_mul_of_nonneg_left hsd hC_P_nn
              _ = C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 := by ring
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hstep (by positivity)) (by positivity)) (by positivity)
        exact le_trans hraw hmono
      -- the coordinates of the two vectors
      have hcoord : ∀ (j : Fin (Module.finrank ℝ E)) (w : TangentSpace I x),
          |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j w|
            ≤ B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x w w) :=
        fun j w => coordCLM_bound (I := I) (M := M) D B₀ hB₀_nn hB₀ i hsrc hON hKy w j
      have hgu : 0 ≤ g₀.inner x u u := by
        rcases eq_or_ne u 0 with h0 | h0
        · rw [h0]; simp
        · exact (g₀.pos x u h0).le
      have hgv : 0 ≤ g₀.inner x v v := by
        rcases eq_or_ne v 0 with h0 | h0
        · rw [h0]; simp
        · exact (g₀.pos x v h0).le
      have hKu : 0 ≤ B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u) :=
        mul_nonneg (mul_nonneg hB₀_nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      have hKv : 0 ≤ B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v) :=
        mul_nonneg (mul_nonneg hB₀_nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      have hKnn : 0 ≤ C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5 := by
        positivity
      rw [deTurckOp_chart_expansion (I := I) (M := M) hLC g₀ D h hsym hpos hsm i hsrc u v]
      calc |∑ j, ∑ l, Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i) y j l
              * (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j u
                * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x l v)|
          ≤ ∑ j, ∑ l, (C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5)
              * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u))
              * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v)) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            refine Finset.sum_le_sum fun j _ => ?_
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            refine Finset.sum_le_sum fun l _ => ?_
            rw [abs_mul, abs_mul]
            have h1 := hK0 j l
            have h2 := hcoord j u
            have h3 := hcoord l v
            calc |Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i) y j l|
                  * (|Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j u|
                    * |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x l v|)
                ≤ (C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5)
                  * ((B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u))
                    * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v))) :=
                  mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) hKu)
                    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hKnn
              _ = (C_P * (2 + CB) ^ 2 * (1 + B) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5)
                  * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u))
                  * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v)) := by ring
        _ = Cf * (1 + B) ^ 2 * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [hCfdef]
            ring
    · -- `ι₀` is empty, hence `M` is empty and the statement is vacuous
      refine ⟨0, le_refl 0, ?_⟩
      intro B h hsym hpos hsm hBN hlow hup x u v
      exact absurd (D.hcover x) (by rintro ⟨i, _⟩; exact hι ⟨i⟩)
  · -- ================= SECOND CONJUNCT =================
    intro B hseq hlim hsym_n hpos_n hsm_n hsym_l hpos_l hsm_l hBn hBl hell_n hell_l hub_n hub_l
      hconv x u v
    obtain ⟨i, -, hψpos, hsrc, hle, -, -⟩ := exists_max_chart (I := I) (M := M) D x
    have hh : ∀ j l : Fin (Module.finrank ℝ E),
        Filter.Tendsto (fun n : ℕ => Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ (hseq n)
            (D.x₀ i) ((extChartAt I (D.x₀ i)) x) j l)
          Filter.atTop (nhds (Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ hlim (D.x₀ i)
            ((extChartAt I (D.x₀ i)) x) j l)) :=
      fun j l => pPhiJetOf_tendsto (I := I) (M := M) D k hseq hlim hsm_n hsm_l lam hlam
        hsym_l hell_l hconv hJet i x hsrc hle hψpos j l
    have hgoal : Filter.Tendsto
        (fun n : ℕ => ∑ j, ∑ l, Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ (hseq n) (D.x₀ i)
              ((extChartAt I (D.x₀ i)) x) j l
              * (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j u
                * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x l v))
        Filter.atTop
        (nhds (∑ j, ∑ l, Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ hlim (D.x₀ i)
              ((extChartAt I (D.x₀ i)) x) j l
              * (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j u
                * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x l v))) := by
      refine tendsto_finsetSum Finset.univ fun j _ =>
        tendsto_finsetSum Finset.univ fun l _ => ?_
      exact (hh j l).mul tendsto_const_nhds
    rw [← deTurckOp_chart_expansion (I := I) (M := M) hLC g₀ D hlim hsym_l hpos_l hsm_l i hsrc
      u v] at hgoal
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n =>
        (deTurckOp_chart_expansion (I := I) (M := M) hLC g₀ D (hseq n) (hsym_n n) (hpos_n n)
          (hsm_n n) i hsrc u v).symm) hgoal

end Work.Diff.STE.Lead
