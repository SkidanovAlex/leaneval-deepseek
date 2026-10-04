import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.MatJetDefs
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.Man.SectSup
import Submission.Work.Diff.STE.flat.limit_aux
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.Lead.pdRList_div_le
import Submission.Work.Diff.STE.Lead.matA_jets
import Submission.Work.Diff.STE.Lead.psi_le_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second-order jet bound for the B3 chart matrices

The localised component of a section `h` in the B3 data `D` is

`D.R i h a b z = matA D i z * D.mat i h a b z`,   `matA D i z = D.psi i z * √(D.dens i z)`,

with `D.mat i h a b` the chart matrix of `h` in the `g₀`-orthonormal frame `e i`.  The composite
norm `D.BNorm k h` is the sum of the weighted Fourier `ℓ²` norms (`H^k`) of the *periodisations*
of the components `D.R i h a b`.

This file proves that, on the part of the chart-`i` `σ`-ball where the localised weight
`D.psi i` stays above a level `c > 0`, the chart matrix `D.mat i h a b` and its first two
coordinate derivatives are bounded by `C (1 + B) / c³` whenever `D.BNorm k h ≤ B` and
`finrank ℝ E + 4 < 2 k`:

* `finrank ℝ E + 4 < 2 k` is exactly the Sobolev exponent needed for a *second order* sup bound
  (`card ι < 2 (k - 2)`), i.e. the level `k - 2` controls two derivatives
  (`flat.sup_pdList_le`, `norm_seriesFun_le`);
* on the `σ`-ball the cut-off `χ i` equals `1`, so `D.R i h a b = matA D i · D.mat i h a b`
  there, and `D.mat i h a b = D.R i h a b / matA D i z`; the division costs one power of the
  weight per derivative (`pdRList_div_le`), i.e. `c³` for two derivatives;
* the weight `matA D i` and its derivatives are uniformly bounded on the `σ`-ball (`matA_jets`),
  and `D.psi i z ≤ M` (`psi_le_const`) bounds the `c` for which the hypothesis `c ≤ D.psi i z`
  is satisfiable, which is what turns `1/δ`, `K/δ²` into `c⁻³`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-! ## 1. Iterated derivatives of eventually equal functions

`pdR`/`pdList` are built from `fderiv`; if two functions agree near a point, all their iterated
partial derivatives at that point agree as well. -/

section Congr

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pdList_eventuallyEq_of_eventuallyEq {f g : (ι → ℝ) → ℂ} {z : ι → ℝ}
    (h : f =ᶠ[𝓝 z] g) : ∀ l : List ι, pdList l f =ᶠ[𝓝 z] pdList l g := by
  intro l
  induction l with
  | nil => exact h
  | cons i l ih =>
    have hfd : fderiv ℝ (pdList l f) =ᶠ[𝓝 z] fderiv ℝ (pdList l g) := ih.fderiv
    filter_upwards [hfd] with y hy
    exact congrArg (fun (L : (ι → ℝ) →L[ℝ] ℂ) => L (Pi.single i 1)) hy

lemma pdList_congr_of_eventuallyEq {f g : (ι → ℝ) → ℂ} {z : ι → ℝ}
    (h : f =ᶠ[𝓝 z] g) (l : List ι) : pdList l f z = pdList l g z :=
  (pdList_eventuallyEq_of_eventuallyEq h l).eq_of_nhds

lemma pdRList_eventuallyEq_of_eventuallyEq {f g : (ι → ℝ) → ℝ} {z : ι → ℝ}
    (h : f =ᶠ[𝓝 z] g) : ∀ l : List ι, pdRList l f =ᶠ[𝓝 z] pdRList l g := by
  intro l
  induction l with
  | nil => exact h
  | cons i l ih =>
    have hfd : fderiv ℝ (pdRList l f) =ᶠ[𝓝 z] fderiv ℝ (pdRList l g) := ih.fderiv
    filter_upwards [hfd] with y hy
    exact congrArg (fun (L : (ι → ℝ) →L[ℝ] ℝ) => L (Pi.single i 1)) hy

lemma pdRList_congr_of_eventuallyEq {f g : (ι → ℝ) → ℝ} {z : ι → ℝ}
    (h : f =ᶠ[𝓝 z] g) (l : List ι) : pdRList l f z = pdRList l g z :=
  (pdRList_eventuallyEq_of_eventuallyEq h l).eq_of_nhds

end Congr

/-! ## 2. The Sobolev sup bound for the two lowest iterated derivatives

This is `flat.sup_pdList_le` at level `k - 2` and order `2`, combined with
`flat.seriesFun_fourierCoeff` (a smooth periodic function is the Fourier series of its
coefficients) and the weighted `ℓ¹` summability of the coefficients of a smooth periodic
function (`summable_wt_pow_norm_fourierCoeff_of_contDiff`). -/

section FourierJet

/-- Sup bound for the iterated partial derivatives of order `≤ 2` of a smooth `1`-periodic
function, in terms of the weighted `ℓ²` norm `CSq k` of its Fourier coefficients. -/
lemma pdList_le_sqrt_CSq_fin (k n : ℕ) (hk : n + 4 < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (Fin n → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → Periodic1 f →
      ∀ (l : List (Fin n)), l.length ≤ 2 → ∀ x : Fin n → ℝ,
      ‖pdList l f x‖ ≤ C * Real.sqrt (CSq k (fourierCoeff f)) := by
  have hk' : n < 2 * (k - 2) := by omega
  obtain ⟨C, hC, hCb⟩ := flat.sup_pdList_le (n := n) (s := k - 2) (K := 2) hk'
  refine ⟨C, hC, fun f hf hper l hl x => ?_⟩
  have hmom : ∀ N : ℕ, Summable (fun m : Fin n → ℤ => wt m ^ N * ‖fourierCoeff f m‖) :=
    summable_wt_pow_norm_fourierCoeff_of_contDiff f hf hper
  have hser : seriesFun (fourierCoeff f) = f :=
    funext (flat.seriesFun_fourierCoeff f hf hper)
  have h1 := hCb (fourierCoeff f) hmom l hl x
  rw [hser] at h1
  rwa [show k - 2 + 2 = k from by omega] at h1

end FourierJet

/-! ## 3. The jet bound for the localised components, in terms of `BNorm` -/

section B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The jets of order `≤ 2` of a localised component are controlled by the composite norm.**
For `‖z‖ ≤ D.σ i` (so that `z` lies in the open unit cube and the periodisation agrees with the
component near `z`), the iterated derivatives of order `≤ 2` of `D.R i h a b` at `z` are bounded
by `C_R (1 + D.BNorm k h)`. -/
private lemma R_jet_le (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (C_R : ℝ)
    (hC_R : ∀ (f : (Fin (Module.finrank ℝ E) → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → Periodic1 f →
      ∀ (l : List (Fin (Module.finrank ℝ E))), l.length ≤ 2 → ∀ x : Fin (Module.finrank ℝ E) → ℝ,
      ‖pdList l f x‖ ≤ C_R * Real.sqrt (CSq k (fourierCoeff f)))
    (hC_R_nn : 0 ≤ C_R)
    (h : Bil (I := I) (M := M)) (hchart : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ D.σ i) :
    ∀ (l : List (Fin (Module.finrank ℝ E))), l.length ≤ 2 →
      |pdRList l (D.R i h a b) z| ≤ C_R * (1 + D.BNorm k h) := by
  intro l hl
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hchart i a b
  obtain ⟨hRper_sm, hRper_per⟩ :=
    Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h a b hsm
  -- `z` lies in the open centred cube
  have hσ8 : D.σ i ≤ 1 / 8 := by have := D.hσ2 i; linarith
  have hz8 : ∀ j : Fin (Module.finrank ℝ E), |z j| ≤ 1 / 8 := by
    intro j
    have h1 : |z j| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j
    linarith
  -- the periodisation agrees with the complexified component near `z`
  have hev : (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b y : ℝ) : ℂ))
      =ᶠ[𝓝 z] D.Rper i h a b := by
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨Metric.ball z (1 / 4), Metric.ball_mem_nhds z (by norm_num), fun y hy => ?_⟩
    have hyc : ∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      intro j
      have h1 : |y j - z j| ≤ ‖y - z‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y - z) j
      have h2 : ‖y - z‖ < 1 / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have h4 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      have h5 : |z j| ≤ 1 / 8 := hz8 j
      have h6 := abs_le.mp h5
      rw [Set.mem_Ioo]
      constructor <;> linarith [h4.1, h4.2, h6.1, h6.2]
    exact (D.Rper_eq_R i h a b hyc).symm
  have hcongr : pdList l (fun y => ((D.R i h a b y : ℝ) : ℂ)) z
      = pdList l (D.Rper i h a b) z :=
    pdList_congr_of_eventuallyEq hev l
  have hBNN : 0 ≤ D.BNorm k h := by
    simp only [B3Data.BNorm]
    exact Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun a' _ =>
      Finset.sum_nonneg fun b' _ => CSq_nonneg k _
  have hle : CSq k (fourierCoeff (D.Rper i h a b)) ≤ D.BNorm k h := by
    simp only [B3Data.BNorm]
    exact sum3_single_le (fun (i' : ι₀) (a' b' : Fin (Module.finrank ℝ E)) =>
      CSq k (fourierCoeff (D.Rper i' h a' b'))) (fun i' a' b' => CSq_nonneg k _) i a b
  have hsqr : Real.sqrt (CSq k (fourierCoeff (D.Rper i h a b))) ≤ 1 + D.BNorm k h := by
    refine (Real.sqrt_le_sqrt hle).trans ?_
    calc Real.sqrt (D.BNorm k h) ≤ Real.sqrt ((1 + D.BNorm k h) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + D.BNorm k h := Real.sqrt_sq (by linarith)
  calc |pdRList l (D.R i h a b) z|
      = ‖(((pdRList l (D.R i h a b) z : ℝ)) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖pdList l (fun y => ((D.R i h a b y : ℝ) : ℂ)) z‖ := by
        rw [cm_pdList_ofReal_smooth l (D.R i h a b) hsm]
    _ = ‖pdList l (D.Rper i h a b) z‖ := by rw [hcongr]
    _ ≤ C_R * Real.sqrt (CSq k (fourierCoeff (D.Rper i h a b))) :=
        hC_R _ hRper_sm hRper_per l hl z
    _ ≤ C_R * (1 + D.BNorm k h) := mul_le_mul_of_nonneg_left hsqr hC_R_nn

/-- **Near a point where the localised weight is positive, the chart matrix is the localised
component divided by the weight.**  `‖z‖ < σ i` (which follows from `0 < D.psi i z`) makes the
cut-off `χ i` equal to `1` on a neighbourhood of `z`, so on that neighbourhood
`D.mat i h a b = D.R i h a b / matA D i`. -/
private lemma mat_eventuallyEq (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ D.σ i) {c : ℝ} (hc : 0 < c)
    (hcl : c ≤ D.psi i z) :
    D.mat i h a b =ᶠ[𝓝 z] fun y => D.R i h a b y / matA D i y := by
  have hz2 : ‖z‖ ≤ 2 * D.σ i := by linarith [D.hσ i]
  have hpsi : 0 < D.psi i z := lt_of_lt_of_le hc hcl
  have hζ : D.ζ i (D.pt i z) ≠ 0 := by
    intro h0
    rw [B3Data.psi, h0, mul_zero] at hpsi
    exact lt_irrefl 0 hpsi
  have hlt : ‖z‖ < D.σ i := by
    have h1 := (D.hζsupp i (D.pt i z) hζ).2
    rwa [D.coord_pt i hz2] at h1
  have hevχ : ∀ᶠ y in 𝓝 z, D.χ i y = 1 := by
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i),
        Metric.isOpen_ball.mem_nhds ?_, fun y hy => ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hlt
    · refine D.hχ1 i y ?_
      have h2 : ‖y‖ < D.σ i := by
        simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy
      exact h2.le
  have hevψ : ∀ᶠ y in 𝓝 z, 0 < D.psi i y :=
    ((D.psi_contDiff i).continuous.continuousAt).preimage_mem_nhds
      (IsOpen.mem_nhds isOpen_Ioi hpsi)
  have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target := D.htarget i z hz2
  have hdg := (Work.Diff.STE.B3.densGood (I := I) (M := M) D i) z hzt
  have hevd : ∀ᶠ y in 𝓝 z, 0 < D.dens i y :=
    hdg.2.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi hdg.1)
  filter_upwards [hevχ, hevψ, hevd] with y hyχ hyψ hyd
  have hA : matA D i y ≠ 0 := by
    simp only [matA]
    exact mul_ne_zero (ne_of_gt hyψ) (Real.sqrt_pos.mpr hyd).ne'
  rw [R_eq_matA_mul_mat D i h a b y]
  exact (mul_div_cancel_left₀ (D.mat i h a b y) hA).symm

end B3

/-! ## 4. The arithmetic constant -/

/-- The constant multiplying `(1 + B) / c³`: it collects the bounds for the weight `matA` and
its derivatives (`Mψ` for `ψ`, `K` for the jets) and the lower bound `d₀` for the density. -/
private noncomputable def matJetCδ (Mψ K d₀ : ℝ) : ℝ :=
  Mψ ^ 2 / Real.sqrt d₀ + 2 * Mψ * K / d₀ + K ^ 2 / (d₀ * Real.sqrt d₀)

private lemma matJetCδ_nonneg {Mψ K d₀ : ℝ} (hM : 0 ≤ Mψ) (hK : 0 ≤ K) (hd : 0 < d₀) :
    0 ≤ matJetCδ Mψ K d₀ := by
  have hs : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd
  rw [matJetCδ]
  have h1 : 0 ≤ Mψ ^ 2 / Real.sqrt d₀ := div_nonneg (sq_nonneg _) hs.le
  have h2 : 0 ≤ 2 * Mψ * K / d₀ := div_nonneg (by positivity) hd.le
  have h3 : 0 ≤ K ^ 2 / (d₀ * Real.sqrt d₀) := div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- The arithmetic core of the passage from the division bound (which produces the factor
`1/δ + 2K/δ² + K²/δ³` with `δ = c √d₀`) to the shape `C / c³` of the statement. -/
private lemma matJetCδ_bound {c Mψ K d₀ : ℝ} (hc : 0 < c) (hd : 0 < d₀) (hK : 0 ≤ K)
    (hcM : c ≤ Mψ) :
    1 / (c * Real.sqrt d₀) + (K + K) / (c * Real.sqrt d₀) ^ 2
        + K ^ 2 / (c * Real.sqrt d₀) ^ 3 ≤ matJetCδ Mψ K d₀ / c ^ 3 := by
  have hs : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd
  have hc3 : 0 < c ^ 3 := by positivity
  rw [matJetCδ, le_div_iff₀ hc3, add_mul, add_mul]
  have e1 : 1 / (c * Real.sqrt d₀) * c ^ 3 = c ^ 2 / Real.sqrt d₀ := by
    field_simp
  have e2 : (K + K) / (c * Real.sqrt d₀) ^ 2 * c ^ 3 = 2 * K * c / d₀ := by
    have h1 : (c * Real.sqrt d₀) ^ 2 = c ^ 2 * d₀ := by rw [mul_pow, Real.sq_sqrt hd.le]
    rw [h1]
    field_simp
    ring
  have e3 : K ^ 2 / (c * Real.sqrt d₀) ^ 3 * c ^ 3 = K ^ 2 / (d₀ * Real.sqrt d₀) := by
    have h1 : (c * Real.sqrt d₀) ^ 3 = c ^ 3 * (d₀ * Real.sqrt d₀) := by
      rw [mul_pow, show (Real.sqrt d₀) ^ 3 = d₀ * Real.sqrt d₀ by
        rw [pow_succ, Real.sq_sqrt hd.le]]
    rw [h1]
    field_simp
  rw [e1, e2, e3]
  have hMnn : 0 ≤ Mψ := le_trans hc.le hcM
  have h1 : c ^ 2 / Real.sqrt d₀ ≤ Mψ ^ 2 / Real.sqrt d₀ :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hc.le hcM 2) hs.le
  have h2 : 2 * K * c / d₀ ≤ 2 * Mψ * K / d₀ :=
    div_le_div_of_nonneg_right (by nlinarith [hcM, hc.le, hMnn, hK]) hd.le
  linarith

/-! ## 5. The target -/

theorem mat_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (hk : Module.finrank ℝ E + 4 < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k h ≤ B →
      ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i →
      ∀ (c : ℝ), 0 < c → c ≤ D.psi i z →
      ∀ (a b : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E))), l.length ≤ 2 →
      |Work.Diff.STE.pdRList l (D.mat i h a b) z| ≤ C * (1 + B) / c ^ 3 := by
  classical
  obtain ⟨C_R, hC_R_nn, hC_R⟩ := pdList_le_sqrt_CSq_fin k (Module.finrank ℝ E) hk
  obtain ⟨C_D, hC_D_nn, hC_D⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A R : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
      (z : Fin (Module.finrank ℝ E) → ℝ) (δ K1 K2 : ℝ),
      0 < δ → δ ≤ |A z| → 0 ≤ K1 → 0 ≤ K2 →
      (∀ p : Fin (Module.finrank ℝ E), |pdR p A z| ≤ K1) →
      (∀ p q : Fin (Module.finrank ℝ E), |pdR q (pdR p A) z| ≤ K2) →
      ContDiffAt ℝ 2 A z → ContDiffAt ℝ 2 R z →
      ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
        |pdRList l (fun y => R y / A y) z|
          ≤ C * (|R z| + ∑ p : Fin (Module.finrank ℝ E), |pdR p R z|
              + ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
                  |pdR q (pdR p R) z|)
            * (1 / δ + (K1 + K2) / δ ^ 2 + K1 ^ 2 / δ ^ 3) := by
    exact Work.Diff.STE.Lead.pdRList_div_le
  obtain ⟨K, hK_nn, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i →
      |matA (I := I) (M := M) D i z| ≤ K ∧
      (∀ p : Fin (Module.finrank ℝ E),
        |pdR p (matA (I := I) (M := M) D i) z| ≤ K) ∧
      (∀ p q : Fin (Module.finrank ℝ E),
        |pdR q (pdR p (matA (I := I) (M := M) D i)) z| ≤ K) := by
    exact Work.Diff.STE.Lead.matA_jets (I := I) (M := M) D
  obtain ⟨Mψ, hMψ_nn, hMψ⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), D.psi i z ≤ M := by
    exact Work.Diff.STE.Lead.psi_le_const (I := I) (M := M) D
  obtain ⟨d₀, hd₀pos, hd₀le⟩ := Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
    (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn_nn : 0 ≤ n := by rw [hn]; positivity
  refine ⟨C_D * (1 + n + n ^ 2) * C_R * matJetCδ Mψ K d₀, ?_, ?_⟩
  · have hn1 : (0 : ℝ) ≤ 1 + n + n ^ 2 := by nlinarith [hn_nn, sq_nonneg n]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC_D_nn hn1) hC_R_nn)
      (matJetCδ_nonneg hMψ_nn hK_nn hd₀pos)
  · intro B h hchart hB i z hz c hc hcl a b l hl
    have hz2 : ‖z‖ ≤ 2 * D.σ i := by linarith [D.hσ i]
    have hBNN : 0 ≤ D.BNorm k h := by
      simp only [B3Data.BNorm]
      exact Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun a' _ =>
        Finset.sum_nonneg fun b' _ => CSq_nonneg k _
    have hBnn : 0 ≤ B := le_trans hBNN hB
    -- the density and the weight at `z`
    have hdens : d₀ ≤ D.dens i z := hd₀le i z hz2
    have hsqrt : Real.sqrt d₀ ≤ Real.sqrt (D.dens i z) := Real.sqrt_le_sqrt hdens
    have hpsi_nn : 0 ≤ D.psi i z := le_trans hc.le hcl
    have hmatA_nn : 0 ≤ matA D i z := by
      simp only [matA]
      exact mul_nonneg hpsi_nn (Real.sqrt_nonneg _)
    have hmatA_ge : c * Real.sqrt d₀ ≤ matA D i z := by
      simp only [matA]
      exact mul_le_mul hcl hsqrt (Real.sqrt_nonneg _) hpsi_nn
    have hsdpos : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd₀pos
    have hδpos : 0 < c * Real.sqrt d₀ := mul_pos hc hsdpos
    have hδle : c * Real.sqrt d₀ ≤ |matA D i z| := by
      rw [abs_of_nonneg hmatA_nn]
      exact hmatA_ge
    -- regularity of the weight
    have hA2 : ContDiffAt ℝ 2 (matA D i) z := by
      have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
        D.htarget i z hz2
      have hdg := (Work.Diff.STE.B3.densGood (I := I) (M := M) D i) z hzt
      have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Real.sqrt (D.dens i y)) z :=
        (Real.contDiffAt_sqrt hdg.1.ne').comp z hdg.2
      have hψ : ContDiffAt ℝ (⊤ : ℕ∞) (D.psi i) z := (D.psi_contDiff i).contDiffAt
      exact (hψ.mul hd).of_le (WithTop.coe_le_coe.mpr le_top)
    have hR2 : ContDiffAt ℝ 2 (D.R i h a b) z :=
      ((Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hchart i a b).contDiffAt).of_le
        (by norm_num)
    -- the jet bound for the localised component
    have hRle : ∀ (l : List (Fin (Module.finrank ℝ E))), l.length ≤ 2 →
        |pdRList l (D.R i h a b) z| ≤ C_R * (1 + B) := fun l hl' =>
      le_trans (R_jet_le D k C_R hC_R hC_R_nn h hchart i a b z hz l hl')
        (mul_le_mul_of_nonneg_left (by linarith) hC_R_nn)
    have hsum : |D.R i h a b z| + (∑ p : Fin (Module.finrank ℝ E), |pdR p (D.R i h a b) z|)
        + (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
            |pdR q (pdR p (D.R i h a b)) z|)
        ≤ (1 + n + n ^ 2) * (C_R * (1 + B)) := by
      have h0 : |D.R i h a b z| ≤ C_R * (1 + B) := hRle [] (by simp)
      have h1 : (∑ p : Fin (Module.finrank ℝ E), |pdR p (D.R i h a b) z|)
          ≤ n * (C_R * (1 + B)) := by
        calc (∑ p : Fin (Module.finrank ℝ E), |pdR p (D.R i h a b) z|)
            ≤ ∑ _p : Fin (Module.finrank ℝ E), C_R * (1 + B) :=
              Finset.sum_le_sum fun p _ => hRle [p] (by simp)
          _ = n * (C_R * (1 + B)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn]
      have h2 : (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
            |pdR q (pdR p (D.R i h a b)) z|)
          ≤ n * (n * (C_R * (1 + B))) := by
        calc (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
              |pdR q (pdR p (D.R i h a b)) z|)
            ≤ ∑ _p : Fin (Module.finrank ℝ E), ∑ _q : Fin (Module.finrank ℝ E),
                C_R * (1 + B) :=
              Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hRle [q, p] (by simp)
          _ = n * (n * (C_R * (1 + B))) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn]
      have := add_le_add (add_le_add h0 h1) h2
      calc |D.R i h a b z| + (∑ p, |pdR p (D.R i h a b) z|)
            + (∑ p, ∑ q, |pdR q (pdR p (D.R i h a b)) z|)
          ≤ C_R * (1 + B) + n * (C_R * (1 + B)) + n * (n * (C_R * (1 + B))) := this
        _ = (1 + n + n ^ 2) * (C_R * (1 + B)) := by ring
    -- the division bound
    have hDIV := hC_D (matA D i) (D.R i h a b) z (c * Real.sqrt d₀) K K hδpos hδle hK_nn hK_nn
      (fun p => (hK i z hz).2.1 p) (fun p q => (hK i z hz).2.2 p q) hA2 hR2 l hl
    have hfac := matJetCδ_bound (c := c) (Mψ := Mψ) (K := K) (d₀ := d₀) hc hd₀pos hK_nn
      (hcl.trans (hMψ i z))
    have hCδ_nn : 0 ≤ matJetCδ Mψ K d₀ := matJetCδ_nonneg hMψ_nn hK_nn hd₀pos
    have hCRB_nn : 0 ≤ C_R * (1 + B) := mul_nonneg hC_R_nn (by linarith)
    have hcongr := pdRList_congr_of_eventuallyEq (mat_eventuallyEq D h i a b z hz hc hcl) l
    calc |pdRList l (D.mat i h a b) z|
        = |pdRList l (fun y => D.R i h a b y / matA D i y) z| := by rw [hcongr]
      _ ≤ C_D * (|D.R i h a b z| + ∑ p : Fin (Module.finrank ℝ E), |pdR p (D.R i h a b) z|
            + ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
                |pdR q (pdR p (D.R i h a b)) z|)
          * (1 / (c * Real.sqrt d₀) + (K + K) / (c * Real.sqrt d₀) ^ 2
              + K ^ 2 / (c * Real.sqrt d₀) ^ 3) := hDIV
      _ ≤ C_D * ((1 + n + n ^ 2) * (C_R * (1 + B))) * (matJetCδ Mψ K d₀ / c ^ 3) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsum hC_D_nn) hfac ?_ ?_
          · have h1 := hK_nn
            positivity
          · exact mul_nonneg hC_D_nn (mul_nonneg (by nlinarith [hn_nn, sq_nonneg n]) hCRB_nn)
      _ = (C_D * (1 + n + n ^ 2) * C_R * matJetCδ Mψ K d₀) * (1 + B) / c ^ 3 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring

end Work.Diff.STE.Lead
