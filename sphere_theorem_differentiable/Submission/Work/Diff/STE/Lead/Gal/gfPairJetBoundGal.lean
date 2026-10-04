import Mathlib
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.mat_eq_inv_zeta_sum
import Submission.Work.Diff.STE.B3.mat_recon_gen
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.Gtot_contDiffOn
import Submission.Work.Diff.STE.Lead.Gal.gardAuxGal
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec
import Submission.Work.Diff.STE.B3.norm_multilinear_le_of_basis
import Submission.Work.Diff.STE.B3.pdVec_mul_comp_le
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.flat.jetP_iteratedFDeriv_bound
import Submission.Work.Diff.STE.D.transMap_contDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet bound for the coordinate-frame chart matrix `Gf`

`Work.Diff.STE.B3.Gf_pair_jet_bound`: the flat jets of the coordinate-frame chart matrix
`Gf D h j · a b` of a section `h` on the ball `‖z‖ ≤ 2 σ j + ρ` are bounded by `C · K`, where `K`
dominates the flat jets (of order `≤ k + 1`) of the `g₀`-orthonormal-frame chart matrices
`D.mat i h c d` on the closed balls of radius `2 σ i`.

## Route

At a point `z` of the ball with `1 / √(card ι₀) ≤ ζ j' (pt j z)`, the orthonormal frame `e j' ·` is
available at the point `p = D.pt j z` (because `ζ j' p ≠ 0` forces `pt j z ∈ source x₀ j'` with
`‖coord j' (pt j z)‖ < σ j'`), so the *pointwise reconstruction* of a section in an orthonormal frame
gives the identity

`Gf D h j z a b = Σ c, Σ d, trCoef D j j' z a c * trCoef D j j' z b d * D.mat j' h c d (xiMap D j j' z)`

(`Gf_eq_sum_mat` below; it is `mat_recon_gen` with the weight `ζ j'` and the square root of the
density cancelled).

The right hand side is a sum of *products with a composition*: with
`A_cd y = trCoef D j j' y a c * trCoef D j j' y b d` (a `D`-dependent coefficient, smooth on the
flat region where the chart at `x₀ j` is genuine) and `W y = xiMap D j j' y` (the chart transition),
the `m`-jet of each summand is controlled by the Leibniz/Faà di Bruno estimate `pdVec_mul_comp_le`
from the jets of `A_cd` at `z`, of `W` at `z` and of `D.mat j' h c d` at `W z`.

The two geometric factors `A_cd` and `W` are smooth only on the region
`{y | flatToE x₀ j y ∈ target x₀ j ∧ 0 < ζ j' (pt j y)}`, so they are replaced by their products
with a cut-off `θ` (`exists_bump_ext`) that equals `1` near every point of the ball `‖z‖ ≤ 2 σ j + ρ`
at which `ζ j' (pt j ·) ≥ 1 / √(card ι₀)` and vanishes near the complement of the smoothness region;
the cut-off makes the products globally smooth, which is what `pdVec_mul_comp_le` requires.  The
`h`-dependent factor `D.mat j' h c d` is cut off radially as well (it is only smooth on the flat
target region of the chart at `x₀ j'`), and *its* jets at `W z` are estimated directly by the
hypothesis `hjet` via `iteratedFDeriv_le_of_pdVec`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead.Gal

-- everything else of the chart-matrix technology lives in the `B3` namespace.
open Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. Generic analytic helpers -/

/-- If `f` takes values in a normed space, is `C^∞` on the open set `U` and the closed support of
the scalar function `g` lies in `U`, then `g • f` is globally `C^∞`. -/
private lemma contDiff_smul_of_tsupport_subset {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set (Fin n → ℝ)} (hU : IsOpen U) {f : (Fin n → ℝ) → F}
    {g : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => g y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hg.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hz))
  · have hz' : z ∉ tsupport g := fun h => hz (hsupp h)
    have hg0 : g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hz'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hzero : (fun y => g y • f y) =ᶠ[𝓝 z] fun _ => (0 : F) := by
      filter_upwards [hg0] with y hy
      rw [hy, zero_smul]
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hzero

/-- Iterated complex partial derivatives of eventually equal functions agree. -/
private lemma pdList_eventuallyEq_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} {z : ι → ℝ} (h : f =ᶠ[𝓝 z] g) :
    ∀ l : List ι, Work.Diff.STE.pdList l f =ᶠ[𝓝 z] Work.Diff.STE.pdList l g := by
  intro l
  induction l with
  | nil => exact h
  | cons i l ih =>
    have hfd : fderiv ℝ (Work.Diff.STE.pdList l f) =ᶠ[𝓝 z] fderiv ℝ (Work.Diff.STE.pdList l g) :=
      ih.fderiv
    filter_upwards [hfd] with y hy
    exact congrArg (fun (L : (ι → ℝ) →L[ℝ] ℂ) => L (Pi.single i 1)) hy

/-- Iterated complex partial derivatives of eventually equal functions agree at the point. -/
private lemma pdVec_congr_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {f g : (ι → ℝ) → ℂ} {z : ι → ℝ} (h : f =ᶠ[𝓝 z] g) (l : Fin m → ι) :
    Work.Diff.STE.pdVec m l f z = Work.Diff.STE.pdVec m l g z := by
  rw [Work.Diff.STE.pdVec]
  exact (pdList_eventuallyEq_of_eventuallyEq h (List.ofFn l)).eq_of_nhds

/-- **A bound for the `pdVec` of a finite sum** of globally smooth complex functions: the norm is at
most the sum of the norms of the summands. -/
private lemma pdVec_finset_sum_le {n m : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → (Fin n → ℝ) → ℂ) (hF : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (F k))
    (β : Fin m → Fin n) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.pdVec m β (fun y => ∑ k, F k y) z‖
      ≤ ∑ k, ‖Work.Diff.STE.pdVec m β (F k) z‖ := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k, F k y) := ContDiff.sum fun k _ => hF k
  rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ hG z β]
  rw [iteratedFDeriv_sum (𝕜 := ℝ) (u := Finset.univ) (fun k _ => (hF k).of_le
      (WithTop.coe_le_coe.mpr le_top : ((m : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))]
  rw [Finset.sum_apply z Finset.univ (fun j => iteratedFDeriv ℝ m (F j))]
  rw [ContinuousMultilinearMap.sum_apply Finset.univ
    (fun c => (iteratedFDeriv ℝ m (F c)) z) (fun j => Pi.single (β j) 1)]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => by
    rw [← Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m (F k) (hF k) z]))

/-- **A bound for the `pdVec` of a double finite sum** of globally smooth complex functions: the
norm is at most the double sum of the norms of the summands. -/
private lemma pdVec_sum2_le {n m : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → κ → (Fin n → ℝ) → ℂ) (hF : ∀ i k, ContDiff ℝ (⊤ : ℕ∞) (F i k))
    (β : Fin m → Fin n) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.pdVec m β (fun y => ∑ i, ∑ k, F i k y) z‖
      ≤ ∑ i, ∑ k, ‖Work.Diff.STE.pdVec m β (F i k) z‖ := by
  have hinner : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k, F i k y) :=
    fun i => ContDiff.sum fun k _ => hF i k
  refine (pdVec_finset_sum_le (fun i => fun y => ∑ k, F i k y) hinner β z).trans ?_
  exact Finset.sum_le_sum fun i _ => pdVec_finset_sum_le (F i) (fun k => hF i k) β z

/-! ## 2. The flat region where the chart at `x₀ j` is genuine -/

/-- The set of flat coordinates at which the chart at `x₀ j` is genuine (its inverse is honest). -/
private def flatReg (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target}

private lemma isOpen_flatReg (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    IsOpen (flatReg (I := I) (M := M) D j) :=
  (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
    (contDiff_flatToE (I := I) (x₀ := D.x₀ j)).continuous

/-- `z ↦ ζ i' (pt j z)` is smooth on the region where the chart at `x₀ j` is genuine. -/
private lemma contDiffOn_zeta_pt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j i' : ι₀) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => D.ζ i' (D.pt j z)) (flatReg (I := I) (M := M) D j) :=
  fun z hz => (contMDiffAt_iff_contDiffAt.mp
    (((D.hζsm i').contMDiffAt).comp z (D.contMDiffAt_pt j hz))).contDiffWithinAt

/-! ## 3. The cut-off that globalises the coefficient and the chart transition -/

/-- **The cut-off of the covering argument.**  There is a globally `C^∞` function `θ` on the flat
coordinates which

* vanishes near every point outside the region where the chart at `x₀ j` is genuine,
* vanishes near every point of that region at which `ζ j' (pt j ·) ≤ 0`,
* equals `1` near every point of the closed ball `‖z‖ ≤ 2 σ j + ρ` at which
  `1 / √(card ι₀) ≤ ζ j' (pt j ·)`. -/
private lemma exists_bump_ext (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j j' : ι₀)
    (ρ : ℝ) (hρ : 0 < ρ)
    (htgt : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + ρ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ∃ θ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ,
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∉ (extChartAt I (D.x₀ j)).target →
        θ =ᶠ[𝓝 z] fun _ => 0) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ,
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target →
        D.ζ j' (D.pt j z) ≤ 0 → θ =ᶠ[𝓝 z] fun _ => 0) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + ρ →
        1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j' (D.pt j z) → θ =ᶠ[𝓝 z] fun _ => 1) := by
  classical
  have hU : IsOpen (flatReg (I := I) (M := M) D j) := isOpen_flatReg (I := I) (M := M) D j
  have hsub : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + ρ) ⊆
      flatReg (I := I) (M := M) D j := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact htgt z hz
  obtain ⟨ρ', hρ'pos, hρ'⟩ :=
    (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + ρ))
      |>.exists_thickening_subset_open hU hsub
  -- the radius of the ball and the radii of the plateau and of the support of the radial factor
  set a : ℝ := 2 * D.σ j + ρ with ha
  have hapos : 0 < a := by rw [ha]; linarith [D.hσ j, hρ]
  set a' : ℝ := a + ρ' / 4 with ha'
  set b : ℝ := a + ρ' / 2 with hb
  have haa' : a < a' := by rw [ha']; linarith
  have ha'b : a' < b := by rw [ha', hb]; linarith
  have hbnn : 0 ≤ b := by rw [hb]; linarith [hapos, hρ'pos]
  have hden : 0 < b ^ 2 - a' ^ 2 := by nlinarith [haa', ha'b, hapos]
  -- the closed `b`-ball is still inside the region where the chart is genuine
  have hsub' : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b ⊆
      flatReg (I := I) (M := M) D j := by
    intro z hz
    refine hρ' ?_
    rw [Metric.mem_thickening_iff]
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    by_cases hz' : ‖z‖ ≤ a
    · exact ⟨z, by rw [Metric.mem_closedBall, dist_zero_right]; exact hz',
        by rw [dist_self]; exact hρ'pos⟩
    · push_neg at hz'
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hapos hz'.le
      refine ⟨(a / ‖z‖) • z, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hapos.le (norm_nonneg _))]
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hzpos), mul_one]
      · rw [dist_eq_norm]
        have h1 : z - (a / ‖z‖) • z = (1 - a / ‖z‖) • z := by rw [sub_smul, one_smul]
        rw [h1, norm_smul, Real.norm_eq_abs]
        have h2 : 0 < 1 - a / ‖z‖ := by
          rw [sub_pos, div_lt_one hzpos]
          rw [hb] at hz
          linarith
        rw [abs_of_pos h2]
        have h3 : (1 - a / ‖z‖) * ‖z‖ = ‖z‖ - a := by
          rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hzpos)]
        rw [h3]
        rw [hb] at hz
        linarith
  -- the one-dimensional cut-off of the radial factor
  set ψ : ℝ → ℝ := fun x => Real.smoothTransition ((b ^ 2 - x ^ 2) / (b ^ 2 - a' ^ 2)) with hψ
  have hψsm : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    rw [hψ]
    refine Real.smoothTransition.contDiff.comp ?_
    exact (contDiff_const.sub (contDiff_id.pow 2)).div_const _
  have hψone : ∀ x : ℝ, |x| ≤ a' → ψ x = 1 := by
    intro x hx
    rw [hψ]
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ hden]
    have hx2 : x ^ 2 ≤ a' ^ 2 := by nlinarith [abs_le.mp hx]
    linarith
  have hψzero : ∀ x : ℝ, b ≤ |x| → ψ x = 0 := by
    intro x hx
    rw [hψ]
    refine Real.smoothTransition.zero_of_nonpos ?_
    refine div_nonpos_of_nonpos_of_nonneg ?_ hden.le
    have h1 : b ^ 2 ≤ |x| ^ 2 := by nlinarith [hx, hbnn]
    have h2 : |x| ^ 2 = x ^ 2 := by rw [sq, sq, abs_mul_abs_self]
    linarith
  -- the radial factor
  set θrad : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun y => ∏ k, ψ (y k) with hθrad
  have hθradsm : ContDiff ℝ (⊤ : ℕ∞) θrad := by
    rw [hθrad]
    exact contDiff_prod fun k _ => hψsm.comp (by fun_prop)
  have hθradone : ∀ y : Fin (Module.finrank ℝ E) → ℝ, (∀ k, |y k| ≤ a') → θrad y = 1 := by
    intro y hy
    rw [hθrad]
    exact Finset.prod_eq_one fun k _ => hψone (y k) (hy k)
  have hθradsupp : Function.support θrad ⊆
      Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk⟩ : ∃ k, b < |y k| := by
      by_contra hc
      push_neg at hc
      exact absurd hlt (not_lt.mpr ((pi_norm_le_iff_of_nonneg hbnn).mpr
        (fun k => by simpa only [Real.norm_eq_abs] using hc k)))
    exact (Function.mem_support.mp hy) (by
      rw [hθrad]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (hψzero (y k) hk.le))
  have hθradtsup : tsupport θrad ⊆ flatReg (I := I) (M := M) D j :=
    (closure_minimal hθradsupp Metric.isClosed_closedBall).trans hsub'
  -- the threshold cut-off in `ζ j' ∘ pt j`
  set τ : ℝ := 1 / Real.sqrt (Fintype.card ι₀) with hτ
  have hcardpos : 0 < Fintype.card ι₀ := Fintype.card_pos_iff.mpr ⟨j'⟩
  have hτpos : 0 < τ := by
    rw [hτ]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hcardpos))
  set δ₀ : ℝ := τ / 4 with hδ₀
  set δ₁ : ℝ := τ / 2 with hδ₁
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; linarith
  have hδ₀δ₁ : δ₀ < δ₁ := by rw [hδ₀, hδ₁]; linarith
  set θz : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun y => Real.smoothTransition ((D.ζ j' (D.pt j y) - δ₀) / (δ₁ - δ₀)) with hθz
  have hθzsm : ContDiffOn ℝ (⊤ : ℕ∞) θz (flatReg (I := I) (M := M) D j) := by
    rw [hθz]
    exact Real.smoothTransition.contDiff.comp_contDiffOn
      (((contDiffOn_zeta_pt (I := I) (M := M) D j j').sub contDiffOn_const).div_const _)
  have hθzone : ∀ y : Fin (Module.finrank ℝ E) → ℝ, δ₁ ≤ D.ζ j' (D.pt j y) → θz y = 1 := by
    intro y hy
    rw [hθz]
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < δ₁ - δ₀)]
    linarith
  have hθzzero : ∀ y : Fin (Module.finrank ℝ E) → ℝ, D.ζ j' (D.pt j y) ≤ δ₀ → θz y = 0 := by
    intro y hy
    rw [hθz]
    refine Real.smoothTransition.zero_of_nonpos ?_
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  -- the cut-off
  refine ⟨fun y => θrad y * θz y, ?_, ?_, ?_, ?_⟩
  · exact contDiff_smul_of_tsupport_subset hU hθzsm hθradsm hθradtsup
  · intro z hz
    have hz' : z ∉ tsupport θrad := fun h => hz (hθradtsup h)
    have hz0 : θrad =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport θrad).isOpen_compl.mem_nhds hz'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    filter_upwards [hz0] with y hy
    rw [hy, zero_mul]
  · intro z hzt hζ
    have hcont : ContinuousAt (fun y => D.ζ j' (D.pt j y)) z :=
      ((contDiffOn_zeta_pt (I := I) (M := M) D j j').contDiffAt (hU.mem_nhds hzt)).continuousAt
    have hev : ∀ᶠ y in 𝓝 z, D.ζ j' (D.pt j y) < δ₀ :=
      hcont.eventually (IsOpen.mem_nhds isOpen_Iio (lt_of_le_of_lt hζ hδ₀pos))
    filter_upwards [hev] with y hy
    rw [hθzzero y hy.le, mul_zero]
  · intro z hz hζ
    have hzt : flatReg (I := I) (M := M) D j z := hsub (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
    have hlt : ‖z‖ < a' := lt_of_le_of_lt hz haa'
    have hk : ∀ᶠ w in 𝓝 z, ∀ k, |w k| ≤ a' := by
      filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hlt)] with w hw
      intro k
      have h1 : |w k - z k| ≤ ‖w - z‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (w - z) k
      have h2 : ‖w - z‖ < a' - ‖z‖ := by
        rw [Metric.mem_ball, dist_eq_norm] at hw
        linarith
      have h3 : |z k| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z k
      have h4 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      have h5 := abs_le.mp h3
      rw [abs_le]
      constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
    have hz1 : ∀ᶠ w in 𝓝 z, δ₁ ≤ D.ζ j' (D.pt j w) := by
      have hcont : ContinuousAt (fun y => D.ζ j' (D.pt j y)) z :=
        ((contDiffOn_zeta_pt (I := I) (M := M) D j j').contDiffAt (hU.mem_nhds hzt)).continuousAt
      have hlt : δ₁ < D.ζ j' (D.pt j z) := by
        rw [hδ₁]
        linarith
      filter_upwards [hcont.eventually (IsOpen.mem_nhds isOpen_Ioi hlt)] with w hw
      exact le_of_lt hw
    filter_upwards [hk, hz1] with w hwk hw1
    rw [hθradone w hwk, hθzone w hw1, one_mul]


/-- A function vanishing near every point outside `U` has its topological support in `U`. -/
private lemma tsupport_subset_of_eventuallyEq_zero {n : ℕ} {θ : (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} (h : ∀ z, z ∉ U → θ =ᶠ[𝓝 z] 0) : tsupport θ ⊆ U := by
  intro z hz
  by_contra hzU
  have hmem : {y | θ y = 0} ∈ 𝓝 z := h z hzU
  obtain ⟨t, htv, hto, hzt⟩ := _root_.mem_nhds_iff.mp hmem
  have hsupp : Function.support θ ⊆ tᶜ := by
    intro y hy hy'
    exact (Function.mem_support.mp hy) (htv hy')
  exact (closure_minimal hsupp hto.isClosed_compl) hz (by simpa using hzt)

/-! ## 2bis. The flat jets of the orthonormal-frame chart matrix -/

/-- The chart matrix of a section in the orthonormal frame `e i` is smooth on the chart target
(this is the `T`-free version of the corresponding lemma of the `B3` area, using the public
`section_contMDiffAt_of_chartData`). -/
private lemma matChart_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target := by
  have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x :=
    fun x => section_contMDiffAt_of_chartData (I := I) (M := M) hh x
  have hmat : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i a x) (D.e i b x)) univ := by
    intro x _
    have hψ := (hsec x).contMDiffWithinAt (s := univ)
    have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i a)) univ x :=
      (D.hesm i a).contMDiffAt.contMDiffWithinAt
    have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i b)) univ x :=
      (D.hesm i b).contMDiffAt.contMDiffWithinAt
    have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
    simp only [contMDiffWithinAt_totalSpace] at hres
    exact hres.2
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => h ((extChartAt I (D.x₀ i)).symm y)
        (D.e i a ((extChartAt I (D.x₀ i)).symm y))
        (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
    hmat.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
      (fun y _ => mem_univ _)
  exact hcomp.contDiffOn

/-! ## 2ter. The reconstruction identity in the orthonormal frame `e j'` -/

/-- **The chart matrix in the coordinate frame is the double sum of the chart matrix in the
orthonormal frame `e j'`**, at every point of the flat ball at which the weight `ζ j'` at `pt j z`
does not vanish.

This is `mat_recon_gen` (the pointwise reconstruction at the chart `j'`) with the weight `ζ j'` and
the square root of the volume density cancelled against the factor `ψ j' √(dens j')` inside the
localised component `D.R j'`. -/
private lemma Gf_eq_sum_mat (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j j' : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E))
    (hζ : D.ζ j' (D.pt j z) ≠ 0) :
    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
      = ∑ c, ∑ d, Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' z a c
          * Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' z b d
          * D.mat j' h c d (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z) := by
  obtain ⟨hsrc, hlt⟩ := D.hζsupp j' (D.pt j z) hζ
  have h2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)‖ ≤ 2 * D.σ j' := by
    have hσ := D.hσ j'
    linarith
  have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j')
      (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)) ∈ (extChartAt I (D.x₀ j')).target :=
    D.htarget j' _ h2
  have hdens : 0 < D.dens j' (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)) :=
    dens_pos_of_mem_target D j' htgt
  have hsqrt : Real.sqrt (D.dens j' (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z))) ≠ 0 :=
    (Real.sqrt_pos.mpr hdens).ne'
  have hχ : D.χ j' (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)) = 1 :=
    D.hχ1 j' _ (le_of_lt hlt)
  have hpt : D.pt j' (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)) = D.pt j z :=
    D.pt_coord j' hsrc
  have hrec := mat_recon_gen (I := I) (M := M) D h j' (D.pt j z)
    (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
    (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b) hζ
  have hGf : Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
      = h (D.pt j z) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
          (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b) := rfl
  rw [hGf, hrec]
  simp only [Work.Diff.STE.B3.trCoef, Work.Diff.STE.B3.xiMap]
  have hsum : (∑ c, ∑ d,
        ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
            (D.e j' c (D.pt j z)))
          * ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b)
            (D.e j' d (D.pt j z)))
          * D.R j' h c d (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)))
      = (D.ζ j' (D.pt j z)
          * Real.sqrt (D.dens j' (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z))))
        * ∑ c, ∑ d,
          ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
            (D.e j' c (D.pt j z)))
          * ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b)
            (D.e j' d (D.pt j z)))
          * D.mat j' h c d (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [B3Data.R, B3Data.psi, hχ, hpt]
    ring
  rw [hsum]
  rw [show (D.ζ j' (D.pt j z))⁻¹
        * (Real.sqrt (D.dens j' (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z))))⁻¹
        * ((D.ζ j' (D.pt j z)
            * Real.sqrt (D.dens j' (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z))))
          * ∑ c, ∑ d,
            ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
              (D.e j' c (D.pt j z)))
            * ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b)
              (D.e j' d (D.pt j z)))
            * D.mat j' h c d (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)))
      = ∑ c, ∑ d,
            ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
              (D.e j' c (D.pt j z)))
            * ((g₀.inner (D.pt j z)) (Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b)
              (D.e j' d (D.pt j z)))
            * D.mat j' h c d (Work.Diff.STE.coord (I := I) (D.x₀ j') (D.pt j z)) from by
    field_simp]

theorem Gf_pair_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (j j' : ι₀)
    (ρ : ℝ) (hρ : 0 < ρ)
    (htgt : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + ρ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (K : ℝ) (hK : 0 ≤ K)
        (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
          (β : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
        ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ j + ρ →
          1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j' (D.pt j z) →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ C * K := by
  classical
  by_cases hn0 : Module.finrank ℝ E = 0
  · refine ⟨0, le_rfl, ?_⟩
    intro h hsym hsmooth K hK hjet m hm β z a b hz hζ
    have hlt : a.val < 0 := by rw [← hn0]; exact a.isLt
    exact absurd hlt (by simp)
  have hn : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero hn0
  -- ## the cut-off of the transition region
  obtain ⟨θ, hθsm, hθ0tgt, hθ0ζ, hθ1⟩ := exists_bump_ext (I := I) (M := M) D j j' ρ hρ htgt
  have htsupθ : tsupport θ ⊆ flatReg (I := I) (M := M) D j ∩ {y | 0 < D.ζ j' (D.pt j y)} :=
    tsupport_subset_of_eventuallyEq_zero (fun z hz => by
      by_cases hzf : z ∈ flatReg (I := I) (M := M) D j
      · exact hθ0ζ z hzf (le_of_not_gt (fun h => hz ⟨hzf, h⟩))
      · exact hθ0tgt z hzf)
  -- ## the radial cut-off of the `h`-dependent factor
  set c₁ : ℝ := D.σ j' with hc₁
  set c₂ : ℝ := 2 * D.σ j' with hc₂
  have hc₁pos : 0 < c₁ := D.hσ j'
  have hc₂nn : 0 ≤ c₂ := by rw [hc₂]; linarith [D.hσ j']
  have hdenR : 0 < c₂ ^ 2 - c₁ ^ 2 := by rw [hc₂, hc₁]; nlinarith [D.hσ j']
  set ψR : ℝ → ℝ := fun x => Real.smoothTransition ((c₂ ^ 2 - x ^ 2) / (c₂ ^ 2 - c₁ ^ 2)) with hψR
  have hψRsm : ContDiff ℝ (⊤ : ℕ∞) ψR := by
    rw [hψR]
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const _)
  have hψRone : ∀ x : ℝ, |x| ≤ c₁ → ψR x = 1 := by
    intro x hx
    rw [hψR]
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ hdenR]
    have hx2 : x ^ 2 ≤ c₁ ^ 2 := by nlinarith [abs_le.mp hx]
    linarith
  have hψRzero : ∀ x : ℝ, c₂ ≤ |x| → ψR x = 0 := by
    intro x hx
    rw [hψR]
    refine Real.smoothTransition.zero_of_nonpos ?_
    refine div_nonpos_of_nonpos_of_nonneg ?_ hdenR.le
    have h1 : c₂ ^ 2 ≤ |x| ^ 2 := by nlinarith [hx, hc₂nn]
    have h2 : |x| ^ 2 = x ^ 2 := by rw [sq, sq, abs_mul_abs_self]
    linarith
  set θR : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun w => ∏ k, ψR (w k) with hθR
  have hθRsm : ContDiff ℝ (⊤ : ℕ∞) θR := by
    rw [hθR]
    exact contDiff_prod fun k _ => hψRsm.comp (by fun_prop)
  have hθRone : ∀ w : Fin (Module.finrank ℝ E) → ℝ, (∀ k, |w k| ≤ c₁) → θR w = 1 := by
    intro w hw
    rw [hθR]
    exact Finset.prod_eq_one fun k _ => hψRone (w k) (hw k)
  have hθRsupp : Function.support θR ⊆ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) c₂ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk⟩ : ∃ k, c₂ < |w k| := by
      by_contra hc
      push_neg at hc
      exact absurd hlt (not_lt.mpr ((pi_norm_le_iff_of_nonneg hc₂nn).mpr
        (fun k => by simpa only [Real.norm_eq_abs] using hc k)))
    exact (Function.mem_support.mp hw) (by
      rw [hθR]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (hψRzero (w k) hk.le))
  have hθRtsup : tsupport θR ⊆ {w | Work.Diff.STE.flatToE (I := I) (D.x₀ j') w ∈
      (extChartAt I (D.x₀ j')).target} :=
    (closure_minimal hθRsupp Metric.isClosed_closedBall).trans (fun w hw => by
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      rw [hc₂] at hw
      exact D.htarget j' w hw)
  -- ## the coefficient and the transition map
  set Φ : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) :=
    fun y => θ y • Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y with hΦ
  set Acoef : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun p q y => θ y • (((Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' y p.1 p.2
        * Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' y q.1 q.2 : ℝ) : ℂ)) with hAcoef
  have hOpenW : IsOpen (flatReg (I := I) (M := M) D j ∩
      {y | D.pt j y ∈ (extChartAt I (D.x₀ j')).source}) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hcont : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ => D.pt j y) y :=
      (D.contMDiffAt_pt j hy.1).continuousAt
    exact Filter.inter_mem ((isOpen_flatReg (I := I) (M := M) D j).mem_nhds hy.1)
      (hcont.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) (D.x₀ j')).mem_nhds hy.2))
  have hxiOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y)
      (flatReg (I := I) (M := M) D j ∩ {y | D.pt j y ∈ (extChartAt I (D.x₀ j')).source}) := by
    refine contDiffOn_of_isOpen_contDiffAt hOpenW (fun y hy => ?_)
    exact Work.Diff.STE.D.transMap_contDiffAt (I := I) (M := M) D j' j y hy.1 hy.2
  have hΦsm : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    rw [hΦ]
    refine contDiff_smul_of_tsupport_subset hOpenW hxiOn hθsm ?_
    exact htsupθ.trans (fun y hy => ⟨hy.1, (D.hζsupp j' (D.pt j y) (ne_of_gt hy.2)).1⟩)
  have hcoefOn : ∀ p q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => ((Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' y p.1 p.2
          * Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' y q.1 q.2 : ℝ) : ℂ))
        (flatReg (I := I) (M := M) D j) := by
    intro p q
    refine contDiffOn_of_isOpen_contDiffAt (isOpen_flatReg (I := I) (M := M) D j)
      (fun y hy => ?_)
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp y
      ((contDiffAt_trCoef (I := I) (M := M) D j j' p.1 p.2 hy).mul
        (contDiffAt_trCoef (I := I) (M := M) D j j' q.1 q.2 hy))
  have hAsm : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (Acoef p q) := by
    intro p q
    rw [hAcoef]
    exact contDiff_smul_of_tsupport_subset (isOpen_flatReg (I := I) (M := M) D j)
      (hcoefOn p q) hθsm (htsupθ.trans Set.inter_subset_left)
  -- ## the uniform jet bounds
  have hKc : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + ρ)) :=
    isCompact_closedBall _ _
  have hKcU : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + ρ) ⊆ Set.univ :=
    fun _ _ => Set.mem_univ _
  obtain ⟨MD₀, hMD₀nn, hMD₀⟩ := Work.Diff.STE.flat.compact_iteratedFDeriv_bound Φ isOpen_univ
    hΦsm.contDiffOn hKc hKcU k
  set MD : ℝ := max 1 MD₀ with hMD
  have hMDnn : 0 ≤ MD := le_trans zero_le_one (le_max_left 1 MD₀)
  have hMD1 : 1 ≤ MD := le_max_left 1 MD₀
  have hMDle : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + ρ),
      ∀ i : ℕ, i ≤ k → ‖iteratedFDeriv ℝ i Φ z‖ ≤ MD :=
    fun z hz i hi => (hMD₀ z hz i hi).trans (le_max_right 1 MD₀)
  have hMAex : ∀ p q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + ρ),
        ∀ i : ℕ, i ≤ k → ‖iteratedFDeriv ℝ i (Acoef p q) z‖ ≤ M :=
    fun p q => Work.Diff.STE.flat.compact_iteratedFDeriv_bound (Acoef p q) isOpen_univ
      (hAsm p q).contDiffOn hKc hKcU k
  choose MAfun hMAnn hMAle using hMAex
  set MA : ℝ := ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), |MAfun p q| with hMAdef
  have hMAnnn : 0 ≤ MA := by
    rw [hMAdef]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _
  have hMAbound : ∀ p q, MAfun p q ≤ MA := by
    intro p q
    rw [hMAdef]
    have h1 : |MAfun p q| ≤ ∑ q' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        |MAfun p q'| :=
      Finset.single_le_sum (f := fun q' => |MAfun p q'|) (fun q' _ => abs_nonneg _)
        (Finset.mem_univ q)
    have h2 : (∑ q' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), |MAfun p q'|) ≤
        ∑ p' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ q' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), |MAfun p' q'| :=
      Finset.single_le_sum (f := fun p' => ∑ q' : Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), |MAfun p' q'|)
        (fun p' _ => Finset.sum_nonneg fun q' _ => abs_nonneg _) (Finset.mem_univ p)
    exact (le_abs_self _).trans (h1.trans h2)
  obtain ⟨Cpd, hCpdn, hCpd⟩ := iteratedFDeriv_le_of_pdVec (n := Module.finrank ℝ E) (M := k)
  have hC4ex : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
        (φ : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
        (R : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
        (z₀ : Fin (Module.finrank ℝ E) → ℝ) (β : Fin m → Fin (Module.finrank ℝ E))
        (MA' MD' MR' : ℝ),
        ContDiff ℝ (⊤ : ℕ∞) A → ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) R →
        (∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i A z₀‖ ≤ MA') →
        (∀ i : ℕ, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i φ z₀‖ ≤ MD' ^ i) →
        (∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i R (φ z₀)‖ ≤ MR') →
        ‖Work.Diff.STE.pdVec m β (fun z => A z * R (φ z)) z₀‖
          ≤ C * MA' * (1 + MD') ^ m * MR' :=
    fun m => pdVec_mul_comp_le (n := Module.finrank ℝ E) (m := m)
  let C4fun : ℕ → ℝ := fun m => Classical.choose (hC4ex m)
  set C4 : ℝ := ∑ i ∈ Finset.range (k + 1), |C4fun i| with hC4def
  have hC4nn : 0 ≤ C4 := by
    rw [hC4def]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hC4le : ∀ m : ℕ, m ≤ k → C4fun m ≤ C4 := by
    intro m hm
    rw [hC4def]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |C4fun i|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)))
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * C4 * (1 + MD) ^ k * Cpd * MA,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hC4nn)
      (pow_nonneg (by linarith) k)) hCpdn) hMAnnn, ?_⟩
  intro h hsym hsmooth K hK hjet m hm β z a b hz hζ
  -- ## the `h`-dependent factor
  set Rmat : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun c d w => θR w • ((D.mat j' h c d w : ℝ) : ℂ) with hRmat
  have hmatOn : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ((D.mat j' h c d w : ℝ) : ℂ))
      {w | Work.Diff.STE.flatToE (I := I) (D.x₀ j') w ∈ (extChartAt I (D.x₀ j')).target} := by
    intro c d
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun w => D.matChart j' h c d (Work.Diff.STE.flatToE (I := I) (D.x₀ j') w))
        {w | Work.Diff.STE.flatToE (I := I) (D.x₀ j') w ∈ (extChartAt I (D.x₀ j')).target} :=
      (matChart_contDiffOn (I := I) (M := M) D h hsmooth j' c d).comp
        (contDiff_flatToE (I := I) (x₀ := D.x₀ j')).contDiffOn (fun w hw => hw)
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => D.mat j' h c d w)
        {w | Work.Diff.STE.flatToE (I := I) (D.x₀ j') w ∈ (extChartAt I (D.x₀ j')).target} := by
      simpa only [B3Data.mat_eq] using h1
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn h2
  have hRsm : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (Rmat c d) := by
    intro c d
    rw [hRmat]
    exact contDiff_smul_of_tsupport_subset
      ((isOpen_extChartAt_target (I := I) (D.x₀ j')).preimage
        (contDiff_flatToE (I := I) (x₀ := D.x₀ j')).continuous)
      (hmatOn c d) hθRsm hθRtsup
  have hzball : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + ρ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz
  -- the value of the cut-off at the point
  have hcardpos : 0 < Fintype.card ι₀ := Fintype.card_pos_iff.mpr ⟨j'⟩
  have hτpos : 0 < (1 : ℝ) / Real.sqrt (Fintype.card ι₀) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hcardpos))
  have hζpos : 0 < D.ζ j' (D.pt j z) := lt_of_lt_of_le hτpos hζ
  have hζne : D.ζ j' (D.pt j z) ≠ 0 := ne_of_gt hζpos
  have hθz : θ z = 1 := (hθ1 z hz hζ).eq_of_nhds
  have hφz : Φ z = Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z := by
    rw [hΦ]
    simp only [hθz, one_smul]
  have hWlt : ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖ < c₁ := by
    rw [hc₁, Work.Diff.STE.B3.xiMap]
    exact (D.hζsupp j' (D.pt j z) hζne).2
  have hzt : flatReg (I := I) (M := M) D j z := htgt z hz
  -- ## the jet bound for the `h`-dependent factor at `Φ z`
  have hMR : ∀ (c d : Fin (Module.finrank ℝ E)) (i : ℕ), i ≤ m →
      ‖iteratedFDeriv ℝ i (Rmat c d) (Φ z)‖ ≤ Cpd * K := by
    intro c d i hi
    have hsm_mat : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.mat j' h c d w) (Φ z) := by
      rw [hφz]
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart j' h c d)
          (extChartAt I (D.x₀ j')).target :=
        matChart_contDiffOn (I := I) (M := M) D h hsmooth j' c d
      have htgtw : Work.Diff.STE.flatToE (I := I) (D.x₀ j')
          (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z) ∈
          (extChartAt I (D.x₀ j')).target := by
        rw [Work.Diff.STE.B3.xiMap, flatToE_coord_cm]
        exact PartialEquiv.map_source (extChartAt I (D.x₀ j'))
          (D.hζsupp j' (D.pt j z) hζne).1
      have h2 := h1.contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ j')).mem_nhds htgtw)
      have h3 := h2.comp (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z)
        (contDiff_flatToE (I := I) (x₀ := D.x₀ j')).contDiffAt
      simpa only [Function.comp_def, B3Data.mat_eq] using h3
    have hpd : ∀ (m' : ℕ), m' ≤ k → ∀ β' : Fin m' → Fin (Module.finrank ℝ E),
        ‖Work.Diff.STE.pdVec m' β' (fun y => ((D.mat j' h c d y : ℝ) : ℂ)) (Φ z)‖ ≤ K := by
      intro m' hm' β'
      rw [hφz]
      exact hjet j' m' (by omega) β' (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z) c d
        (le_trans (le_of_lt hWlt) (by rw [hc₁]; linarith [D.hσ j']))
    have hreal := hCpd (D.mat j' h c d) (Φ z) K hK hsm_mat hpd i (le_trans hi hm)
    have hcoe := Work.Diff.STE.Lead.Gal.norm_iteratedFDeriv_ofReal (D.mat j' h c d) i hsm_mat
    have hgerm : Rmat c d =ᶠ[𝓝 (Φ z)] (fun w => ((D.mat j' h c d w : ℝ) : ℂ)) := by
      rw [hφz] at *
      filter_upwards [Metric.ball_mem_nhds (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z)
        (sub_pos.mpr hWlt)] with w hw
      have h1 : θR w = 1 := hθRone w (fun k => by
        have ha : |w k| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w k
        have hb : ‖w‖ < c₁ := by
          have hc : ‖w‖ ≤ ‖w - Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖
              + ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖ := by
            conv_lhs => rw [← sub_add_cancel w
              (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z)]
            exact norm_add_le _ _
          have hd : ‖w - Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖ <
              c₁ - ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖ := by
            simpa only [Metric.mem_ball, dist_eq_norm] using hw
          linarith
        linarith)
      simp only [hRmat, h1, one_smul]
    rw [Work.Diff.STE.Lead.Gal.iteratedFDeriv_congr_of_eventuallyEq hgerm i]
    exact hcoe.trans hreal
  -- ## the eventual identity
  have hxi_cont : ContinuousAt (fun y => Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) z := by
    have h1 : (fun y => Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) =ᶠ[𝓝 z] Φ := by
      filter_upwards [hθ1 z hz hζ] with y hy
      rw [hΦ]
      simp only [hy, one_smul]
    exact (hΦsm.continuous.continuousAt).congr h1.symm
  have hgerm : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ))
      =ᶠ[𝓝 z] (fun y => ∑ c, ∑ d, Acoef (a, c) (b, d) y * Rmat c d (Φ y)) := by
    have hwit : ∀ᶠ y in 𝓝 z, 0 < D.ζ j' (D.pt j y) := by
      have hcont : ContinuousAt (fun y => D.ζ j' (D.pt j y)) z :=
        ((contDiffOn_zeta_pt (I := I) (M := M) D j j').contDiffAt
          ((isOpen_flatReg (I := I) (M := M) D j).mem_nhds hzt)).continuousAt
      exact hcont.eventually (IsOpen.mem_nhds isOpen_Ioi hζpos)
    have hcut : ∀ᶠ y in 𝓝 z, θ y = 1 := hθ1 z hz hζ
    have hmatval : ∀ᶠ y in 𝓝 z, ∀ c d, Rmat c d (Φ y)
        = ((D.mat j' h c d (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) : ℝ) : ℂ) := by
      have hΦeq : ∀ᶠ y in 𝓝 z, Φ y = Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y := by
        filter_upwards [hcut] with y hy
        rw [hΦ]
        simp only [hy, one_smul]
      have hnear : ∀ᶠ y in 𝓝 z, ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y
          - Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖ < c₁ - ‖Work.Diff.STE.B3.xiMap
            (I := I) (M := M) D j j' z‖ := by
        have h1 : Metric.ball (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z)
            (c₁ - ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖) ∈
            𝓝 (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z) :=
          Metric.ball_mem_nhds _ (sub_pos.mpr hWlt)
        filter_upwards [hxi_cont.preimage_mem_nhds h1] with y hy
        simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hy
      filter_upwards [hΦeq, hnear] with y hy1 hy2
      intro c d
      have h1 : θR (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) = 1 :=
        hθRone _ (fun k => by
          have ha : |(Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) k| ≤
              ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y‖ := by
            simpa only [Real.norm_eq_abs] using
              norm_le_pi_norm (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) k
          have hb : ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y‖ < c₁ := by
            have hc : ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y‖ ≤
                ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y
                  - Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖
                + ‖Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z‖ := by
              conv_lhs => rw [← sub_add_cancel
                (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y)
                (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' z)]
              exact norm_add_le _ _
            linarith
          linarith)
      simp only [hRmat, hy1, h1, one_smul]
    filter_upwards [hwit, hcut, hmatval] with y hyζ hycut hymat
    rw [Gf_eq_sum_mat (I := I) (M := M) D h j j' y a b (ne_of_gt hyζ)]
    have hswap : (∑ c, ∑ d, Acoef (a, c) (b, d) y * Rmat c d (Φ y))
        = ∑ c, ∑ d, ((Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' y a c
            * Work.Diff.STE.B3.trCoef (I := I) (M := M) D j j' y b d
            * D.mat j' h c d (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
      have hyd : θR (Φ y) • ((D.mat j' h c d (Φ y) : ℝ) : ℂ)
          = ((D.mat j' h c d (Work.Diff.STE.B3.xiMap (I := I) (M := M) D j j' y) : ℝ) : ℂ) := by
        have hh := hymat c d
        rw [hRmat] at hh
        exact hh
      simp only [hAcoef, hRmat, hycut, one_smul, hyd]
      push_cast
      ring
    rw [hswap]
    push_cast
    ring
  -- ## the per-summand bound and the sum
  have hterm : ∀ (c d : Fin (Module.finrank ℝ E)),
      ‖Work.Diff.STE.pdVec m β (fun y => Acoef (a, c) (b, d) y * Rmat c d (Φ y)) z‖
        ≤ C4 * MA * (1 + MD) ^ k * (Cpd * K) := by
    intro c d
    have h1 : ‖Work.Diff.STE.pdVec m β (fun y => Acoef (a, c) (b, d) y * Rmat c d (Φ y)) z‖
        ≤ C4fun m * MAfun (a, c) (b, d) * (1 + MD) ^ m * (Cpd * K) :=
      (Classical.choose_spec (hC4ex m)).2 (Acoef (a, c) (b, d)) Φ (Rmat c d) z β
        (MAfun (a, c) (b, d)) MD (Cpd * K) (hAsm _ _) hΦsm (hRsm c d)
        (fun i hi => hMAle (a, c) (b, d) z hzball i (le_trans hi hm))
        (fun i hi1 hi2 => by
          have h2 : ‖iteratedFDeriv ℝ i Φ z‖ ≤ MD := hMDle z hzball i (le_trans hi2 hm)
          calc ‖iteratedFDeriv ℝ i Φ z‖ ≤ MD := h2
            _ = MD ^ 1 := (pow_one MD).symm
            _ ≤ MD ^ i := pow_le_pow_right₀ hMD1 hi1)
        (fun i hi => hMR c d i hi)
    have h2 : C4fun m * MAfun (a, c) (b, d) * (1 + MD) ^ m * (Cpd * K)
        ≤ C4 * MA * (1 + MD) ^ k * (Cpd * K) := by
      have hC4m : C4fun m ≤ C4 := hC4le m hm
      have hMAm : MAfun (a, c) (b, d) ≤ MA := hMAbound _ _
      have hMDm : (1 + MD) ^ m ≤ (1 + MD) ^ k := pow_le_pow_right₀ (by linarith) hm
      have hC40 : (0 : ℝ) ≤ C4 := hC4nn
      have hMA0 : (0 : ℝ) ≤ MA := hMAnnn
      have hCK0 : (0 : ℝ) ≤ Cpd * K := mul_nonneg hCpdn hK
      have h4m : (0 : ℝ) ≤ C4fun m := (Classical.choose_spec (hC4ex m)).1
      have hMm : (0 : ℝ) ≤ MAfun (a, c) (b, d) := hMAnn _ _
      have hpm : (0 : ℝ) ≤ (1 + MD) ^ m := pow_nonneg (by linarith) m
      have hpk : (0 : ℝ) ≤ (1 + MD) ^ k := pow_nonneg (by linarith) k
      calc C4fun m * MAfun (a, c) (b, d) * (1 + MD) ^ m * (Cpd * K)
          ≤ C4 * MA * (1 + MD) ^ m * (Cpd * K) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul hC4m hMAm hMm hC40) hpm) hCK0
        _ ≤ C4 * MA * (1 + MD) ^ k * (Cpd * K) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hMDm (mul_nonneg hC40 hMA0)) hCK0
    exact h1.trans h2
  calc ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖
      = ‖Work.Diff.STE.pdVec m β (fun y => ∑ c, ∑ d,
          Acoef (a, c) (b, d) y * Rmat c d (Φ y)) z‖ := by
        rw [pdVec_congr_of_eventuallyEq hgerm β]
    _ ≤ ∑ c, ∑ d, ‖Work.Diff.STE.pdVec m β
          (fun y => Acoef (a, c) (b, d) y * Rmat c d (Φ y)) z‖ :=
        pdVec_sum2_le (fun c d => fun y => Acoef (a, c) (b, d) y * Rmat c d (Φ y))
          (fun c d => (hAsm (a, c) (b, d)).mul ((hRsm c d).comp hΦsm)) β z
    _ ≤ ∑ c, ∑ d, C4 * MA * (1 + MD) ^ k * (Cpd * K) :=
        Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ => hterm c d))
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * C4 * (1 + MD) ^ k * Cpd * MA * K := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring_nf


end Work.Diff.STE.Lead.Gal
