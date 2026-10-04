import Mathlib
import Submission.Work.Diff.EXT.ConnCov.reactJetsDefs
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets
import Submission.Work.Diff.EXT.ConnCov.norm_iteratedFDeriv_fderiv_apply_le
import Submission.Work.Diff.EXT.chartMat_jets_bounded
import Submission.Work.Diff.EXT.gram_det_bound
import Submission.Work.Diff.EXT.ricAt_invGram_chart
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_comp_le_of_contDiffAt
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.GE.covRm_family_jointSmooth
import Submission.Work.Diff.GE.rmChartExpr_joint_smooth
import Submission.Work.Diff.T.clairaut_fderiv_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The identity `reactArr = reactExpr` and jet bounds for `reactExpr`

This module contains

* the ingredients of the pointwise identity
  `Work.Diff.EXT.ConnCov.reactArr = Work.Diff.EXT.ConnCov.reactExpr`:
  - `hasDerivAt_chartMat_entry` — the entrywise time derivative of the chart matrix of a Ricci flow
    (`∂_s g_{lp} = -2 Ric_{lp}`, with `Ric` read in the coordinate frame);
  - `ricFun_eq_ricArr` — the chart Ricci matrix is the inverse-Gram contraction of the chart
    curvature;
  - `deriv_sKz_dJet1` — Clairaut's theorem in time for the Koszul pairing read off the first
    spatial jet of the chart matrix;
* the jet bounds of the explicit chart expression `reactExpr` (`reactExpr_jets`), proved from the
  chart jets of `chartMat` and of `rmChartExpr` and from the determinant lower bound for `GramM`
  (`Work.Diff.EXT.gram_det_bound`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The pointwise identity `reactArr = reactExpr` -/

/-- **The time derivative of an entry of the chart matrix along a Ricci flow** is `-2` times the
corresponding entry of the chart Ricci matrix, i.e. `-2 Ric_{lp}` with `Ric` read in the coordinate
frame of the chart at `x₀`. -/
lemma hasDerivAt_chartMat_entry
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) (y : E) (l p : Fin (Module.finrank ℝ E)) :
    HasDerivAt (fun s : ℝ => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s y l p)
      (-2 * ricFun (I := I) (M := M) G x₀ t y l p) t := by
  have h := Work.Diff.EXT.hasDerivAt_chartMat_of_isRicciFlow (I := I) (M := M) hflow ht x₀ y
  rw [hasDerivAt_pi] at h
  have h2 := (hasDerivAt_pi.mp (h l)) p
  have hric : Work.Diff.EXT.chartRicMat (G t) x₀ y l p
      = ricFun (I := I) (M := M) G x₀ t y l p := rfl
  simpa only [Pi.smul_apply, smul_eq_mul, hric] using h2

/-- **The `fderiv` of a constant multiple of a real-valued function**, with no differentiability
hypothesis (both sides vanish when the function is not differentiable). -/
lemma fderiv_fun_const_mul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (hc : c ≠ 0) (g : F → ℝ) (y : F) :
    fderiv ℝ (fun u => c * g u) y = c • fderiv ℝ g y := by
  by_cases hd : DifferentiableAt ℝ g y
  · exact fderiv_const_mul hd c
  · have hd' : ¬ DifferentiableAt ℝ (fun u : F => c * g u) y := by
      intro h
      refine hd ?_
      have h1 : DifferentiableAt ℝ (fun u : F => c⁻¹ * (c * g u)) y := h.const_mul c⁻¹
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => ?_))
      show g u = c⁻¹ * (c * g u)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd, smul_zero]

/-- **The chart Ricci matrix in the coordinate frame is the inverse-Gram contraction of the chart
curvature**: `Ric_{ab} = ∑_{k,l} γ^{kl} R_{kalb}`. -/
theorem ricFun_eq_ricArr
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b : Fin (Module.finrank ℝ E)) :
    ricFun (I := I) (M := M) G x₀ t y a b
      = ricArr (I := I) (M := M) G x₀ t y a b := by
  have hp_src : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    rw [Work.Diff.EXT.pt, ← extChartAt_source (I := I) x₀]
    exact (extChartAt I x₀).map_target hy
  have hmat : Work.Diff.EXT.cgramM (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y)
      = Work.Diff.GE.GramM (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) := by
    ext i j
    simp only [Work.Diff.EXT.cgramM, Work.Diff.GE.GramM, Work.Diff.GE.mComp,
      Work.Diff.GE.cFrame_apply, Matrix.of_apply]
  have hcf : ∀ i : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)
        = Work.Diff.EXT.cvec (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.EXT.bB (E := E) i) := fun i => rfl
  have h1 := Work.Diff.EXT.ricAt_invGram_chart (I := I) (M := M) (G t) x₀ hp_src a b
  rw [ricFun]
  simp only [hcf]
  rw [h1, hmat, ricArr]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [show (Work.Diff.GE.GramM (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y))⁻¹ k l
      = Work.Diff.GE.GramInv (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) k l from rfl]
  rw [show (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Submission.Diff.rmVec (Submission.Diff.lcOf (G t)) (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.EXT.cvec (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.EXT.bB (E := E) k))
          (Work.Diff.EXT.cvec (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.EXT.bB (E := E) a))
          (Work.Diff.EXT.cvec (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.EXT.bB (E := E) b)))
        (Work.Diff.EXT.cvec (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.EXT.bB (E := E) l))
      = Work.Diff.GE.rmC4 (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) k a l b from rfl]
  rw [Work.Diff.EXT.pcj_rmC4_rmChartExpr (I := I) hLC G x₀ t hp_src k a l b]

/-- **Joint smoothness (in time and in the chart coordinate) of an entry of the chart matrix**, at
an interior time and a point of the chart target. -/
lemma contDiffAt_chartMat_entry_joint
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (l p : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ 2
      (fun q : ℝ × E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ q.1 q.2 l p) (t, y) := by
  have hmem : Set.Ico 0 T ×ˢ (extChartAt I x₀).target ∈ 𝓝 (t, y) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self)
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have hw := (Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth_gen (I := I) (M := M)
    hflow.1 ⟨le_of_lt ht.1, ht.2⟩ x₀ hy).contDiffAt hmem
  have hproj : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ q.1 q.2 l p) (t, y) :=
    (ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj p : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj l : Work.Diff.EXT.MatE (E := E) →L[ℝ]
          (Fin (Module.finrank ℝ E) → ℝ)))).contDiffAt.comp (t, y) hw
  exact hproj.of_le (by norm_num)

/-- **Clairaut in time for the Koszul pairing of the first chart jets.**  The `s`-derivative at `t`
of `sKz (dJet1 (G s) x₀ y) i j l = ½(∂_i g_{jl} + ∂_j g_{il} − ∂_l g_{ij})` is
`-(∂_i Ric_{jl} + ∂_j Ric_{il} − ∂_l Ric_{ij})` at `(t,y)`: Clairaut's theorem commutes `∂_s` with
the first spatial derivative, and `∂_s g = -2 Ric` by the Ricci-flow equation. -/
theorem deriv_sKz_dJet1
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j l : Fin (Module.finrank ℝ E)) :
    HasDerivAt (fun s : ℝ => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G s) x₀ y) i j l)
      (- (fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' j l) y
            (Work.Diff.EXT.bB (E := E) i)
         + fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i l) y
            (Work.Diff.EXT.bB (E := E) j)
         - fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i j) y
            (Work.Diff.EXT.bB (E := E) l))) t := by
  have hcl : ∀ (a b c : Fin (Module.finrank ℝ E)),
      HasDerivAt (fun s : ℝ => fderiv ℝ
          (fun u : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u b c) y
          (Work.Diff.EXT.bB (E := E) a))
        (fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u b c) y
          (Work.Diff.EXT.bB (E := E) a)) t := by
    intro a b c
    have hΦ : ContDiffAt ℝ 2
        (fun q : ℝ × E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ q.1 q.2 b c) (t, y) :=
      contDiffAt_chartMat_entry_joint hflow ht x₀ hy b c
    have h := Work.Diff.T.clairaut_fderiv_apply
      (Φ := fun q : ℝ × E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ q.1 q.2 b c)
      hΦ (Work.Diff.EXT.bB (E := E) a)
    have hev : (fun u : E => deriv
          (fun s : ℝ => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u b c) t)
        =ᶠ[𝓝 y] (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u b c) := by
      filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hy] with u _hu
      exact (hasDerivAt_chartMat_entry (I := I) (M := M) hflow ht x₀ u b c).deriv
    rwa [hev.fderiv_eq] at h
  have hA := hcl i j l
  have hB := hcl j i l
  have hC := hcl l i j
  have hsKz : ∀ s : ℝ, Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G s) x₀ y) i j l
      = (1 / 2) * (fderiv ℝ
              (fun u : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u j l) y
              (Work.Diff.EXT.bB (E := E) i)
          + fderiv ℝ (fun u : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u i l) y
              (Work.Diff.EXT.bB (E := E) j)
          - fderiv ℝ (fun u : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u i j) y
              (Work.Diff.EXT.bB (E := E) l)) := by
    intro s
    simp only [Work.Diff.EXT.sKz, Work.Diff.EXT.dJet1, Work.Diff.EXT.chartMat]
    rw [Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G s) x₀ hy i j l,
      Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G s) x₀ hy j i l,
      Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G s) x₀ hy l i j]
    try ring
  have hmain : HasDerivAt
      (fun s : ℝ => (1 / 2) * (fderiv ℝ
                (fun u : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u j l) y
                (Work.Diff.EXT.bB (E := E) i)
            + fderiv ℝ (fun u : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u i l) y
                (Work.Diff.EXT.bB (E := E) j)
            - fderiv ℝ (fun u : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s u i j) y
                (Work.Diff.EXT.bB (E := E) l)))
      ((1 / 2) * (fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u j l) y
                (Work.Diff.EXT.bB (E := E) i)
            + fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u i l) y
                (Work.Diff.EXT.bB (E := E) j)
            - fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u i j) y
                (Work.Diff.EXT.bB (E := E) l))) t := by
    have h1 := ((hA.add hB).sub hC).const_smul (1 / 2 : ℝ)
    convert h1 using 1 <;> simp only [smul_eq_mul]
  have hdst : (1 / 2) * (fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u j l) y
              (Work.Diff.EXT.bB (E := E) i)
          + fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u i l) y
              (Work.Diff.EXT.bB (E := E) j)
          - fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u i j) y
              (Work.Diff.EXT.bB (E := E) l))
      = - (fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' j l) y
            (Work.Diff.EXT.bB (E := E) i)
         + fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i l) y
            (Work.Diff.EXT.bB (E := E) j)
         - fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i j) y
            (Work.Diff.EXT.bB (E := E) l)) := by
    rw [fderiv_fun_const_mul (-2) (by norm_num)
        (fun u : E => ricFun (I := I) (M := M) G x₀ t u j l) y,
      fderiv_fun_const_mul (-2) (by norm_num)
        (fun u : E => ricFun (I := I) (M := M) G x₀ t u i l) y,
      fderiv_fun_const_mul (-2) (by norm_num)
        (fun u : E => ricFun (I := I) (M := M) G x₀ t u i j) y]
    simp only [smul_apply, smul_eq_mul]
    ring
  have hmain' : HasDerivAt (fun s : ℝ => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G s) x₀ y) i j l)
      ((1 / 2) * (fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u j l) y
                (Work.Diff.EXT.bB (E := E) i)
            + fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u i l) y
                (Work.Diff.EXT.bB (E := E) j)
            - fderiv ℝ (fun u : E => -2 * ricFun (I := I) (M := M) G x₀ t u i j) y
                (Work.Diff.EXT.bB (E := E) l))) t :=
    hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => hsKz s))
  rw [hdst] at hmain'
  exact hmain'

/-! ## Jet bounds of the explicit chart expression `reactExpr`

We use a local interface `JBd` (a single-constant version of `Work.Diff.EXT.CBound.JBu`) which
bundles smoothness in the chart coordinate with a uniform bound for the iterated derivatives of
order `≤ k`, and is closed under sums, products and directional derivatives. -/

/-- A uniform jet bound of order `≤ k` for a family `A : ℝ → E → ℝ` on the slab `[σ,T) × K'`:
smoothness in the chart coordinate plus a common bound for the iterated derivatives of order
`≤ k`. -/
def JBd (σ T : ℝ) (K' : Set E) (k : ℕ) (A : ℝ → E → ℝ) (B : ℝ) : Prop :=
  (∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ContDiffAt ℝ (⊤ : ℕ∞) (A t) y) ∧
  (∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ i ≤ k, ‖iteratedFDeriv ℝ i (A t) y‖ ≤ B)

namespace JBd

variable {σ T : ℝ} {K' : Set E} {k : ℕ} {A A' : ℝ → E → ℝ} {B B' : ℝ}

lemma weaken (hB : B ≤ B') (h : JBd σ T K' k A B) : JBd σ T K' k A B' :=
  ⟨h.1, fun t ht y hy i hi => le_trans (h.2 t ht y hy i hi) hB⟩

lemma mono {k'} (hk : k' ≤ k) (h : JBd σ T K' k A B) : JBd σ T K' k' A B :=
  ⟨h.1, fun t ht y hy i hi => h.2 t ht y hy i (le_trans hi hk)⟩

lemma congr (h : ∀ t y, A t y = A' t y) (hA : JBd σ T K' k A B) : JBd σ T K' k A' B := by
  obtain ⟨hsm, hbd⟩ := hA
  refine ⟨fun t ht y hy => (hsm t ht y hy).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y' => (h t y').symm)), ?_⟩
  intro t ht y hy i hi
  rw [show A' t = A t from funext (fun y' => (h t y').symm)]
  exact hbd t ht y hy i hi

lemma add (hA : JBd σ T K' k A B) (hA' : JBd σ T K' k A' B') :
    JBd σ T K' k (fun t y => A t y + A' t y) (B + B') := by
  refine ⟨fun t ht y hy => (hA.1 t ht y hy).add (hA'.1 t ht y hy), fun t ht y hy i hi => ?_⟩
  exact Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (hA.1 t ht y hy) (hA'.1 t ht y hy)
    (hA.2 t ht y hy i hi) (hA'.2 t ht y hy i hi)

lemma neg (hA : JBd σ T K' k A B) : JBd σ T K' k (fun t y => -A t y) B := by
  refine ⟨fun t ht y hy => (hA.1 t ht y hy).neg, fun t ht y hy i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun y' : E => -A t y') y = -iteratedFDeriv ℝ i (A t) y :=
    iteratedFDeriv_neg_apply
  rw [h1, norm_neg]
  exact hA.2 t ht y hy i hi

lemma sub (hA : JBd σ T K' k A B) (hA' : JBd σ T K' k A' B') :
    JBd σ T K' k (fun t y => A t y - A' t y) (B + B') :=
  (hA.add hA'.neg).congr (fun t y => by ring)

lemma mul (hA : JBd σ T K' k A B) (hA' : JBd σ T K' k A' B) :
    JBd σ T K' k (fun t y => A t y * A' t y) ((2 : ℝ) ^ k * B * B) := by
  refine ⟨fun t ht y hy => (hA.1 t ht y hy).mul (hA'.1 t ht y hy), fun t ht y hy i hi => ?_⟩
  exact Work.Diff.EXT.norm_iteratedFDeriv_mul_le_at_le (B := B) hi (hA.1 t ht y hy)
    (hA'.1 t ht y hy) (le_trans (norm_nonneg _) (hA.2 t ht y hy 0 (Nat.zero_le k)))
    (hA.2 t ht y hy) (hA'.2 t ht y hy)

lemma const_mul (c : ℝ) (hA : JBd σ T K' k A B) :
    JBd σ T K' k (fun t y => c * A t y) (|c| * B) := by
  refine ⟨fun t ht y hy => ((hA.1 t ht y hy).const_smul c).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y' => smul_eq_mul c (A t y'))),
    fun t ht y hy i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun y' : E => c * A t y') y
      = c • iteratedFDeriv ℝ i (A t) y := by
    rw [show (fun y' : E => c * A t y') = (fun y' : E => c • A t y') from
      funext (fun y' => (smul_eq_mul c (A t y')).symm)]
    exact iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (f := A t) (x := y) (a := c)
      ((hA.1 t ht y hy).of_le (by simp))
  rw [h1, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hA.2 t ht y hy i hi) (abs_nonneg c)

lemma sum {ι : Type*} [Fintype ι] {F : ι → ℝ → E → ℝ}
    (hF : ∀ i, JBd σ T K' k (F i) B) :
    JBd σ T K' k (fun t y => ∑ i, F i t y) ((Fintype.card ι : ℝ) * B) := by
  refine ⟨fun t ht y hy => ContDiffAt.sum (fun i _ => (hF i).1 t ht y hy),
    fun t ht y hy m hm => ?_⟩
  have h := Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at (s := Finset.univ)
    (φ := fun i y' => F i t y') (x := y) (n := m) (C := B)
    (fun i _ => (hF i).1 t ht y hy) (fun i _ => (hF i).2 t ht y hy m hm)
  simpa only [Finset.card_univ] using h

lemma fderiv_apply (v : E) (hA : JBd σ T K' (k + 1) A B) :
    JBd σ T K' k (fun t y => fderiv ℝ (A t) y v) (‖v‖ * B) := by
  refine ⟨fun t ht y hy =>
    ((hA.1 t ht y hy).fderiv_right (by simp)).clm_apply contDiffAt_const, fun t ht y hy i hi => ?_⟩
  refine le_trans (Work.Diff.EXT.ConnCov.norm_iteratedFDeriv_fderiv_apply_le (ψ := A t)
    (y := y) (ζ := v) (j := i) (hA.1 t ht y hy)) ?_
  exact mul_le_mul_of_nonneg_left (hA.2 t ht y hy (i + 1) (by omega)) (norm_nonneg v)

end JBd

/-- **Smoothness in the chart coordinate of the chart curvature array**, from the joint smoothness
of `rmChartExpr` (`Work.Diff.GE.rmChartExpr_jointSmooth`) and the smoothness of the chart inverse. -/
lemma contDiffAt_rmChartExpr_pt
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l t
        (Work.Diff.EXT.pt (I := I) x₀ y')) y := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  have hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l p.1 p.2)
      (Set.Ico 0 T ×ˢ (chartAt H x₀).source) :=
    Work.Diff.GE.rmChartExpr_joint_smooth (I := I) (G := G) hflow.1 x₀
      (fun hu hX => Work.Diff.GE.joint_deriv hu hX) i j k l
  have hchart := Work.Diff.GE.chartPush_source (I := I) x₀ hjoint
  have hmem : Set.Ico 0 T ×ˢ (extChartAt I x₀).target ∈ 𝓝 (t, y) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self)
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have h1 := hchart.contMDiffAt hmem
  have hslice : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l t
        ((extChartAt I x₀).symm y')) y :=
    h1.comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  exact contMDiffAt_iff_contDiffAt.mp hslice

/-- The set of matrices with non-vanishing determinant is open. -/
lemma isOpen_det_ne_zero_pi {n : ℕ} :
    IsOpen {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} := by
  have hc : Continuous (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) :=
    (Work.Diff.EXT.contDiff_matrix_det_pi (n := n)).continuous
  have hset : {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0}
      = {A : Fin n → Fin n → ℝ | (Matrix.of A).det = 0}ᶜ := by
    ext A; simp
  rw [hset]
  exact (isClosed_eq hc continuous_const).isOpen_compl

/-- The entries of the inverse of a matrix are smooth on the set of invertible matrices. -/
lemma contDiffOn_invEntry_pi {n : ℕ} (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => (Matrix.of A)⁻¹ i j)
      {A | (Matrix.of A).det ≠ 0} := by
  intro A hA
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A' : Fin n → Fin n → ℝ => fun i j => (Matrix.of A')⁻¹ i j) A :=
    Work.Diff.EXT.contDiffAt_matrix_inv_pi A hA
  have h2 := (contDiffAt_pi.mp h1) i
  exact ((contDiffAt_pi.mp h2) j).contDiffWithinAt

/-- **Bounds for the iterated derivatives of the entries of the inverse matrix on a compact set of
invertible matrices.**  The iterated derivatives of `A ↦ A⁻¹ i j` of order `≤ k` are uniformly
bounded on a compact set on which the determinant does not vanish. -/
lemma exists_bound_invEntry_pi (n : ℕ) {T : Set (Fin n → Fin n → ℝ)} (hT : IsCompact T)
    (hTsub : T ⊆ {A | (Matrix.of A).det ≠ 0}) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A ∈ T, ∀ (i j : Fin n), ∀ s ≤ k,
      ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ i j) A‖ ≤ C := by
  classical
  have hone : ∀ (p : Fin n × Fin n) (s : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ A ∈ T,
      ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ p.1 p.2) A‖ ≤ C := by
    intro p s
    have hU : IsOpen {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} := isOpen_det_ne_zero_pi
    have hcont : ContinuousOn (fun A : Fin n → Fin n → ℝ =>
        ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ p.1 p.2) A‖)
        {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} :=
      (ContinuousOn.continuousOn_iteratedFDeriv (contDiffOn_invEntry_pi p.1 p.2) hU
        (by simp)).norm
    obtain ⟨C, hC⟩ := (hT.image_of_continuousOn (hcont.mono hTsub)).bddAbove
    refine ⟨max C 0, le_max_right _ _, fun A hA => ?_⟩
    have hmem : (fun A : Fin n → Fin n → ℝ =>
        ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ p.1 p.2) A‖) A
        ∈ (fun A : Fin n → Fin n → ℝ =>
          ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ p.1 p.2) A‖) '' T :=
      ⟨A, hA, rfl⟩
    exact le_trans (hC hmem) (le_max_left _ _)
  choose C hC0 hC using fun p : (Fin n × Fin n) × Fin (k + 1) => hone p.1 p.2
  refine ⟨∑ p : (Fin n × Fin n) × Fin (k + 1), C p, Finset.sum_nonneg (fun p _ => hC0 p), ?_⟩
  intro A hA i j s hs
  have hlt : s < k + 1 := Nat.lt_succ_of_le hs
  have hb := hC ((i, j), ⟨s, hlt⟩) A hA
  exact hb.trans (Finset.single_le_sum (fun p _ => hC0 p) (Finset.mem_univ _))

/-- **Jet bounds of the inverse chart Gram matrix from jet bounds of the chart Gram matrix, up to a
fixed order.**  This is the fixed-order form of `Work.Diff.EXT.gramInv_bounds_of_gram_bounds`, with
the (unused) hypothesis `UniqueDiffOn ℝ K` removed — that hypothesis cannot be supplied for a
general compact set, which is the only case in which the statement is needed. -/
theorem gramInv_jets_of_gram_jets_at
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K' : Set E) (K : ℕ)
    (hKt : K' ⊆ (extChartAt I x₀).target)
    (hG : ∀ k ≤ K, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K',
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramM G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C)
    (hbd : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K',
      c ≤ (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).det) :
    ∀ k ≤ K, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K',
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramInv G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C := by
  classical
  have hCf : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (k ≤ K → ∀ t ∈ Set.Ico σ T, ∀ y ∈ K',
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramM G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C) := by
    intro k
    by_cases hk : k ≤ K
    · obtain ⟨C, hC0, hC⟩ := hG k hk
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun hk' => absurd hk' hk⟩
  choose Cf hCf0 hCfbd using hCf
  have hCfn : ∀ i : ℕ, 0 ≤ Cf i := fun i => hCf0 i
  obtain ⟨c, hcpos, hcdet⟩ := hbd
  intro k hkK
  set D0 : ℝ := ∑ i ∈ Finset.range (K + 1), Cf i with hD0
  have hD0nn : 0 ≤ D0 := by rw [hD0]; exact Finset.sum_nonneg (fun i _ => hCfn i)
  have hCf_le_D0 : ∀ i, i ≤ K → Cf i ≤ D0 := by
    intro i hi
    rw [hD0]
    exact Finset.single_le_sum (fun j _ => hCfn j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set B : ℝ := ∑ _ : Fin (Module.finrank ℝ E), ∑ _ : Fin (Module.finrank ℝ E), D0 with hB
  set D : ℝ := max 1 B with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDB : B ≤ D := le_max_right _ _
  have hDkey : ∀ s, 1 ≤ s → s ≤ k → B ≤ D ^ s := by
    intro s hs1 _
    calc B ≤ D := hDB
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ s := pow_le_pow_right₀ hD1 hs1
  set Tset : Set (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
      {A | c ≤ (Matrix.of A).det ∧ ‖A‖ ≤ B} with hTset
  have hTset_compact : IsCompact Tset := by
    rw [hTset]
    have hclosed : IsClosed {A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ |
        c ≤ (Matrix.of A).det} :=
      isClosed_le continuous_const (Work.Diff.EXT.contDiff_matrix_det_pi.continuous)
    have hball : IsCompact (Metric.closedBall
        (0 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) B) :=
      isCompact_closedBall 0 B
    convert hball.inter_left hclosed using 1
    ext A
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hTset_sub : Tset ⊆ {A | (Matrix.of A).det ≠ 0} := by
    intro A hA
    exact ne_of_gt (lt_of_lt_of_le hcpos hA.1)
  obtain ⟨M, hMnn, hMbd⟩ :=
    exists_bound_invEntry_pi (Module.finrank ℝ E) hTset_compact hTset_sub k
  refine ⟨max 0 ((Nat.factorial k : ℝ) * M * D ^ k), le_max_left _ _, ?_⟩
  intro t ht y hy i j
  have hFm_smooth : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y :=
    (Work.Diff.EXT.contDiffAt_chartMatFun (I := I) (G t) x₀ (hKt hy)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y' => by funext a b; rfl))
  have hFm_bound : ∀ s, s ≤ k → ‖iteratedFDeriv ℝ s
      (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ ≤ B := by
    intro s hsk
    have hpi1 : ‖iteratedFDeriv ℝ s (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
          Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖
        ≤ ∑ a, ‖iteratedFDeriv ℝ s (fun y' : E => fun b : Fin (Module.finrank ℝ E) =>
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ :=
      Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum _ y s hFm_smooth
    refine hpi1.trans ?_
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hpi2 : ‖iteratedFDeriv ℝ s (fun y' : E => fun b : Fin (Module.finrank ℝ E) =>
          Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖
        ≤ ∑ b, ‖iteratedFDeriv ℝ s (fun y' : E =>
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ :=
      Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum _ y s ((contDiffAt_pi.mp hFm_smooth) a)
    refine hpi2.trans ?_
    refine Finset.sum_le_sum (fun b _ => ?_)
    refine (hCfbd s (le_trans hsk hkK) t ht y hy a b).trans ?_
    exact hCf_le_D0 s (le_trans hsk hkK)
  have hFm_mem : (fun a b : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) a b) ∈ Tset := by
    refine ⟨hcdet t ht y hy, ?_⟩
    have h0 := hFm_bound 0 (Nat.zero_le k)
    rwa [norm_iteratedFDeriv_zero] at h0
  have hFm_jet : ∀ s, 1 ≤ s → s ≤ k → ‖iteratedFDeriv ℝ s
      (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ ≤ D ^ s :=
    fun s hs1 hsk => (hFm_bound s hsk).trans (hDkey s hs1 hsk)
  have hdet0 : (Matrix.of (fun a b : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) a b)).det ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hcpos (hcdet t ht y hy))
  have hg_smooth : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
        (Matrix.of A')⁻¹ i j)
      (fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) a b) :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp (Work.Diff.EXT.contDiffAt_matrix_inv_pi _ hdet0) i)) j
  have hcomp := Work.Diff.EXT.norm_iteratedFDeriv_comp_le_of_contDiffAt
    (f := fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b)
    (g := fun A' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
      (Matrix.of A')⁻¹ i j)
    hFm_smooth hg_smooth (fun s hs => hMbd _ hFm_mem i j s hs) hFm_jet
  have hrw : (fun y' : E => Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') i j)
      = (fun A' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of A')⁻¹ i j)
        ∘ (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) := by
    funext y'
    rfl
  rw [hrw]
  exact hcomp.trans (le_max_right _ _)

/-- **Jet bounds of the explicit reaction expression.**  The explicit chart expression
`reactExpr` of the reaction array `∂_t aComp` is
`-(∂_i Ric_{jl} + ∂_j Ric_{il} - ∂_l Ric_{ij}) + 2 ∑_p Ric_{lp}Γ^p_{ij}(G 0)`, where
`Ric_{ab}(t,y) = ∑_{k,l} γ^{kl}(t,y) R_{kalb}(t,y)`.  Its spatial iterated derivatives of order
`≤ K` are bounded on the compact chart set `K'` and on `[T/2, T)` as soon as the chart jets of
`chartMat` and of `rmChartExpr` of order `≤ K + 1` are bounded there and `G t` is comparable with
`G 0` (which bounds the inverse Gram matrix via the determinant lower bound
`Work.Diff.EXT.gram_det_bound`). -/
theorem reactExpr_jets
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (K : ℕ) (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (hrm : ∃ Crm : ℝ, 0 ≤ Crm ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ K + 1 →
      ∀ (i j' k l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j' k l t
            (Work.Diff.EXT.pt (I := I) x₀ y')) y‖ ≤ Crm)
    (hmat : ∃ Cmt : ℝ, 0 ≤ Cmt ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ K + 1 →
      ∀ (i j' : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j') y‖ ≤ Cmt) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (m : ℕ), m ≤ K →
      ∀ (i j l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => reactExpr (I := I) (M := M) G x₀ i j l t y') y‖ ≤ Cd := by
  classical
  obtain ⟨Crm, hCrm0, hrmbd⟩ := hrm
  obtain ⟨Cmt, hCmt0, hmatbd⟩ := hmat
  -- the chart matrix is the Gram matrix of the coordinate frame
  have hGmbd : ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ K + 1 →
      ∀ y ∈ K', ∀ (i j' : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.GramM (I := I) G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j') y‖ ≤ Cmt := by
    intro t ht j hj y hy i j'
    have hfun : (fun y' : E => Work.Diff.GE.GramM (I := I) G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j')
        = (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j') := by
      funext y'
      rfl
    rw [hfun]
    exact hmatbd t ht j hj i j' y hy
  -- the determinant lower bound, and hence the bounds for the inverse Gram matrix
  obtain ⟨cdet, hcdet_pos, hcdet⟩ :=
    Work.Diff.EXT.gram_det_bound (I := I) (M := M) G T C hT hC hmet x₀ K' hK'c hK't
  have hGinv := gramInv_jets_of_gram_jets_at (I := I) (M := M) G (T / 2) T x₀ K' (K + 1) hK't
    (fun k hk => ⟨Cmt, hCmt0, fun t ht y hy i j' => hGmbd t ht k hk y hy i j'⟩)
    ⟨cdet, hcdet_pos, hcdet⟩
  -- per-order constants, and a uniform constant for all orders `≤ K + 1`
  have hper : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (k ≤ K + 1 → ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K',
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramInv (I := I) G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C) := by
    intro k
    by_cases hk : k ≤ K + 1
    · obtain ⟨C, hC0, hC⟩ := hGinv k hk
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun hk' => absurd hk' hk⟩
  choose Cgi hCgi0 hCgibd using hper
  set Bgi : ℝ := ∑ k ∈ Finset.range (K + 2), Cgi k with hBgidef
  have hBgi_nn : 0 ≤ Bgi := by
    rw [hBgidef]; exact Finset.sum_nonneg (fun k _ => hCgi0 k)
  have hCgi_le : ∀ i, i ≤ K + 1 → Cgi i ≤ Bgi := by
    intro i hi
    rw [hBgidef]
    exact Finset.single_le_sum (fun k _ => hCgi0 k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  -- the Christoffel symbols of the initial metric
  have hcg : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (k ≤ K → ∀ y ∈ K',
      ∀ (p i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') p i j) y‖ ≤ C) := by
    intro k
    by_cases hk : k ≤ K
    · obtain ⟨C, hC0, hC⟩ :=
        Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound (I := I) (M := M) G x₀ K' hK'c hK't k
      exact ⟨C, hC0, fun _ => fun y hy p i j => hC y hy i j p⟩
    · exact ⟨0, le_rfl, fun hk' => absurd hk' hk⟩
  choose Ccg hCcg0 hCcgbd using hcg
  set Bcg : ℝ := ∑ k ∈ Finset.range (K + 1), Ccg k with hBcgdef
  have hCcg_le : ∀ i, i ≤ K → Ccg i ≤ Bcg := by
    intro i hi
    rw [hBcgdef]
    exact Finset.single_le_sum (fun k _ => hCcg0 k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  -- the common constant for the Gram-quantities of order `≤ K + 1`
  set Bbig : ℝ := max Bgi Crm with hBbigdef
  have hBbig_nn : 0 ≤ Bbig := le_trans hBgi_nn (le_max_left _ _)
  -- the inverse Gram matrix and the chart curvature as `JBd` families of order `K + 1`
  have hInvM : ∀ (i j : Fin (Module.finrank ℝ E)), JBd (T / 2) T K' (K + 1)
      (fun t y => Work.Diff.GE.GramInv (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i j)
      Bbig := by
    intro i j
    refine ⟨fun t ht y hy =>
      Work.Diff.EXT.CBound.GramInv_contDiffAt_of_target (I := I) (M := M) G x₀ t (hK't hy) i j,
      fun t ht y hy s hs => ?_⟩
    refine le_trans (hCgibd s hs t ht y hy i j) ?_
    exact le_trans (hCgi_le s hs) (le_max_left _ _)
  have hRmM : ∀ (i j' k l : Fin (Module.finrank ℝ E)), JBd (T / 2) T K' (K + 1)
      (fun t y => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j' k l t (Work.Diff.EXT.pt (I := I) x₀ y))
      Bbig := by
    intro i j' k l
    refine ⟨fun t ht y hy =>
      contDiffAt_rmChartExpr_pt hflow ⟨by linarith [ht.1, hT], ht.2⟩ x₀ (hK't hy) i j' k l,
      fun t ht y hy s hs => ?_⟩
    refine le_trans (hrmbd t ht s hs i j' k l y hy) (le_max_right _ _)
  -- the chart Ricci components as `JBd` families of order `K + 1`
  set Bric : ℝ := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)
      * ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)
        * ((2 : ℝ) ^ (K + 1) * Bbig * Bbig)) with hBricdef
  have hBric_nn : 0 ≤ Bric := by
    rw [hBricdef]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (K + 1) := by positivity
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg h2 hBbig_nn) hBbig_nn))
  have hRic : ∀ (a b : Fin (Module.finrank ℝ E)), JBd (T / 2) T K' (K + 1)
      (fun t y => ricArr (I := I) (M := M) G x₀ t y a b) Bric := by
    intro a b
    refine (JBd.sum (fun k => JBd.sum (fun l => JBd.mul (hInvM k l) (hRmM k a l b)))).congr
      (fun t y => ?_)
    rfl
  -- the directional derivatives of the Ricci components
  set Bn : ℝ := ∑ i : Fin (Module.finrank ℝ E), ‖Work.Diff.EXT.bB (E := E) i‖ with hBndef
  have hBn_nn : 0 ≤ Bn := by rw [hBndef]; exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hBn_le : ∀ i : Fin (Module.finrank ℝ E), ‖Work.Diff.EXT.bB (E := E) i‖ ≤ Bn := by
    intro i
    rw [hBndef]
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  -- the Christoffel symbols of the initial metric as `JBd` families of order `K`
  have hCgM : ∀ (p i j : Fin (Module.finrank ℝ E)), JBd (T / 2) T K' K
      (fun _ y => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j) Bcg := by
    intro p i j
    refine ⟨fun t ht y hy =>
      Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ (hK't hy) p i j,
      fun t ht y hy s hs => ?_⟩
    exact le_trans (hCcgbd s hs y hy p i j) (hCcg_le s hs)
  -- the two summands of `reactExpr`, and the final combination
  set Bmax : ℝ := max Bric Bcg with hBmaxdef
  -- the derivative terms
  have hF1 : ∀ (a b c : Fin (Module.finrank ℝ E)), JBd (T / 2) T K' K
      (fun t y => fderiv ℝ (fun y' : E => ricArr (I := I) (M := M) G x₀ t y' a b) y
        (Work.Diff.EXT.bB (E := E) c)) (Bn * Bric) := by
    intro a b c
    refine (JBd.fderiv_apply (Work.Diff.EXT.bB (E := E) c) (hRic a b)).weaken ?_
    exact mul_le_mul_of_nonneg_right (hBn_le c) hBric_nn
  refine ⟨max ((((Bn * Bric) + (Bn * Bric)) + (Bn * Bric))
      + |(2 : ℝ)| * ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)
          * ((2 : ℝ) ^ K * Bmax * Bmax))) 0, le_max_right _ _, ?_⟩
  intro t ht m hm i j l y hy
  have hX : JBd (T / 2) T K' K
      (fun t y => - (fderiv ℝ (fun y' : E => ricArr (I := I) (M := M) G x₀ t y' j l) y
            (Work.Diff.EXT.bB (E := E) i)
          + fderiv ℝ (fun y' : E => ricArr (I := I) (M := M) G x₀ t y' i l) y
            (Work.Diff.EXT.bB (E := E) j)
          - fderiv ℝ (fun y' : E => ricArr (I := I) (M := M) G x₀ t y' i j) y
            (Work.Diff.EXT.bB (E := E) l)))
      (((Bn * Bric) + (Bn * Bric)) + (Bn * Bric)) :=
    (((hF1 j l i).add (hF1 i l j)).sub (hF1 i j l)).neg
  have hProd : ∀ p : Fin (Module.finrank ℝ E), JBd (T / 2) T K' K
      (fun t y => ricArr (I := I) (M := M) G x₀ t y l p *
        Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      ((2 : ℝ) ^ K * Bmax * Bmax) := fun p =>
    JBd.mul ((hRic l p).mono (Nat.le_succ K) |>.weaken (le_max_left _ _))
      ((hCgM p i j).weaken (le_max_right _ _))
  have hY : JBd (T / 2) T K' K
      (fun t y => 2 * ∑ p : Fin (Module.finrank ℝ E), ricArr (I := I) (M := M) G x₀ t y l p *
        Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      (|(2 : ℝ)| * ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)
        * ((2 : ℝ) ^ K * Bmax * Bmax))) :=
    JBd.const_mul 2 (JBd.sum hProd)
  have hfin : JBd (T / 2) T K' K (fun t y => reactExpr (I := I) (M := M) G x₀ i j l t y)
      ((((Bn * Bric) + (Bn * Bric)) + (Bn * Bric))
        + |(2 : ℝ)| * ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)
          * ((2 : ℝ) ^ K * Bmax * Bmax))) :=
    (hX.add hY).congr (fun t y => rfl)
  refine le_trans ?_ (le_max_left _ _)
  simpa only [] using hfin.2 t ht y hy m hm


/-! ## The identity `reactArr = reactExpr`, and the jet bounds for `reactArr` -/

/-- **The pointwise identity `reactArr = reactExpr`.**  For an interior time `t ∈ (0,T)` and a point
`y` of the chart target at `x₀`, the reaction array `∂_t aComp` (which is `reactArr` by definition)
equals the explicit chart expression `reactExpr`:  `aComp` is the Koszul pairing minus the
`G 0`-Christoffel contribution, the time derivative of the Koszul pairing is Clairaut's theorem
(`deriv_sKz_dJet1`), the time derivative of the chart matrix is `-2 Ric`
(`hasDerivAt_chartMat_entry`) and the chart Ricci matrix is the inverse-Gram contraction of the
chart curvature (`ricFun_eq_ricArr`). -/
theorem reactArr_eq_reactExpr
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j l : Fin (Module.finrank ℝ E)) :
    reactArr (I := I) (M := M) G x₀ t y i j l
      = reactExpr (I := I) (M := M) G x₀ i j l t y := by
  -- the derivative of the Koszul term
  have h1 : HasDerivAt (fun s : ℝ => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G s) x₀ y) i j l)
      (- (fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' j l) y
            (Work.Diff.EXT.bB (E := E) i)
         + fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i l) y
            (Work.Diff.EXT.bB (E := E) j)
         - fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i j) y
            (Work.Diff.EXT.bB (E := E) l))) t :=
    deriv_sKz_dJet1 (I := I) (M := M) hflow ht x₀ hy i j l
  -- the derivative of the `G 0`-Christoffel term
  have h2 : HasDerivAt (fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s y l p
          * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      (∑ p : Fin (Module.finrank ℝ E),
        (-2 * ricFun (I := I) (M := M) G x₀ t y l p)
          * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j) t := by
    have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (A := fun p s => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s y l p
        * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      (A' := fun p => (-2 * ricFun (I := I) (M := M) G x₀ t y l p)
        * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      (fun p _ => by
        have hp : HasDerivAt (fun s : ℝ => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s y l p)
            (-2 * ricFun (I := I) (M := M) G x₀ t y l p) t :=
          hasDerivAt_chartMat_entry (I := I) (M := M) hflow ht x₀ y l p
        simpa only [smul_eq_mul, mul_zero, add_zero] using
          hp.smul_const (Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j))
    have hfun : (∑ p : Fin (Module.finrank ℝ E), fun s : ℝ =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s y l p
            * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
        = fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s y l p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j := by
      funext s
      rw [Finset.sum_apply]
    rw [hfun] at hsum
    exact hsum
  -- `reactArr` is the time derivative of `aComp`, which is the Koszul term minus the second term
  have hmain : deriv (fun s : ℝ => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ s y i j l) t
      = (- (fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' j l) y
              (Work.Diff.EXT.bB (E := E) i)
           + fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i l) y
              (Work.Diff.EXT.bB (E := E) j)
           - fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i j) y
              (Work.Diff.EXT.bB (E := E) l)))
        - (∑ p : Fin (Module.finrank ℝ E),
            (-2 * ricFun (I := I) (M := M) G x₀ t y l p)
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j) := by
    have hev : (fun s : ℝ => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ s y i j l)
        =ᶠ[𝓝 t] (fun s : ℝ => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G s) x₀ y) i j l
          - ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s y l p
                * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j) :=
      Filter.Eventually.of_forall (fun s =>
        Work.Diff.EXT.ConnCov.aComp_eq_sKz_sub (I := I) (M := M) G x₀ s hy i j l)
    rw [hev.deriv_eq]
    exact (h1.sub h2).deriv
  -- rewrite `ricFun` as the inverse-Gram contraction of the curvature
  have hric_eq : ∀ (a b : Fin (Module.finrank ℝ E)),
      (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' a b)
        =ᶠ[𝓝 y] (fun y' : E => ricArr (I := I) (M := M) G x₀ t y' a b) := by
    intro a b
    filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hy] with y' hy'
    exact ricFun_eq_ricArr (I := I) (M := M) hLC G x₀ t hy' a b
  have hfd : ∀ (a b k : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' a b) y
          (Work.Diff.EXT.bB (E := E) k)
        = fderiv ℝ (fun y' : E => ricArr (I := I) (M := M) G x₀ t y' a b) y
            (Work.Diff.EXT.bB (E := E) k) := by
    intro a b k
    rw [(hric_eq a b).fderiv_eq]
  have hsum : (∑ p : Fin (Module.finrank ℝ E),
        (-2 * ricFun (I := I) (M := M) G x₀ t y l p)
          * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      = -2 * ∑ p : Fin (Module.finrank ℝ E),
          ricArr (I := I) (M := M) G x₀ t y l p
            * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [ricFun_eq_ricArr (I := I) (M := M) hLC G x₀ t hy l p]
    ring
  have hval : (- (fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' j l) y
              (Work.Diff.EXT.bB (E := E) i)
           + fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i l) y
              (Work.Diff.EXT.bB (E := E) j)
           - fderiv ℝ (fun y' : E => ricFun (I := I) (M := M) G x₀ t y' i j) y
              (Work.Diff.EXT.bB (E := E) l)))
        - (∑ p : Fin (Module.finrank ℝ E),
            (-2 * ricFun (I := I) (M := M) G x₀ t y l p)
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      = reactExpr (I := I) (M := M) G x₀ i j l t y := by
    rw [reactExpr, hfd j l i, hfd i l j, hfd i j l, hsum]
    ring
  rw [reactArr, hmain, hval]

/-- **Jet bounds of the reaction array `reactArr = ∂_t aComp`** — the statement requested as
`Work.Diff.EXT.ConnCov.reactArr_jets`, with a *fresh* name `m` for the derivative order.  In the
requested statement the order in the conclusion is the `Fin` index `j` (which shadows the `ℕ` binder
`j` of the hypothesis `j ≤ K`), so that statement demands bounds for the derivative orders `0,…,n-1`
independently of `K`; see the warning in `Work.Diff.EXT.ConnCov.reactJetsDefs`. -/
theorem reactArr_jets'
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (K : ℕ) (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (hrm : ∃ Crm : ℝ, 0 ≤ Crm ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ K + 1 →
      ∀ (i j' k l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j' k l t
            (Work.Diff.EXT.pt (I := I) x₀ y')) y‖ ≤ Crm)
    (hmat : ∃ Cmt : ℝ, 0 ≤ Cmt ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ K + 1 →
      ∀ (i j' : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j') y‖ ≤ Cmt)
    (hcomp : ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ K →
      ∀ (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j' l) y‖ ≤ Ca) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (m : ℕ), m ≤ K →
      ∀ (i j l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => reactArr (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ Cd := by
  obtain ⟨Cd, hCd0, hCd⟩ := reactExpr_jets (I := I) (M := M) G T C hT hC hflow hmet K x₀ K'
    hK'c hK't hrm hmat
  refine ⟨Cd, hCd0, ?_⟩
  intro t ht m hm i j l y hy
  have hev : (fun y' : E => reactArr (I := I) (M := M) G x₀ t y' i j l)
      =ᶠ[𝓝 y] (fun y' : E => reactExpr (I := I) (M := M) G x₀ i j l t y') := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds (hK't hy)] with y' hy'
    exact reactArr_eq_reactExpr (I := I) (M := M) hLC hflow ⟨by linarith [ht.1, hT], ht.2⟩ x₀ hy' i j l
  rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
  exact hCd t ht m hm i j l y hy

end Work.Diff.EXT.ConnCov
