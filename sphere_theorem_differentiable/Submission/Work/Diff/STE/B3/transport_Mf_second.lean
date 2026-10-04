import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_triple2
import Submission.Work.Diff.STE.B3.transport_tame_leibniz
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second derivative of the frame-change identity `Mf = Ff · Gf · Ffᵀ`

On the chart target of the chart at `D.x₀ j`, the `g₀`-orthonormal-frame chart matrix of a section
`h` factors through the coordinate-frame chart matrix:
`Mf z a b = Σ_{ik} Ff z a i * Gf z i k * Ff z b k`
(`Work.Diff.STE.B3.Mf_eq`, whose hypothesis `‖z‖ ≤ 2 * D.σ j` is used only to know that the flat
coordinate lies in the chart target — an *open* condition, hence valid in a neighbourhood of `z`).

This file differentiates that identity twice at `z` (the target statement of this module):

`∂_c∂_d Mf a b = eightTerm + Σ_{ik} Ff z a i * ∂_c∂_d Gf i k * Ff z b k`,

where the eight terms collected in `Work.Diff.STE.B3.eightTerm` are those of the nine-term Leibniz
expansion of `∂_c∂_d (Ff · Gf · Ff)` which do **not** contain `∂_c∂_d Gf`.

Route:

* the two sides of the frame-change identity agree on the *neighbourhood* of `z` where
  `flatToE (x₀ j) · ∈ (extChartAt I (x₀ j)).target`, and `pdR c (pdR d ·) z` depends only on the
  germ at `z` (`pdR2_congr`);
* `Σ_{ik}` is pulled out of the two derivatives (`pdR2_fun_sum_at`, already proved in
  `Diff/STE/B3/transport_tame_leibniz`);
* each summand is expanded by the local nine-term Leibniz rule for a triple product
  (`pdR2_triple_at`, same file).

The only genuinely geometric inputs are the smoothness on that neighbourhood of the two factor
families:

* `Gf z i k = h(∂_i, ∂_k)(pt j z)` is smooth by the hypothesis `ChartData h`;
* `Ff z a i = coordCLM (x₀ j) (pt j z) i (e j a (pt j z))` is smooth because `e j a` is a smooth
  section of the tangent bundle and the coordinates of a smooth section in the trivialisation at
  `x₀ j` are smooth (`Trivialization.contMDiffAt_section_iff`), composed with the smooth chart
  parametrisation `pt j = (extChartAt I (x₀ j)).symm ∘ flatToE`
  (`Work.Diff.STE.B3Data.contMDiffAt_pt`).
-/

namespace Work.Diff.STE.B3

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-! ## 1. Germ invariance of the partial derivatives -/

/-- `pdR c` depends only on the germ at the point. -/
lemma pdR_congr {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (h : f =ᶠ[𝓝 z] g) (c : Fin n) :
    Work.Diff.STE.pdR c f z = Work.Diff.STE.pdR c g z := by
  rw [Work.Diff.STE.pdR, Work.Diff.STE.pdR, h.fderiv_eq]

/-- `pdR c (pdR d ·) z` depends only on the germ at the point. -/
lemma pdR2_congr {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (h : f =ᶠ[𝓝 z] g) (c d : Fin n) :
    Work.Diff.STE.pdR c (Work.Diff.STE.pdR d f) z
      = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d g) z := by
  obtain ⟨t, ht_sub, ht_open, hzt⟩ := _root_.mem_nhds_iff.mp h
  refine pdR_congr ?_ c
  refine Filter.mem_of_superset (ht_open.mem_nhds hzt) ?_
  intro y hy
  exact pdR_congr (Filter.eventually_of_mem (ht_open.mem_nhds hy)
    (fun w hw => ht_sub hw)) d

/-! ## 2. The frame-change identity on the chart target -/

/-- On the chart target, the point of flat coordinate `z` lies in the chart source. -/
lemma pt_mem_source_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    D.pt j z ∈ (chartAt H (D.x₀ j)).source := by
  have h1 : D.pt j z ∈ (extChartAt I (D.x₀ j)).source :=
    (extChartAt I (D.x₀ j)).map_target hz
  rwa [extChartAt_source] at h1

/-- The expansion of the orthonormal frame vector `e j a` in the coordinate frame of the chart at
`x₀ j`, valid wherever the flat coordinate lies in the chart target. -/
lemma ef_expand_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    D.e j a (D.pt j z)
      = ∑ i, Ff (I := I) (M := M) D j z a i
          • Work.Diff.GE.cFrame (I := I) (D.x₀ j) i (D.pt j z) :=
  Work.Diff.STE.D.psi.self_eq_sum_coordCLM_smul_cFrame (I := I) (M := M) (D.x₀ j)
    (pt_mem_source_of_target (I := I) (M := M) D j hz) (D.e j a (D.pt j z))

/-- **The frame-change identity on the chart target**: the orthonormal-frame chart matrix is the
coordinate-frame chart matrix conjugated by the frame matrix. -/
lemma Mf_eq_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    Mf (I := I) (M := M) D h j z a b
      = ∑ i, ∑ k, Ff (I := I) (M := M) D j z a i * Gf (I := I) (M := M) D h j z i k
          * Ff (I := I) (M := M) D j z b k := by
  simp only [Mf, Gf, Work.Diff.STE.B3Data.mat, Work.Diff.STE.D.chartMatOf_apply]
  rw [ef_expand_of_target (I := I) (M := M) D j a hz,
    ef_expand_of_target (I := I) (M := M) D j b hz]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Gf, yf, Work.Diff.STE.B3Data.pt, Work.Diff.GE.cFrame_apply, Work.Diff.GE.cBasis,
    Work.Diff.EXT.bB]
  ac_rfl

/-! ## 3. Smoothness of the two factor families -/

/-- **Smoothness of the frame matrix** `Ff z a i = coordCLM (x₀ j) (pt j z) i (e j a (pt j z))`.

The coordinates of the smooth section `e j a` in the trivialisation of the tangent bundle at
`x₀ j` are smooth (`Trivialization.contMDiffAt_section_iff`), and `pt j ·` is smooth on the chart
target, so the composite is smooth. -/
lemma Ff_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a i : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ ∞ (fun y : Fin (Module.finrank ℝ E) → ℝ => Ff (I := I) (M := M) D j y a i) z := by
  -- the trivialisation at `x₀ j` and the two neighbourhoods involved
  have hpt : ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I ∞ (D.pt j) z :=
    D.contMDiffAt_pt j hz
  have hsrc : D.pt j z ∈ (extChartAt I (D.x₀ j)).source :=
    (extChartAt I (D.x₀ j)).map_target hz
  have hbs : D.pt j z ∈ (trivializationAt E (TangentSpace I) (D.x₀ j)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hsrc
  -- smoothness of the trivialisation coordinates of `e j a` on `M`
  have hsm : CMDiffAt ∞ (T% (D.e j a)) (D.pt j z) := (D.hesm j a).contMDiffAt
  have hkey := (Trivialization.contMDiffAt_section_iff
    (trivializationAt E (TangentSpace I) (D.x₀ j)) hbs).mp hsm
  -- compose with the chart parametrisation
  have hcomp : ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) 𝓘(ℝ, E) ∞
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((trivializationAt E (TangentSpace I) (D.x₀ j))
          ⟨D.pt j y, D.e j a (D.pt j y)⟩).2) z := by
    simpa only [Function.comp_def] using hkey.comp z hpt
  have hcomp' : ContDiffAt ℝ ∞
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((trivializationAt E (TangentSpace I) (D.x₀ j))
          ⟨D.pt j y, D.e j a (D.pt j y)⟩).2) z :=
    contMDiffAt_iff_contDiffAt.mp hcomp
  -- apply the coordinate functional
  have hcoord : ContDiffAt ℝ ∞
      (fun y : Fin (Module.finrank ℝ E) → ℝ => (Work.Diff.EXT.bB (E := E)).coord i
        ((trivializationAt E (TangentSpace I) (D.x₀ j))
          ⟨D.pt j y, D.e j a (D.pt j y)⟩).2) z := by
    have hc : ContDiffAt ℝ ∞ (fun _ : Fin (Module.finrank ℝ E) → ℝ =>
        ((Work.Diff.EXT.bB (E := E)).coord i).toContinuousLinearMap) z := contDiffAt_const
    refine (hc.clm_apply hcomp').congr_of_eventuallyEq (EventuallyEq.of_eq ?_)
    funext y
    simp only [LinearMap.coe_toContinuousLinearMap']
  -- identify with `Ff` on a neighbourhood of `z`
  have hev : (fun y : Fin (Module.finrank ℝ E) → ℝ => Ff (I := I) (M := M) D j y a i)
      =ᶠ[𝓝 z] (fun y : Fin (Module.finrank ℝ E) → ℝ => (Work.Diff.EXT.bB (E := E)).coord i
        ((trivializationAt E (TangentSpace I) (D.x₀ j))
          ⟨D.pt j y, D.e j a (D.pt j y)⟩).2) := by
    filter_upwards [((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds hz] with y hy
    have hsrcy : D.pt j y ∈ (extChartAt I (D.x₀ j)).source :=
      (extChartAt I (D.x₀ j)).map_target hy
    have hbsy : D.pt j y ∈ (trivializationAt E (TangentSpace I) (D.x₀ j)).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      rwa [extChartAt_source] at hsrcy
    simp only [Ff, Work.Diff.STE.D.coordCLM_apply, Work.Diff.STE.D.chartCoordOf]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hbsy]
  exact hcoord.congr_of_eventuallyEq hev

/-- **Smoothness of the coordinate-frame chart matrix** `Gf z i k = h(∂_i, ∂_k)(pt j z)`, from the
smoothness hypothesis `ChartData h`. -/
lemma Gf_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (i k : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ ∞
      (fun y : Fin (Module.finrank ℝ E) → ℝ => Gf (I := I) (M := M) D h j y i k) z := by
  have h1 : ContDiffAt ℝ ∞ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
      (flatToE (I := I) (D.x₀ j) z) :=
    (hsmooth (D.x₀ j)).contDiffAt
      ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds hz)
  have h2 : ContDiffAt ℝ ∞ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)
        (flatToE (I := I) (D.x₀ j) y)) z :=
    h1.comp z ((Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).contDiffAt)
  have h3 : ContDiffAt ℝ ∞ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)
        (flatToE (I := I) (D.x₀ j) y) i) z := (contDiffAt_pi.mp h2) i
  have h4 : ContDiffAt ℝ ∞ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)
        (flatToE (I := I) (D.x₀ j) y) i k) z := (contDiffAt_pi.mp h3) k
  refine h4.congr_of_eventuallyEq (EventuallyEq.of_eq ?_)
  funext y
  rfl

end

theorem transport_Mf_second
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (c d a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.pdR c
        (Work.Diff.STE.pdR d
          (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b)) z
      = Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z c d a b
        + ∑ i, ∑ k, Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
            * (Work.Diff.STE.pdR c
                (Work.Diff.STE.pdR d
                  (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z)
            * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k := by
  classical
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    D.htarget j z hz
  -- the flat coordinates stay in the chart target on a neighbourhood of `z`
  have hU : ∀ᶠ y in 𝓝 z,
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
    ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds hzt
  -- smoothness of the two factor families at `z`
  have hFf : ∀ (a i : Fin (Module.finrank ℝ E)), ContDiffAt ℝ ∞
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z :=
    fun a i => Ff_contDiffAt (I := I) (M := M) D j a i hzt
  have hGf : ∀ (i k : Fin (Module.finrank ℝ E)), ContDiffAt ℝ ∞
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z :=
    fun i k => Gf_contDiffAt (I := I) (M := M) D h hsmooth j i k hzt
  -- the frame-change identity in a neighbourhood
  have hev : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b)
      =ᶠ[𝓝 z] (fun y : Fin (Module.finrank ℝ E) → ℝ => ∑ i, ∑ k,
        Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
          * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) := by
    filter_upwards [hU] with y hy
    exact Mf_eq_of_target (I := I) (M := M) D h j a b hy
  rw [pdR2_congr hev c d]
  -- differentiate the finite sum twice
  have hpartial : ∀ i : Fin (Module.finrank ℝ E), ContDiffAt ℝ 2
      (fun y : Fin (Module.finrank ℝ E) → ℝ => ∑ k,
        Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
          * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z := by
    intro i
    refine ContDiffAt.sum (fun k _ => ?_)
    exact ContDiffAt.mul (ContDiffAt.mul ((hFf a i).of_le (by norm_num))
      ((hGf i k).of_le (by norm_num))) ((hFf b k).of_le (by norm_num))
  rw [pdR2_fun_sum_at c d hpartial]
  rw [Finset.sum_congr rfl (fun i _ => pdR2_fun_sum_at c d
    (fun k => ContDiffAt.mul (ContDiffAt.mul ((hFf a i).of_le (by norm_num))
      ((hGf i k).of_le (by norm_num))) ((hFf b k).of_le (by norm_num))))]
  -- the nine-term expansion of each summand, with the `∂_c∂_d Gf` term isolated
  have hpoint : ∀ (i k : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
            * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k
            * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k)) z
        = ( Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
              (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i)) z
              * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
              * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
          + Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
              * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
              * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
          + Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
              * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
              * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
          + Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
              * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
              * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
          + Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
              * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
              * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
          + Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
              * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
              * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
          + Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
              * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
              * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
          + Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
              * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
              * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
                (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k)) z )
        + Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
            * (Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z)
            * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k := by
    intro i k
    rw [pdR2_triple_at c d ((hFf a i).of_le (by norm_num)) ((hGf i k).of_le (by norm_num))
      ((hFf b k).of_le (by norm_num))]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => hpoint i k))]
  simp only [Finset.sum_add_distrib, eightTerm]

end Work.Diff.STE.B3
