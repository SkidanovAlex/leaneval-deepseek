import Mathlib
import Submission.Work.Diff.STE.Lead.chartMatJetDefs
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.contDiffOn_chartComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness and second-order jet bounds for the frame-change coefficients `Bmat`

`Bmat D i a p z = g₀(∂_a, e_p)` is the frame-change coefficient of the coordinate-frame vector
`∂_a` of the chart at `x₀ i` in the `g₀`-orthonormal frame `e i`, at the point of flat coordinate
`z` (`Work.Diff.STE.Lead.Bmat`, see `chartMatJetDefs`).  This module proves the two facts about it
that the sharp jet bound of the chart matrix (`chartMatJet_sharp`) takes as hypotheses:

* **smoothness**: `Bmat D i a p` is `C²` at every `z` with `‖z‖ ≤ 2 * D.σ i` (in fact `C^∞`
  there, which is what the proof establishes);
* **jet bound**: there is a single `K ≥ 0` with `|pdRList l (Bmat D i a p) z| ≤ K` for all charts
  `i`, all `a p`, all `‖z‖ ≤ D.σ i` and all lists `l` of length `≤ 2`.

The proof of the smoothness is the same computation as in `Work.Diff.STE.contDiffOn_chartComp`:
on the chart source the section `x ↦ g₀.inner x (frameVector x₀ x A) (Z x)` is `C^∞` because the
metric is a smooth section of the bundle of bilinear forms and both tangent sections are smooth
(`Z` by hypothesis, the chart-constant field by `contMDiffAt_frameSection'`); composing with the
smooth inverse chart and the (affine, hence smooth) map `flatToE` gives the smoothness in `z`.  On
`‖z‖ ≤ 2 D.σ i` the point `flatToE (x₀ i) z` lies in the chart target (`B3Data.htarget`), which is
open, so the smoothness is *local* there — no global extension is needed.

The jet bound is then a compactness argument: `Bmat D i a p` is `C^∞` on the open set
`flatToE ⁻¹' target`, which contains the compact closed `σ i`-ball; the tower bound
`Work.Diff.STE.flat.compact_iteratedFDeriv_bound` bounds `‖iteratedFDeriv ℝ j‖` for `j ≤ 2` there,
and the three possible lists `l` (`[]`, `[q]`, `[q,p]`) are converted into the corresponding
iterated derivatives (`norm_iteratedFDeriv_zero`, `norm_iteratedFDeriv_one`, and
`pdR_pdR_eq_iteratedFDeriv_two`).  Finally the finitely many chartwise constants are summed.
-/

noncomputable section

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField Metric Filter

namespace Work.Diff.STE.Lead

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. Iterated partial derivatives of order `≤ 2` -/

private lemma pdRList_nil {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ) :
    Work.Diff.STE.pdRList ([] : List ι) f = f := rfl

private lemma pdRList_singleton {ι : Type*} [DecidableEq ι] (i : ι) (f : (ι → ℝ) → ℝ) :
    Work.Diff.STE.pdRList [i] f = Work.Diff.STE.pdR i f := rfl

private lemma pdRList_pair {ι : Type*} [DecidableEq ι] (i j : ι) (f : (ι → ℝ) → ℝ) :
    Work.Diff.STE.pdRList [i, j] f = Work.Diff.STE.pdR i (Work.Diff.STE.pdR j f) := rfl

/-- `pdR q (pdR p f) z` is the second iterated derivative of `f` at `z` evaluated on the tuple
`(∂_q, ∂_p) = ![single q 1, single p 1]`.

This is the chain rule hidden in `DifferentiableAt.iteratedFDeriv_succ_apply_left'` at `n = 1`,
applied to the function `y ↦ fderiv ℝ f y (single p 1) = pdR p f y`; only differentiability of
`fderiv ℝ f` at `z` is needed (the original in `matA_jets` assumes global smoothness). -/
private lemma pdR_pdR_eq_iteratedFDeriv_two {n : ℕ} (f : (Fin n → ℝ) → ℝ) {z : Fin n → ℝ}
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) z) (p q : Fin n) :
    Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z =
      iteratedFDeriv ℝ 2 f z (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)) := by
  have hk : iteratedFDeriv ℝ 2 f z (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)) =
      (fderiv ℝ (fun y => (iteratedFDeriv ℝ 1 f y)
        (Fin.tail (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)))) z)
        ((![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)) 0) := by
    simpa using hd.iteratedFDeriv_succ_apply_left'
      (m := (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)))
  rw [hk]
  rw [show (fun y => (iteratedFDeriv ℝ 1 f y)
        (Fin.tail (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ))))
      = fun y => fderiv ℝ f y (Pi.single p 1) from by
    funext y
    rw [iteratedFDeriv_one_apply]
    rfl]
  rfl

/-- The second derivative tuple `![single q 1, single p 1]` has multilinear norm `1`. -/
private lemma norm_prod_tuple_two {n : ℕ} (p q : Fin n) :
    ∏ i : Fin 2, ‖(![Pi.single q (1 : ℝ), Pi.single p (1 : ℝ)] :
      Fin 2 → (Fin n → ℝ)) i‖ = 1 := by
  rw [Fin.prod_univ_two]
  simp [Pi.norm_single]

/-! ## 2. Smoothness of the frame-change coefficient -/

/-- The frame-change coefficient read in the chart coordinate `y` (the "chart-side" form of
`Bmat`, before composing with the affine map `flatToE`). -/
private noncomputable def Bchart (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a p : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => g₀.inner ((extChartAt I (D.x₀ i)).symm y)
    (Submission.Geodesic.frameVector (I := I) (D.x₀ i) ((extChartAt I (D.x₀ i)).symm y)
      (Work.Diff.EXT.bB (E := E) a))
    (D.e i p ((extChartAt I (D.x₀ i)).symm y))

/-- `Bmat D i a p` is the composition of the chart-side coefficient with `flatToE (x₀ i)`. -/
private lemma Bmat_eq_comp_Bchart (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a p : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p
      = Bchart (I := I) (M := M) (g₀ := g₀) D i a p ∘ Work.Diff.STE.flatToE (I := I) (D.x₀ i) :=
  rfl

/-- The metric paired with a chart-constant field and a globally smooth field is smooth on the
chart source.  (`Work.Diff.STE.contMDiffOn_metricComp` with the second chart-constant field
replaced by an arbitrary globally `C^∞` one.) -/
private lemma contMDiffOn_metricComp_frame (g : Submission.Diff.SMet I M) (x₀ : M) (A : E)
    {Z : Π y : M, TangentSpace I y} (hZ : CMDiff ∞ (T% Z)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => g.inner x (Submission.Geodesic.frameVector (I := I) x₀ x A) (Z x))
      (chartAt H x₀).source := by
  intro x hx
  have hψ := (g.contMDiff (x := x)).contMDiffWithinAt (s := (chartAt H x₀).source)
  have hv := (Work.Diff.STE.contMDiffAt_frameSection' (I := I) x₀ A hx).contMDiffWithinAt
    (s := (chartAt H x₀).source)
  have hw := (hZ (x := x)).contMDiffWithinAt (s := (chartAt H x₀).source)
  have h := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
  simp only [contMDiffWithinAt_totalSpace] at h
  exact h.2

/-- **The frame-change coefficient is `C^∞` in the chart coordinate**, on the chart target. -/
private lemma Bchart_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a p : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Bchart (I := I) (M := M) (g₀ := g₀) D i a p)
      (extChartAt I (D.x₀ i)).target := by
  have hsec : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => g₀.inner x
        (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
        (D.e i p x)) (chartAt H (D.x₀ i)).source :=
    contMDiffOn_metricComp_frame (I := I) (M := M) g₀ (D.x₀ i) (Work.Diff.EXT.bB (E := E) a)
      (D.hesm i p)
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => g₀.inner x
        (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
        (D.e i p x)) ∘ (extChartAt I (D.x₀ i)).symm) (extChartAt I (D.x₀ i)).target :=
    hsec.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := ∞)) (fun y hy => by
      rw [← extChartAt_source (I := I) (D.x₀ i)]
      exact (extChartAt I (D.x₀ i)).map_target hy)
  exact hcomp.contDiffOn

/-- **`Bmat D i a p` is `C^∞` on the preimage of the chart target under `flatToE`.** -/
private lemma Bmat_contDiffOn_preimage (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) (a p : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) ⁻¹' (extChartAt I (D.x₀ i)).target) := by
  have hb := Bchart_contDiffOn (I := I) (M := M) (g₀ := g₀) D i a p
  have hfl : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.flatToE (I := I) (D.x₀ i))
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) ⁻¹' (extChartAt I (D.x₀ i)).target) :=
    (Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffOn.mono (Set.subset_univ _)
  have hcomp := hb.comp hfl (fun z hz => hz)
  rwa [← Bmat_eq_comp_Bchart] at hcomp

/-- The preimage of the chart target under `flatToE` is open. -/
private lemma isOpen_flatToE_preimage_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) :
    IsOpen (Work.Diff.STE.flatToE (I := I) (D.x₀ i) ⁻¹' (extChartAt I (D.x₀ i)).target) :=
  (isOpen_extChartAt_target (I := I) (D.x₀ i)).preimage
    ((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ i)).continuous)

/-! ## 3. The target theorem -/

theorem Bmat_smooth_jets_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    (∀ (i : ι₀) (a p : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i →
        ContDiffAt ℝ 2 (Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p) z)
    ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : ι₀) (a p : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i →
        ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p) z| ≤ K := by
  classical
  have hns : ∀ (i : ι₀) (a p : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
      ContDiffAt ℝ 2 (Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p) z := by
    intro i a p z hz
    have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      D.htarget i z hz
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p) z :=
      (Bmat_contDiffOn_preimage (I := I) (M := M) (g₀ := g₀) D i a p).contDiffAt
        ((isOpen_flatToE_preimage_target (I := I) (M := M) D i).mem_nhds hzt)
    exact h1.of_le (by norm_num)
  refine ⟨hns, ?_⟩
  -- chartwise bounds
  have hper : ∀ (i : ι₀) (a p : Fin (Module.finrank ℝ E)), ∃ Ki : ℝ, 0 ≤ Ki ∧
      ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i →
      ∀ (l : List (Fin (Module.finrank ℝ E))), l.length ≤ 2 →
        |Work.Diff.STE.pdRList l (Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p) z| ≤ Ki := by
    intro i a p
    let f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
      Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p
    have hUopen := isOpen_flatToE_preimage_target (I := I) (M := M) D i
    have hUcd := Bmat_contDiffOn_preimage (I := I) (M := M) (g₀ := g₀) D i a p
    have hsub : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) ⊆
        Work.Diff.STE.flatToE (I := I) (D.x₀ i) ⁻¹' (extChartAt I (D.x₀ i)).target := by
      intro z hzmem
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hzmem
      exact D.htarget i z (by linarith [D.hσ i])
    obtain ⟨Ki, hKi0, hKi⟩ := Work.Diff.STE.flat.compact_iteratedFDeriv_bound
      (Work.Diff.STE.Lead.Bmat (I := I) (M := M) D i a p) hUopen hUcd
      (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)) hsub 2
    refine ⟨Ki, hKi0, ?_⟩
    intro z hz l hl
    change |Work.Diff.STE.pdRList l f z| ≤ Ki
    have hzmem : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hz
    have hb0 := hKi z hzmem 0 (by norm_num)
    have hb1 := hKi z hzmem 1 (by norm_num)
    have hb2 := hKi z hzmem 2 (by norm_num)
    rcases l with _ | ⟨q, l⟩
    · -- `l = []`
      simpa only [pdRList_nil, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb0
    · rcases l with _ | ⟨p', l⟩
      · -- `l = [q]`
        have hpd : |Work.Diff.STE.pdRList [q] f z| =
            ‖(fderiv ℝ f z) (Pi.single q (1 : ℝ))‖ := by
          rw [pdRList_singleton]
          exact (Real.norm_eq_abs _).symm
        rw [hpd]
        calc ‖(fderiv ℝ f z) (Pi.single q (1 : ℝ))‖
            ≤ ‖fderiv ℝ f z‖ *
                ‖(Pi.single q (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ f z‖ := by rw [Pi.norm_single]; simp
          _ = ‖iteratedFDeriv ℝ 1 f z‖ := (norm_iteratedFDeriv_one f).symm
          _ ≤ Ki := hb1
      · rcases l with _ | ⟨r, l⟩
        · -- `l = [q, p']`
          have h2 : ContDiffAt ℝ 2 f z := hns i a p z (by linarith [D.hσ i])
          have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) z :=
            (h2.iteratedFDeriv_right (m := (1 : WithTop ℕ∞)) (i := 1)
              (by norm_num)).differentiableAt (by norm_num)
          rw [pdRList_pair, pdR_pdR_eq_iteratedFDeriv_two f hd p' q]
          have habs : |(iteratedFDeriv ℝ 2 f z)
                (![Pi.single q 1, Pi.single p' 1] : Fin 2 → (Fin (Module.finrank ℝ E) → ℝ))| =
              ‖(iteratedFDeriv ℝ 2 f z)
                (![Pi.single q 1, Pi.single p' 1] : Fin 2 → (Fin (Module.finrank ℝ E) → ℝ))‖ :=
            (Real.norm_eq_abs _).symm
          rw [habs]
          calc ‖(iteratedFDeriv ℝ 2 f z)
                (![Pi.single q 1, Pi.single p' 1] :
                  Fin 2 → (Fin (Module.finrank ℝ E) → ℝ))‖
              ≤ ‖iteratedFDeriv ℝ 2 f z‖ * ∏ i : Fin 2,
                  ‖(![Pi.single q 1, Pi.single p' 1] :
                    Fin 2 → (Fin (Module.finrank ℝ E) → ℝ)) i‖ :=
                ContinuousMultilinearMap.le_opNorm _ _
            _ = ‖iteratedFDeriv ℝ 2 f z‖ := by rw [norm_prod_tuple_two, mul_one]
            _ ≤ Ki := hb2
        · -- `l` has length at least `3`
          exfalso
          simp only [List.length_cons] at hl
          omega
  choose Kf hKf0 hKf using hper
  refine ⟨∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ p : Fin (Module.finrank ℝ E), Kf i a p,
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun p _ => hKf0 i a p, ?_⟩
  intro i a p z hz l hl
  have hle1 : Kf i a p ≤ ∑ p' : Fin (Module.finrank ℝ E), Kf i a p' :=
    Finset.single_le_sum (fun p' _ => hKf0 i a p') (Finset.mem_univ p)
  have hle2 : (∑ p' : Fin (Module.finrank ℝ E), Kf i a p') ≤
      ∑ a' : Fin (Module.finrank ℝ E), ∑ p' : Fin (Module.finrank ℝ E), Kf i a' p' :=
    Finset.single_le_sum (fun a' _ => Finset.sum_nonneg fun p' _ => hKf0 i a' p')
      (Finset.mem_univ a)
  have hle3 : (∑ a' : Fin (Module.finrank ℝ E), ∑ p' : Fin (Module.finrank ℝ E), Kf i a' p') ≤
      ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E),
        ∑ p' : Fin (Module.finrank ℝ E), Kf i' a' p' :=
    Finset.single_le_sum
      (fun i' _ => Finset.sum_nonneg fun a' _ =>
        Finset.sum_nonneg fun p' _ => hKf0 i' a' p') (Finset.mem_univ i)
  exact le_trans (hKf i a p z hz l hl) (le_trans hle1 (le_trans hle2 hle3))

end Work.Diff.STE.Lead
