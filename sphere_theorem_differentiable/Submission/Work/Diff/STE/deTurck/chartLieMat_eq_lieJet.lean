import Mathlib
import Submission.Work.Diff.STE.LieMet
import Submission.Work.Diff.STE.deTurck.deTurckVec_eq_sum_chartComp
import Submission.Work.Diff.STE.deTurck.jointField_deTurckVec
import Submission.Work.Diff.STE.deTurck.koszulPair_eq_jKz
import Submission.Work.Diff.EXT.rmChartExpr_eq_jRm_jet
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.STE.deTurck.deTurckChartComp_eq_jWU
import Submission.Work.Diff.STE.deTurck.lcOf_pairing_frame
import Submission.Work.Diff.STE.deTurck.contMDiffAt_deTurckChartComp_at
import Submission.Work.Diff.STE.deTurck.deTurckChartComp_mvfderiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart matrix of the Lie derivative `L_{W(g)}g` is the jet expression `jLW`

The *geometric* chart matrix of the Lie derivative of the metric `g` along the DeTurck field
`W(g) = tr_g(∇^g - ∇^{gbar})` is `Work.Diff.STE.DeTurck.chartLieMat g gbar x₀ y i j =
lieMet g W (χ⁻¹ y) (σᵢ) (σⱼ)` (`Submission.Work.Diff.STE.LieMet`), and the *jet-level* expression is
`Work.Diff.STE.DeTurck.lieJet g gbar x₀ y = jLW A L B Ã L̃ B̃`, where `(A,L,B)` is the spatial
`2`-jet of the chart matrix `chartMatFun g x₀` at the chart coordinate `y`
(`Submission.Work.Diff.STE.DeTurckJet`).  This file proves that the two agree.

The classical content, in coordinates: with `Γ^c_{ab}` the Christoffel symbols of `g` and
`Γ̃^c_{ab}` those of `gbar`, the DeTurck field is `W^c = ∑_{ij}γ^{ij}(Γ^c_{ij} - Γ̃^c_{ij})`, its
lowering is `W_b = g_{bc}W^c`, and the Lie derivative of the metric is

`(L_Wg)_{ab} = ∇_aW_b + ∇_bW_a = (∂_aW_b - Γ^c_{ab}W_c) + (∂_bW_a - Γ^c_{ba}W_c)`,

which is exactly `jnabW a b + jnabW b a = jLW A L B Ã L̃ B̃ a b` (see `DeTurckJet.lean`).

The proof is assembled from
* the pointwise chart expansion `deTurckVec_eq_sum_chartComp` of the DeTurck field,
* the value dictionary `deTurckChartComp_eq_jWU` (component `↔` jet expression),
* the differentiation of the chart components `deTurckChartComp_mvfderiv` (with, underneath,
  `gramInv_mvfderiv` and the `chrCoord`/`koszulPair` derivative bridges), and
* the metric compatibility identity `lcOf_pairing_frame`, which turns the pairing of `∇_{σᵢ}W`
  with the frame into the derivative of the pairing minus the Christoffel contraction.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

namespace Work.Diff.STE.deTurck

open Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

noncomputable section

/-! ## The chart matrix is the Gram matrix of the coordinate frame -/

/-- The Gram matrix `gmat` of the coordinate frame at the point with chart coordinate `y` is the
chart matrix `chartMatFun` (they are the same array). -/
lemma gmat_eq_chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    Work.Diff.EXT.gmat (I := I) g x₀ ((extChartAt I x₀).symm y)
      = Work.Diff.EXT.chartMatFun (I := I) g x₀ y := rfl

/-! ## The Christoffel symbol dictionary -/

/-- **The Christoffel symbol in the frame is its jet expression.**  The upper Christoffel symbol
`chrCoord c i j = ∑_p γ^{cp}Γ_{ijp}` of the coordinate frame at `x₀` is the jet expression
`jGamU A L c i j = ∑_p γ^{cp}jKz(L) i j p`, by the two dictionary lemmas
`GramInv_eq_jInv` (`GramInv = jInv (chartMatFun)`) and `koszulPair_eq_jKz`
(`koszulPair = jKz (fderiv chartMatFun)`). -/
lemma chrCoord_eq_jGamU (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (c i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.chrCoord (fun _ : ℝ => g) (I := I) x₀ c i j 0 ((extChartAt I x₀).symm y)
      = Work.Diff.EXT.jGamU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y) c i j := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  simp only [Work.Diff.GE.chrCoord, Work.Diff.EXT.jGamU]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Work.Diff.EXT.GramInv_eq_jInv (I := I) g x₀ y c p, gmat_eq_chartMatFun]
  rw [Work.Diff.STE.deTurck.koszulPair_eq_jKz (I := I) g x₀ hp i j p]
  rw [PartialEquiv.right_inv (extChartAt I x₀) hy]

/-! ## Elementary calculus lemmas on the manifold -/

/-- `mvfderiv` only depends on the germ at the base point. -/
lemma mvfderiv_congr_nhds {f h : M → ℝ} {x : M} (hf : f =ᶠ[𝓝 x] h) :
    mvfderiv I f x = mvfderiv I h x := by
  rw [mvfderiv, mvfderiv, hf.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq hf]
  all_goals first | rfl | (ext v; rfl)

/-- `mvfderiv` is additive over a finite sum of real-valued functions. -/
lemma mvfderiv_finset_sum {ι : Type*} (s : Finset ι) (F : ι → M → ℝ) {x : M}
    (hF : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ,ℝ) (F i) x) :
    mvfderiv I (fun y : M => ∑ i ∈ s, F i y) x = ∑ i ∈ s, mvfderiv I (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y : M => ∑ i ∈ (∅ : Finset ι), F i y) = fun _ : M => (0 : ℝ) := by
        funext y; simp
      rw [hz, mvfderiv_const]
      simp
  | insert a s ha ih =>
      have hsplit : (fun y : M => ∑ i ∈ insert a s, F i y)
          = F a + (fun y : M => ∑ i ∈ s, F i y) := by
        funext y; rw [Finset.sum_insert ha]; rfl
      have hMda : MDifferentiableAt I 𝓘(ℝ,ℝ) (F a) x := hF a (Finset.mem_insert_self a s)
      have hMds : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => ∑ i ∈ s, F i y) x := by
        have h := MDifferentiableAt.sum (t := s) (f := F)
          (fun i hi => hF i (Finset.mem_insert_of_mem hi))
        have hfun : (∑ i ∈ s, F i) = (fun y : M => ∑ i ∈ s, F i y) := by
          funext y; rw [Finset.sum_apply]
        rwa [hfun] at h
      rw [hsplit, mvfderiv_add hMda hMds, ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)),
        Finset.sum_insert ha]

/-! ## The jet tuple of `LieMet.lean` and the scalar jet -/

/-- The first component of the spatial `2`-jet is the value of the chart matrix. -/
lemma chartJet_fst (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    (Work.Diff.STE.DeTurck.chartJet g x₀ y).1
      = Work.Diff.EXT.chartMatFun (I := I) g x₀ y := rfl

/-- The second component of the spatial `2`-jet is the first derivative of the chart matrix. -/
lemma chartJet_snd_fst (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    (Work.Diff.STE.DeTurck.chartJet g x₀ y).2.1
      = fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y := rfl

/-- The third component of the spatial `2`-jet is the second derivative of the chart matrix. -/
lemma chartJet_snd_snd (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    (Work.Diff.STE.DeTurck.chartJet g x₀ y).2.2
      = fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀)) y := rfl

/-! ## The pairing of two coordinate frame vectors -/

/-- The metric pairing of two coordinate frame vectors is a chart matrix coefficient (with the two
indices exchanged, by the symmetry of the metric). -/
lemma inner_cFrame_eq_chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b : Fin (Module.finrank ℝ E)) :
    g.inner ((extChartAt I x₀).symm y)
        (Work.Diff.GE.cFrame (I := I) x₀ a ((extChartAt I x₀).symm y))
        (Work.Diff.GE.cFrame (I := I) x₀ b ((extChartAt I x₀).symm y))
      = Work.Diff.EXT.chartMatFun (I := I) g x₀ y b a := by
  rw [Work.Diff.GE.cFrame_apply, Work.Diff.GE.cFrame_apply]
  simp only [Work.Diff.EXT.chartMatFun]
  exact g.symm _ _ _

/-! ## The pairing derivative of a field given in the coordinate frame -/

/-- **The derivative of the metric pairing of a frame combination.**  If a field is a combination
`∑_c w_c σ_c` of the coordinate frame along coefficient functions `w_c`, then the derivative of its
pairing with `σ_j` in the direction `σ_i` is

`∑_c ((∂_iw_c) · g(σ_c,σ_j) + w_c · ∂_i g(σ_c,σ_j))
 = ∑_c (L(∂_i)_jc · w_c(p) + A_jc · ∂_iw_c)`,

the first jet `L = fderiv (chartMatFun g x₀) y` and the value `A = chartMatFun g x₀ y` providing the
two factors.  This is the Leibniz rule for the pairing, with the metric's symmetry used to bring the
indices into the order of `jdWb`. -/
theorem mvfderiv_metric_pairing_sum_frame
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j : Fin (Module.finrank ℝ E)) (w : Fin (Module.finrank ℝ E) → M → ℝ)
    (J D : Fin (Module.finrank ℝ E) → ℝ)
    (hw : ∀ c, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (w c) ((extChartAt I x₀).symm y))
    (hval : ∀ c, w c ((extChartAt I x₀).symm y) = J c)
    (hdw : ∀ c, mvfderiv I (w c) ((extChartAt I x₀).symm y)
        (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y)) = D c) :
    mvfderiv I (fun q : M => g.inner q
        (∑ c, w c q • Work.Diff.GE.cFrame (I := I) x₀ c q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q))
      ((extChartAt I x₀).symm y)
      (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
      = ∑ c, ((fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
            (Work.Diff.EXT.bB (E := E) i)) j c * J c
          + ∑ c, Work.Diff.EXT.chartMatFun (I := I) g x₀ y j c * D c := by
  classical
  set p : M := (extChartAt I x₀).symm y with hpdef
  have hp : p ∈ (chartAt H x₀).source := by
    rw [hpdef, ← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hpy : (extChartAt I x₀) p = y := by
    rw [hpdef]; exact PartialEquiv.right_inv (extChartAt I x₀) hy
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hframe : ∀ c : Fin (Module.finrank ℝ E),
      ContMDiffAt I I.tangent ∞ (T% (Work.Diff.GE.cFrame (I := I) x₀ c)) p :=
    fun c => Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (Module.finBasis ℝ E c) hp
  have hGsm : ∀ c : Fin (Module.finrank ℝ E), ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun q : M => g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q)) p :=
    fun c => Work.Diff.GE.smooth_onframe_pairing (I := I) g p (hframe c) (hframe j)
  -- germ rewrite: distribute the pairing over the frame combination
  have hgerm : (fun q : M => g.inner q
        (∑ c, w c q • Work.Diff.GE.cFrame (I := I) x₀ c q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q))
      =ᶠ[𝓝 p] (fun q : M => ∑ c, w c q
        * g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
          (Work.Diff.GE.cFrame (I := I) x₀ j q)) := by
    filter_upwards with q
    change Inner.inner ℝ (∑ c, w c q • Work.Diff.GE.cFrame (I := I) x₀ c q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q)
      = ∑ c, w c q * Inner.inner ℝ (Work.Diff.GE.cFrame (I := I) x₀ c q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q)
    rw [sum_inner]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_smul_left]
    simp
  rw [mvfderiv_congr_nhds hgerm]
  -- the Leibniz rule, term by term
  have hstep : ∀ c : Fin (Module.finrank ℝ E),
      mvfderiv I (fun q : M => w c q
          * g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
            (Work.Diff.GE.cFrame (I := I) x₀ j q)) p
        (Work.Diff.GE.cFrame (I := I) x₀ i p)
      = w c p * mvfderiv I (fun q : M => g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
            (Work.Diff.GE.cFrame (I := I) x₀ j q)) p (Work.Diff.GE.cFrame (I := I) x₀ i p)
        + g.inner p (Work.Diff.GE.cFrame (I := I) x₀ c p)
            (Work.Diff.GE.cFrame (I := I) x₀ j p)
          * mvfderiv I (w c) p (Work.Diff.GE.cFrame (I := I) x₀ i p) := by
    intro c
    have h1 : MDifferentiableAt I 𝓘(ℝ,ℝ) (w c) p := (hw c).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun q : M => g.inner q
        (Work.Diff.GE.cFrame (I := I) x₀ c q) (Work.Diff.GE.cFrame (I := I) x₀ j q)) p :=
      (hGsm c).mdifferentiableAt (by simp)
    have hfun : (fun q : M => w c q * g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
          (Work.Diff.GE.cFrame (I := I) x₀ j q))
        = w c * (fun q : M => g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
          (Work.Diff.GE.cFrame (I := I) x₀ j q)) := rfl
    rw [hfun, mvfderiv_mul h1 h2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- distribute over the finite sum
  have hsumd : mvfderiv I (fun q : M => ∑ c, w c q
        * g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
          (Work.Diff.GE.cFrame (I := I) x₀ j q)) p
      (Work.Diff.GE.cFrame (I := I) x₀ i p)
      = ∑ c, mvfderiv I (fun q : M => w c q
          * g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
            (Work.Diff.GE.cFrame (I := I) x₀ j q)) p
        (Work.Diff.GE.cFrame (I := I) x₀ i p) := by
    rw [mvfderiv_finset_sum (s := Finset.univ)
      (F := fun c q => w c q * g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q)) (x := p)]
    · simp only [ContinuousLinearMap.sum_apply]
    · intro c _
      exact ((hw c).mdifferentiableAt (by simp)).mul ((hGsm c).mdifferentiableAt (by simp))
  rw [hsumd]
  rw [show (∑ c, mvfderiv I (fun q : M => w c q
          * g.inner q (Work.Diff.GE.cFrame (I := I) x₀ c q)
            (Work.Diff.GE.cFrame (I := I) x₀ j q)) p
        (Work.Diff.GE.cFrame (I := I) x₀ i p))
      = ∑ c, (w c p * mvfderiv I (fun q : M => g.inner q
              (Work.Diff.GE.cFrame (I := I) x₀ c q)
              (Work.Diff.GE.cFrame (I := I) x₀ j q)) p
            (Work.Diff.GE.cFrame (I := I) x₀ i p)
          + g.inner p (Work.Diff.GE.cFrame (I := I) x₀ c p)
              (Work.Diff.GE.cFrame (I := I) x₀ j p)
            * mvfderiv I (w c) p (Work.Diff.GE.cFrame (I := I) x₀ i p))
      from Finset.sum_congr rfl fun c _ => hstep c]
  rw [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [hval c]
    rw [Work.Diff.EXT.kz_mvfderiv_metricComp_eq (I := I) g x₀ hy c j i]
    rw [Work.Diff.EXT.kz_chartMatFun_swap (I := I) g x₀ hy i c j]
    ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [hdw c]
    have hsrc : p ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source (I := I) x₀]; exact hp
    have hthis : Work.Diff.EXT.chartMatFun (I := I) g x₀ y j c
        = g.inner p (Work.Diff.GE.cFrame (I := I) x₀ c p)
            (Work.Diff.GE.cFrame (I := I) x₀ j p) := by
      rw [Work.Diff.GE.cFrame_apply, Work.Diff.GE.cFrame_apply]
      simp only [Work.Diff.EXT.chartMatFun]
      rw [← hpy, PartialEquiv.left_inv (extChartAt I x₀) hsrc]
      exact (g.symm p _ _).symm
    rw [hthis]

/-! ## The DeTurck field paired with the coordinate frame -/

/-- **The pairing of the DeTurck field with the frame is the lowered jet component.**  With
`W = deTurckVec g gbar = ∑_c W^cσ_c` and `W^c = jWU` (`deTurckChartComp_eq_jWU`), the pairing
`g(W,σ_j) = ∑_c g_{jc}W^c` is exactly `jWb j`. -/
lemma inner_deTurckVec_frame_eq_jWb (g gbar : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (j : Fin (Module.finrank ℝ E)) :
    g.inner ((extChartAt I x₀).symm y) (Work.Diff.STE.DeTurck.deTurckVec g gbar
        ((extChartAt I x₀).symm y))
        (Work.Diff.GE.cFrame (I := I) x₀ j ((extChartAt I x₀).symm y))
      = Work.Diff.STE.DeTurck.jWb (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
          (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y) j := by
  set p : M := (extChartAt I x₀).symm y with hpdef
  have hp : p ∈ (chartAt H x₀).source := by
    rw [hpdef, ← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [Work.Diff.STE.deTurck.deTurckVec_eq_sum_chartComp (I := I) g gbar x₀ hp]
  change Inner.inner ℝ (∑ c, Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ p c
      • Work.Diff.GE.cFrame (I := I) x₀ c p) (Work.Diff.GE.cFrame (I := I) x₀ j p)
    = Work.Diff.STE.DeTurck.jWb (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
        (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
        (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
        (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y) j
  rw [sum_inner]
  rw [Work.Diff.STE.DeTurck.jWb]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [inner_smul_left]
  rw [starRingEnd_apply, star_trivial]
  rw [Work.Diff.STE.deTurck.deTurckChartComp_eq_jWU g gbar x₀ hy c]
  rw [show Inner.inner ℝ (Work.Diff.GE.cFrame (I := I) x₀ c p)
        (Work.Diff.GE.cFrame (I := I) x₀ j p)
      = Work.Diff.EXT.chartMatFun (I := I) g x₀ y j c from by
    rw [hpdef]; exact inner_cFrame_eq_chartMatFun (I := I) g x₀ hy c j]
  ring

/-- **The derivative of the pairing of the DeTurck field with the frame is `jdWb`.**  Applying the
Leibniz rule to `∑_c W^c·g_{cj}` (with `W^c` the chart components of the DeTurck field, whose value
is `jWU` and whose derivative is `jdWU`) gives exactly `jdWb i j`. -/
theorem mvfderiv_pairing_deTurckVec (g gbar : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun q : M => g.inner q (Work.Diff.STE.DeTurck.deTurckVec g gbar q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q))
      ((extChartAt I x₀).symm y)
      (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
      = Work.Diff.STE.DeTurck.jdWb (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
          (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀)) y)
          (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y)
          (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀)) y) i j := by
  set p : M := (extChartAt I x₀).symm y with hpdef
  have hp : p ∈ (chartAt H x₀).source := by
    rw [hpdef, ← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hgerm : (fun q : M => g.inner q (Work.Diff.STE.DeTurck.deTurckVec g gbar q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q))
      =ᶠ[𝓝 p] (fun q : M => g.inner q
        (∑ c, Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ q c
          • Work.Diff.GE.cFrame (I := I) x₀ c q)
        (Work.Diff.GE.cFrame (I := I) x₀ j q)) := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hp] with q hq
    rw [Work.Diff.STE.deTurck.deTurckVec_eq_sum_chartComp (I := I) g gbar x₀ hq]
  rw [mvfderiv_congr_nhds hgerm]
  rw [mvfderiv_metric_pairing_sum_frame (g := g) (x₀ := x₀) hy i j
    (fun c q => Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ q c)
    (fun c => Work.Diff.STE.DeTurck.jWU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
      (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
      (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
      (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y) c)
    (fun c => Work.Diff.STE.DeTurck.jdWU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
      (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
      (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀)) y)
      (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
      (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y)
      (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀)) y) i c)
    (fun c => Work.Diff.STE.deTurck.contMDiffAt_deTurckChartComp_at g gbar x₀ hy c)
    (fun c => Work.Diff.STE.deTurck.deTurckChartComp_eq_jWU g gbar x₀ hy c)
    (fun c => Work.Diff.STE.deTurck.deTurckChartComp_mvfderiv g gbar x₀ hy i c)]
  -- identify the two sums with `jdWb`
  rw [Work.Diff.STE.DeTurck.jdWb, Finset.sum_add_distrib]

/-! ## The bridge -/

/-- **The chart matrix of the Lie derivative of `g` along the DeTurck field is its jet expression.**

Both sides compute `(L_{W(g)}g)_{ij}`: the geometric side from `L_Wg = ∇_iW_j + ∇_jW_i` (metric
compatibility, `lcOf_pairing_frame`), the jet side from the coordinate formula
`∇_iW_j = ∂_iW_j - Γ^c_{ij}W_c` with `W^c = jWU`, `∂_iW^c = jdWU` and `W_j = jWb`. -/
theorem chartLieMat_eq_lieJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] (g gbar : Submission.Diff.SMet I M) (x₀ : M) (y : E)
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.STE.DeTurck.chartLieMat g gbar x₀ y
      = Work.Diff.STE.DeTurck.lieJet g gbar x₀ y := by
  ext i j
  rw [Work.Diff.STE.DeTurck.chartLieMat_apply, Work.Diff.STE.DeTurck.lieJet_apply]
  simp only [Work.Diff.STE.DeTurck.lieMet, Work.Diff.STE.DeTurck.jLW,
    Work.Diff.STE.DeTurck.jnabW, chartJet_fst, chartJet_snd_fst, chartJet_snd_snd]
  have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
  have hW : Work.Diff.EXT.SmoothTField (I := I) (M := M)
      (Work.Diff.STE.DeTurck.deTurckVec g gbar) :=
    Work.Diff.STE.deTurck.contMDiff_deTurckVec_of_joint (I := I) (M := M) hLC g gbar
  have h1 := Work.Diff.STE.deTurck.lcOf_pairing_frame (I := I) hLC g hW x₀ hy i j
  have h2 := Work.Diff.STE.deTurck.lcOf_pairing_frame (I := I) hLC g hW x₀ hy j i
  rw [h1]
  rw [g.symm ((extChartAt I x₀).symm y)
    (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
    ((Submission.Diff.lcOf g) (Work.Diff.STE.DeTurck.deTurckVec g gbar)
      ((extChartAt I x₀).symm y)
      (Work.Diff.GE.cFrame (I := I) x₀ j ((extChartAt I x₀).symm y)))]
  rw [h2]
  rw [mvfderiv_pairing_deTurckVec (I := I) g gbar x₀ hy i j,
    mvfderiv_pairing_deTurckVec (I := I) g gbar x₀ hy j i]
  have hsum1 : (∑ c : Fin (Module.finrank ℝ E),
        Work.Diff.GE.chrCoord (fun _ : ℝ => g) (I := I) x₀ c i j 0 ((extChartAt I x₀).symm y)
          * g.inner ((extChartAt I x₀).symm y) (Work.Diff.STE.DeTurck.deTurckVec g gbar
              ((extChartAt I x₀).symm y))
            (Work.Diff.GE.cFrame (I := I) x₀ c ((extChartAt I x₀).symm y)))
      = ∑ c : Fin (Module.finrank ℝ E),
          Work.Diff.EXT.jGamU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
              (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y) c i j
            * Work.Diff.STE.DeTurck.jWb (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
              (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
              (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
              (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y) c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chrCoord_eq_jGamU (I := I) g x₀ hy c i j,
      inner_deTurckVec_frame_eq_jWb (I := I) g gbar x₀ hy c]
  have hsum2 : (∑ c : Fin (Module.finrank ℝ E),
        Work.Diff.GE.chrCoord (fun _ : ℝ => g) (I := I) x₀ c j i 0 ((extChartAt I x₀).symm y)
          * g.inner ((extChartAt I x₀).symm y) (Work.Diff.STE.DeTurck.deTurckVec g gbar
              ((extChartAt I x₀).symm y))
            (Work.Diff.GE.cFrame (I := I) x₀ c ((extChartAt I x₀).symm y)))
      = ∑ c : Fin (Module.finrank ℝ E),
          Work.Diff.EXT.jGamU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
              (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y) c j i
            * Work.Diff.STE.DeTurck.jWb (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
              (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
              (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
              (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y) c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chrCoord_eq_jGamU (I := I) g x₀ hy c j i,
      inner_deTurckVec_frame_eq_jWb (I := I) g gbar x₀ hy c]
  rw [hsum1, hsum2]

end

end Work.Diff.STE.deTurck
