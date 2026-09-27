import Mathlib
import Submission.Work.Drive.sideGermSepDefs
import Submission.Work.Drive.sepFamDefs
import Submission.Work.Drive.goodFaceMulti
import Submission.Work.Drive.eventuallyFamMeetSubset
import Submission.Work.Drive.sepExistsFamilyCover
import Submission.Work.Drive.sepContMDiffFams
import Submission.Work.Drive.sepLoopSmoothJoint
import Submission.Work.Drive.sepLoopMfderivSurj
import Submission.Work.Drive.sepCutoffSystemSmooth
import Submission.Work.Drive.sgAssembly
import Submission.Work.Drive.loopFam_faceHyp_of_good_family
import Submission.Work.Drive.cofactorVec_mem_ker

/-!
# The Sard regularity `Work.Drive.sep_fam_regular`

For the two configurations `A`, `B` (loop chart and sweep chart) and the two angle lifts `tR`, `t'R`,
the family of the straight path between them, with the loop's chart shifted by `τ₁` and the sweep's by
`τ₂`, is *regular* at arbitrarily small shifts: the difference of the two derivatives is onto at every
meet of the five-box family, and at every boundary meet exactly one coordinate lies on a face and the
meet is crossed there.

The proof is the multi-chart parametric Sard `Work.Drive.goodFaceMulti`:

* the parameter is the shift `τ₁` of the loop's chart only (`τ₂ = 0`); the parameter-derivative of the
  charted difference system is then `∂_{τ₁}` of the loop's charted value, which is onto by
  `ChartPert` — the second shift is not needed for the *Sard*;
* the values of the family over the box are compact, and every meet of the family at the shift `0` is
  covered by a compact piece `K i` inside an open set `V i` on which both values lie in the source of
  the chart at `p i`, uniformly over a parameter ball (`Work.Drive.SepFamilyCover`);
* for each chart piece the *charted difference system*, cut off in the parameter (`γ`) and in the box
  (`β i`), is `C^∞` and has an onto parameter-derivative at every zero;
* `goodFaceMulti` returns a single (small) parameter `s` at which every system has an onto
  `z`-derivative at its zeros in `K i`, its restriction to the face hyperplanes is onto at the zeros on
  the faces, and no zero lies over the two-face skeleton of `K i`;
* the transfer lemmas below turn those three conclusions into the `SepTrans` and `SepFace` clauses of
  `Work.Drive.SepRegular`, and the smoothness clauses come from `Work.Drive.SepLoopSmooth` /
  `Work.Drive.SepChainSmooth`.

Authoritative note on the layout: `Submission/Work/Drive/sepFamDefs.lean` (the packaged interface).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 4000000

noncomputable section

variable {m : ℕ}

/-! ## 1. The linear-algebra transfers -/

/-- **The transversality transfer**: if the `z`-derivative of the charted difference map is onto at a
meet, then so is the chart-independent difference `FamBox.Lf` of the two derivatives. -/
theorem sep_Lf_surj_of_chartDif (p : CappingSpace) (F G : Amb 4 → CappingSpace)
    (hF : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hG : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    {y : Amb 4} (hy : y ∈ FamBox.chartReg p F G) (heq : F y = G y)
    (hsurj : Function.Surjective (fderiv ℝ (FamBox.chartDif p F G) y)) :
    Function.Surjective (FamBox.Lf F G y) := by
  have heqfd : fderiv ℝ (FamBox.chartDif p F G) y
      = (tangentCoordChange (𝓡 4) (F y) p (F y)).comp (FamBox.Lf F G y) :=
    ContinuousLinearMap.ext fun v => FamBox.fderiv_chartDif_eq_Lf p F G hF hG hy heq v
  have hsrc1 : F y ∈ (extChartAt (𝓡 4) (F y)).source := mem_extChartAt_source (I := 𝓡 4) _
  have hsrc2 : F y ∈ (extChartAt (𝓡 4) p).source := by
    rw [extChartAt_source]
    exact hy.1
  have hinj : Function.Injective (tangentCoordChange (𝓡 4) (F y) p (F y)) :=
    tangentCoordChange_injective (x := F y) (y := p) (z := F y) ⟨hsrc1, hsrc2⟩
  intro w
  obtain ⟨v, hv⟩ := hsurj (tangentCoordChange (𝓡 4) (F y) p (F y) w)
  refine ⟨v, hinj ?_⟩
  have h1 : (fderiv ℝ (FamBox.chartDif p F G) y) v
      = tangentCoordChange (𝓡 4) (F y) p (F y) ((FamBox.Lf F G y) v) := by
    rw [heqfd, ContinuousLinearMap.comp_apply]
  rw [← h1]
  exact hv

/-- **The face transfer**: if the `z`-derivative of the charted difference map is onto at a meet and
its restriction to the coordinate hyperplane `{v | v i = 0}` is onto as well, then the difference of
the two derivatives has a kernel vector whose `i`-th coordinate does not vanish. -/
theorem sep_sigma_of_faceSurj (p : CappingSpace) (F G : Amb 4 → CappingSpace)
    (hF : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hG : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    {y : Amb 4} (hy : y ∈ FamBox.chartReg p F G) (heq : F y = G y) {i : Fin 5}
    (hsurj : Function.Surjective (fderiv ℝ (FamBox.chartDif p F G) y))
    (hface : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (FamBox.chartDif p F G) y v.1)) :
    ∃ σ : Amb 4, FamBox.Lf F G y σ = 0 ∧ σ i ≠ 0 := by
  set Φ : Amb 4 →L[ℝ] Tgt 4 := fderiv ℝ (FamBox.chartDif p F G) y with hΦ
  refine ⟨Work.Drive.cofactorVec Φ, ?_, ?_⟩
  · have hker : fderiv ℝ (FamBox.chartDif p F G) y (Work.Drive.cofactorVec Φ) = 0 := by
      rw [← hΦ]
      exact Work.Drive.cofactorVec_mem_ker Φ
    have hTeq := FamBox.fderiv_chartDif_eq_Lf p F G hF hG hy heq (Work.Drive.cofactorVec Φ)
    rw [hker] at hTeq
    have hsrc : F y ∈ (extChartAt (𝓡 4) p).source := by
      have h := hy.1
      rwa [chr, ← extChartAt_source (I := 𝓡 4) p] at h
    have hinj : Function.Injective (tangentCoordChange (𝓡 4) (F y) p (F y)) :=
      tangentCoordChange_injective (x := F y) (y := p) (z := F y)
        ⟨mem_extChartAt_source (I := 𝓡 4) (F y), hsrc⟩
    refine hinj ?_
    rw [map_zero]
    exact hTeq.symm
  · exact (Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero Φ hsurj i).mp hface


/-! ## 2. The main theorem -/

theorem sep_fam_regular {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsSmoothChart Q) (hc : 0 < c)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ) :
    ∀ ε' : ℝ, 0 < ε' → ∃ τ₁ τ₂ : EuclideanSpace ℝ (Fin m), ‖τ₁‖ < ε' ∧ ‖τ₂‖ < ε' ∧
      Work.Drive.SepRegular Ξ Q c tR t'R A B τ₁ τ₂ := by
  classical
  intro ε' hε'
  -- ## 0. Notation: the loop family (the Sard parameter) and the fixed chain family.
  set Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace := fun τ => sepLoopFam Ξ Q A B τ with hLf
  set N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace := fun _ => sepChainFam Ξ Q c tR t'R A B 0 with hN
  -- ## 1. Smoothness and continuity of the pair.
  have hloop_joint : ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2) := by
    rw [hLf]
    exact sepLoopSmoothJoint Ξ Q hΞ hQ A B
  have hchain_joint : ContMDiff ((𝓡 m).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2) := by
    have hfix : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (sepChainFam Ξ Q c tR t'R A B 0) :=
      (sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B 0 0).2.1
    rw [hN]
    exact hfix.comp contMDiff_snd
  have hfam_smooth : SepFamSmooth Lf N := ⟨hloop_joint, hchain_joint⟩
  have hfam_cont : SepFamContinuous Lf N :=
    ⟨hfam_smooth.1.continuous, hfam_smooth.2.continuous⟩
  -- ## 2. A finite cover of the meet set at the zero shift, by charted pieces.
  obtain ⟨cov⟩ := sepExistsFamilyCover Lf N hfam_cont
  -- ## 3. The meet sets of small shifts stay in the pieces.
  have hstay : ∀ᶠ τ in 𝓝 (0 : EuclideanSpace ℝ (Fin m)), ∀ y : Amb 4, y ∈ Submission.Drive.unitBox 4 →
      famLoop (Lf τ) y = famChain (N τ) y → y ∈ ⋃ i, interior (cov.K i) :=
    eventuallyFamMeetSubset Lf hfam_cont.1 N hfam_cont.2
      (isOpen_iUnion fun i => isOpen_interior) cov.hbase
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hstay
  have hδ : ∀ τ : EuclideanSpace ℝ (Fin m), ‖τ‖ < δ → ∀ y : Amb 4, y ∈ Submission.Drive.unitBox 4 →
      famLoop (Lf τ) y = famChain (N τ) y → y ∈ ⋃ i, interior (cov.K i) := by
    intro τ hτ y hy hmeet
    exact hδsub (by rw [Metric.mem_ball, dist_zero_right]; exact hτ) y hy hmeet
  -- ## 4. The working radius.
  set R : ℝ := min (min cov.ε₀ δ) (min ε' 1) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact lt_min (lt_min cov.hε₀ hδpos) (lt_min hε' zero_lt_one)
  have hRε₀ : R ≤ cov.ε₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRδ : R ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRε' : R ≤ ε' := le_trans (min_le_right _ _) (min_le_left _ _)
  -- ## 5. The cut-offs and the squeeze of the parameter.
  obtain ⟨γ, hγsm, hγone, hγsupp⟩ := exists_cutoff_one_on_of_subset
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (R / 2)) Metric.isOpen_ball
    (fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
  have hγsupp' : tsupport γ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) cov.ε₀ := fun x hx =>
    Metric.ball_subset_ball (by linarith) (hγsupp hx)
  choose β hβsm hβone hβsupp using fun i : Fin cov.r =>
    exists_cutoff_one_on_of_subset (cov.hK i) (cov.hV i) (cov.hKV i)
  obtain ⟨sq, hsqsm, hsqbound, hsqsurj⟩ := sep_squeeze_map (m := m) (δ := R / 2) (by linarith)
  -- ## 6. The charted difference systems of the pieces.
  set Φ : Fin cov.r → EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 := fun i q =>
    (γ (sq q.1) * β i q.2) •
      FamBox.chartDif (cov.p i) (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2 with hΦ
  have hΦsm : ∀ i : Fin cov.r, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ i) := by
    intro i
    have hbase : SepBumpedSmooth Lf N (cov.p i) γ (β i) :=
      sepCutoffSystemSmooth Lf N hfam_smooth (cov.p i) hγsm (hβsm i) (cov.chartReg i)
        hγsupp' (hβsupp i)
    have hcomp := hbase.comp ((hsqsm.comp contDiff_fst).prodMk contDiff_snd)
    rw [hΦ]
    exact hcomp
  have hΦsurj : ∀ (i : Fin cov.r) (p : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖p‖ < 1 →
      (z ∈ cov.K i ∨ ∃ j : FaceIdx4,
        z ∈ (fun l : Fdir4 j => Fbase4 j + (l : Amb 4)) '' Fcov4 (cov.K i) j) →
      Φ i (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) p) := by
    intro i p z _ hz h0
    have hzK : z ∈ cov.K i := by
      rcases hz with h | ⟨j, l, hl, hlz⟩
      · exact h
      · rw [← hlz]; exact hl
    have hsqb : ‖sq p‖ ≤ R / 2 := hsqbound p
    have hβ1 : β i z = 1 := hβone i z hzK
    have hγ1 : γ (sq p) = 1 := hγone (sq p) (by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hsqbound p])
    have hreg : z ∈ FamBox.chartReg (cov.p i) (famLoop (Lf (sq p))) (famChain (N (sq p))) :=
      cov.hchart i (sq p) z (by linarith [hsqbound p]) (cov.hKV i hzK)
    have hΨ0 : FamBox.chartDif (cov.p i) (famLoop (Lf (sq p))) (famChain (N (sq p))) z = 0 := by
      have h := h0
      rw [show Φ i (p, z) = (γ (sq p) * β i z) •
          FamBox.chartDif (cov.p i) (famLoop (Lf (sq p))) (famChain (N (sq p))) z from rfl] at h
      simpa only [hγ1, hβ1, one_mul, one_smul] using h
    -- the charted difference family along the parameter
    set Ψ : EuclideanSpace ℝ (Fin m) → Tgt 4 :=
      fun τ => FamBox.chartDif (cov.p i) (famLoop (Lf τ)) (famChain (N τ)) z with hΨdef
    have hfun : (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) = fun p' => Ψ (sq p') := by
      funext p'
      have hγ1' : γ (sq p') = 1 := hγone (sq p') (by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [hsqbound p'])
      show (γ (sq p') * β i z) •
        FamBox.chartDif (cov.p i) (famLoop (Lf (sq p'))) (famChain (N (sq p'))) z = Ψ (sq p')
      rw [hγ1', hβ1, one_mul, one_smul]
    -- `Ψ` is the charted loop value minus a constant
    set Aloop : EuclideanSpace ℝ (Fin m) → CappingSpace := fun τ => famLoop (Lf τ) z with hAloop
    set Achr : EuclideanSpace ℝ (Fin m) → Tgt 4 := fun τ => chr (cov.p i) (Aloop τ) with hAchr
    have hAeq : Ψ = fun τ => Achr τ - chr (cov.p i) (famChain (N 0) z) := by
      funext τ
      show chr (cov.p i) (famLoop (Lf τ) z) - chr (cov.p i) (famChain (N τ) z)
        = chr (cov.p i) (famLoop (Lf τ) z) - chr (cov.p i) (famChain (N 0) z)
      rfl
    have hsmIn : ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Aloop := by
      rw [hAloop]
      have hpair : ContMDiff (𝓡 m) ((𝓡 m).prod (𝓡 2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun τ' : EuclideanSpace ℝ (Fin m) => (τ', mk2 (z 0) (z 1))) :=
        contMDiff_id.prodMk contMDiff_const
      have h := (sepLoopSmoothJoint Ξ Q hΞ hQ A B).comp hpair
      simpa only [Function.comp_def, famLoop] using h
    have hAdiff : DifferentiableAt ℝ Achr (sq p) := by
      rw [hAchr]
      exact (fderiv_chart_comp_hasFDerivAt Aloop hsmIn (cov.p i) hreg.1).differentiableAt
    have hAder : fderiv ℝ Achr (sq p)
        = (tangentCoordChange (𝓡 4) (Aloop (sq p)) (cov.p i) (Aloop (sq p))).comp
          (mfderiv (𝓡 m) (𝓡 4) Aloop (sq p)) := by
      rw [hAchr]
      exact fderiv_chart_comp Aloop hsmIn (cov.p i) hreg.1
    have hmfd : SepLoopMfderivSurj Ξ Q A B (sq p) z :=
      sepLoopMfderivSurj Ξ Q hΞ hQ A B (sq p) z
    have hA_surj : Function.Surjective (fderiv ℝ Achr (sq p)) := by
      rw [hAder]
      have hsrc1 : Aloop (sq p) ∈ (extChartAt (𝓡 4) (Aloop (sq p))).source :=
        mem_extChartAt_source (I := 𝓡 4) _
      have hsrc2 : Aloop (sq p) ∈ (extChartAt (𝓡 4) (cov.p i)).source := by
        rw [extChartAt_source]; exact hreg.1
      have hleft : Function.LeftInverse
          (tangentCoordChange (𝓡 4) (Aloop (sq p)) (cov.p i) (Aloop (sq p)))
          (tangentCoordChange (𝓡 4) (cov.p i) (Aloop (sq p)) (Aloop (sq p))) :=
        fun v => tangentCoordChange_comp_inv ⟨hsrc2, hsrc1⟩ v
      exact hleft.surjective.comp hmfd
    have hΨder : Function.Surjective (fderiv ℝ Ψ (sq p)) := by
      have hder : fderiv ℝ Ψ (sq p) = fderiv ℝ Achr (sq p) := by
        rw [hAeq, fderiv_sub_const]
      rw [hder]; exact hA_surj
    have hΨdiff : DifferentiableAt ℝ Ψ (sq p) := by
      rw [hAeq]
      exact hAdiff.sub (differentiableAt_const _)
    have hcomp : fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Ψ (sq p')) p
        = (fderiv ℝ Ψ (sq p)).comp (fderiv ℝ sq p) := by
      simpa only [Function.comp_def] using fderiv_comp (x := p) (f := sq) (g := Ψ) hΨdiff
        ((hsqsm.differentiable (by simp)).differentiableAt)
    rw [hfun, hcomp]
    exact hΨder.comp (hsqsurj p)
  -- ## 7. The parametric Sard.
  obtain ⟨s, hsnorm, hsgood, hsface, hsavoid⟩ := goodFaceMulti m 4 cov.r cov.K cov.hK
    (fun _ : Fin cov.r => FaceIdx4) (fun _ j => ↥(Fdir4 j)) (fun _ j => Fdir4_finrank_lt j)
    (fun _ j l => Fbase4 j + (l : Amb 4)) (fun _ j => contDiff_Fparam4 j)
    (fun i j => Fcov4 (cov.K i) j) (fun i j => Fcov4_isCompact (cov.K i) (cov.hK i) j)
    Φ hΦsm 1 zero_lt_one hΦsurj
  -- ## 8. The conclusions.
  have hsqs_ε' : ‖sq s‖ < ε' := lt_of_le_of_lt (hsqbound s) (by linarith)
  have hsqs_δ : ‖sq s‖ < δ := lt_of_le_of_lt (hsqbound s) (by linarith)
  have hsqs_ε₀ : ‖sq s‖ < cov.ε₀ := lt_of_le_of_lt (hsqbound s) (by linarith)
  have hγsq : γ (sq s) = 1 := hγone (sq s) (by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith [hsqbound s])
  -- the meet of the final family in the box is a meet of the cover
  have hmem : ∀ y : Amb 4, y ∈ Submission.Drive.unitBox 4 →
      famLoop (Lf (sq s)) y = famChain (N (sq s)) y → y ∈ ⋃ i, interior (cov.K i) :=
    hδ (sq s) hsqs_δ
  -- the meet at a piece gives a zero of the corresponding system
  have hΦzero' : ∀ (i : Fin cov.r) (y : Amb 4), y ∈ cov.K i →
      famLoop (Lf (sq s)) y = famChain (N (sq s)) y → Φ i (s, y) = 0 := by
    intro i y hyK hmeet
    have hreg : y ∈ FamBox.chartReg (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) :=
      cov.hchart i (sq s) y hsqs_ε₀ (cov.hKV i hyK)
    have hzd : FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) y = 0 :=
      (FamBox.chartDif_eq_zero_iff hreg).mpr hmeet
    rw [hΦ]
    show (γ (sq s) * β i y) •
      FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) y = 0
    rw [hγsq, hβone i y hyK, one_mul, hzd, smul_zero]
  -- the box-derivative of the bumped system is the derivative of the charted difference
  have hfderiv_system : ∀ (i : Fin cov.r) (y : Amb 4), y ∈ cov.K i → Φ i (s, y) = 0 →
      fderiv ℝ (fun z' : Amb 4 => Φ i (s, z')) y
        = fderiv ℝ (FamBox.chartDif (cov.p i) (famLoop (Lf (sq s)))
            (famChain (N (sq s)))) y := by
    intro i y hyK h0
    have hreg : y ∈ FamBox.chartReg (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) :=
      cov.hchart i (sq s) y hsqs_ε₀ (cov.hKV i hyK)
    have hzd : FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) y = 0 := by
      have h := h0
      rw [hΦ] at h
      simpa only [hγsq, hβone i y hyK, one_mul, one_smul] using h
    have hFcdt : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (famLoop (Lf (sq s))) :=
      FamBox.contMDiff_famLoop _ ((sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).1
        )
    have hGt : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (famChain (N (sq s))) :=
      FamBox.contMDiff_famChain _ ((sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).2.1)
    have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z' : Amb 4 =>
          FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y :=
      (FamBox.contDiffOn_chartDif _ _ _ hFcdt hGt).contDiffAt
        ((FamBox.isOpen_chartReg _ _ _ hFcdt.continuous hGt.continuous).mem_nhds hreg)
    have hχp : HasFDerivAt
        (fun z' : Amb 4 =>
          FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) z')
        (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y) y :=
      (hχat.differentiableAt (by simp)).hasFDerivAt
    have hβp : HasFDerivAt (fun z' : Amb 4 => γ (sq s) * β i z')
        (fderiv ℝ (fun z' : Amb 4 => γ (sq s) * β i z') y) y :=
      ((contDiffAt_const.mul (hβsm i).contDiffAt).differentiableAt (by simp)).hasFDerivAt
    have hsmul := hβp.smul hχp
    have h1 : (γ (sq s) * β i y) •
          (fderiv ℝ (fun z' : Amb 4 =>
            FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y)
        + (fderiv ℝ (fun z' : Amb 4 => γ (sq s) * β i z') y).smulRight
            (FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) y)
        = fderiv ℝ (fun z' : Amb 4 =>
            FamBox.chartDif (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y := by
      rw [hγsq, hβone i y hyK, one_mul, hzd]
      simp
    rw [h1] at hsmul
    rw [hΦ]
    exact hsmul.fderiv
  -- the three structures
  have hsmooth : SepSmooth Ξ Q c tR t'R A B (sq s) 0 :=
    ⟨(sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).1,
     (sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).2.1⟩
  have htrans : SepTrans Ξ Q c tR t'R A B (sq s) 0 := by
    refine ⟨fun y hybox hmeet => ?_⟩
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp (hmem y hybox hmeet)
    have hyK : y ∈ cov.K i := interior_subset hyi
    have hΦ0 : Φ i (s, y) = 0 := hΦzero' i y hyK hmeet
    have hreg : y ∈ FamBox.chartReg (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) :=
      cov.hchart i (sq s) y hsqs_ε₀ (cov.hKV i hyK)
    have hFcdt : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (famLoop (Lf (sq s))) :=
      FamBox.contMDiff_famLoop _ ((sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).1)
    have hGt : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (famChain (N (sq s))) :=
      FamBox.contMDiff_famChain _ ((sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).2.1)
    have hsurjχ : Function.Surjective
        (fderiv ℝ (FamBox.chartDif (cov.p i) (famLoop (Lf (sq s)))
          (famChain (N (sq s)))) y) := by
      rw [← hfderiv_system i y hyK hΦ0]
      exact hsgood i y hyK hΦ0
    have hLfSurj := sep_Lf_surj_of_chartDif (cov.p i) (famLoop (Lf (sq s)))
      (famChain (N (sq s))) hFcdt hGt hreg hmeet hsurjχ
    exact hLfSurj
  have hface : SepFace Ξ Q c tR t'R A B (sq s) 0 := by
    refine ⟨fun y hybox hmeet hbdry => ?_⟩
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp (hmem y hybox hmeet)
    have hyK : y ∈ cov.K i := interior_subset hyi
    have hΦ0 : Φ i (s, y) = 0 := hΦzero' i y hyK hmeet
    have hreg : y ∈ FamBox.chartReg (cov.p i) (famLoop (Lf (sq s))) (famChain (N (sq s))) :=
      cov.hchart i (sq s) y hsqs_ε₀ (cov.hKV i hyK)
    have hFcdt : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (famLoop (Lf (sq s))) :=
      FamBox.contMDiff_famLoop _ ((sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).1)
    have hGt : ContMDiff (𝓡 5) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (famChain (N (sq s))) :=
      FamBox.contMDiff_famChain _ ((sepContMDiffFams Ξ Q hΞ hQ c tR t'R A B (sq s) 0).2.1)
    -- there is at most one face coordinate
    have hnotwo : ¬ (∃ i₁ j₁ : Fin 5, i₁ ≠ j₁ ∧ (y i₁ = 0 ∨ y i₁ = 1) ∧
        (y j₁ = 0 ∨ y j₁ = 1)) := by
      rintro ⟨i₁, j₁, hij, hi₁, hj₁⟩
      obtain ⟨t, l, hl, hlz⟩ := Fcov4_cover (cov.K i) hyK ⟨i₁, j₁, hij, hi₁, hj₁⟩
      have hne := hsavoid i t l hl
      rw [hlz] at hne
      exact hne hΦ0
    obtain ⟨i₀, hi₀⟩ := hbdry.2
    have hother : ∀ j : Fin 5, j ≠ i₀ → y j ∈ Set.Ioo (0 : ℝ) 1 := by
      intro j hj
      have hyj : y j ∈ Set.Icc (0 : ℝ) 1 := hybox j
      rw [Set.mem_Icc] at hyj
      refine ⟨lt_of_le_of_ne hyj.1 (fun h => ?_), lt_of_le_of_ne hyj.2 (fun h => ?_)⟩
      · exact hnotwo ⟨i₀, j, fun hc => hj hc.symm, hi₀, Or.inl h.symm⟩
      · exact hnotwo ⟨i₀, j, fun hc => hj hc.symm, hi₀, Or.inr h⟩
    have hfaceSurj := hsface i i₀ y hyK hΦ0 hi₀
    have hsurjχ : Function.Surjective
        (fderiv ℝ (FamBox.chartDif (cov.p i) (famLoop (Lf (sq s)))
          (famChain (N (sq s)))) y) := by
      rw [← hfderiv_system i y hyK hΦ0]
      exact hsgood i y hyK hΦ0
    have hfaceχ : Function.Surjective (fun v : {v : Amb 4 // v i₀ = 0} =>
        fderiv ℝ (FamBox.chartDif (cov.p i) (famLoop (Lf (sq s)))
          (famChain (N (sq s)))) y v.1) := by
      rw [← hfderiv_system i y hyK hΦ0]
      exact hfaceSurj
    obtain ⟨σ, hσ, hσi⟩ := sep_sigma_of_faceSurj (cov.p i) (famLoop (Lf (sq s)))
      (famChain (N (sq s))) hFcdt hGt hreg hmeet hsurjχ hfaceχ
    refine ⟨i₀, hi₀, hother, σ, ?_, hσi⟩
    have h2 := hσ
    rw [FamBox.Lf_apply] at h2
    exact sub_eq_zero.mp h2
  exact ⟨sq s, 0, hsqs_ε', by simpa using hε', SepRegular.of_pieces hsmooth htrans hface⟩


end

end Work.Drive
