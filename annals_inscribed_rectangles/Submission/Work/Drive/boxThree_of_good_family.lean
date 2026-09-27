import Mathlib
import Submission.Work.Drive.boxThreeDefs
import Submission.Work.Drive.goodFaceMulti
import Submission.Work.Drive.exists_compact_chart_cover
import Submission.Work.Drive.exists_pos_norm_subset_of_isCompact_subset_isOpen
import Submission.Work.Drive.contDiff_bump_of_isCompact_subset_isOpen
import Submission.Work.Drive.chartDiffRangeBridge
import Submission.Work.Drive.contDiffAt_chartDiff_family_fin
import Submission.Work.Drive.loopFam_faceHyp_of_good_family

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set Metric Filter

noncomputable section

set_option maxHeartbeats 1000000

/-- The differentiability order `⊤` is not zero. -/
private lemma btg_top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma btg_eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- The "square" block projection is continuous. -/
private lemma btg_continuous_sqPart :
    Continuous (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) := by
  rw [show (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) = ⇑sqPartCLM from
    funext sqPartCLM_eq_sqPart]
  exact sqPartCLM.continuous

/-- The "cube" block projection is continuous. -/
private lemma btg_continuous_cbPart :
    Continuous (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) := by
  rw [show (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) = ⇑cbPartCLM from
    funext cbPartCLM_eq_cbPart]
  exact cbPartCLM.continuous

/-- The two block projections are inverse to `mkPart`. -/
private lemma btg_mkPart_sqPart_cbPart (x : Amb 4) : mkPart (sqPart x) (cbPart x) = x := by
  ext i
  revert i
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun i => mkPart (sqPart x) (cbPart x) i = x i) ?_ ?_
  · intro i
    simp [mkPart, sqPart, sqIdx, Fin.addCases_left]
  · intro j
    simp [mkPart, cbPart, cbIdx, Fin.addCases_right]

section Aux

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- Smoothness in the target variable of the single chain `G t` of the family. -/
private lemma btg_contMDiff_fixed_chain {m : ℕ}
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t) := by
  have hconst : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : EuclideanSpace ℝ (Fin 3) => (t, (0 : EuclideanSpace ℝ (Fin 3)))) :=
    contMDiff_const
  have hinr : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 3) => ((0 : EuclideanSpace ℝ (Fin m)), y)) :=
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 3))).contMDiff
  have hcomp := hG.comp (hconst.add hinr)
  simpa only [Function.comp_def, Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
    using hcomp

/-- **The shifted chain family** `q ↦ G (base + q.1) q.2` is jointly smooth. -/
private lemma btg_contMDiff_shift_chain {m : ℕ}
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (base : EuclideanSpace ℝ (Fin m)) :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G (base + q.1) q.2) := by
  have h : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) =>
        (base, (0 : EuclideanSpace ℝ (Fin 3))) + q) :=
    contMDiff_const.add contMDiff_id
  have h2 := hG.comp h
  simpa only [Function.comp_def, Prod.fst_add, Prod.snd_add, zero_add, Prod.mk.eta] using h2

/-- **Global smoothness of the cut-off-scaled charted difference system** of a fixed loop `D`
against a parametrised chain `G`: the cut-off `χ` vanishes outside the region where both values lie
in the source of the chart at `p`, which is the only place the charted difference is defined. -/
private theorem btg_contDiff_cutoff_chartDiff {m : ℕ}
    (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) {χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {U : Set (EuclideanSpace ℝ (Fin m) × Amb 4)}
    (hU : U ⊆ {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      D (sqPart q.2) ∈ (chr p).source ∧ G q.1 (cbPart q.2) ∈ (chr p).source})
    (hχsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => χ q • chartDiff p D (G q.1) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases h0 : q₀ ∈ tsupport χ
  · have hreg : D (sqPart q₀.2) ∈ (chr p).source ∧ G q₀.1 (cbPart q₀.2) ∈ (chr p).source :=
      hU (hχsupp h0)
    exact hχ.contDiffAt.smul (contDiffAt_chartDiff_family_fin m D hD G hG p q₀.1 hreg)
  · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [btg_eventually_eq_zero_of_notMem_tsupport h0] with q hq
    rw [hq, zero_smul]

/-- **Removing the cut-off from the `z`-derivative at a zero**: at a zero of the system at which the
cut-off equals `1`, the `z`-derivative of the cut-off system is the `z`-derivative of the charted
difference map itself. -/
private lemma btg_fderiv_cutoff_chartDiff_z {m : ℕ}
    (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) {χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {s : EuclideanSpace ℝ (Fin m)} {y : Amb 4} (hχv : χ (s, y) = 1)
    (hcont : y ∈ chartRegion p D (G s)) (hzy : chartDiff p D (G s) y = 0) :
    fderiv ℝ (fun z' : Amb 4 => χ (s, z') • chartDiff p D (G s) z') y
      = fderiv ℝ (fun z' : Amb 4 => chartDiff p D (G s) z') y := by
  have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => chartDiff p D (G q.1) q.2) (s, y) :=
    contDiffAt_chartDiff_family_fin m D hD G hG p s hcont
  have hχp : HasFDerivAt (fun z' : Amb 4 => chartDiff p D (G s) z')
      (fderiv ℝ (fun z' : Amb 4 => chartDiff p D (G s) z') y) y :=
    (hχat.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      btg_top_ne_zero_order |>.hasFDerivAt
  have hβp : HasFDerivAt (fun z' : Amb 4 => χ (s, z'))
      (fderiv ℝ (fun z' : Amb 4 => χ (s, z')) y) y :=
    (((hχ.contDiffAt.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      btg_top_ne_zero_order)).hasFDerivAt
  have hsmul := hβp.smul hχp
  have h1 : (χ (s, y)) • (fderiv ℝ (fun z' : Amb 4 => chartDiff p D (G s) z') y)
      + (fderiv ℝ (fun z' : Amb 4 => χ (s, z')) y).smulRight (chartDiff p D (G s) y)
      = fderiv ℝ (fun z' : Amb 4 => chartDiff p D (G s) z') y := by
    rw [hχv, hzy]
    simp
  rw [h1] at hsmul
  exact hsmul.fderiv

/-- **Removing the cut-off from the parameter derivative at a zero**: at a zero of the system at
which the cut-off equals `1`, the parameter derivative of the cut-off system is the parameter
derivative of the charted difference map itself. -/
private lemma btg_fderiv_cutoff_chartDiff_p {m : ℕ}
    (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) {χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {s : EuclideanSpace ℝ (Fin m)} {y : Amb 4} (hχv : χ (s, y) = 1)
    (hcont : y ∈ chartRegion p D (G s)) (hzy : chartDiff p D (G s) y = 0) :
    fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => χ (t', y) • chartDiff p D (G t') y) s
      = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chartDiff p D (G t') y) s := by
  have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => chartDiff p D (G q.1) q.2) (s, y) :=
    contDiffAt_chartDiff_family_fin m D hD G hG p s hcont
  have hχp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => chartDiff p D (G t') y)
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chartDiff p D (G t') y) s) s := by
    have h := (hχat.comp s (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      btg_top_ne_zero_order
    exact h.hasFDerivAt
  have hβp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => χ (t', y))
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => χ (t', y)) s) s :=
    (((hχ.contDiffAt.comp s (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      btg_top_ne_zero_order)).hasFDerivAt
  have hsmul := hβp.smul hχp
  have h1 : (χ (s, y)) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chartDiff p D (G t') y) s)
      + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => χ (t', y)) s).smulRight
          (chartDiff p D (G s) y)
      = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chartDiff p D (G t') y) s := by
    rw [hχv, hzy]
    simp
  rw [h1] at hsmul
  exact hsmul.fderiv


/-- **The converse of the face criterion for the charted difference map**: a surjective `z`-derivative
whose restriction to the coordinate hyperplane `{v | v i = 0}` is also onto produces a common
direction `(σ, τ)` of the two derivatives with non-zero `i`-th coordinate. -/
private theorem btg_exists_sigma_tau_of_faceSurjective_loop {M : Type*} [TopologicalSpace M]
    [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (p : M) (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    {y : Amb 4} (hy : y ∈ chartRegion p D N)
    (heq : D (sqPart y) = N (cbPart y))
    {i : Fin 5}
    (hsurj : Function.Surjective (fderiv ℝ (chartDiff p D N) y))
    (hface : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDiff p D N) y v.1)) :
    ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) D (sqPart y) σ
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) N (cbPart y) τ ∧
      mkPart σ τ i ≠ 0 := by
  set T : Amb 4 →L[ℝ] Tgt 4 := fderiv ℝ (chartDiff p D N) y with hT
  have hcof : cofactorVec T i ≠ 0 :=
    (surjective_domRestrict_iff_cofactorVec_ne_zero T hsurj i).mp hface
  have hker : T (cofactorVec T) = 0 := cofactorVec_mem_ker T
  refine ⟨sqPart (cofactorVec T), cbPart (cofactorVec T), ?_, ?_⟩
  · have hmk : mkPart (sqPart (cofactorVec T)) (cbPart (cofactorVec T)) = cofactorVec T :=
      btg_mkPart_sqPart_cbPart _
    have hf := chartDiff_fderiv_mkPart p D N hD hN hy
      (sqPart (cofactorVec T)) (cbPart (cofactorVec T))
    have hAB : tangentCoordChange (𝓡 4) (D (sqPart y)) p (D (sqPart y))
          (mfderiv (𝓡 2) (𝓡 4) D (sqPart y) (sqPart (cofactorVec T)))
        - tangentCoordChange (𝓡 4) (N (cbPart y)) p (N (cbPart y))
          (mfderiv (𝓡 3) (𝓡 4) N (cbPart y) (cbPart (cofactorVec T))) = 0 := by
      rw [← hf, hmk, ← hT]
      exact hker
    have htceq : tangentCoordChange (𝓡 4) (D (sqPart y)) p (D (sqPart y))
        = tangentCoordChange (𝓡 4) (N (cbPart y)) p (N (cbPart y)) := by
      rw [← heq]
    have hsrc1 : D (sqPart y) ∈ (extChartAt (𝓡 4) (D (sqPart y))).source :=
      mem_extChartAt_source (I := 𝓡 4) (D (sqPart y))
    have hsrc2 : D (sqPart y) ∈ (extChartAt (𝓡 4) p).source := by
      rw [extChartAt_source]
      exact hy.1
    have hinj : Function.Injective (tangentCoordChange (𝓡 4) (D (sqPart y)) p
        (D (sqPart y))) :=
      tangentCoordChange_injective ⟨hsrc1, hsrc2⟩
    have h3 : tangentCoordChange (𝓡 4) (D (sqPart y)) p (D (sqPart y))
          (mfderiv (𝓡 2) (𝓡 4) D (sqPart y) (sqPart (cofactorVec T)))
        = tangentCoordChange (𝓡 4) (D (sqPart y)) p (D (sqPart y))
          (mfderiv (𝓡 3) (𝓡 4) N (cbPart y) (cbPart (cofactorVec T))) := by
      have h := sub_eq_zero.mp hAB
      rw [← htceq] at h
      exact h
    exact hinj h3
  · rw [btg_mkPart_sqPart_cbPart]
    exact hcof


/-- **The charted chain map `u ↦ chr p (G u w)` is differentiable wherever its value lies in the
chart source.** -/
private lemma btg_hasFDerivAt_charted_chain {m : ℕ}
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) (w : EuclideanSpace ℝ (Fin 3)) (t : EuclideanSpace ℝ (Fin m))
    (hsrc : G t w ∈ (chr p).source) :
    HasFDerivAt (fun u : EuclideanSpace ℝ (Fin m) => chr p (G u w))
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin m) => chr p (G u w)) t) t := by
  have hinner : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin m) => G u w) := by
    have hpair : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin m) => (u, w)) := by
      have hc0 : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : EuclideanSpace ℝ (Fin m) =>
            ((0 : EuclideanSpace ℝ (Fin m)), w)) := contMDiff_const
      have hi0 : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : EuclideanSpace ℝ (Fin m) =>
            ((u, (0 : EuclideanSpace ℝ (Fin 3))) :
              EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) :=
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin 3))).contMDiff
      have hh := hi0.add hc0
      have hfun : ((fun u : EuclideanSpace ℝ (Fin m) =>
            ((u, (0 : EuclideanSpace ℝ (Fin 3))) :
              EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) +
          (fun _ : EuclideanSpace ℝ (Fin m) =>
            ((0 : EuclideanSpace ℝ (Fin m)), w)))
          = (fun u : EuclideanSpace ℝ (Fin m) => (u, w)) := by
        funext u
        simp
      rw [hfun] at hh
      exact hh
    simpa only [Function.comp_def] using hG.comp hpair
  have hchrOn : ContMDiffOn (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chr p) (chr p).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    simpa [chr] using h
  have h3 : ContMDiffAt (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin m) => chr p (G u w)) t :=
    (hchrOn.contMDiffAt ((chr p).open_source.mem_nhds hsrc)).comp t hinner.contMDiffAt
  exact ((contMDiffAt_iff_contDiffAt.mp h3).differentiableAt btg_top_ne_zero_order).hasFDerivAt

end Aux

/-- **The multi-chart parametric Sard for a finite family of two-parameter loop families.**  See the
module docstring of `boxThree_of_good_family`. -/
private theorem btg_main {m : ℕ} {ι : Type*} [Fintype ι]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (A : ι → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ∀ i, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (A i))
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (hsurj : ∀ (i : ι) (t : EuclideanSpace ℝ (Fin m)) (y : Amb 4),
      y ∈ Submission.Drive.unitBox 4 → A i (sqPart y) = G t (cbPart y) →
      ∀ (p : M), G t (cbPart y) ∈ (chr p).source →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (G t' (cbPart y))) t))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < δ ∧ ∀ i : ι, BoxThree (A i) (G p) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hne
  · exact ⟨0, by simpa using hδ, fun i => (hι.false i).elim⟩
  obtain ⟨i₀⟩ := hne
  -- ## Step 1: the compact set of loop values and its finite chart cover
  have hScomp : IsCompact (⋃ i : ι, A i '' Submission.Drive.unitBox 1) :=
    isCompact_iUnion (fun i => (isCompact_unitBox 1).image (hA i).continuous)
  obtain ⟨r, pch, C0, C1, hC0c, hC1c, hC0int, hC1sub, hcover⟩ :=
    exists_compact_chart_cover _ hScomp
  -- ## Step 2: the compact sets `Sc`, the chart-containment regions `Uc`
  set Sc : Fin r → ι → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun k i =>
    {q | ‖q.1‖ ≤ 1 ∧ q.2 ∈ Submission.Drive.unitBox 4 ∧
      A i (sqPart q.2) ∈ C0 k ∧ G q.1 (cbPart q.2) ∈ C1 k} with hSc
  set Uc : Fin r → ι → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun k i =>
    {q | A i (sqPart q.2) ∈ (chr (pch k)).source ∧
      G q.1 (cbPart q.2) ∈ (chr (pch k)).source} with hUc
  have hcont_sq : ∀ i, Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      A i (sqPart q.2)) :=
    fun i => (hA i).continuous.comp (btg_continuous_sqPart.comp continuous_snd)
  have hcont_cb : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      G q.1 (cbPart q.2)) :=
    hG.continuous.comp (continuous_fst.prodMk (btg_continuous_cbPart.comp continuous_snd))
  have hSc_compact : ∀ k i, IsCompact (Sc k i) := by
    intro k i
    have hEq : Sc k i = (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ
          Submission.Drive.unitBox 4)
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => A i (sqPart q.2)) ⁻¹' (C0 k))
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => G q.1 (cbPart q.2)) ⁻¹' (C1 k)) := by
      rw [hSc]
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right]
      tauto
    refine IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1).prod (isCompact_unitBox 4)) ?_ ?_
    · rw [hEq]
      exact (((Metric.isClosed_closedBall.prod (isClosed_unitBox 4)).inter
        ((hC0c k).isClosed.preimage (hcont_sq i))).inter
        ((hC1c k).isClosed.preimage hcont_cb))
    · intro q hq
      rw [hEq] at hq
      exact ⟨hq.1.1.1, hq.1.1.2⟩
  have hUc_open : ∀ k i, IsOpen (Uc k i) := by
    intro k i
    rw [hUc]
    exact ((hcont_sq i).isOpen_preimage _ (chr (pch k)).open_source).inter
      (hcont_cb.isOpen_preimage _ (chr (pch k)).open_source)
  have hSc_Uc : ∀ k i, Sc k i ⊆ Uc k i := by
    intro k i q hq
    simp only [hSc, Set.mem_setOf_eq] at hq
    simp only [hUc, Set.mem_setOf_eq]
    exact ⟨hC1sub k (interior_subset (hC0int k hq.2.2.1)), hC1sub k hq.2.2.2⟩
  have hthick : ∀ k i, ∃ δk : ℝ, 0 < δk ∧ ∀ (q q' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
      (q, z) ∈ Sc k i → ‖q' - q‖ ≤ δk → (q', z) ∈ Uc k i :=
    fun k i => exists_pos_norm_subset_of_isCompact_subset_isOpen
      (hSc_compact k i) (hUc_open k i) (hSc_Uc k i)
  choose δk hδkpos hδk using hthick
  -- ## Step 3: the index encoding, the uniform thickening radius and `ε`
  have hrne : Nonempty (Fin r) := by
    have hmem : A i₀ (0 : EuclideanSpace ℝ (Fin 2)) ∈
        ⋃ i : ι, A i '' Submission.Drive.unitBox 1 :=
      Set.mem_iUnion.mpr ⟨i₀, ⟨0, by simp [Submission.Drive.unitBox], rfl⟩⟩
    obtain ⟨k, -⟩ := Set.mem_iUnion.mp (hcover hmem)
    exact ⟨k⟩
  set δ0 : ℝ := (Finset.univ : Finset (Fin r × ι)).inf'
      ⟨(Classical.choice hrne, i₀), Finset.mem_univ _⟩ (fun ki => δk ki.1 ki.2) with hδ0
  have hδ0pos : 0 < δ0 := by
    rw [hδ0]
    exact (Finset.lt_inf'_iff (s := (Finset.univ : Finset (Fin r × ι)))
      ⟨(Classical.choice hrne, i₀), Finset.mem_univ _⟩).mpr (fun ki _ => hδkpos ki.1 ki.2)
  have hδ0le : ∀ k i, δ0 ≤ δk k i := by
    intro k i
    rw [hδ0]
    exact Finset.inf'_le (fun ki : Fin r × ι => δk ki.1 ki.2) (Finset.mem_univ (k, i))
  set ε : ℝ := min (min (δ / 2) (1 / 2)) (δ0 / 4) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
  have hεδ : ε < δ := by
    have h1 : ε ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hε1 : ε ≤ 1 := by
    have h1 : ε ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have h2ε : 2 * ε ≤ δ0 := by
    have h1 : ε ≤ δ0 / 4 := min_le_right _ _
    linarith
  -- ## Step 4: the projected compact sets `Kc` and the uniform chart containment
  set Kc : Fin r → ι → Set (Amb 4) := fun k i => {z | ∃ q : EuclideanSpace ℝ (Fin m),
      ‖q‖ ≤ ε ∧ (q, z) ∈ Sc k i} with hKc
  have hKc_compact : ∀ k i, IsCompact (Kc k i) := by
    intro k i
    have hEq : Kc k i = Prod.snd ''
        (Sc k i ∩ {q : EuclideanSpace ℝ (Fin m) × Amb 4 | ‖q.1‖ ≤ ε}) := by
      rw [hKc]
      ext z
      constructor
      · rintro ⟨q, hqε, hqS⟩
        exact ⟨(q, z), ⟨hqS, hqε⟩, rfl⟩
      · rintro ⟨q, ⟨hqS, hqε⟩, rfl⟩
        exact ⟨q.1, hqε, hqS⟩
    rw [hEq]
    have hclosed : IsClosed ({q : EuclideanSpace ℝ (Fin m) × Amb 4 | ‖q.1‖ ≤ ε}) :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    exact ((hSc_compact k i).inter_right hclosed).image continuous_snd
  have hKsub : ∀ k i,
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) ×ˢ Kc k i ⊆ Uc k i := by
    intro k i
    rintro ⟨q, z⟩ ⟨hq, hz⟩
    simp only [hKc, Set.mem_setOf_eq] at hz
    obtain ⟨q₀, hq₀, hq₀S⟩ := hz
    have hqq : ‖q - q₀‖ ≤ δk k i := by
      have hqε : ‖q‖ ≤ ε := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hq
      have h1 : ‖q - q₀‖ ≤ ‖q‖ + ‖q₀‖ := norm_sub_le q q₀
      have h2 : δ0 ≤ δk k i := hδ0le k i
      linarith
    exact hδk k i q₀ q z hq₀S hqq
  have hKmeet : ∀ k i (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖q‖ ≤ ε → z ∈ Kc k i →
      (q, z) ∈ Uc k i := fun k i q z hq hz => hKsub k i
        ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hq, hz⟩
  -- ## Step 5: the cut-off functions and the systems
  have hcut : ∀ k i, ∃ χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) ×ˢ Kc k i, χ q = 1) ∧
      tsupport χ ⊆ Uc k i := by
    intro k i
    obtain ⟨χ, hχsm, -, hχone', hχsupp⟩ := contDiff_bump_of_isCompact_subset_isOpen
      ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) ε).prod (hKc_compact k i))
      (hUc_open k i) (hKsub k i)
    exact ⟨χ, hχsm, hχone', hχsupp⟩
  choose χ hχsm hχone hχsupp using hcut
  have hχval : ∀ k i (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖q‖ ≤ ε → z ∈ Kc k i →
      χ k i (q, z) = 1 := fun k i q z hq hz => hχone k i (q, z)
        ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hq, hz⟩
  set Φ : Fin r → ι → EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 :=
    fun k i q => χ k i q • chartDiff (pch k) (A i) (G q.1) q.2 with hΦ
  have hΦsm : ∀ k i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k i) := by
    intro k i
    rw [hΦ]
    exact btg_contDiff_cutoff_chartDiff (A i) (hA i) G hG (pch k) (hχsm k i)
      (fun q hq => by rw [hUc] at hq; exact hq) (hχsupp k i)
  have hΦzero : ∀ k i (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖q‖ ≤ ε → z ∈ Kc k i →
      (Φ k i (q, z) = 0 ↔ A i (sqPart z) = G q (cbPart z)) := by
    intro k i q z hq hz
    have hχ1 : χ k i (q, z) = 1 := hχval k i q z hq hz
    have hU : z ∈ chartRegion (pch k) (A i) (G q) := by
      have h := hKmeet k i q z hq hz
      simp only [hUc, Set.mem_setOf_eq] at h
      exact h
    simp only [hΦ]
    rw [hχ1, one_smul, chartDiff_eq_zero_iff hU]
  -- ## Step 6: the encoded family index
  set Ef : (ι × Fin r) ≃ Fin (Fintype.card (ι × Fin r)) := Fintype.equivFin (ι × Fin r) with hEf
  let Kf : Fin (Fintype.card (ι × Fin r)) → Set (Amb 4) :=
    fun j => Kc (Ef.symm j).2 (Ef.symm j).1
  let Φf : Fin (Fintype.card (ι × Fin r)) →
      EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 :=
    fun j => Φ (Ef.symm j).2 (Ef.symm j).1
  have hKf_apply : ∀ (i : ι) (k : Fin r), Kf (Ef (i, k)) = Kc k i := by
    intro i k
    dsimp only [Kf]
    rw [Equiv.symm_apply_apply]
  have hΦf_apply : ∀ (i : ι) (k : Fin r), Φf (Ef (i, k)) = Φ k i := by
    intro i k
    dsimp only [Φf]
    rw [Equiv.symm_apply_apply]
  have hKf_compact : ∀ j, IsCompact (Kf j) := by
    intro j
    obtain ⟨x, rfl⟩ := Ef.surjective j
    rcases x with ⟨i, k⟩
    rw [hKf_apply i k]
    exact hKc_compact k i
  have hΦf_sm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φf j) := by
    intro j
    obtain ⟨x, rfl⟩ := Ef.surjective j
    rcases x with ⟨i, k⟩
    rw [hΦf_apply i k]
    exact hΦsm k i
  -- ## Step 7: the parametric-Sard hypothesis of the family of systems
  have hsurjΦ : ∀ (j : Fin (Fintype.card (ι × Fin r)))
      (p : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖p‖ < ε →
      (z ∈ Kf j ∨ ∃ l : FaceIdx4,
        z ∈ (fun y : ↥(Fdir4 l) => Fbase4 l + (y : Amb 4)) '' (Fcov4 (Kf j) l)) →
      Φf j (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φf j (p', z)) p) := by
    intro j p z hp hzdisj h0
    obtain ⟨x, rfl⟩ := Ef.surjective j
    rcases x with ⟨i, k⟩
    rw [hKf_apply i k] at hzdisj
    rw [hΦf_apply i k] at h0 ⊢
    have hzK : z ∈ Kc k i := hzdisj.elim id (fun h => by
      obtain ⟨l, y, hy, hyl⟩ := h
      rw [← hyl]
      exact hy)
    have hχ1 : χ k i (p, z) = 1 := hχval k i p z (le_of_lt hp) hzK
    have hmeet : A i (sqPart z) = G p (cbPart z) := (hΦzero k i p z (le_of_lt hp) hzK).mp h0
    have hU : z ∈ chartRegion (pch k) (A i) (G p) := by
      have h := hKmeet k i p z (le_of_lt hp) hzK
      simp only [hUc, Set.mem_setOf_eq] at h
      exact h
    have hzy : chartDiff (pch k) (A i) (G p) z = 0 :=
      (chartDiff_eq_zero_iff hU).mpr hmeet
    have hfd := btg_fderiv_cutoff_chartDiff_p (A i) (hA i) G hG (pch k) (hχsm k i) hχ1 hU hzy
    have hzbox : z ∈ Submission.Drive.unitBox 4 := by
      simp only [hKc, Set.mem_setOf_eq] at hzK
      obtain ⟨q, -, hqS⟩ := hzK
      simp only [hSc, Set.mem_setOf_eq] at hqS
      exact hqS.2.1
    have hbase := hsurj i p z hzbox hmeet (pch k) hU.2
    -- ## the charted chain map `u ↦ chr (pch k) (G u (cbPart z))` is differentiable at `p`
    have hchain' : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr (pch k) (G t' (cbPart z)))
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chr (pch k) (G t' (cbPart z))) p) p := by
      have hinner : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : EuclideanSpace ℝ (Fin m) => G u (cbPart z)) := by
        have hpair : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
            (modelWithCornersSelf ℝ
              (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
            ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun u : EuclideanSpace ℝ (Fin m) => (u, cbPart z)) := by
          have hc0 : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
              (modelWithCornersSelf ℝ
                (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
              ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun _ : EuclideanSpace ℝ (Fin m) =>
                ((0 : EuclideanSpace ℝ (Fin m)), cbPart z)) := contMDiff_const
          have hi0 : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
              (modelWithCornersSelf ℝ
                (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
              ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun u : EuclideanSpace ℝ (Fin m) =>
                ((u, (0 : EuclideanSpace ℝ (Fin 3))) :
                  EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) :=
            (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m))
              (EuclideanSpace ℝ (Fin 3))).contMDiff
          have hh := hi0.add hc0
          have hfun : ((fun u : EuclideanSpace ℝ (Fin m) =>
                ((u, (0 : EuclideanSpace ℝ (Fin 3))) :
                  EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) +
              (fun _ : EuclideanSpace ℝ (Fin m) =>
                ((0 : EuclideanSpace ℝ (Fin m)), cbPart z)))
              = (fun u : EuclideanSpace ℝ (Fin m) => (u, cbPart z)) := by
            funext u
            simp
          rw [hfun] at hh
          exact hh
        simpa only [Function.comp_def] using hG.comp hpair
      have hchrOn : ContMDiffOn (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chr (pch k))
          (chr (pch k)).source := by
        have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := pch k)
          (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
        simpa [chr] using h
      have h3 : ContMDiffAt (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : EuclideanSpace ℝ (Fin m) => chr (pch k) (G u (cbPart z))) p :=
        (hchrOn.contMDiffAt ((chr (pch k)).open_source.mem_nhds hU.2)).comp p
          hinner.contMDiffAt
      exact ((contMDiffAt_iff_contDiffAt.mp h3).differentiableAt btg_top_ne_zero_order).hasFDerivAt
    have hneg : fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          chartDiff (pch k) (A i) (G t') z) p
        = - (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            chr (pch k) (G t' (cbPart z))) p) := by
      have hconst' : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin m) =>
          chr (pch k) (A i (sqPart z))) (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] Tgt 4) p :=
        hasFDerivAt_const (x := p) (c := chr (pch k) (A i (sqPart z)))
      have hsub := hconst'.sub hchain'
      have hfun : (fun t' : EuclideanSpace ℝ (Fin m) => chartDiff (pch k) (A i) (G t') z)
          = ((fun _ : EuclideanSpace ℝ (Fin m) => chr (pch k) (A i (sqPart z))) -
             (fun t' : EuclideanSpace ℝ (Fin m) => chr (pch k) (G t' (cbPart z)))) := by
        funext t'
        rfl
      rw [hfun, hsub.fderiv]
      simp
    simp only [hΦ] at h0
    rw [hfd, hneg]
    intro w
    obtain ⟨v, hv⟩ := hbase (-w)
    refine ⟨v, ?_⟩
    have hv' : (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr (pch k) (G t' (cbPart z))) p) v = -w := hv
    show - ((fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr (pch k) (G t' (cbPart z))) p) v) = w
    rw [hv']
    simp
  -- ## Step 8: the multi-chart parametric Sard
  obtain ⟨p, hpε, hreg, hfac, havoid⟩ :=
    goodFaceMulti (m := m) (n := 4) (r := Fintype.card (ι × Fin r)) (K := Kf)
      (hK := hKf_compact)
      (ι := fun _ => FaceIdx4) (X := fun _ l => ↥(Fdir4 l))
      (hX := fun _ l => Fdir4_finrank_lt l)
      (B := fun _ l => fun y : ↥(Fdir4 l) => Fbase4 l + (y : Amb 4))
      (hB := fun _ l => contDiff_Fparam4 l)
      (K₀ := fun j l => Fcov4 (Kf j) l)
      (hK₀ := fun j l => Fcov4_isCompact (Kf j) (hKf_compact j) l)
      (Φ := Φf) (hΦ := hΦf_sm) (ε := ε) (hε := hεpos) (hsurj := hsurjΦ)
  refine ⟨p, lt_of_lt_of_le hpε (le_of_lt hεδ), ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · -- ### clause 1: transversality
    intro x hxbox hmeet
    have hx1 : sqPart x ∈ Submission.Drive.unitBox 1 :=
      ((mem_unitBox_five_iff x).mp hxbox).1
    have hval : A i (sqPart x) ∈ ⋃ k : Fin r, C0 k :=
      hcover (Set.mem_iUnion.mpr ⟨i, ⟨sqPart x, hx1, rfl⟩⟩)
    obtain ⟨k, hkC0⟩ := Set.mem_iUnion.mp hval
    have hxK : x ∈ Kc k i := by
      refine ⟨p, le_of_lt hpε, ?_⟩
      simp only [hSc, Set.mem_setOf_eq]
      exact ⟨le_trans (le_of_lt hpε) hε1, hxbox, hkC0, by
        rw [← hmeet]
        exact interior_subset (hC0int k hkC0)⟩
    have hΦ0 : Φf (Ef (i, k)) (p, x) = 0 := by
      rw [hΦf_apply i k, (hΦzero k i p x (le_of_lt hpε) hxK).mpr hmeet]
    have hzsurj := hreg (Ef (i, k)) x (by rw [hKf_apply i k]; exact hxK) hΦ0
    rw [hΦf_apply i k] at hzsurj
    simp only [hΦ] at hzsurj
    have hχ1 : χ k i (p, x) = 1 := hχval k i p x (le_of_lt hpε) hxK
    have hU : x ∈ chartRegion (pch k) (A i) (G p) := by
      have h := hKmeet k i p x (le_of_lt hpε) hxK
      simp only [hUc, Set.mem_setOf_eq] at h
      exact h
    have hzy : chartDiff (pch k) (A i) (G p) x = 0 :=
      (chartDiff_eq_zero_iff hU).mpr hmeet
    have hfd := btg_fderiv_cutoff_chartDiff_z (A i) (hA i) G hG (pch k) (hχsm k i) hχ1 hU hzy
    rw [hfd] at hzsurj
    exact range_sup_eq_top_of_chartDiff_surjective (pch k) (A i) (G p) (hA i)
      (btg_contMDiff_fixed_chain G hG p) hU hmeet hzsurj
  · -- ### clause 2: no two faces
    intro x hxbox hmeet h2
    have hx1 : sqPart x ∈ Submission.Drive.unitBox 1 :=
      ((mem_unitBox_five_iff x).mp hxbox).1
    have hval : A i (sqPart x) ∈ ⋃ k : Fin r, C0 k :=
      hcover (Set.mem_iUnion.mpr ⟨i, ⟨sqPart x, hx1, rfl⟩⟩)
    obtain ⟨k, hkC0⟩ := Set.mem_iUnion.mp hval
    have hxK : x ∈ Kc k i := by
      refine ⟨p, le_of_lt hpε, ?_⟩
      simp only [hSc, Set.mem_setOf_eq]
      exact ⟨le_trans (le_of_lt hpε) hε1, hxbox, hkC0, by
        rw [← hmeet]
        exact interior_subset (hC0int k hkC0)⟩
    have hΦ0k : Φ k i (p, x) = 0 := (hΦzero k i p x (le_of_lt hpε) hxK).mpr hmeet
    obtain ⟨l, y, hy, hyl⟩ := Fcov4_cover (Kf (Ef (i, k)))
      (by rw [hKf_apply i k]; exact hxK) h2
    have hyK : y ∈ Fcov4 (Kf (Ef (i, k))) l := hy
    have havoid' := havoid (Ef (i, k)) l y hyK
    rw [hΦf_apply i k] at havoid'
    rw [hyl] at havoid'
    exact havoid' hΦ0k
  · -- ### clause 3: the crossing direction
    intro x hxbox hmeet i0 hi0 _hinter
    have hx1 : sqPart x ∈ Submission.Drive.unitBox 1 :=
      ((mem_unitBox_five_iff x).mp hxbox).1
    have hval : A i (sqPart x) ∈ ⋃ k : Fin r, C0 k :=
      hcover (Set.mem_iUnion.mpr ⟨i, ⟨sqPart x, hx1, rfl⟩⟩)
    obtain ⟨k, hkC0⟩ := Set.mem_iUnion.mp hval
    have hxK : x ∈ Kc k i := by
      refine ⟨p, le_of_lt hpε, ?_⟩
      simp only [hSc, Set.mem_setOf_eq]
      exact ⟨le_trans (le_of_lt hpε) hε1, hxbox, hkC0, by
        rw [← hmeet]
        exact interior_subset (hC0int k hkC0)⟩
    have hΦ0k : Φ k i (p, x) = 0 := (hΦzero k i p x (le_of_lt hpε) hxK).mpr hmeet
    have hΦ0 : Φf (Ef (i, k)) (p, x) = 0 := by rw [hΦf_apply i k]; exact hΦ0k
    have hxKk : x ∈ Kf (Ef (i, k)) := by rw [hKf_apply i k]; exact hxK
    have hfull := hreg (Ef (i, k)) x hxKk hΦ0
    have hface := hfac (Ef (i, k)) i0 x hxKk hΦ0 hi0
    rw [hΦf_apply i k] at hfull hface
    simp only [hΦ] at hfull hface
    have hχ1 : χ k i (p, x) = 1 := hχval k i p x (le_of_lt hpε) hxK
    have hU : x ∈ chartRegion (pch k) (A i) (G p) := by
      have h := hKmeet k i p x (le_of_lt hpε) hxK
      simp only [hUc, Set.mem_setOf_eq] at h
      exact h
    have hzy : chartDiff (pch k) (A i) (G p) x = 0 :=
      (chartDiff_eq_zero_iff hU).mpr hmeet
    have hfd := btg_fderiv_cutoff_chartDiff_z (A i) (hA i) G hG (pch k) (hχsm k i) hχ1 hU hzy
    rw [hfd] at hfull hface
    exact btg_exists_sigma_tau_of_faceSurjective_loop (pch k) (A i) (G p) (hA i)
      (btg_contMDiff_fixed_chain G hG p) hU hmeet hfull hface



/-- **Multi-chart parametric Sard for a finite family of two-parameter loop families.**

The multi-chart upgrade of `Work.Drive.loopFamData_of_good_family` and, simultaneously, its
multi-loop upgrade: the conclusion is the three-clause `Work.Drive.BoxThree` at the box.  `M` is an
arbitrary smooth four-manifold; the two regularity facts about the family (smoothness of `G` and the
parameter-surjectivity `hsurj`) are hypotheses. -/
theorem boxThree_of_good_family {m : ℕ} {ι : Type*} [Fintype ι]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (A : ι → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ∀ i, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (A i))
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (base : EuclideanSpace ℝ (Fin m)) (δ : ℝ) (hδ : 0 < δ)
    (hsurj : ∀ (i : ι) (t : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Amb 4),
      y ∈ Submission.Drive.unitBox 4 → A i (Work.Drive.sqPart y) = G t (Work.Drive.cbPart y) →
      ∀ (p : M), G t (Work.Drive.cbPart y) ∈ (Work.Drive.chr p).source →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.chr p (G t' (Work.Drive.cbPart y))) t)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < δ ∧ ∀ i : ι, Work.Drive.BoxThree (A i) (G (base + p)) := by
  refine btg_main A hA (fun t' => fun y' => G (base + t') y') ?_ ?_ δ hδ
  · exact btg_contMDiff_shift_chain G hG base
  · intro i t y hy heq p hsrc
    have hmeet : A i (sqPart y) = G (base + t) (cbPart y) := heq
    have hsrc' : G (base + t) (cbPart y) ∈ (chr p).source := hsrc
    have hb := hsurj i (base + t) y hy hmeet p hsrc'
    have hFdiff := btg_hasFDerivAt_charted_chain G hG p (cbPart y) (base + t) hsrc'
    have hshift : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => base + t')
        (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) t :=
      (hasFDerivAt_id t).const_add base
    have hcomp := hFdiff.comp t hshift
    have hfd : fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          chr p (G (base + t') (cbPart y))) t
        = fderiv ℝ (fun u : EuclideanSpace ℝ (Fin m) => chr p (G u (cbPart y)))
            (base + t) := by
      have h1 : fderiv ℝ ((fun u : EuclideanSpace ℝ (Fin m) => chr p (G u (cbPart y))) ∘
          (fun t' : EuclideanSpace ℝ (Fin m) => base + t')) t
          = fderiv ℝ (fun u : EuclideanSpace ℝ (Fin m) => chr p (G u (cbPart y)))
              (base + t) := by
        rw [hcomp.fderiv]
        ext v
        simp
      simpa only [Function.comp_def] using h1
    show Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
      chr p (G (base + t') (cbPart y))) t)
    intro w
    obtain ⟨v, hv⟩ := hb w
    exact ⟨v, by rw [hfd]; exact hv⟩

end

end Work.Drive
