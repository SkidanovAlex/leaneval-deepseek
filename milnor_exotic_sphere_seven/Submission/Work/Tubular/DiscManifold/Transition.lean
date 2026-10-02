import Submission.Work.Tubular.DiscManifold.ChartCont

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The transition maps of the disc charts are `C¹`

The disc charts `discChart C p` of `ChartCont.lean` cover the normal disc bundle.  This file proves
that their transitions are `C¹`, which is the mathematical content of the statement that the disc
bundle is a smooth manifold with boundary.

Three lemmas:

* `chartBaseTransition` — the transition between two preferred charts of the base `V.pt`, read on
  the model `ℝ⁸`;
* `frameChangeDiscPt` — the fibre factor `(y, c) ↦ ballChart (frameChange (c₀.symm y) c)`, whose
  smoothness uses the smoothness of the change of trivialisation `readF ∘ insF` and of the
  preferred chart of the closed ball;
* `transitionSmooth` — the transition of the disc charts themselves, assembled from the two.
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter
open OpenPartialHomeomorph

open Work.ThomBordism.PontryaginThom (EmbeddingData CoverIdx coverBaseSet coverIndexAt
  mem_coverBaseSet_indexAt)

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.SignatureBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-! ## The transition of the base charts -/

theorem chartBaseTransition (V : Work.ThomBordism.Man8) (x₀ x₁ : V.pt) :
    ContDiffOn ℝ 1 (fun y : Euc 8 => (chartAt (Euc 8) x₁) ((chartAt (Euc 8) x₀).symm y))
      ((chartAt (Euc 8) x₀).target ∩
        (chartAt (Euc 8) x₀).symm ⁻¹' (chartAt (Euc 8) x₁).source) := by
  have _ : IsManifold (𝓡 8) 1 V.pt := V.isManifold_one
  have hmem : (chartAt (Euc 8) x₀).symm ≫ₕ (chartAt (Euc 8) x₁) ∈ contDiffGroupoid 1 (𝓡 8) :=
    (contDiffGroupoid 1 (𝓡 8)).compatible (chart_mem_atlas (Euc 8) x₀)
      (chart_mem_atlas (Euc 8) x₁)
  have h := contMDiffOn_of_mem_contDiffGroupoid hmem
  exact (contMDiffOn_iff_contDiffOn).mp h

/-! ## The fibre factor -/

theorem frameChangeDiscPt {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i j : CoverIdx V k) (x₀ : V.pt) (b : Ball (k - 1)) :
    ContDiffOn ℝ 1
      (fun z : Euc 8 × Euc ((k - 1) + 1) =>
        ((chartAt (Half (k - 1)) b)
          (discPt (k - 1) (frameChangeE C i j ((chartAt (Euc 8) x₀).symm z.1) z.2))).val)
      {z | z.1 ∈ chartCover E i x₀ ∧ z.1 ∈ chartCover E j x₀ ∧ ‖z.2‖ ≤ 1 ∧
        frameChangeE C i j ((chartAt (Euc 8) x₀).symm z.1) z.2 ∈
          DiscManifold.ballChartAmb (k - 1) b} := by
  set T : Set (Euc 8 × Euc ((k - 1) + 1)) :=
    {z | z.1 ∈ chartCover E i x₀ ∧ z.1 ∈ chartCover E j x₀ ∧ ‖z.2‖ ≤ 1 ∧
      frameChangeE C i j ((chartAt (Euc 8) x₀).symm z.1) z.2 ∈
        DiscManifold.ballChartAmb (k - 1) b} with hT
  set g : Euc 8 × Euc ((k - 1) + 1) → Euc ((k - 1) + 1) :=
    fun z => frameChangeE C i j ((chartAt (Euc 8) x₀).symm z.1) z.2 with hg
  have hg_smooth : ContDiffOn ℝ 1 g ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) := by
    have hbase := contDiffOn_readF_insFE_chart C i j x₀
    have hlin : ContDiffOn ℝ 1 (fun z : Euc 8 × Euc ((k - 1) + 1) =>
        reindexFibreCLM k (readF C j ((chartAt (Euc 8) x₀).symm z.1)
          (insFE C i ((chartAt (Euc 8) x₀).symm z.1) z.2)))
        ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) :=
      (reindexFibreCLM k).contDiff.comp_contDiffOn hbase
    refine hlin.congr fun z _ => ?_
    show frameChangeE C i j ((chartAt (Euc 8) x₀).symm z.1) z.2 =
      reindexFibreCLM k (readF C j ((chartAt (Euc 8) x₀).symm z.1)
        (insFE C i ((chartAt (Euc 8) x₀).symm z.1) z.2))
    rw [frameChangeE_apply, frameChange, ContinuousLinearMap.comp_apply, insFE_apply]
    rfl
  have hg_maps : Set.MapsTo g T {v : Euc ((k - 1) + 1) |
      v ∈ Ball (k - 1) ∧ discPt (k - 1) v ∈ (chartAt (Half (k - 1)) b).source} := by
    intro z hz
    rw [hT] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hnorm : ‖g z‖ = ‖z.2‖ := norm_frameChangeE C i j h1.2 h2.2 z.2
    have hball : g z ∈ Ball (k - 1) := by
      rw [Metric.mem_closedBall, dist_zero_right, hnorm]; exact h3
    exact ⟨hball,
      ((DiscManifold.ballChartAmb_spec (k - 1) b).2 (g z) hball).mpr h4⟩
  have hmain : ContDiffOn ℝ 1 ((fun v : Euc ((k - 1) + 1) =>
      ((chartAt (Half (k - 1)) b) (discPt (k - 1) v)).val) ∘ g) T :=
    (DiscManifold.contDiffOn_ballChartAt (k - 1) b).comp (hg_smooth.mono (by
      intro z hz; rw [hT] at hz; exact ⟨⟨hz.1, hz.2.1⟩, Set.mem_univ _⟩)) hg_maps
  exact hmain.congr fun z _ => rfl


/-- The trivialization identity behind `frameChangeE`: reading `insFE` back with `readFE` is the
change of trivialization. -/
theorem readFE_insFE' {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i j : CoverIdx V k) (x : V.pt) (c : Euc ((k - 1) + 1)) :
    readFE C j x (insFE C i x c) = frameChangeE C i j x c := by
  rw [readFE_apply, insFE_apply, frameChangeE_apply, frameChange]
  rfl

/-! ## The transition of the disc charts -/

theorem transitionSmooth {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (p q : NormalDiscSub E ε) :
    ContDiffOn ℝ 1
      (↑(Iprod k) ∘ ⇑((discChart C p).symm ≫ₕ discChart C q) ∘ ↑(Iprod k).symm)
      ((↑(Iprod k).symm) ⁻¹' ((discChart C p).symm ≫ₕ discChart C q).source ∩
        Set.range ↑(Iprod k)) := by
  set D : Set (Euc 8 × Euc ((k - 1) + 1)) :=
    (↑(Iprod k).symm) ⁻¹' ((discChart C p).symm ≫ₕ discChart C q).source ∩
      Set.range ↑(Iprod k) with hD
  have hz1 : ∀ x : Euc 8 × Euc ((k - 1) + 1), (((Iprod k).symm).toFun x).1 = x.1 :=
    fun x => rfl
  have hz2 : ∀ x : Euc 8 × Euc ((k - 1) + 1),
      (((Iprod k).symm).toFun x).2 = (hModel (k - 1)).symm x.2 := fun x => rfl
  have hrange : ∀ x : Euc 8 × Euc ((k - 1) + 1),
      x ∈ Set.range ((Iprod k).toFun) → 0 ≤ x.2 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact y.2.property
  have hdom : ∀ x, x ∈ D →
      (chartBaseC p).symm x.1 ∈ coverBaseSet E.e (discPiece p) ∧
      x.1 ∈ (chartBaseC p).target ∧
      (chartBaseC p).symm x.1 ∈ (chartBaseC q).source ∧
      (chartBaseC p).symm x.1 ∈ coverBaseSet E.e (discPiece q) ∧
      (hModel (k - 1)).symm x.2 ∈ (chartFibC C p).target ∧
      frameChangeE C (discPiece p) (discPiece q) ((chartBaseC p).symm x.1)
        (((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val) ∈
          DiscManifold.ballChartAmb (k - 1) (chartFibPt C q) ∧
      0 ≤ x.2 0 := by
    intro x hx
    rw [hD] at hx
    obtain ⟨hz, hr⟩ := hx
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    have htgt : (((Iprod k).symm).toFun x) ∈ chartTarget C p := by
      rw [← discChart_target]; exact hz.1
    have hsrc : chartInvFun C p (((Iprod k).symm).toFun x) ∈ chartSource C q := by
      rw [← discChart_source]; exact hz.2
    obtain ⟨h1', h2', h3'⟩ := (mem_chartTarget_iff C p).mp htgt
    have hc : chartInvCond C p (((Iprod k).symm).toFun x) := ⟨h1', h3'⟩
    have hproj : NormalTotal.proj (chartInvFun C p (((Iprod k).symm).toFun x)).1 =
        (chartBaseC p).symm (((Iprod k).symm).toFun x).1 := by
      rw [chartInvFun, dif_pos hc]
      rfl
    have hvec : NormalTotal.vec (chartInvFun C p (((Iprod k).symm).toFun x)).1 =
        insFE C (discPiece p) ((chartBaseC p).symm (((Iprod k).symm).toFun x).1)
          (ε • ((chartFibC C p).symm (((Iprod k).symm).toFun x).2).val) := by
      rw [chartInvFun, dif_pos hc]
      rfl
    have hsrcf := (mem_chartSource_iff C q).mp hsrc
    have hk1 : (chartBaseC p).symm (((Iprod k).symm).toFun x).1
        ∈ coverBaseSet E.e (discPiece q) := by
      rw [← hproj]; exact hsrcf.1
    have hk2 : (chartBaseC p).symm (((Iprod k).symm).toFun x).1 ∈ (chartBaseC q).source := by
      rw [← hproj]; exact hsrcf.2.1
    have hk3 : frameChangeE C (discPiece p) (discPiece q)
        ((chartBaseC p).symm (((Iprod k).symm).toFun x).1)
        (((chartFibC C p).symm (((Iprod k).symm).toFun x).2).val) ∈
          DiscManifold.ballChartAmb (k - 1) (chartFibPt C q) := by
      have hbveq : ballVecI C (discPiece q) (chartInvFun C p (((Iprod k).symm).toFun x)) =
          frameChangeE C (discPiece p) (discPiece q)
            ((chartBaseC p).symm (((Iprod k).symm).toFun x).1)
            (((chartFibC C p).symm (((Iprod k).symm).toFun x).2).val) := by
        simp only [ballVecI]
        rw [hproj, hvec]
        rw [readFE_insFE' C (discPiece p) (discPiece q)
          ((chartBaseC p).symm (((Iprod k).symm).toFun x).1)
          (ε • ((chartFibC C p).symm (((Iprod k).symm).toFun x).2).val), map_smul,
          inv_smul_smul₀ (ne_of_gt C.eps_pos)]
      rw [← hbveq]
      exact hsrcf.2.2
    rw [hz1 x] at h1' h2' hk1 hk2 hk3
    rw [hz2 x] at h3' hk3
    exact ⟨h1', h2', hk2, hk1, h3', hk3, hrange x hr⟩
  have hA : ContDiffOn ℝ 1 (fun x : Euc 8 × Euc ((k - 1) + 1) =>
      (chartBaseC q) ((chartBaseC p).symm x.1)) D := by
    have h0 := chartBaseTransition V (NormalTotal.proj p.1) (NormalTotal.proj q.1)
    have hfst : ContDiffOn ℝ 1 (fun x : Euc 8 × Euc ((k - 1) + 1) => x.1) D :=
      contDiff_fst.contDiffOn
    have hmaps : Set.MapsTo (fun x : Euc 8 × Euc ((k - 1) + 1) => x.1) D
        ((chartAt (Euc 8) (NormalTotal.proj p.1)).target ∩
          (chartAt (Euc 8) (NormalTotal.proj p.1)).symm ⁻¹'
            (chartAt (Euc 8) (NormalTotal.proj q.1)).source) := by
      intro x hx
      obtain ⟨-, h2, h3, -, -, -, -⟩ := hdom x hx
      exact ⟨h2, h3⟩
    have hcomp : ContDiffOn ℝ 1 ((fun y : Euc 8 =>
          (chartAt (Euc 8) (NormalTotal.proj q.1))
            ((chartAt (Euc 8) (NormalTotal.proj p.1)).symm y)) ∘
        (fun x : Euc 8 × Euc ((k - 1) + 1) => x.1)) D :=
      h0.comp hfst hmaps
    exact hcomp.congr (fun x _ => rfl)
  have hB : ContDiffOn ℝ 1 (fun x : Euc 8 × Euc ((k - 1) + 1) =>
      ((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val) D := by
    have h0 := DiscManifold.contDiffOn_ballChartAt_symm (k - 1) (chartFibPt C p)
    have hsnd : ContDiffOn ℝ 1 (fun x : Euc 8 × Euc ((k - 1) + 1) => x.2) D :=
      contDiff_snd.contDiffOn
    have hmaps : Set.MapsTo (fun x : Euc 8 × Euc ((k - 1) + 1) => x.2) D
        {w : Euc ((k - 1) + 1) | 0 ≤ w 0 ∧
          (hModel (k - 1)).symm w ∈ (chartAt (Half (k - 1)) (chartFibPt C p)).target} := by
      intro x hx
      obtain ⟨-, -, -, -, h5, -, h7⟩ := hdom x hx
      exact ⟨h7, h5⟩
    have hcomp : ContDiffOn ℝ 1 ((fun w : Euc ((k - 1) + 1) =>
          (((chartAt (Half (k - 1)) (chartFibPt C p)).symm ((hModel (k - 1)).symm w) :
            Ball (k - 1))).val) ∘ (fun x : Euc 8 × Euc ((k - 1) + 1) => x.2)) D :=
      h0.comp hsnd hmaps
    exact hcomp.congr (fun x _ => rfl)
  have hHB : ContDiffOn ℝ 1 (fun x : Euc 8 × Euc ((k - 1) + 1) =>
      ((chartFibC C q) (discPt (k - 1) (frameChangeE C (discPiece p) (discPiece q)
        ((chartBaseC p).symm x.1) (((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val)))).val)
      D := by
    have hH := frameChangeDiscPt C (discPiece p) (discPiece q) (NormalTotal.proj p.1)
      (chartFibPt C q)
    have hu : ContDiffOn ℝ 1 (fun x : Euc 8 × Euc ((k - 1) + 1) =>
        (x.1, ((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val)) D :=
      (contDiff_fst.contDiffOn).prodMk hB
    have hmaps : Set.MapsTo (fun x : Euc 8 × Euc ((k - 1) + 1) =>
        (x.1, ((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val)) D
        {u : Euc 8 × Euc ((k - 1) + 1) |
          u.1 ∈ chartCover E (discPiece p) (NormalTotal.proj p.1) ∧
          u.1 ∈ chartCover E (discPiece q) (NormalTotal.proj p.1) ∧
          ‖u.2‖ ≤ 1 ∧
          frameChangeE C (discPiece p) (discPiece q)
            ((chartAt (Euc 8) (NormalTotal.proj p.1)).symm u.1) u.2 ∈
              DiscManifold.ballChartAmb (k - 1) (chartFibPt C q)} := by
      intro x hx
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hdom x hx
      have hbz : ((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val ∈ Ball (k - 1) :=
        ((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).2
      refine ⟨⟨h2, h1⟩, ⟨h2, h4⟩, ?_, h6⟩
      show ‖(((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val)‖ ≤ 1
      rw [Metric.mem_closedBall, dist_zero_right] at hbz
      exact hbz
    have hcomp : ContDiffOn ℝ 1 ((fun u : Euc 8 × Euc ((k - 1) + 1) =>
          ((chartAt (Half (k - 1)) (chartFibPt C q))
            (discPt (k - 1) (frameChangeE C (discPiece p) (discPiece q)
              ((chartAt (Euc 8) (NormalTotal.proj p.1)).symm u.1) u.2))).val) ∘
        (fun x : Euc 8 × Euc ((k - 1) + 1) =>
          (x.1, ((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val))) D :=
      hH.comp hu hmaps
    exact hcomp.congr (fun x _ => rfl)
  have hmain : ContDiffOn ℝ 1 (fun x : Euc 8 × Euc ((k - 1) + 1) =>
      ((chartBaseC q) ((chartBaseC p).symm x.1),
       ((chartFibC C q) (discPt (k - 1) (frameChangeE C (discPiece p) (discPiece q)
          ((chartBaseC p).symm x.1) (((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val)))).val))
      D := hA.prodMk hHB
  refine hmain.congr fun x hx => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hdom x hx
  have hsymm : (((Iprod k).symm).toFun x) = (x.1, ⟨x.2, h7⟩) := by
    rw [modelWithCorners_prod_coe_symm, Prod.map_apply]
    rw [show (𝓡 8).symm x.1 = x.1 from rfl]
    rw [halfModel_symm_apply_of_le (k - 1) h7]
  rw [Function.comp_apply, Function.comp_apply, hsymm]
  have hcond : chartInvCond C p (x.1, ⟨x.2, h7⟩) := by
    refine ⟨?_, ?_⟩
    · show (chartBaseC p).symm x.1 ∈ coverBaseSet E.e (discPiece p); exact h1
    · show (⟨x.2, h7⟩ : Half (k - 1)) ∈ (chartFibC C p).target
      rw [← halfModel_symm_apply_of_le (k - 1) h7]; exact h5
  refine Prod.ext ?_ ?_
  · show ((𝓡 8) ((chartBaseC q) (NormalTotal.proj
        (chartInvFun C p (x.1, ⟨x.2, h7⟩)).1))) = (chartBaseC q) ((chartBaseC p).symm x.1)
    rw [chartInvFun, dif_pos hcond]
    rfl
  · show ((hModel (k - 1)) ((chartFibC C q) (discPt (k - 1)
        (ballVecI C (discPiece q) (chartInvFun C p (x.1, ⟨x.2, h7⟩)))))) =
      ((chartFibC C q) (discPt (k - 1) (frameChangeE C (discPiece p) (discPiece q)
        ((chartBaseC p).symm x.1) (((chartFibC C p).symm ((hModel (k - 1)).symm x.2)).val)))).val
    rw [chartInvFun, dif_pos hcond]
    simp only [ballVecI, NormalTotal.proj, NormalTotal.vec, Subtype.coe_mk,
      modelWithCornersEuclideanHalfSpace_apply]
    congr 2
    rw [readFE_insFE' C (discPiece p) (discPiece q) ((chartBaseC p).symm x.1)
      (ε • ((chartFibC C p).symm (⟨x.2, h7⟩)).val), map_smul,
      inv_smul_smul₀ (ne_of_gt C.eps_pos)]
    rw [← halfModel_symm_apply_of_le (k - 1) h7]

end

end Work.Tubular
