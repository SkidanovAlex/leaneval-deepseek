import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.lensFramesWide
import Submission.Work.Drive.PushDisc.lensCornerSignOfChartsArc
import Submission.Work.Drive.PushDisc.lensNhd
import Submission.Work.Drive.PushDisc.lensTangentRows

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold
open Set Metric

noncomputable section

/-- **The chart `v`-frame of the finger agrees with `G.V` on the finger's arc.**  The frame
`G.V` is defined by the `v`-derivative of the global parametrisation `G.S₂`, while the corner-sign
lemma `lensCornerSignOfChartsArc` produces it as the `v`-derivative of the *chart* representation
`q ↦ Φ₀ (f (c.symm (splitE k q)))`; the two agree wherever the rows `hS₂ag`/`hS₂d` of the finger
data are available, i.e. on `[-F.X', F.X'] ⊇ [-1, 1]`. -/
theorem lensChartFrame_eq_V {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C)
    (F : Work.Drive.PushDisc.LWFingerChart k M C)
    (G : Work.Drive.PushDisc.LWFingerData k M C T F)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (fun j : Fin k => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
        T.Φ₀ (C.f (F.c.symm (Work.Drive.PushDisc.splitE k (x, w))))) 0
        (EuclideanSpace.single j (1 : ℝ))) = G.V x := by
  have hxabs : |x| ≤ F.X' := by
    have h1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    linarith [F.hX']
  have hsig : Work.Drive.Whitney.sigR x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.mem_Icc]
    constructor
    · simp only [Work.Drive.Whitney.sigR]; linarith [hx.1]
    · simp only [Work.Drive.Whitney.sigR]; linarith [hx.2]
  have hmem : C.γ₂ (Work.Drive.Whitney.sigR x) ∈ F.c.source :=
    F.hcarc ⟨Work.Drive.Whitney.sigR x, hsig, rfl⟩
  have hchart : F.c (C.γ₂ (Work.Drive.Whitney.sigR x))
      = Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) := by
    have h := F.harc₂ (Work.Drive.Whitney.sigR x) hsig
    have h2 : (2 : ℝ) * Work.Drive.Whitney.sigR x - 1 = x := by
      simp only [Work.Drive.Whitney.sigR]; ring
    rw [h2] at h
    exact h
  set chartRep : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k :=
    fun q => T.Φ₀ (C.f (F.c.symm (Work.Drive.PushDisc.splitE k q))) with hchartRepdef
  have hdchart : DifferentiableAt ℝ chartRep (x, 0) := by
    have h := (Work.Drive.PushDisc.chartSplit_hasFDerivAt C.hf T.Φ₀ T.hΦ₀sm F.c
      F.hcsmooth hmem).differentiableAt
    rw [hchart, LinearEquiv.symm_apply_apply] at h
    exact h
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdS2 : DifferentiableAt ℝ G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k))) :=
    (G.hS₂sm.differentiable hne) (x, 0)
  have hfdeq : fderiv ℝ G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k))) = fderiv ℝ chartRep (x, 0) :=
    G.hS₂d (x, (0 : EuclideanSpace ℝ (Fin k))) hxabs (by simpa using F.hr.le)
  funext j
  show (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => chartRep (x, w)) 0)
      (EuclideanSpace.single j (1 : ℝ)) = G.V x j
  rw [Work.Drive.PushDisc.lensFderivCompInr (F := chartRep) hdchart]
  rw [← hfdeq]
  rw [← Work.Drive.PushDisc.lensFderivCompInr (F := G.S₂) hdS2]
  rw [G.hVdef x (EuclideanSpace.single j (1 : ℝ)) hxabs]
  simp [PiLp.single_apply]

theorem lensFramesSolid {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C)
    (F : Work.Drive.PushDisc.LWFingerChart k M C)
    (G : Work.Drive.PushDisc.LWFingerData k M C T F)
    (D : Work.Drive.PushDisc.LWLensDisc k M C T F G)
    (c₁ : Work.Drive.PushDisc.LWFirstArcChart k M C T) :
    Nonempty (Work.Drive.PushDisc.LWFrames k M C T F G D) := by
  classical
  have hk : 2 ≤ k := by have h := C.hn; omega
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- the two partial derivative fields of the disc approximation
  set dx : ℝ × ℝ → Work.Drive.Whitney.Mdl k := fun p => fderiv ℝ D.Δ p (1, 0) with hdxdef
  set dy : ℝ × ℝ → Work.Drive.Whitney.Mdl k := fun p => fderiv ℝ D.Δ p (0, 1) with hdydef
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ D.Δ) :=
    D.hΔsm.fderiv_right le_rfl
  have hdx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dx := by
    rw [hdxdef]; exact hfd.clm_apply contDiff_const
  have hdy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dy := by
    rw [hdydef]; exact hfd.clm_apply contDiff_const
  have himm : ∀ p ∈ Work.Drive.PushDisc.lensK,
      LinearIndependent ℝ (Work.Drive.PushDisc.planeFrame k dx dy p) := by
    intro p hp
    have h2 : LinearIndependent ℝ
        (fun i : Fin 2 => (fderiv ℝ D.Δ p) ((Module.Basis.finTwoProd ℝ) i)) :=
      (Work.Drive.PushDisc.injective_iff_linearIndependent_finTwo
        ((fderiv ℝ D.Δ p).toLinearMap)).mp (D.hΔimm p hp)
    have hfe : (fun i : Fin 2 => (fderiv ℝ D.Δ p) ((Module.Basis.finTwoProd ℝ) i))
        = Work.Drive.PushDisc.planeFrame k dx dy p := by
      funext i
      fin_cases i <;> simp [Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
        Work.Drive.PushDisc.planeFrame, hdxdef, hdydef]
    rwa [hfe] at h2
  -- ## the corner sign, for the frame `G.V`
  have hp₂c₂ : C.p₂ ∈ F.c.source := by
    rw [← C.hγ₂0]
    exact F.hcarc ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
  have hq₂c₂ : C.q₂ ∈ F.c.source := by
    rw [← C.hγ₂1]
    exact F.hcarc ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩
  have hsign : ∃ Tl : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 + k + k)),
      0 < Work.Drive.PushDisc.frameDet (2 + k + k) Tl
            (Work.Drive.PushDisc.cornerFrame dx dy G.V (-1))
        * Work.Drive.PushDisc.frameDet (2 + k + k) Tl
            (Work.Drive.PushDisc.cornerFrame dx dy G.V 1) := by
    have hΔ1 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        D.Δ (x, Work.Drive.PushDisc.arch x)
          = T.Φ₀ (C.f (F.c.symm (Work.Drive.PushDisc.splitE k
              (x, (0 : EuclideanSpace ℝ (Fin k)))))) := by
      intro x hxI
      have hxabs : |x| ≤ F.X' := by
        have h1 : |x| ≤ 1 := abs_le.mpr ⟨hxI.1, hxI.2⟩
        linarith [F.hX']
      rw [D.hΔ1 x hxabs]
      exact G.hS₂ag (x, 0) hxabs (by simpa using F.hr.le)
    obtain ⟨Tl, hTl⟩ := Work.Drive.PushDisc.lensCornerSignOfChartsArc
      C.f C.hf C.himm T.Φ₀ T.Θ₀ T.hΦ₀sm T.hΘ₀sm T.hΘ₀Φ₀ T.hΦ₀Θ₀
      C.γ₁ C.γ₂ C.p₁ C.p₂ C.q₁ C.q₂ C.hγ₁ C.hγ₂ C.hγ₁0 C.hγ₁1 C.hγ₂0 C.hγ₂1
      C.hfp C.hfq C.hsign
      c₁.c₁ c₁.hc₁ c₁.hp₁c₁ c₁.hq₁c₁ (fun t ht => c₁.hc₁arc ⟨t, ht, rfl⟩) c₁.hsh₁
      F.c F.hcsmooth hp₂c₂ hq₂c₂ (fun t ht => F.hcarc ⟨t, ht, rfl⟩) F.harc₂
      D.Δ D.hΔ0 hΔ1 ((D.hΔsm.differentiable hne) (1, 0))
      ((D.hΔsm.differentiable hne) (-1, 0))
    refine ⟨Tl, ?_⟩
    have hfp1 : (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
        T.Φ₀ (C.f (F.c.symm (Work.Drive.PushDisc.splitE k (x, w))))) 0
        (EuclideanSpace.single j (1 : ℝ))) 1 = G.V 1 :=
      lensChartFrame_eq_V C T F G 1 ⟨by norm_num, by norm_num⟩
    have hfpm1 : (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
        T.Φ₀ (C.f (F.c.symm (Work.Drive.PushDisc.splitE k (x, w))))) 0
        (EuclideanSpace.single j (1 : ℝ))) (-1) = G.V (-1) :=
      lensChartFrame_eq_V C T F G (-1) ⟨by norm_num, by norm_num⟩
    have e1 : Work.Drive.PushDisc.cornerFrame dx dy (fun x j => fderiv ℝ
        (fun w : EuclideanSpace ℝ (Fin k) =>
          T.Φ₀ (C.f (F.c.symm (Work.Drive.PushDisc.splitE k (x, w))))) 0
        (EuclideanSpace.single j (1 : ℝ))) 1
        = Work.Drive.PushDisc.cornerFrame dx dy G.V 1 := by
      unfold Work.Drive.PushDisc.cornerFrame
      rw [hfp1]
    have em1 : Work.Drive.PushDisc.cornerFrame dx dy (fun x j => fderiv ℝ
        (fun w : EuclideanSpace ℝ (Fin k) =>
          T.Φ₀ (C.f (F.c.symm (Work.Drive.PushDisc.splitE k (x, w))))) 0
        (EuclideanSpace.single j (1 : ℝ))) (-1)
        = Work.Drive.PushDisc.cornerFrame dx dy G.V (-1) := by
      unfold Work.Drive.PushDisc.cornerFrame
      rw [hfpm1]
    rw [← e1, ← em1, mul_comm]
    exact hTl
  -- ## the wide frames
  obtain ⟨X', hX', U, W, hUsm, hWsm, hU0, hWtop, hframe⟩ :=
    Work.Drive.PushDisc.lensFramesWide hk dx dy hdx hdy himm G.V G.hVsm D.htop D.hbot hsign
  exact ⟨⟨X', hX', U, W, hUsm, hWsm, hU0, hWtop, hframe⟩⟩

end

end Work.Drive.PushDisc
