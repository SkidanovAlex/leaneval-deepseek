import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.smoothChartOfInjOnImmersion
import Submission.Work.Drive.PushDisc.sheetChartOfFlatTube
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff Topology
open Set Filter

/-- **The first-arc chart inside the flat tube.**

`T.U₁` is an open flat tube of the first sheet on which `f` is injective; the map
`g z = splitE k ((Φ₀ (f z)).1, (Φ₀ (f z)).2.2.1)` is a smooth injective immersion on `U₁`
(the `(x,u)`-coordinates of `Φ₀ ∘ f`, the `sheetA`-coordinates), hence a smooth chart there by the
inverse function theorem.  Its source is `U₁`, which contains the first arc and the two points
`p₁ = γ₁ 0` and `q₁ = γ₁ 1`, and on it `Φ₀ (f x) ∈ sheetA` — the shadow row of `LWFirstArcChart`. -/
theorem flatArcChartSolid {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C) :
    Nonempty (Work.Drive.PushDisc.LWFirstArcChart k M C T) := by
  classical
  have hne : hInf ≠ 0 := by decide
  -- ## the two endpoints of the first arc lie in the tube `U₁`
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hp₁U₁ : C.p₁ ∈ T.U₁ := by
    have h : C.γ₁ 0 ∈ T.U₁ := T.hU₁arc ⟨0, h0, rfl⟩
    rwa [C.hγ₁0] at h
  have hq₁U₁ : C.q₁ ∈ T.U₁ := by
    have h : C.γ₁ 1 ∈ T.U₁ := T.hU₁arc ⟨1, h1, rfl⟩
    rwa [C.hγ₁1] at h
  have hU₁ne : T.U₁.Nonempty := ⟨C.p₁, hp₁U₁⟩
  -- ## the chart map `g`: the `sheetA`-coordinates of `Φ₀ ∘ f`
  let g : M → ES (k + 1) :=
    fun z => splitE k ((T.Φ₀ (C.f z)).1, (T.Φ₀ (C.f z)).2.2.1)
  have hgsm : ContMDiff (MWC (k + 1)) (MWC (k + 1)) hInf g := by
    have h1' : ContMDiff (MWC (k + 1))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) hInf
        (fun z : M => T.Φ₀ (C.f z)) := T.hΦ₀sm.contMDiff.comp C.hf
    have hc : ContDiff ℝ hInf (fun ξ : Work.Drive.Whitney.Mdl k =>
        ((ξ.1, ξ.2.2.1) : ℝ × ES k)) := by fun_prop
    have h3 : ContDiff ℝ hInf (fun ξ : Work.Drive.Whitney.Mdl k =>
        splitE k ((ξ.1, ξ.2.2.1))) :=
      (LinearEquiv.toContinuousLinearEquiv (splitE k)).contDiff.comp hc
    have h2' : ContMDiff (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
        (MWC (k + 1)) hInf (fun ξ : Work.Drive.Whitney.Mdl k =>
          splitE k ((ξ.1, ξ.2.2.1))) := h3.contMDiff
    exact h2'.comp h1'
  -- ## injectivity of `f` on the flat tube
  have hinjf : Set.InjOn C.f T.U₁ := by
    intro y hy z hz hyz
    rcases C.hclean y z (T.hU₁W hy) (T.hU₁W hz) hyz with h | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ |
      ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact h
    · exact absurd (h2' ▸ hz) T.hp₂U₁
    · exact absurd (h1' ▸ hy) T.hp₂U₁
    · exact absurd (h2' ▸ hz) T.hq₂U₁
    · exact absurd (h1' ▸ hy) T.hq₂U₁
  -- ## the linear embedding of the model plane `sheetA` and the recovery of `Φ₀ ∘ f` from `g`
  let Slin : ES (k + 1) →L[ℝ] (ℝ × ES k) :=
    ((LinearEquiv.toContinuousLinearEquiv (splitE k)).symm : ES (k + 1) →L[ℝ] (ℝ × ES k))
  let pr1 : ES (k + 1) →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ (ES k)).comp Slin
  let pr2 : ES (k + 1) →L[ℝ] ES k := (ContinuousLinearMap.snd ℝ ℝ (ES k)).comp Slin
  let Bemb : ES (k + 1) →L[ℝ] Work.Drive.Whitney.Mdl k :=
    ContinuousLinearMap.prod pr1
      (ContinuousLinearMap.prod (0 : ES (k + 1) →L[ℝ] ℝ)
        (ContinuousLinearMap.prod pr2 (0 : ES (k + 1) →L[ℝ] ES k)))
  have hBemb : ∀ w : ES (k + 1),
      Bemb w = (((splitE k).symm w).1, (0 : ℝ), ((splitE k).symm w).2, (0 : ES k)) := by
    intro w
    simp [Bemb, pr1, pr2, Slin]
  have hBg : ∀ z : M, z ∈ T.U₁ → Bemb (g z) = T.Φ₀ (C.f z) := by
    intro z hz
    have hsymm : (splitE k).symm (g z)
        = ((T.Φ₀ (C.f z)).1, (T.Φ₀ (C.f z)).2.2.1) := by
      show (splitE k).symm (splitE k _) = _
      rw [LinearEquiv.symm_apply_apply]
    have hrow := T.hU₁row z hz
    simp only [Work.Drive.Whitney.sheetA, Set.mem_ofPred_eq] at hrow
    obtain ⟨hfy, hfv⟩ := hrow
    have hEq : ((T.Φ₀ (C.f z)).1, (0 : ℝ), (T.Φ₀ (C.f z)).2.2.1, (0 : ES k))
        = T.Φ₀ (C.f z) := by
      rw [← hfy, ← hfv]
    calc Bemb (g z)
        = (((splitE k).symm (g z)).1, (0 : ℝ), ((splitE k).symm (g z)).2,
            (0 : ES k)) := hBemb (g z)
      _ = ((T.Φ₀ (C.f z)).1, (0 : ℝ), (T.Φ₀ (C.f z)).2.2.1, (0 : ES k)) := by rw [hsymm]
      _ = T.Φ₀ (C.f z) := hEq
  have hΦ₀inj : Function.Injective T.Φ₀ := by
    intro a b hab
    have h := congrArg T.Θ₀ hab
    simpa only [T.hΘ₀Φ₀] using h
  have hinjg : Set.InjOn g T.U₁ := by
    intro x hx y hy hxy
    refine hinjf hx hy (hΦ₀inj ?_)
    rw [← hBg x hx, ← hBg y hy, hxy]
  -- ## `g` is an immersion on the flat tube
  have himmg : ∀ x : M, x ∈ T.U₁ →
      Function.Injective (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x) := by
    intro x hx
    let F : ES (k + 1) → ES (2 * (k + 1)) := fun w => T.Θ₀ (Bemb w)
    have hF : ContDiff ℝ hInf F := by
      have h := T.hΘ₀sm.comp (ContinuousLinearMap.contDiff Bemb : ContDiff ℝ hInf (⇑Bemb))
      simpa only [F, Function.comp_def] using h
    have hev : (fun z : M => F (g z)) =ᶠ[𝓝 x] C.f := by
      filter_upwards [T.hU₁o.mem_nhds hx] with z hz
      show T.Θ₀ (Bemb (g z)) = C.f z
      rw [hBg z hz, T.hΘ₀Φ₀]
    have hchain : mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) (fun z : M => F (g z)) x
        = (mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) F (g x)).comp
          (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x) :=
      mfderiv_comp x (hF.contMDiff.mdifferentiableAt hne) (hgsm.mdifferentiableAt hne)
    have hmf : mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) C.f x
        = (mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) F (g x)).comp
          (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x) := by
      rw [← hev.mfderiv_eq_v433]
      exact hchain
    exact injective_of_comp_injective (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x)
      (mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) F (g x)) (by rw [← hmf]; exact C.himm x)
  -- ## the chart
  obtain ⟨c, hcsrc, hceq, hcsmooth⟩ :=
    exists_smoothChart_of_injOn_immersion_of_nonempty_source g T.U₁ T.hU₁o hU₁ne
      hgsm hinjg himmg
  refine ⟨c, hcsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcsrc]
  · rw [hcsrc]; exact T.hU₁arc
  · rw [hcsrc]; exact hp₁U₁
  · rw [hcsrc]; exact hq₁U₁
  · intro x hx
    have hx' : x ∈ T.U₁ := by rwa [← hcsrc]
    have h := T.hU₁row x hx'
    simpa only [Work.Drive.Whitney.sheetA, Set.mem_ofPred_eq] using h

end Work.Drive.PushDisc
