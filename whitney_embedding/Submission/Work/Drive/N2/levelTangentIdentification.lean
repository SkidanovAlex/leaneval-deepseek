import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.regularLevelCircles

/-!
# The tangent space of a regular level set is the kernel of the differential

Let `M` be a smooth surface (a `2`-manifold modelled on `ℝ²`) and `f : M → ℝ` a smooth function for
which `b` is a regular value (`Work.Drive.N2.LevelHyp f b`).  The level set `LevelSet f b` is
equipped with a smooth structure in `Submission/Work/Drive/N2/regularLevelCircles.lean` (it is a
`1`-dimensional manifold); write `ι : LevelSet f b → M` for the inclusion.

This file proves the identification of the tangent space of the level set with the kernel of the
differential of `f`:

  `Set.range (mfderiv ι p) = {v | mfderiv f (p : M) v = 0}`.

The inclusion `⊆` is the chain rule applied to the constant function `f ∘ ι = b`.  For the reverse
inclusion we use that the model space `E1` of the level set is one-dimensional and that the kernel
of `mfderiv f (p : M)` is one-dimensional as well (`b` is a regular value, so the differential does
not vanish and the target `ℝ` is one-dimensional); it therefore suffices to see that `mfderiv ι p`
does not vanish.  Nonvanishing is proved through the local parametrisation
`w ↦ levelParam f b p (stdE1.symm w)` of the level set: the ambient chart coordinate
`coordOf f b p` is a left inverse of that parametrisation, so the derivative of the parametrisation
at the chart point of `p` is injective, hence (the domain being one-dimensional) nonzero; the chain
rule along the level set chart then transfers this to `mfderiv ι p`.

The helper lemmas below isolate the analytic input (nonvanishing of `mfderiv ι p`) and the linear
algebra (range versus kernel) so that the main statement is a short assembly.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- The ambient chart coordinate `coordOf f b p` is smooth at the base point `p`. -/
lemma levelTangent_coordOf_mdiff (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (coordOf f b p) (p : M) := by
  have h1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2) ∞ (chartAt E2 (p : M)) (p : M) :=
    (contMDiffOn_chart (I := 𝓡 2) (x := (p : M))).contMDiffAt
      ((chartAt E2 (p : M)).open_source.mem_nhds (mem_chart_source E2 (p : M)))
  have h2 : ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) ∞ (levelCoordProj (mainModel f b p).i)
      ((chartAt E2 (p : M)) (p : M)) := (levelCoordProj _).contMDiffAt
  exact (ContMDiffAt.comp (x := (p : M)) h2 h1).mdifferentiableAt (by simp)

/-- The local parametrisation of the level set through `p`, read in the ambient manifold, is
differentiable at the chart point of `p`. -/
lemma levelTangent_Phi_mdiff (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    MDifferentiableAt 𝓘(ℝ, E1) (𝓡 2)
      (fun w : E1 => levelParam f b p (stdE1.symm w)) (levelChart f b p p) := by
  have hs : coordOf f b p (p : M) ∈ (mainModel f b p).T :=
    coordOf_mem_T f b p (mem_chart_source E2 (p : M)) (mem_chart_source E1 p).2 p.2
  have h1 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (levelParam f b p)
      (stdE1.symm (levelChart f b p p)) := by
    have hT : (mainModel f b p).T ∈ 𝓝 (coordOf f b p (p : M)) :=
      (mainModel f b p).isOpen_T.mem_nhds hs
    rw [show stdE1.symm (levelChart f b p p) = coordOf f b p (p : M) from by
      rw [levelChart_apply, stdE1.symm_apply_apply]]
    exact (levelParam_contMDiffOn f b p).contMDiffAt hT
  have h2 : ContMDiffAt 𝓘(ℝ, E1) 𝓘(ℝ, ℝ) ∞ (⇑stdE1.symm) (levelChart f b p p) := by
    have := ((stdE1.symm : E1 →L[ℝ] ℝ)).contMDiffAt (n := ∞) (x := levelChart f b p p)
    simpa using this
  exact (ContMDiffAt.comp (x := levelChart f b p p) h1 h2).mdifferentiableAt (by simp)

/-- Composing the ambient chart coordinate with the local parametrisation gives back the model
coordinate, near the chart point of `p`. -/
lemma levelTangent_coordOf_Phi_eventuallyEq (f : M → ℝ) (b : ℝ) [LevelHyp f b]
    (p : LevelSet f b) :
    ((coordOf f b p) ∘ (fun w : E1 => levelParam f b p (stdE1.symm w)))
      =ᶠ[𝓝 (levelChart f b p p)] ⇑(stdE1.symm : E1 →L[ℝ] ℝ) := by
  filter_upwards [(levelChart f b p).open_target.mem_nhds
    ((levelChart f b p).map_source (mem_chart_source E1 p))] with w hw
  have hwT : stdE1.symm w ∈ (mainModel f b p).T := by
    rw [levelChart_target, levelTarget] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    simpa using hs
  exact coordOf_levelParam f b p hwT

/-- **The local parametrisation of the level set is nondegenerate at the chart point of `p`**: its
derivative there does not vanish.  (A left inverse is given by `coordOf f b p`, so the derivative
is injective, and the domain `E1` is nontrivial.) -/
lemma levelTangent_Phi_ne_zero (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    (mfderiv 𝓘(ℝ, E1) (𝓡 2) (fun w : E1 => levelParam f b p (stdE1.symm w))
      (levelChart f b p p) : E1 →L[ℝ] E2) ≠ 0 := by
  have hΦw : (fun w : E1 => levelParam f b p (stdE1.symm w)) (levelChart f b p p) = (p : M) := by
    show levelParam f b p (stdE1.symm (levelChart f b p p)) = (p : M)
    rw [levelChart_apply, stdE1.symm_apply_apply]
    exact levelParam_coordOf f b p (mem_chart_source E2 (p:M)) (mem_chart_source E1 p).2 p.2
  have hcmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (coordOf f b p)
      ((fun w : E1 => levelParam f b p (stdE1.symm w)) (levelChart f b p p)) :=
    hΦw.symm ▸ levelTangent_coordOf_mdiff f b p
  have hcomp := mfderiv_comp (I := 𝓘(ℝ,E1)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℝ))
    (f := fun w : E1 => levelParam f b p (stdE1.symm w)) (g := coordOf f b p)
    (x := levelChart f b p p) hcmd (levelTangent_Phi_mdiff f b p)
  have hstd : mfderiv 𝓘(ℝ,E1) 𝓘(ℝ,ℝ) (⇑(stdE1.symm : E1 →L[ℝ]ℝ)) (levelChart f b p p)
      = (stdE1.symm : E1 →L[ℝ]ℝ) := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  have hm : mfderiv 𝓘(ℝ,E1) 𝓘(ℝ,ℝ)
      ((coordOf f b p) ∘ (fun w : E1 => levelParam f b p (stdE1.symm w))) (levelChart f b p p)
      = (stdE1.symm : E1 →L[ℝ]ℝ) :=
    (levelTangent_coordOf_Phi_eventuallyEq f b p).mfderiv_eq.trans hstd
  have key : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) (coordOf f b p)
        (levelParam f b p (stdE1.symm (levelChart f b p p)))).comp
      (mfderiv 𝓘(ℝ,E1) (𝓡 2) (fun w : E1 => levelParam f b p (stdE1.symm w))
        (levelChart f b p p))
      = (stdE1.symm : E1 →L[ℝ]ℝ) := hcomp.symm.trans hm
  have hstdne : (stdE1.symm : E1 →L[ℝ]ℝ) ≠ 0 := by
    intro h0
    have h1 : (stdE1.symm : E1 →L[ℝ]ℝ) (stdE1 1) = (0 : E1 →L[ℝ]ℝ) (stdE1 1) :=
      congrArg (fun g : E1 →L[ℝ]ℝ => g (stdE1 1)) h0
    have h2 : (stdE1.symm : E1 →L[ℝ]ℝ) (stdE1 1) = 0 := by simpa using h1
    have h3 : (1:ℝ) = 0 := by simpa using h2
    exact one_ne_zero h3
  intro hz
  refine hstdne (key.symm.trans ?_)
  have h := congrArg (fun g : E1 →L[ℝ] E2 =>
    (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) (coordOf f b p)
      (levelParam f b p (stdE1.symm (levelChart f b p p)))).comp g) hz
  exact h.trans (ContinuousLinearMap.comp_zero _)

/-- The inverse of the level set chart at `p` is differentiable at the chart point of `p`. -/
lemma levelTangent_symm_mdiff (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    MDifferentiableAt 𝓘(ℝ, E1) (𝓡 1) (⇑(levelChart f b p).symm) (levelChart f b p p) := by
  have h := contMDiffOn_chart_symm (I := (𝓡 1)) (x := p) (n := ∞)
  have hmem : levelChart f b p p ∈ (chartAt E1 p).target := by
    rw [show chartAt E1 p = levelChart f b p from rfl]
    exact (levelChart f b p).map_source (mem_chart_source E1 p)
  have h' := h.contMDiffAt (by
    rw [show (chartAt E1 p).target = (levelChart f b p).target from rfl]
    exact (levelChart f b p).open_target.mem_nhds hmem)
  exact h'.mdifferentiableAt (by simp)

/-- The inverse of the level set chart at `p` sends the chart point of `p` back to `p`. -/
lemma levelTangent_symm_self (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    (⇑(levelChart f b p).symm) (levelChart f b p p) = p :=
  OpenPartialHomeomorph.left_inv _ (mem_chart_source E1 p)

/-- The local parametrisation of the level set factors through the inclusion and the inverse of the
level set chart, near the chart point of `p`. -/
lemma levelTangent_Phi_eventuallyEq (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    (fun w : E1 => levelParam f b p (stdE1.symm w))
      =ᶠ[𝓝 (levelChart f b p p)]
        ((Subtype.val : LevelSet f b → M) ∘ ⇑(levelChart f b p).symm) := by
  filter_upwards [(levelChart f b p).open_target.mem_nhds
    ((levelChart f b p).map_source (mem_chart_source E1 p))] with w hw
  rw [Function.comp_apply, show (⇑(levelChart f b p).symm) w = levelInv f b p w from rfl,
    levelInv_coe_of_mem f b p hw]

/-- **The chain rule along the level set chart**: the derivative of the local parametrisation at the
chart point of `p` is the derivative of the inclusion composed with the derivative of the inverse
level set chart. -/
lemma levelTangent_Phi_eq_comp (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    (mfderiv 𝓘(ℝ, E1) (𝓡 2) (fun w : E1 => levelParam f b p (stdE1.symm w))
        (levelChart f b p p) : E1 →L[ℝ] E2)
      = ((mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M) p : E1 →L[ℝ] E2).comp
        (mfderiv 𝓘(ℝ, E1) (𝓡 1) (⇑(levelChart f b p).symm) (levelChart f b p p)
          : E1 →L[ℝ] E1)) := by
  have hsub_md : MDifferentiableAt (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M) p :=
    (subtypeVal_contMDiff f b).contMDiffAt.mdifferentiableAt (by simp)
  have hsub_md' : MDifferentiableAt (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M)
      ((⇑(levelChart f b p).symm) (levelChart f b p p)) :=
    (levelTangent_symm_self f b p).symm ▸ hsub_md
  have hcomp := mfderiv_comp (I := 𝓘(ℝ,E1)) (I' := 𝓡 1) (I'' := 𝓡 2)
    (f := ⇑(levelChart f b p).symm) (g := (Subtype.val : LevelSet f b → M))
    (x := levelChart f b p p) hsub_md' (levelTangent_symm_mdiff f b p)
  have hpoint : (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M)
        ((⇑(levelChart f b p).symm) (levelChart f b p p)) : E1 →L[ℝ] E2)
      = (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M) p : E1 →L[ℝ] E2) := by
    rw [levelTangent_symm_self f b p]
  have h1 : (mfderiv 𝓘(ℝ,E1) (𝓡 2) (fun w : E1 => levelParam f b p (stdE1.symm w))
      (levelChart f b p p) : E1 →L[ℝ] E2)
      = ((mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M)
          ((⇑(levelChart f b p).symm) (levelChart f b p p)) : E1 →L[ℝ] E2).comp
        (mfderiv 𝓘(ℝ, E1) (𝓡 1) (⇑(levelChart f b p).symm) (levelChart f b p p)
          : E1 →L[ℝ] E1)) :=
    (levelTangent_Phi_eventuallyEq f b p).mfderiv_eq.trans hcomp
  rw [hpoint] at h1
  exact h1

/-- **The inclusion of a regular level set is an immersion**: its derivative at every point of the
level set does not vanish.  (The model space of the level set is one-dimensional, so this is
equivalent to injectivity of the derivative.) -/
lemma levelTangent_subtypeVal_ne_zero (f : M → ℝ) (b : ℝ) [LevelHyp f b] (p : LevelSet f b) :
    (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M) p : E1 →L[ℝ] E2) ≠ 0 := by
  set M' : E1 →L[ℝ] E2 := mfderiv 𝓘(ℝ, E1) (𝓡 2)
    (fun w : E1 => levelParam f b p (stdE1.symm w)) (levelChart f b p p) with hM'
  set X : E1 →L[ℝ] E1 := mfderiv 𝓘(ℝ, E1) (𝓡 1)
    (⇑(levelChart f b p).symm) (levelChart f b p p) with hX
  set d : E1 →L[ℝ] E2 := mfderiv (𝓡 1) (𝓡 2)
    (Subtype.val : LevelSet f b → M) p with hd
  have hM_ne : M' ≠ 0 := by
    rw [hM']
    exact levelTangent_Phi_ne_zero f b p
  have hchain : M' = d.comp X := by
    rw [hM', hX, hd]
    exact levelTangent_Phi_eq_comp f b p
  intro hd0
  refine hM_ne ?_
  rw [hchain, hd0]
  exact ContinuousLinearMap.zero_comp X

/-- Abstract linear algebra: if `E1` is one-dimensional and `g : E2 →ₗ ℝ` is a nonvanishing
functional on the two-dimensional space `E2`, then the range of a nonvanishing map `d : E1 →ₗ E2`
whose range lies in the kernel of `g` is exactly that kernel. -/
lemma levelTangent_range_eq_ker (d : E1 →ₗ[ℝ] E2) (g : E2 →ₗ[ℝ] ℝ) (hd : d ≠ 0) (hg : g ≠ 0)
    (hle : d.range ≤ g.ker) : d.range = g.ker := by
  have hE1 : Module.finrank ℝ E1 = 1 := by rw [finrank_euclideanSpace]; simp
  have hE2 : Module.finrank ℝ E2 = 2 := by rw [finrank_euclideanSpace]; simp
  have hfin_range : Module.finrank ℝ d.range = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker d
    have hker : Module.finrank ℝ d.ker = 0 := by
      have hle1 : Module.finrank ℝ d.ker ≤ 1 := by
        have hmono := Submodule.finrank_mono (le_top : d.ker ≤ ⊤)
        rwa [finrank_top, hE1] at hmono
      have hne1 : Module.finrank ℝ d.ker ≠ 1 := by
        intro hc
        have htop : d.ker = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hc, hE1])
        exact hd (LinearMap.ker_eq_top.mp htop)
      omega
    omega
  have hfin_ker : Module.finrank ℝ g.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker g
    have hfr : Module.finrank ℝ g.range = 1 := by
      have hle1 : Module.finrank ℝ g.range ≤ 1 := by
        have hmono := Submodule.finrank_mono (le_top : g.range ≤ ⊤)
        rwa [finrank_top, Module.finrank_self] at hmono
      have hne0 : Module.finrank ℝ g.range ≠ 0 := by
        intro hc
        exact hg (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hc))
      omega
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin_range, hfin_ker])

end

open scoped Manifold ContDiff in
theorem levelTangentIdentification {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (b : ℝ) [Work.Drive.N2.LevelHyp f b]
    (p : Work.Drive.N2.LevelSet f b) :
    Set.range (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : Work.Drive.N2.LevelSet f b → M) p) =
      {v : TangentSpace (𝓡 2) ((p : M)) |
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (p : M) v = 0} := by
  set d : E1 →L[ℝ] E2 := mfderiv (𝓡 1) (𝓡 2)
    (Subtype.val : LevelSet f b → M) p with hd
  set g : E2 →L[ℝ] ℝ := mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (p : M) with hg
  -- the range is contained in the kernel of the differential
  have hle : d.range ≤ g.ker := by
    intro v hv
    rw [LinearMap.mem_ker]
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
    have hsub_md : MDifferentiableAt (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M) p :=
      (subtypeVal_contMDiff f b).contMDiffAt.mdifferentiableAt (by simp)
    have hmdf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (p : M) :=
      hf.contMDiffAt.mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_apply (I := 𝓡 1) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
      (f := (Subtype.val : LevelSet f b → M)) (g := f) (x := p) hmdf hsub_md w
    have hconst : (f ∘ (Subtype.val : LevelSet f b → M)) = fun _ => b := funext fun z => z.2
    rw [hconst, mfderiv_const] at hcomp
    have hraw : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (p : M))
        ((mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f b → M) p) w) = 0 := hcomp.symm
    rw [hd, hg]
    exact hraw
  -- the two sides have the same dimension, hence they agree
  have hd_ne : d ≠ 0 := by
    rw [hd]
    exact levelTangent_subtypeVal_ne_zero f b p
  have hg_ne : g ≠ 0 := by
    rw [hg]
    exact fun h0 => (‹Work.Drive.N2.LevelHyp f b›).regular (p : M) p.2 h0
  have hfin : d.range = g.ker := by
    have hd' : (d : E1 →ₗ[ℝ] E2) ≠ 0 := by
      intro h0
      exact hd_ne (ContinuousLinearMap.ext fun x =>
        congrArg (fun L : E1 →ₗ[ℝ] E2 => L x) h0)
    have hg' : (g : E2 →ₗ[ℝ] ℝ) ≠ 0 := by
      intro h0
      exact hg_ne (ContinuousLinearMap.ext fun x =>
        congrArg (fun L : E2 →ₗ[ℝ] ℝ => L x) h0)
    exact levelTangent_range_eq_ker (d : E1 →ₗ[ℝ] E2) (g : E2 →ₗ[ℝ] ℝ) hd' hg' hle
  change (d.range : Set E2) = (g.ker : Set E2)
  rw [hfin]

end Work.Drive.N2
