import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField Filter

namespace Work.Diff.EXT

/-- **Spatial derivative of a smooth function along a section smooth at a point, general target.**
The "at a point" form of the already-proved global statement
`Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff`
(module `Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff`, importable in
this workspace), and the `F`-valued generalisation of the already-proved
`Work.Diff.C.mvfderiv_contMDiffAt` (module `Submission.Work.Diff.C.mvfderiv_contMDiffAt`, the
`F = ℝ` case), whose proof is the template: `contMDiffAt_infty`, restriction to an open
neighbourhood on which `f` and `X` are `C^N` for the relevant finite `N`, smoothness of the bundled
derivative `tangentMap% f` on that neighbourhood (`ContMDiffOn.contMDiffOn_tangentMapWithin` +
`tangentMapWithin_eq_tangentMap`), composition with the (smooth) total-space map of the section, and
finally the second projection `p ↦ p.2` of the trivial tangent bundle of the target model space,
which is smooth by `contMDiff_snd_tangentBundle_modelSpace F (modelWithCornersSelf ℝ F)`;
`simp only [mvfderiv, tangentMap]; rfl` closes the identification. -/
theorem contMDiffAt_mvfderiv_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {X : Π y : M, TangentSpace I y} {x : M}
    (hf : ContMDiffAt I (modelWithCornersSelf ℝ F) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f x)
    (hX : ContMDiffAt I I.tangent (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)) x) :
    ContMDiffAt I (modelWithCornersSelf ℝ F) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => mvfderiv I f y (X y)) x := by
  -- `C^∞` at a point means `C^n` at that point for every finite order `n`; prove all of them.
  rw [contMDiffAt_infty]
  intro N
  -- On a neighbourhood of `x`, `f` and `X` are `C^{N+1}`, hence so is everything below.
  obtain ⟨u₁, hu₁, hf₁⟩ := (contMDiffAt_iff_contMDiffOn_nhds
    (n := ((N+1:ℕ):ℕ∞ω)) (by simp)).mp (hf.of_le (by simp))
  obtain ⟨u₂, hu₂, hX₁⟩ := (contMDiffAt_iff_contMDiffOn_nhds
    (n := ((N+1:ℕ):ℕ∞ω)) (by simp)).mp (hX.of_le (by simp))
  obtain ⟨v, hvsub, hvopen, hxv⟩ := mem_nhds_iff.mp (Filter.inter_mem hu₁ hu₂)
  have hfv : ContMDiffOn I (modelWithCornersSelf ℝ F) (((N+1:ℕ)):ℕ∞ω) f v :=
    hf₁.mono (hvsub.trans inter_subset_left)
  have hXv : ContMDiffOn I I.tangent (((N+1:ℕ)):ℕ∞ω)
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)) v :=
    hX₁.mono (hvsub.trans inter_subset_right)
  -- `f` is differentiable at every point of the open set `v`.
  have hmdiff : ∀ p : TangentBundle I M, p.proj ∈ v → MDiffAt f p.proj := by
    intro p hpv
    exact (ContMDiffWithinAt.contMDiffAt (hfv p.proj hpv)
      (hvopen.mem_nhds hpv)).mdifferentiableAt (by simp)
  -- The bundled derivative of `f` is `C^N` near `x`, first as a map within `v` ...
  have hV : ContMDiffOn I.tangent (modelWithCornersSelf ℝ F).tangent (N:ℕ∞ω)
      (tangentMapWithin I (modelWithCornersSelf ℝ F) f v)
      (Bundle.TotalSpace.proj ⁻¹' (v : Set M)) :=
    hfv.contMDiffOn_tangentMapWithin (m := (N:ℕ∞ω)) (by simp) hvopen.uniqueMDiffOn
  -- ... and then, on `π ⁻¹' v`, the derivative within `v` is the unrestricted derivative.
  have hV' : ContMDiffOn I.tangent (modelWithCornersSelf ℝ F).tangent (N:ℕ∞ω)
      (tangentMap I (modelWithCornersSelf ℝ F) f)
      (Bundle.TotalSpace.proj ⁻¹' (v : Set M)) :=
    hV.congr (f₁ := tangentMap I (modelWithCornersSelf ℝ F) f) (fun p hp =>
      (tangentMapWithin_eq_tangentMap (hvopen.uniqueMDiffWithinAt hp) (hmdiff p hp)).symm)
  have hXv' : ContMDiffOn I I.tangent (N:ℕ∞ω)
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)) v := hXv.of_le (by simp)
  have hcomp : ContMDiffOn I (modelWithCornersSelf ℝ F).tangent (N:ℕ∞ω)
      (fun y => tangentMap I (modelWithCornersSelf ℝ F) f (⟨y, X y⟩ : TangentBundle I M)) v :=
    hV'.comp hXv' (fun y hy => by simpa using hy)
  -- Projecting to the second component of the (trivial) tangent bundle of `F` gives the value.
  have hsnd := (contMDiff_snd_tangentBundle_modelSpace F (modelWithCornersSelf ℝ F)
    (n := (N:ℕ∞ω))).contMDiffOn (s := Set.univ)
  have hres : ContMDiffOn I (modelWithCornersSelf ℝ F) (N:ℕ∞ω)
      ((fun p : TangentBundle (modelWithCornersSelf ℝ F) F => (p.2 : F)) ∘
        (fun y => tangentMap I (modelWithCornersSelf ℝ F) f
          (⟨y, X y⟩ : TangentBundle I M))) v :=
    hsnd.comp hcomp (fun y hy => Set.mem_univ _)
  have hfinal : ContMDiffOn I (modelWithCornersSelf ℝ F) (N:ℕ∞ω)
      (fun y => mvfderiv I f y (X y)) v :=
    hres.congr (fun y hy => by
      simp only [mvfderiv, tangentMap]
      rfl)
  exact hfinal.contMDiffAt (hvopen.mem_nhds hxv)

end Work.Diff.EXT
