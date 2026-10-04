import Mathlib
import Submission.Work.Diff.C.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField Filter

theorem mvfderiv_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : M → ℝ} {X : Π y : M, TangentSpace I y} {x : M}
    (hF : CMDiffAt ∞ F x) (hX : CMDiffAt ∞ (T% X) x) :
    CMDiffAt ∞ (fun y ↦ mvfderiv I F y (X y)) x := by
  -- `C^∞` at a point means `C^n` at that point for every `n`; we prove all the finite orders.
  rw [contMDiffAt_infty]
  intro N
  -- On a neighbourhood of `x`, `F` and `X` are `C^{N+1}`, hence so is everything below.
  have hN1 : IsManifold I (((N+1:ℕ)):ℕ∞ω) M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨u₁, hu₁, hF₁⟩ := (contMDiffAt_iff_contMDiffOn_nhds (n := ((N+1:ℕ):ℕ∞ω)) (by simp)).mp
    (hF.of_le (by simp))
  obtain ⟨u₂, hu₂, hX₁⟩ := (contMDiffAt_iff_contMDiffOn_nhds (n := ((N+1:ℕ):ℕ∞ω)) (by simp)).mp
    (hX.of_le (by simp))
  obtain ⟨v, hvsub, hvopen, hxv⟩ := mem_nhds_iff.mp (Filter.inter_mem hu₁ hu₂)
  have hFv : CMDiff[v] (((N+1:ℕ)):ℕ∞ω) F := hF₁.mono (hvsub.trans inter_subset_left)
  have hXv : CMDiff[v] (((N+1:ℕ)):ℕ∞ω) (T% X) := hX₁.mono (hvsub.trans inter_subset_right)
  -- `F` is differentiable at every point of the open set `v`.
  have hmdiff : ∀ p : TangentBundle I M, p.proj ∈ v → MDiffAt F p.proj := by
    intro p hpv
    exact (ContMDiffWithinAt.contMDiffAt (hFv p.proj hpv)
      (hvopen.mem_nhds hpv)).mdifferentiableAt (by simp)
  -- The bundled derivative of `F` is `C^N` near `x`, first as a map within `v` ...
  have hV : CMDiff[(Bundle.TotalSpace.proj ⁻¹' v : Set (TangentBundle I M))] (N:ℕ∞ω)
      (tangentMap[v] F) :=
    hFv.contMDiffOn_tangentMapWithin (m := (N:ℕ∞ω)) (by simp) hvopen.uniqueMDiffOn
  -- ... and then, on `π ⁻¹' v`, the derivative within `v` is the unrestricted derivative.
  have hV' : CMDiff[(Bundle.TotalSpace.proj ⁻¹' v : Set (TangentBundle I M))] (N:ℕ∞ω)
      (tangentMap% F) :=
    hV.congr (f₁ := tangentMap% F) (fun p hp =>
      (tangentMapWithin_eq_tangentMap (hvopen.uniqueMDiffWithinAt hp) (hmdiff p hp)).symm)
  have hXv' : CMDiff[v] (N:ℕ∞ω) (T% X) := hXv.of_le (by simp)
  have hcomp : CMDiff[v] (N:ℕ∞ω) (fun y => tangentMap% F (T% X y)) :=
    hV'.comp hXv' (fun y hy => by simpa using hy)
  -- Projecting to the second component of the (trivial) tangent bundle of `ℝ` gives the value.
  have hsnd := (contMDiff_snd_tangentBundle_modelSpace ℝ (𝓘(ℝ,ℝ)) (n := (N:ℕ∞ω))).contMDiffOn
    (s := Set.univ)
  have hres : CMDiff[v] (N:ℕ∞ω)
      ((fun p : TangentBundle (𝓘(ℝ,ℝ)) ℝ => (p.2 : ℝ)) ∘ (fun y => tangentMap% F (T% X y))) :=
    hsnd.comp hcomp (fun y hy => Set.mem_univ _)
  have hfinal : CMDiff[v] (N:ℕ∞ω) (fun y => mvfderiv I F y (X y)) :=
    hres.congr (fun y hy => by
      simp only [mvfderiv, tangentMap]; rfl)
  exact hfinal.contMDiffAt (hvopen.mem_nhds hxv)

end Work.Diff.C
