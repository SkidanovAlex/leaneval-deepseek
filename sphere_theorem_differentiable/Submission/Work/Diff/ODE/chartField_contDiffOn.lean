import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the coordinate expression of a jointly smooth time-dependent vector field

This file proves `Work.Diff.ODE.chartField_contDiffOn`: if `X` is a jointly smooth
time-dependent vector field on a `C^∞` manifold `M` (smooth as a section of the tangent
bundle, see the hypothesis `hX`), then its coordinate expression in the chart at a point
`x₀` -- the vector `X t (chart⁻¹ u)` read in the tangent-bundle trivialisation at `x₀` --
is smooth in `(t, u)` on `univ × (extChartAt I x₀).target`.

The proof reads the section `p ↦ ⟨p.2, X p.1 p.2⟩` in the tangent-bundle trivialisation at
`x₀` using `Bundle.Trivialization.contMDiffOn_iff` (a smoothness statement for a bundle
section can be read off in *any* trivialisation), rewrites the fibre coordinate as
`continuousLinearMapAt` on the base set, and then composes with the chart inverse
`q ↦ (q.1, (extChartAt I x₀).symm q.2)`.
-/

namespace Work.Diff.ODE

open Bundle Manifold ContDiff Set
open scoped Manifold ContDiff Bundle Topology

theorem chartField_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {X : ℝ → Π x : M, TangentSpace I x}
    (hX : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent
      ((⊤ : ENat) : WithTop ENat)
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (x₀ : M) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun p : ℝ × E ↦
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          ((extChartAt I x₀).symm p.2) (X p.1 ((extChartAt I x₀).symm p.2)))
      (Set.prod Set.univ (extChartAt I x₀).target) := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  set S : Set (ℝ × E) := Set.prod Set.univ (extChartAt I x₀).target with hS
  -- The section is smooth on the product of the time axis with the chart source.
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ((⊤ : ENat) : WithTop ENat)
      (fun p : ℝ × M => (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))
      (Set.prod Set.univ (chartAt H x₀).source) :=
    (hX.contMDiffOn (s := Set.univ)).mono (fun _ _ => trivial)
  have hmap : Set.MapsTo (fun p : ℝ × M => (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))
      (Set.prod Set.univ (chartAt H x₀).source) e.source := by
    intro p hp
    rw [Trivialization.mem_source]
    change p.2 ∈ e.baseSet
    rw [he, TangentBundle.trivializationAt_baseSet]
    exact hp.2
  -- Read it in the trivialisation at `x₀`.
  have hψ := (Trivialization.contMDiffOn_iff (e := e) hmap).mp hΦ
  -- Identify the fibre coordinate with `continuousLinearMapAt` on the base set.
  have hψ' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ((⊤ : ENat) : WithTop ENat)
      (fun p : ℝ × M => (e.continuousLinearMapAt ℝ p.2) (X p.1 p.2))
      (Set.prod Set.univ (chartAt H x₀).source) := by
    refine hψ.2.congr ?_
    intro p hp
    have hb : p.2 ∈ e.baseSet := by
      rw [he, TangentBundle.trivializationAt_baseSet]; exact hp.2
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hb (X p.1 p.2)
  -- The chart inverse as a map `ℝ × E → ℝ × M` is smooth on `univ × target`.
  have hG : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ((⊤ : ENat) : WithTop ENat)
      (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2)) S := by
    have hfst : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ((⊤ : ENat) : WithTop ENat)
        (fun q : ℝ × E => q.1) S :=
      (contDiffOn_fst (𝕜 := ℝ) (E := ℝ) (F := E) (s := S)).contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) I ((⊤ : ENat) : WithTop ENat)
        (fun q : ℝ × E => (extChartAt I x₀).symm q.2) S :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).comp
        ((contDiffOn_snd (𝕜 := ℝ) (E := ℝ) (F := E) (s := S)).contMDiffOn)
        (fun _ hq => hq.2)
    exact hfst.prodMk hsnd
  -- Compose.
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ((⊤ : ENat) : WithTop ENat)
      ((fun p : ℝ × M => (e.continuousLinearMapAt ℝ p.2) (X p.1 p.2)) ∘
        (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2))) S :=
    hψ'.comp hG (fun _ hq => by
      refine ⟨trivial, ?_⟩
      rw [← extChartAt_source I x₀]
      exact PartialEquiv.map_target (extChartAt I x₀) hq.2)
  -- Transfer to the coordinate expression of the statement.
  have h := (contMDiffOn_iff_contDiffOn (𝕜 := ℝ)).mp hcomp
  exact h.congr (fun _ _ => rfl)

end Work.Diff.ODE
