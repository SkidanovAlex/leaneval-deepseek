import Mathlib
import Submission.Work.ThomBordism.locClass_eq_frameSign_smul_chartTr
import Submission.Work.ThomBordism.chartTr_relHmapOf

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the push of a piece's local fundamental class along a chart-compatible map

`Work.ThomBordism.relHmapOf_locClass_eq_chartTr` is the *pushforward* form of
`Work.ThomBordism.locClass_eq_frameSign_smul_chartTr`: if a map `f : V.pt → Y` carries a chart
`e = (chartOf V i).1` of the closed oriented `8`-manifold `V` to a partial homeomorphism
`g : Y ⇀ ℝ⁸` (i.e. `g ∘ f = e` on `e.source`, `f` injective at `x`), then the image of the local
fundamental class of `V` at `x` under `f` is, up to the *universal* constant `c₀` of the chart
comparison times the chart sign `frameSign V i x`, the transfer along `g` of the Euclidean generator.

This is exactly the computation of the local class of the *transported* piece class: in the last mile
of `Work.ThomBordism.thomRational`, the collapse identification carries the piece `(Fam a).pt` into
the boundary of the level set, and `g` is the chart of the boundary part obtained by transporting the
piece's chart along it.  Combined with `Work.ThomBordism.locClass_sourceBoundaryClass_piece` it gives
the explicit constant

  `locClass ῆ y = (c₀ · frameSign) • chartTr g y (eucFam 8 _ (g y))`

for the boundary class `ῆ` of the pieces, i.e. it replaces the sign-blind constant of
`Work.ThomBordism.sourceBoundaryClass_localGenerator` by a computable one; the remaining per-piece
factor `frameSign` is exactly the factor carried by the coorientation of the level set (TEL,
`Work.ThomBordism.sigmaTelescope_gauss`), which is why the ratio of the two has a universal sign
(`Submission/Work/ThomBordism/NOTE_SESSION63.md`).

The proof is `locClass_eq_frameSign_smul_chartTr` (the chart form) followed by
`chartTr_relHmapOf` (the transfer along a chart-compatible map) and one cast.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric.HOF

/-- **The push of a piece's local fundamental class along a chart-compatible map.**

There is a universal `c₀ = ±1` (the constant of the chart comparison
`Work.ThomBordism.locClass_eq_frameSign_smul_chartTr`) such that for every closed oriented smooth
`8`-manifold `V`, every chart `i`, every `x ∈ src V i`, every map `f : V.pt → Y`, every partial
homeomorphism `g : Y ⇀ ℝ⁸` with `g ∘ f = (chartOf V i).1` on the chart source and `f` injective at
`x`, the image under `f` of the local fundamental class of `V` at `x` is `c₀ · frameSign` times the
`g`-transfer of the Euclidean generator. -/
theorem relHmapOf_locClass_eq_chartTr :
    ∃ c₀ : ℤ, (c₀ = 1 ∨ c₀ = -1) ∧
      ∀ (V : Work.ThomBordism.Man8) (i : Work.ThomBordism.FrameSigns.ChartIdx V) (x : V.pt)
        (hx : x ∈ Work.ThomBordism.FrameSigns.src V i)
        {Y : TopCat} [T1Space Y] (f : C(V.pt, Y))
        (g : OpenPartialHomeomorph Y (Euc 8)) (y : Y) (hy : y ∈ g.source)
        (hf : f x = y)
        (hgs : ∀ z, z ∈ (Work.ThomBordism.FrameSigns.chartOf V i).1.source → f z ∈ g.source)
        (hgc : ∀ z, z ∈ (Work.ThomBordism.FrameSigns.chartOf V i).1.source →
          g (f z) = (Work.ThomBordism.FrameSigns.chartOf V i).1 z)
        (hinj : ∀ z : V.pt, z ∉ ({x} : Set V.pt) → f z ∉ ({y} : Set Y)),
        RelHmapOf 8 (TopCat.ofHom f) ({x} : Set V.pt) ({y} : Set Y) hinj
            (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x)
          = (c₀ * (if 0 < Work.ThomBordism.FrameSigns.pairVal V i x hx then (1 : ℤ) else -1)) •
            chartTr (W := Y) g y hy (eucFam 8 (by norm_num) (g y)) := by
  classical
  obtain ⟨c₀, hc₀, hspec⟩ := Work.ThomBordism.locClass_eq_frameSign_smul_chartTr
  refine ⟨c₀, hc₀, ?_⟩
  intro V i x hx Y _ f g y hy hf hgs hgc hinj
  have hinj' : ∀ z : V.pt, z ≠ x → f z ≠ f x := by
    intro z hz h
    exact hinj z hz (by rw [h]; exact hf.symm ▸ rfl)
  have hpair0 : ∀ z : V.pt, z ∉ ({x} : Set V.pt) → f z ∉ ({f x} : Set Y) :=
    fun z hz h => hz (by_contra (fun hzx => hinj' z hzx h))
  subst hf
  rw [hspec V i x hx, map_zsmul]
  congr 1
  have hmain := chartTr_relHmapOf (N := 8) (by norm_num)
    (W := TopCat.of V.pt) (W' := Y)
    (Work.ThomBordism.FrameSigns.chartOf V i).1 g f x hx hgs hgc hinj'
  rw [show RelHmapOf 8 (TopCat.ofHom f) ({x} : Set V.pt) ({f x} : Set Y) hinj
        (chartTr (W := TopCat.of V.pt) (Work.ThomBordism.FrameSigns.chartOf V i).1 x hx
          (eucFam 8 (by norm_num) ((Work.ThomBordism.FrameSigns.chartOf V i).1 x)))
      = RelHmapOf 8 (TopCat.ofHom f) ({x} : Set V.pt) ({f x} : Set Y) hpair0
        (chartTr (W := TopCat.of V.pt) (Work.ThomBordism.FrameSigns.chartOf V i).1 x hx
          (eucFam 8 (by norm_num) ((Work.ThomBordism.FrameSigns.chartOf V i).1 x))) from
    LinearMap.congr_fun (RelHmapOf_congr rfl hinj hpair0) _]
  exact hmain

end

end Work.ThomBordism
