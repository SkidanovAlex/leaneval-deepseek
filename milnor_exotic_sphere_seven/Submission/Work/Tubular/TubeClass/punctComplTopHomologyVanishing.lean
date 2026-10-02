import Mathlib
import Submission.Work.Tubular.TubeClass.Core
import Submission.Work.Tubular.TubeClass.ComplPointMan8
import Submission.Work.Tubular.PuncturedDiscPair.punctComplTopHomologyVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Tubular.TubeClass

/-!
# Vanishing of the top homology of `ν⁺ ∖ {x₀}`

**Status.**  This is the "geometric input `hA`" of the tubular chapter's item (B2)
(`Work.Tubular.TubeClass.Core`): it is the injection half of the reconstruction of the
Pontryagin–Thom collapse class (`Work.Tubular.TubeClass.Reduction`,
`Submission/Work/Tubular/tubeCollapseClass_span_top.lean`).

**What is proved here.**

* `Submission/Work/Tubular/TubeClass/ComplPointMan8.lean`:
  `H_8(V.pt ∖ {v₀}) = 0` for a connected `Man8` `V` (from the *given* fundamental class `Man8.c`,
  via the long exact sequence of the pair `(V.pt, V.pt∖{v₀})` and the "one point suffices"
  theorem `Work.Orient.eq_zero_of_locClass_eq_zero_at`).  This is the `k = 0` case of the
  phenomenon, and it is the model of the general statement.

**The remaining reduction** (to be assembled here).  With `A := {p : ν⁺ // p ∉ zero section}`
(the complement of the zero section, `Work.Tubular.onePointNonzero`, contractible), the long exact
sequence of the pair `(ν⁺, A)` and `Work.Cohomology.excision` give

  `H_{8+k}(ν⁺ ∖ {x₀}) ≅ H_{8+k}(Y, Y∖W)`,

where `Y = {p : ν // p ≠ x₀, ‖p‖ < 1}` is the punctured open unit disc bundle of `ν` and
`W = {p : Y // 0 < ‖p‖}` its complement of the zero section.  For `k ≥ 1` the vanishing of
`H_{8+k}(Y,W)` is exactly the statement that the relative fundamental class of the disc-bundle pair
localises non-trivially at `x₀` — the "local degree is one" statement for the Thom space, i.e. the
same geometric content as the second missing input `localisationCollapseClassSpanTop` of
`Submission/Work/Tubular/TubeClass/TempInputs.lean`.  It is *not* a consequence of dimension alone:
in the model case `V = pt`, `ν = ℝ^k` one has `ν⁺ = S^k`, `x₀ = 0` and the claim is `H_k(S^k∖0) = 0`,
which is true but needs `S^k` to be a *manifold*, unavailable for the general Thom space.
The two routes recorded in the docstring of the delegated lemma
`Submission.Work.Tubular.PuncturedDiscPair.puncturedDiscBundlePair_vanishing` are (i) via the
fundamental class `Man8.c` and naturality of the localisation along the zero section, and (ii) by
dualising the *proved* fibre-wise generation of the local Thom class
(`Work.Tubular.localThomOfChart_fibre_span_top`) through `Work.Tubular.exists_relKronH_eval_iso`.

For `k = 0` the pair `(Y,W)` is `(ν∖{x₀}, ∅)`, and the claim reduces to
`H_8(ν∖{x₀}) ≅ H_8(V.pt∖{v₀}) = 0` (`Work.Tubular.TubeClass.isZero_homology_compl_point_man8`),
via the homeomorphism `NormalTotal E ≃ₜ V.pt` of a `0`-codimensional normal bundle.
-/

theorem punctComplTopHomologyVanishing {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Tubular.PunctCompl E v₀))).homology (8 + k)) :=
  Work.Tubular.PuncturedDiscPair.punctComplTopHomologyVanishing E v₀

end Work.Tubular.TubeClass
