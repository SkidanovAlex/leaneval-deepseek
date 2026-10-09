import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.nonempty_galois_completion_equiv
import Submission.Work.LocalFields.completion_algebraMap_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

/-- **The image of the algebra structure map `K_v → L_w` does not depend on the structure.**

Let `σ := φ.algebraMap : K_v →+* L_w` be the structure map.  By the scalar tower `σ` agrees
with the canonical map `ρ := CompletionHom.ringHom v w` on the image of `K`, which is dense in
`K_v` (`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`).  The local-field content is
that `σ` is *continuous* (`Work.LocalFields.completion_algebraMap_continuous`, proved from the
rigidity of local fields under `n`-th powers, which is `Hensel` in disguise): indeed
`v_{L_w}(σ x) = v_{K_v}(x)^{e(w/v)}` for all `x ∈ K_v`, so `σ` is bounded on neighbourhoods of
`0`.  Two continuous maps into the Hausdorff space `L_w` that agree on a dense set are equal,
so `σ = ρ`, and therefore their ranges agree. -/
theorem completion_algebra_range_eq {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [φ : Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)] :
    Set.range φ.algebraMap = Set.range (Work.LocalFields.CompletionHom.ringHom v w) := by
  have hcont : Continuous (φ.algebraMap : Completion K v → Completion L w) :=
    completion_algebraMap_continuous (K := K) (L := L) v w
  have hfun : (φ.algebraMap : Completion K v → Completion L w) =
      ⇑(CompletionHom.ringHom v w) := by
    refine DenseRange.equalizer
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v)
      hcont (CompletionHom.continuous_ringHom v w) ?_
    funext y
    show φ.algebraMap (algebraMap K (Completion K v) y) =
      CompletionHom.ringHom v w (algebraMap K (Completion K v) y)
    rw [← IsScalarTower.algebraMap_apply K (Completion K v) (Completion L w) y,
      CompletionHom.ringHom_algebraMap]
  rw [show φ.algebraMap = CompletionHom.ringHom v w from RingHom.ext fun x => congrFun hfun x]

end Work.LocalFields
