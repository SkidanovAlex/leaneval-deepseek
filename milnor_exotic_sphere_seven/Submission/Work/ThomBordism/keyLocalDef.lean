import Mathlib
import Submission.Work.ThomBordism.ambientFibreComparison
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.tautologicalBundleHoriO

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.KeyLocal`: the local comparison of the canonical class with the chart model class

This file records the **key local statement (KL)** of the last mile, exactly as specified by the
project lead (probe 48).  It is the *per-datum*, sign-uniform comparison

  `π^*(w) ⌣ Ucan = s • ambientValueClass E C x`   (`s = ±1` a *single* sign for all data),

for every degree-`8` class `w` of the normal total space with `⟨(zeroSection)^* w, V.c⟩ = 1`, where

* `Ucan = gtdUWith E ND G hgm (realThomClassOf hk (tautologicalBundle k 10) horiO)` is the pullback
  of the **canonical** (chart-constructed) Thom class of the tautological oriented bundle, and
* `ambientValueClass E C x = chartModelClass E C x _` is the pullback of the determinate standard
  generator `stdModelGen (8+k)` of `(ℝ^{8+k}, ℝ^{8+k}∖0)` along the capped ambient chart
  `p ↦ chartAffine E x (cap E ε p)`.

## Why it is true (the lead's plan, (i)–(v))

(i) `H⁸(V;ℤ) ≅ ℤ` with the pairing against `V.c`, so `w` is *unique*; it suffices to test one good
`w`, namely `w₀ := π^*(image of the local generator o_x ∈ H⁸(V, V∖x) dual to the localisation of
V.c)`, for which `⟨z^* w₀, V.c⟩ = 1` by naturality.
(ii) `w₀ ⌣ Ucan` is the image of the relative–relative cup
`π^*(o_x) ⌣ Ucan ∈ H^{8+k}(ν, π⁻¹(V∖x) ∪ (ν∖0)) = H^{8+k}(ν, ν∖{p})`, `p = (x,0)`.
(iii) `ambientValueClass E C x` is also the image of a class of `H^{8+k}(ν, ν∖p)` (the pullback of
`stdModelGen (8+k)` along `φ = y ↦ cap y − e x`, which is nonzero away from `p` near `p`), and the
map `H^{8+k}(ν, ν∖p) → H^{8+k}(ν, ν∖0)` is injective (`localisation_injective_zeroSection`,
`relH_localisation_injective_normalTotal`), so it suffices to compare the two *local* classes at `p`.
(iv) Excise to a product neighbourhood `N ≅ B⁸ × ℝ^k` of `p` given by a `V`-chart at `x` plus the
`ND` trivialisation.  There, `π^*(o_x) ⌣ Ucan` is `(o_x|_B) × (fibre class)`, and the fibre class
is `coorFibre` read in `gframe` (`nfRes_gtdUWith_realThomClassOf_eq_coorFibre`, `B` contractible).
A cross product of local generators is the pullback of the standard generator along the product
chart, up to a fixed convention sign `c_{8,k}`.
(v) The germ of `φ` at `p` against the product chart has linear part
`(tangent frame oriented by V.c) ⊕ gframe → ℝ^{8+k}`, whose determinant sign is
`pairSign (flipTan E i x (frameSign V i.1 x)) (gframe E ND i x)`, equal to `1` by the PROVED
`Work.ThomBordism.sigmaTelescope_gauss`.  Hence `s = c_{8,k}` is uniform.

## Consequences

`KeyLocal k hk` gives (P2) (`coorFibre_fibreGenerator`, H4-L2678) by applying the `z`-hypothesis at
`U := Ucan` and using `AmbientUniform` (now unconditional, from the PROVED
`collapseLocalisation_ambientV2`), and hence the canonical Gauss sign statement — with **no**
`AmbientFibreLink` needed (the link is what the circle was made of).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory


/-! **Module split note (session 53).**  The *definition* `Work.ThomBordism.KeyLocal` lives here, in its
own module, because `keyLocal.lean` must import its own proof (`keyLocalProof.lean`), which in turn
imports the modules that use the definition.  The theorem `Work.ThomBordism.keyLocal` is still
declared in `keyLocal.lean`, which imports this file, so every existing importer of `keyLocal.lean`
(and hence of this module) sees the same names as before. -/

namespace Work.ThomBordism

noncomputable section

/-- **The key local statement (KL)**: for every datum and every degree-`8` class `w` of the normal
total space with `⟨(zeroSection)^* w, V.c⟩ = 1`, the cup product of `w` with the canonical Thom
class `Ucan` equals a *single* sign `s = ±1` times the ambient chart model class. -/
def KeyLocal (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
      (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E))),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 →
      Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w
          (Work.ThomBordism.gtdUWith E ND G hgm
            (Work.Thom.realThomClassOf hk
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.tautologicalBundle_horiO k)))
        = s • Work.ThomBordism.ambientValueClass E C x

end

end Work.ThomBordism
