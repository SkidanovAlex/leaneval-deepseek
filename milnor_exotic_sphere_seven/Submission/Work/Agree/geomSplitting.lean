import Mathlib
import Submission.Work.Agree.crux
import Submission.Work.Agree.mapFibreIso
import Submission.Work.Agree.plumbChain
import Submission.Work.Agree.whitneySumRAssoc
import Submission.Work.Agree.complexificationIso
import Submission.Work.Agree.chernClassPeel
import Submission.Work.Agree.clutchStable
import Submission.Work.Agree.modelTransfer
import Submission.Work.Agree.tangentRestriction
import Submission.Work.Agree.sphereStableTrivial
import Submission.Work.Agree.plumb
import Submission.Work.Agree.geometryB
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Gen.TangentPresentation
import Submission.Work.Gen.cp4ChernPresentation
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The geometric half of the AREA AGREE: `GeometryB → GeomSplitting`

This file proves `Work.Agree.geomSplitting`: from the geometric input `GeometryB` (the tangent
bundle of the disc bundle `D(ξ) = Vk (-2)` splits, in the two-chart presentation, as the pullback
along `π : D(ξ) → S⁴` of `TS⁴ ⊕ ξ = L¹R¹ ⊕ L²R⁻¹`), the second Chern class of the pulled-back
complexified tangent bundle of `X = D(ξ) ∪_F D⁸` is ± the pullback of the second Chern class of
`ξ ⊗_ℝ ℂ`.

The proof is the bookkeeping of the chain

`restrictedC2 = c₂(ℂ(TX|_{D(ξ)}))`  (plumbing, model transfer, tangent restriction; `plumbChain`)
`= c₂(ℂ(π^*(TS⁴ ⊕ ξ)))`           (Geometry B)
`= c₂(ℂ(π^*(ξ ⊕ ε⁴)))`            (stable triviality of `TS⁴ = L¹R¹`, `Work.Agree.clutchStable`)
`= π^*(c₂(ℂ ξ))`                   (stability of the Chern classes, `Work.Agree.chernClassPeel`)

together with the naturality of `chernClass` under pullback and bundle isomorphisms.

The fleet of lemmas this rests on (all in `Submission/Work/Agree/`):

* `plumbChain` (a copy of `Work.Agree.restrictedC2Plumb`, needed here because the original lives
  downstream of this file) — the plumbing;
* `Work.Agree.whitneySumRAssoc`, `Work.Agree.whitneySumRRotate` — associativity of `whitneySumR`;
* `Work.Agree.whitneySumRComm` — commutativity of `whitneySumR`;
* `Work.Agree.whitneySumRCongr` — congruence of `whitneySumR`;
* `Work.Agree.chernClass_complexificationCore_eq'` — isomorphism-invariance, across ranks;
* `Work.Agree.chernClassPeel` — stability of the Chern classes under trivial summands;
* `Work.Agree.clutchStable` — `TS⁴ ⊕ ε¹ ≅ ε⁵`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The key computation over `S⁴` -/

/-- **The stable triviality of `L¹R¹` makes it invisible in `c₂`.**  Over `S⁴`,
`c₂(ℂ(L¹R¹ ⊕ L²R⁻¹)) = c₂(ℂ(L²R⁻¹))`: the summand `L¹R¹ = TS⁴` is stably trivial
(`Work.Agree.clutchStable`), so it contributes nothing to the second Chern class. -/
theorem chernClass_whitneySumR_clutch :
    Work.Thom.chernClass 8 2
        (Work.Thom.complexificationCore
          (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
            (Work.Agree.clutchBundle (2 : ℤ) (-1))))
      = Work.Thom.chernClass 4 2
          (Work.Thom.complexificationCore (Work.Agree.clutchBundle (2 : ℤ) (-1))) := by
  -- `L¹R¹ ⊕ ε¹` is trivial of rank `5`
  have hAe : Nonempty (Work.Thom.BundleIso
      (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
        (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 1)) (Fin 1)))
      (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 5)) (Fin 1))) := by
    obtain ⟨c1⟩ := whitneySumR_sum_iso (Work.Agree.clutchBundle (1 : ℤ) 1)
      (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 1)) (Fin 1))
    obtain ⟨c2⟩ := Work.Agree.clutchStable (Fin 1) (Fin 1)
    exact ⟨c1.trans c2⟩
  -- add one trivial line to `L¹R¹ ⊕ L²R⁻¹`
  have s1 : Work.Thom.chernClass (4 + 4) 2
        (Work.Thom.complexificationCore
          (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
            (Work.Agree.clutchBundle (2 : ℤ) (-1))))
      = Work.Thom.chernClass ((4 + 4) + 1) 2
          (Work.Thom.complexificationCore
            (Work.Whitney.whitneySumR
              (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
                (Work.Agree.clutchBundle (2 : ℤ) (-1)))
              (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 1)) (Fin 1)))) :=
    (Work.Whitney.chernClass_complexification_whitneySumR_trivial (ι₀ := Fin 1)
      (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
        (Work.Agree.clutchBundle (2 : ℤ) (-1))) 2).symm
  -- rotate the trivial summand past `L²R⁻¹`
  have s2 : Work.Thom.chernClass ((4 + 4) + 1) 2
        (Work.Thom.complexificationCore
          (Work.Whitney.whitneySumR
            (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
              (Work.Agree.clutchBundle (2 : ℤ) (-1)))
            (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 1)) (Fin 1))))
      = Work.Thom.chernClass (4 + 5) 2
          (Work.Thom.complexificationCore
            (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (2 : ℤ) (-1))
              (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 5)) (Fin 1)))) := by
    obtain ⟨e1⟩ := whitneySumRRotate (Work.Agree.clutchBundle (1 : ℤ) 1)
      (Work.Agree.clutchBundle (2 : ℤ) (-1))
      (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 1)) (Fin 1))
    obtain ⟨e2⟩ := whitneySumRCongr
      (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
        (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 1)) (Fin 1)))
      (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 5)) (Fin 1))
      (Work.Agree.clutchBundle (2 : ℤ) (-1)) (Work.Agree.clutchBundle (2 : ℤ) (-1))
      hAe ⟨Work.Thom.BundleIso.refl _⟩
    obtain ⟨e3⟩ := whitneySumRComm
      (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 5)) (Fin 1))
      (Work.Agree.clutchBundle (2 : ℤ) (-1))
    have hiso : Nonempty (Work.Thom.BundleIso
        (Work.Whitney.whitneySumR
          (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
            (Work.Agree.clutchBundle (2 : ℤ) (-1)))
          (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 1)) (Fin 1)))
        (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (2 : ℤ) (-1))
          (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 5)) (Fin 1)))) :=
      ⟨e1.trans (e2.trans e3)⟩
    exact chernClass_complexificationCore_eq' (by norm_num : (4 + 4) + 1 = 4 + 5)
      _ _ hiso 2
  -- peel the five trivial summands back off
  have s3 : Work.Thom.chernClass (4 + 5) 2
        (Work.Thom.complexificationCore
          (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (2 : ℤ) (-1))
            (trivialVectorBundleCore ℝ S4 (EuclideanSpace ℝ (Fin 5)) (Fin 1))))
      = Work.Thom.chernClass 4 2
          (Work.Thom.complexificationCore (Work.Agree.clutchBundle (2 : ℤ) (-1))) :=
    chernClassPeel 5 2 (by norm_num) (Work.Agree.clutchBundle (2 : ℤ) (-1))
  exact s1.trans (s2.trans s3)

/-! ## The target -/

/-- **`geomSplitting`** — the geometric/plumbing half of the AREA AGREE: from the geometric input
`GeometryB` (the splitting of the tangent bundle of the disc bundle), the second Chern class of the
pulled-back complexified tangent bundle of `X = D(ξ) ∪_F D⁸` is ± the pullback along `π` of the
second Chern class of `ξ ⊗_ℝ ℂ`. -/
theorem geomSplitting (hB : Work.Agree.GeometryB) : Work.Agree.GeomSplitting := by
  intro F hF
  left
  have hL : Work.Thom.chernClass 8 2
        (Work.Thom.complexificationCore
          (Work.Thom.bundleComap
            (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
              (Work.Agree.clutchBundle (2 : ℤ) (-1)))
            Work.TangentClasses.discProj))
      = (Work.Thom.CohMap Work.TangentClasses.discProj ℤ 4).hom
          (Work.Thom.chernClass 8 2
            (Work.Thom.complexificationCore
              (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
                (Work.Agree.clutchBundle (2 : ℤ) (-1))))) := by
    rw [Work.Thom.complexificationCore_bundleComap]
    rw [Work.Thom.chernClass_comap]
  have hR : (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom Work.Agree.xiC2
      = (Work.Thom.CohMap Work.TangentClasses.discProj ℤ 4).hom
          (Work.Thom.chernClass 4 2
            (Work.Thom.complexificationCore (Work.Agree.clutchBundle (2 : ℤ) (-1)))) :=
    rfl
  rw [Work.Agree.plumbChain hB F hF, hL, hR]
  exact congrArg (fun c => (Work.Thom.CohMap Work.TangentClasses.discProj ℤ 4).hom c)
    chernClass_whitneySumR_clutch

end

end Work.Agree
