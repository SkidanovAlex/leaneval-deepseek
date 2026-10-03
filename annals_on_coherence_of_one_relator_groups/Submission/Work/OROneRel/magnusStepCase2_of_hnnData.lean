import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv

/-!
# The Magnus step from HNN data over the vertex subgroup

`Work.OROneRel.magnusStepCase2_of_hnnData` is the *assembly* half of the residual case of the
Magnus--Moldavanskii step `Work.OROneRel.magnusStepCase2`: it takes the vertex subgroup
`H ≤ G = ⟨α | u ^ l⟩`, an isomorphism `ψ` identifying it with the one-relator group
`⟨β | v ^ l⟩` (subject to the root-tracking condition `ψ (mk v) = mk u`), and an isomorphism
`e : HNNExtension ↥H A B φ ≃* G` whose restriction to the base `↥H` is the inclusion
(`e (of h) = h`), and produces the conclusion of the target: an isomorphism
`G ≃* HNNExtension (⟨β | v ^ l⟩) A' B' φ'` sending `mk u` to the stable generator `of (mk v)` up to
conjugation.

Everything else about the residual case -- the norm bound `relatorNorm v < relatorNorm u`, the
`¬ IsProperPower v` condition, the construction of the `ℤ`-domain, the identification
`π₁(D) ≅ ⟨β | v ^ l⟩` and the HNN structure of the `ℤ`-cover (Linton, *One-relator hierarchies*,
Prop. 4.3/2.2.19) -- is *not* part of this file: it supplies the hypotheses.  This file is the
transport bookkeeping, which is independent of how the HNN structure is obtained (in particular it
does not depend on the telescoping/meet-condition route, which is now known to be insufficient: see
`Submission/Work/OROneRel/NOTES_meet_conditions_insufficient.md`).

The proof is the standard transport of an HNN extension along an isomorphism of its base
(`Work.OROneRel.hnnExtension_iso_of_baseMulEquiv`) together with the root tracking: the class of `u`
is the image of the class of `v` under `ψ` in `G`, so it corresponds to `of (mk v)`.
-/

namespace Work.OROneRel

universe u

theorem magnusStepCase2_of_hnnData {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (β : Type u) (v : FreeGroup β)
    (hpp : ¬ Work.OROneRel.IsProperPower v)
    (hnorm : Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u)
    (H : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α))))
    (ψ : PresentedGroup ({v ^ l} : Set (FreeGroup β)) ≃* ↥H)
    (hψ : ((ψ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) : ↥H)
        : PresentedGroup ({u ^ l} : Set (FreeGroup α))) = PresentedGroup.mk ({u ^ l}) u)
    (A B : Subgroup ↥H) (φ : A ≃* B)
    (e : HNNExtension ↥H A B φ ≃* PresentedGroup ({u ^ l} : Set (FreeGroup α)))
    (he : ∀ h : ↥H, e (HNNExtension.of (φ := φ) h) = ((h : ↥H) : PresentedGroup ({u ^ l}))) :
    ∃ (A' B' : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ' : A' ≃* B')
      (e' : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A' B' φ'),
      ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A' B' φ',
        e' (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
          c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  -- transport the HNN structure along `ψ⁻¹`
  obtain ⟨A', B', φ', Ĥ, -, -, hof, -⟩ :=
    hnnExtension_iso_of_baseMulEquiv ψ.symm A B φ
  refine ⟨A', B', φ', e.symm.trans Ĥ, 1, ?_⟩
  -- the class of `u` is the image of the class of `v`
  have hsymm : e.symm (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
      HNNExtension.of (ψ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v)) := by
    have h := he (ψ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v))
    rw [hψ] at h
    rw [← h, MulEquiv.symm_apply_apply]
  rw [MulEquiv.trans_apply, hsymm, hof]
  simp

end Work.OROneRel
