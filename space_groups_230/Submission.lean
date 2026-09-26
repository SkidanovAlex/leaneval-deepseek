import ChallengeDeps
import Submission.Helpers
import Submission.Work.SG.encard_classes_eq
import Submission.Work.SG.affEquiv_facts
import Submission.Work.SG.sg_data_facts
import Submission.Work.SG.classification

open LeanEval.Geometry.SpaceGroupsProblem
open Work.SG

namespace Submission

theorem space_groups :
    crystallographicCountOP 3 = 230 ∧
      crystallographicCount 3 = 219 ∧
        crystallographicCountOPOnly 3 = 65 := by

  obtain ⟨G, hcov, hop, haff, hsoh⟩ := classification
  obtain ⟨hAeq, hOPeq, hpres⟩ := affEquiv_facts 3
  obtain ⟨-, -, hsurj, hcard⟩ := sg_data_facts
  have aff_of_op : ∀ {G₁ G₂ : Subgroup (EuclideanIsom 3)}, AffOPEquivalent G₁ G₂ →
      AffinelyEquivalent G₁ G₂ := fun ⟨φ, _, h⟩ => ⟨φ, h⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := encard_classes_eq hOPeq G id Function.surjective_id hcov
      (fun k l => by simpa using hop k l)
    simpa [crystallographicCountOP] using h
  · have h := encard_classes_eq hAeq G sgAffClass hsurj
      (fun x => (hcov x).imp fun k hk => aff_of_op hk) haff
    simpa [crystallographicCount] using h
  · let K : Set (Fin 230) := {k | ∀ A ∈ arithRep (sgArith k), A.det = 1}
    let X := {G : CrystallographicGroup 3 // ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g}
    let G' : K → X := fun k => ⟨G k.1, fun g hg => (hsoh k.1).2 k.2 g hg⟩
    have hr : Equivalence (fun a b : X => AffOPEquivalent a.1.1 b.1.1) :=
      ⟨fun a => hOPeq.refl a.1, fun h => hOPeq.symm h, fun h h' => hOPeq.trans h h'⟩
    have hcov' : ∀ x : X, ∃ k : K, AffOPEquivalent (G' k).1.1 x.1.1 := by
      intro x
      obtain ⟨k, hk⟩ := hcov x.1
      have hkK : k ∈ K := (hsoh k).1 (hpres _ _ (aff_of_op (hOPeq.symm hk)) x.2)
      exact ⟨⟨k, hkK⟩, hk⟩
    have hsep' : ∀ k l : K, AffOPEquivalent (G' k).1.1 (G' l).1.1 ↔ id k = id l := by
      intro k l
      rw [hop, id, id, Subtype.ext_iff]
    have h := encard_classes_eq hr G' id Function.surjective_id hcov' hsep'
    rw [Nat.card_coe_set_eq, hcard] at h
    unfold crystallographicCountOPOnly
    exact_mod_cast h

end Submission
