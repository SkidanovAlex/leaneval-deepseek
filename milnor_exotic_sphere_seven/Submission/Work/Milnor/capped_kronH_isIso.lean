import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Milnor.homology_capped_compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Kronecker pairing of the capped space `X = D(ξ) ∪_F D⁸` is an isomorphism

`Work.Cohomology.kronH_isIso` shows that for any space `X` whose integral singular homology is
degreewise free, the Kronecker evaluation

`Hⁿ(X) → Hom(Hₙ(X), ℤ)`

is a bijection.  The homology of the closed `8`-manifold `X = D(ξ) ∪_F D⁸` is computed in
`Work.Milnor.homology_capped_datum`: `Hₙ(X) ≅ ℤ` for `n ∈ {0, 4, 8}` and `0` otherwise, hence
degreewise free.  This gives the Kronecker isomorphism for the capped space.
-/

namespace Work.Milnor

noncomputable section

/-- The integral singular homology of the capped space `X = D(ξ) ∪_F D⁸` is degreewise free:
`Hₙ(X) ≅ ℤ` for `n ∈ {0, 4, 8}` and `0` otherwise. -/
lemma free_homology_capped (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    ∀ n, Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology n) := by
  intro n
  obtain ⟨e⟩ := Work.Milnor.homology_capped_datum F hF n
  exact Module.Free.of_equiv (Work.Cohomology.redH0_linEquivOfIso e.symm)

theorem capped_kronH_isIso (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) (n : ℕ) :
    Function.Bijective (fun α : ↥((Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology n) =>
      Work.Cohomology.kronH ℤ
        (TopCat.toSSet.obj (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))) n α) :=
  Work.Cohomology.kronH_isIso
    (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
    (free_homology_capped F hF) n

end

end Work.Milnor
